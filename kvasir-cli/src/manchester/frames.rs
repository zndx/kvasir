//! The Manchester DOCUMENT layer: prefixes, frames, sections.
//!
//! Line-structured scanner (frame headers at column 0, sections inline or indented,
//! section bodies may continue across indented lines — parens/braces spanning lines
//! work because bodies accumulate as text and parse through the real expression
//! grammar, not per-line regexes). This is the layer the OxiRS reference lacks; the
//! expression layer beneath it is the part they materialized.
//!
//! Containment posture: an unparseable SECTION becomes a [`ParseIssue`] and the rest
//! of the document proceeds; nothing is skipped silently.

use super::expr;
use super::lexer::{tokenize, Token};
use super::{DisjointBlock, Document, Frame, FrameKind, ParseIssue, Section};

const FRAME_KINDS: &[(&str, FrameKind)] = &[
    ("Class", FrameKind::Class),
    ("ObjectProperty", FrameKind::ObjectProperty),
    ("DataProperty", FrameKind::DataProperty),
    ("AnnotationProperty", FrameKind::AnnotationProperty),
    ("Datatype", FrameKind::Datatype),
    ("Individual", FrameKind::Individual),
];

/// Sections whose bodies parse as expression lists.
const EXPR_SECTIONS: &[&str] = &[
    "SubClassOf",
    "EquivalentTo",
    "DisjointWith",
    "Domain",
    "Range",
    "Types",
];

/// Sections we recognize (so the inline scanner can split on them) but whose bodies
/// the v0 lowering only COUNTS — recorded by keyword, routed at lowering.
const OTHER_SECTIONS: &[&str] = &[
    "Annotations",
    "SubPropertyOf",
    "Characteristics",
    "InverseOf",
    "HasKey",
    "Facts",
    "SameAs",
    "DifferentFrom",
    "EquivalentProperties",
    "DisjointProperties",
    "DisjointUnionOf",
    "SubPropertyChain",
];

fn section_keyword(word: &str) -> bool {
    EXPR_SECTIONS.contains(&word) || OTHER_SECTIONS.contains(&word)
}

fn strip_angles(tok: &str) -> String {
    tok.trim_start_matches('<').trim_end_matches('>').to_string()
}

/// Split `text` into `(keyword, body)` segments on word-boundary `Keyword:` markers.
/// The leading segment (before any keyword) is returned separately.
fn split_inline_sections(text: &str) -> (String, Vec<(String, String)>) {
    let mut segments: Vec<(String, String)> = Vec::new();
    let mut lead = String::new();
    let mut cur_kw: Option<String> = None;
    let mut cur_body = String::new();
    for word in text.split_whitespace() {
        let is_kw = word
            .strip_suffix(':')
            .filter(|w| section_keyword(w))
            .map(str::to_string);
        if let Some(kw) = is_kw {
            if let Some(k) = cur_kw.take() {
                segments.push((k, cur_body.trim().to_string()));
            } else {
                lead = cur_body.trim().to_string();
            }
            cur_body = String::new();
            cur_kw = Some(kw);
        } else {
            cur_body.push(' ');
            cur_body.push_str(word);
        }
    }
    if let Some(k) = cur_kw {
        segments.push((k, cur_body.trim().to_string()));
    } else {
        lead = cur_body.trim().to_string();
    }
    (lead, segments)
}

/// Accumulating parse state: one pending section body awaiting flush.
struct Pending {
    keyword: String,
    line: usize,
    body: String,
}

struct Scanner {
    doc: Document,
    issues: Vec<ParseIssue>,
    frame: Option<Frame>,
    pending: Option<Pending>,
}

impl Scanner {
    fn flush_pending(&mut self) {
        let Some(p) = self.pending.take() else { return };
        let Some(frame) = self.frame.as_mut() else {
            self.issues.push(ParseIssue {
                line: p.line,
                context: p.keyword,
                message: "section outside any frame".into(),
            });
            return;
        };
        if p.keyword == "Annotations" {
            parse_annotations(&p.body, p.line, frame, &mut self.issues);
        } else if EXPR_SECTIONS.contains(&p.keyword.as_str()) {
            match expr::parse_list(&p.body) {
                Ok(items) => frame.sections.push(Section {
                    keyword: p.keyword,
                    line: p.line,
                    items,
                }),
                Err(e) => self.issues.push(ParseIssue {
                    line: p.line,
                    context: format!("{}: {}", frame.subject, p.keyword),
                    message: e.to_string(),
                }),
            }
        } else {
            // recognized-but-unlowered section: recorded keyword-only (routed at lowering)
            frame.sections.push(Section {
                keyword: p.keyword,
                line: p.line,
                items: Vec::new(),
            });
        }
    }

    fn flush_frame(&mut self) {
        self.flush_pending();
        if let Some(f) = self.frame.take() {
            self.doc.frames.push(f);
        }
    }

    fn begin_sections(&mut self, segments: Vec<(String, String)>, line: usize) {
        for (kw, body) in segments {
            self.flush_pending();
            self.pending = Some(Pending {
                keyword: kw,
                line,
                body,
            });
        }
    }
}

/// Parse `prop "literal", prop "literal", …` into a frame's annotations.
fn parse_annotations(body: &str, line: usize, frame: &mut Frame, issues: &mut Vec<ParseIssue>) {
    let toks = match tokenize(body) {
        Ok(t) => t,
        Err(e) => {
            issues.push(ParseIssue {
                line,
                context: format!("{}: Annotations", frame.subject),
                message: e.to_string(),
            });
            return;
        }
    };
    let mut i = 0usize;
    while i < toks.len() {
        match (&toks[i].0, toks.get(i + 1).map(|t| &t.0)) {
            (Token::Ident(p) | Token::Iri(p), Some(Token::Str(s))) => {
                frame.annotations.push((p.clone(), s.clone()));
                i += 2;
            }
            (Token::Comma, _) => i += 1,
            (Token::Eof, _) => break,
            (other, _) => {
                issues.push(ParseIssue {
                    line,
                    context: format!("{}: Annotations", frame.subject),
                    message: format!("non-string annotation value near {other} (skipped)"),
                });
                // resync to the next comma
                while i < toks.len()
                    && !matches!(toks[i].0, Token::Comma | Token::Eof)
                {
                    i += 1;
                }
            }
        }
    }
}

/// Parse a whole Manchester document. Returns the document plus per-section issues
/// (loud containment — see the module posture).
pub fn parse_document(text: &str) -> (Document, Vec<ParseIssue>) {
    let mut sc = Scanner {
        doc: Document::default(),
        issues: Vec::new(),
        frame: None,
        pending: None,
    };

    for (i, raw) in text.lines().enumerate() {
        let line_no = i + 1;
        let trimmed = raw.trim();
        if trimmed.is_empty() {
            continue;
        }
        let at_col0 = !raw.starts_with(' ') && !raw.starts_with('\t');

        if at_col0 {
            // ── column-0 constructs ────────────────────────────────────────────
            if let Some(rest) = trimmed.strip_prefix("Prefix:") {
                sc.flush_frame();
                let rest = rest.trim();
                if let Some((name, uri_part)) = rest.split_once('<') {
                    let prefix = name.trim().to_string(); // "sdg:" or ":" (default)
                    let uri = uri_part.trim_end().trim_end_matches('>').to_string();
                    if !prefix.is_empty() {
                        sc.doc.prefixes.push((prefix, uri));
                    }
                } else {
                    sc.issues.push(ParseIssue {
                        line: line_no,
                        context: "Prefix".into(),
                        message: "malformed prefix declaration".into(),
                    });
                }
                continue;
            }
            if trimmed.starts_with("Ontology:") || trimmed.starts_with("Import:") {
                sc.flush_frame();
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix("DisjointClasses:") {
                sc.flush_frame();
                match expr::parse_list(rest) {
                    Ok(items) => {
                        let mut atoms = Vec::new();
                        for it in &items {
                            if let super::Expr::Named(n) = it {
                                atoms.push(n.clone());
                            } else {
                                sc.issues.push(ParseIssue {
                                    line: line_no,
                                    context: "DisjointClasses".into(),
                                    message: "non-atomic member (skipped)".into(),
                                });
                            }
                        }
                        sc.doc.disjoint_blocks.push(DisjointBlock {
                            line: line_no,
                            atoms,
                        });
                    }
                    Err(e) => sc.issues.push(ParseIssue {
                        line: line_no,
                        context: "DisjointClasses".into(),
                        message: e.to_string(),
                    }),
                }
                continue;
            }
            let frame_kind = FRAME_KINDS.iter().find_map(|(kw, kind)| {
                trimmed
                    .strip_prefix(kw)
                    .and_then(|r| r.strip_prefix(':'))
                    .map(|rest| (*kind, rest.trim()))
            });
            if let Some((kind, rest)) = frame_kind {
                sc.flush_frame();
                let mut parts = rest.splitn(2, char::is_whitespace);
                let subject_tok = parts.next().unwrap_or("");
                if subject_tok.is_empty() {
                    sc.issues.push(ParseIssue {
                        line: line_no,
                        context: kind.keyword().into(),
                        message: "frame header without a subject".into(),
                    });
                    continue;
                }
                let remainder = parts.next().unwrap_or("");
                sc.frame = Some(Frame {
                    kind,
                    subject: strip_angles(subject_tok),
                    line: line_no,
                    sections: Vec::new(),
                    annotations: Vec::new(),
                });
                let (lead, segments) = split_inline_sections(remainder);
                if !lead.is_empty() {
                    sc.issues.push(ParseIssue {
                        line: line_no,
                        context: kind.keyword().into(),
                        message: format!("unexpected text after subject: {lead}"),
                    });
                }
                sc.begin_sections(segments, line_no);
                continue;
            }
            sc.flush_frame();
            sc.issues.push(ParseIssue {
                line: line_no,
                context: "document".into(),
                message: format!("unrecognized top-level line: {}", &trimmed[..trimmed.len().min(60)]),
            });
        } else {
            // ── indented: a section header, or continuation of the pending body ─
            let (lead, segments) = split_inline_sections(trimmed);
            if segments.is_empty() {
                if let Some(p) = sc.pending.as_mut() {
                    p.body.push(' ');
                    p.body.push_str(trimmed);
                } else {
                    sc.issues.push(ParseIssue {
                        line: line_no,
                        context: "document".into(),
                        message: "indented content with no active section".into(),
                    });
                }
            } else {
                if !lead.is_empty() {
                    if let Some(p) = sc.pending.as_mut() {
                        p.body.push(' ');
                        p.body.push_str(&lead);
                    }
                }
                sc.begin_sections(segments, line_no);
            }
        }
    }
    sc.flush_frame();
    (sc.doc, sc.issues)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DOC: &str = "\
Prefix: sdg: <https://signals.zndx.org/sdg#>
Prefix: bfo: <http://purl.obolibrary.org/obo/BFO_>

Ontology: <https://signals.zndx.org/sdg>

Class: bfo:0000002 SubClassOf: bfo:0000001
DisjointClasses: bfo:0000002, bfo:0000003
Class: <https://signals.zndx.org/sdg#ParentingRole> SubClassOf: bfo:0000023, sdg:inheresIn exactly 1 <https://signals.zndx.org/sdg#DisabledAdult>, sdg:realizes some <https://signals.zndx.org/sdg#ParentingActivity>
Class: sdg:Widget
    Annotations: rdfs:label \"widget\", skos:definition \"a made thing\"
    SubClassOf: bfo:0000002 and sdg:partakes some
        sdg:Ritual
ObjectProperty: sdg:partakes
    Domain: sdg:Widget
    Range: sdg:Ritual
";

    #[test]
    fn document_structure_parses() {
        let (doc, issues) = parse_document(DOC);
        assert!(issues.is_empty(), "unexpected issues: {issues:?}");
        assert_eq!(doc.prefixes.len(), 2);
        assert_eq!(doc.frames.len(), 4);
        assert_eq!(doc.disjoint_blocks.len(), 1);
        // comma list on the role frame = 3 items
        let role = &doc.frames[1];
        assert!(role.subject.ends_with("ParentingRole"));
        assert_eq!(role.sections[0].items.len(), 3);
        // widget frame: annotations + a section body spanning lines
        let widget = &doc.frames[2];
        assert_eq!(widget.annotations.len(), 2);
        assert_eq!(widget.annotations[0].1, "widget");
        assert_eq!(widget.sections[0].items.len(), 1);
        // object property domain/range
        let prop = &doc.frames[3];
        assert_eq!(prop.sections.len(), 2);
    }

    #[test]
    fn expansion_uses_declared_prefixes() {
        let (doc, _) = parse_document(DOC);
        assert_eq!(
            doc.expand("bfo:0000002"),
            "http://purl.obolibrary.org/obo/BFO_0000002"
        );
        assert_eq!(doc.expand("plain"), "plain");
    }
}
