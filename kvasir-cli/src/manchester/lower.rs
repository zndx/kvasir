//! Manchester document → tiered KFS lowering.
//!
//! REASONING TIER (sound for refutation — every emitted line is ENTAILED by the source;
//! skips only MISS clashes, never invent them; parity target: the Python
//! `kvasir_bridge.lower_manchester` twin, compared as a line multiset on real artifacts):
//!   - atomic superclass conjuncts → `SubClassOf`
//!   - `p some C`, `p exactly/min n≥1 C` (named filler) → `SubClassOfExistential`
//!     (the entailed weakening; TRUE bounds go to the annotation tier)
//!   - `DisjointWith` atoms / top-level `DisjointClasses:` → pairwise `DisjointClasses`
//!   - ObjectProperty `Domain:`/`Range:` atoms → `PropertyDomain`/`PropertyRange`
//!   - Individual `Types:` atoms → `ClassAssertion`
//!   - everything else skipped-with-count (`expr:*`, `section:*`, `frame:*`)
//!
//! ANNOTATION TIER (`@`-forms; routed, never into the calculus):
//!   - frame `rdfs:label` → `@Label` (unquotable text skipped-with-count, never sanitized)
//!   - restrictions with an `xsd:` filler → `@Attribute`
//!   - `exactly n` → `@Cardinality n n`; `min n>1` → `n *`; `max n` → `0 n`
//!
//! All entity tokens canonicalize to FULL IRIs via the document's own prefix
//! declarations (one class, one name, across tiers — the split-name lesson).

use std::collections::{BTreeMap, BTreeSet};

use super::{Document, Expr, FrameKind};

/// The lowering result: tiered KFS text + accounting.
///
/// `src_lines[i]` is the SOURCE (omn) line that produced the i-th emitted KFS line
/// (axioms first, then annotations) — the citation provenance kvasir-ddl consumes so
/// DDL elements cite the USER's document, not an intermediate.
#[derive(Debug)]
pub struct Lowering {
    pub kfs: String,
    pub n_axioms: usize,
    pub n_annotations: usize,
    pub src_lines: Vec<usize>,
    pub skipped: BTreeMap<String, usize>,
}

const XSD_NS: &str = "http://www.w3.org/2001/XMLSchema#";

fn is_label_prop(tok: &str, doc: &Document) -> bool {
    tok == "rdfs:label" || doc.expand(tok).ends_with("rdf-schema#label")
}

fn is_definition_prop(tok: &str, doc: &Document) -> bool {
    tok == "skos:definition" || doc.expand(tok).ends_with("skos/core#definition")
}

/// Port of aegir's `rows.parse_enum_from_definition` (the Python differential twin —
/// which additionally consults a curated generic-token stop set): a closed value set
/// from a definition, via a non-illustrative parenthetical list ("(pending / running /
/// complete)") or an explicit "one of|value(s)|state(s)|status(es): a, b, c" cue.
/// Illustrative parentheticals (e.g./i.e./such as/including/for example) never fire.
fn parse_enum_from_definition(defn: &str) -> Option<Vec<String>> {
    let mut cand: Option<String> = None;
    let mut rest = defn;
    while let Some(open) = rest.find('(') {
        let Some(close_rel) = rest[open + 1..].find(')') else { break };
        let grp = rest[open + 1..open + 1 + close_rel].trim();
        let low = grp.to_ascii_lowercase();
        let illustrative = ["e.g", "i.e", "such as", "including", "for example"]
            .iter()
            .any(|p| low.starts_with(p));
        if !illustrative
            && (grp.contains(',') || grp.contains('/') || grp.contains('|') || low.contains(" or "))
        {
            cand = Some(grp.to_string());
            break;
        }
        rest = &rest[open + 1 + close_rel + 1..];
    }
    if cand.is_none() {
        let low = defn.to_ascii_lowercase();
        for cue in ["one of", "values", "value", "statuses", "status", "states", "state"] {
            if let Some(i) = low.find(cue) {
                let after = defn[i + cue.len()..].trim_start();
                if let Some(after) = after.strip_prefix(':').or_else(|| after.strip_prefix('-')) {
                    let taken: String = after
                        .chars()
                        .take_while(|c| c.is_ascii_alphanumeric() || matches!(c, ' ' | ',' | '/' | '|'))
                        .collect();
                    if taken.trim().len() > 1 {
                        cand = Some(taken);
                        break;
                    }
                }
            }
        }
    }
    let cand = cand?;
    let mut vals: Vec<String> = Vec::new();
    for piece in cand.replace(" or ", ",").split(|c| matches!(c, ',' | '/' | '|')) {
        let p = piece.trim().trim_end_matches('.').trim().to_ascii_lowercase();
        let ok = (2..=21).contains(&p.len())
            && p.chars().next().is_some_and(|c| c.is_ascii_lowercase())
            && p.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == ' ')
            && !["a", "an", "of", "etc", "such", "value", "the"].contains(&p.as_str());
        if ok && !vals.contains(&p) {
            vals.push(p);
        }
    }
    (vals.len() >= 2).then_some(vals)
}

fn quotable(s: &str) -> bool {
    !s.contains('"') && !s.contains('#')
}

struct Ctx<'a> {
    doc: &'a Document,
    axioms: Vec<String>,
    annotations: Vec<String>,
    ax_lines: Vec<usize>,
    ann_lines: Vec<usize>,
    cur_line: usize,
    skipped: BTreeMap<String, usize>,
    seen_labels: BTreeSet<String>,
    seen_attrs: BTreeSet<(String, String)>,
    seen_cards: BTreeSet<(String, String)>,
    seen_enums: BTreeSet<String>,
}

impl<'a> Ctx<'a> {
    fn ax(&mut self, line: String) {
        self.axioms.push(line);
        self.ax_lines.push(self.cur_line);
    }

    fn ann(&mut self, line: String) {
        self.annotations.push(line);
        self.ann_lines.push(self.cur_line);
    }

    fn skip(&mut self, key: &str) {
        *self.skipped.entry(key.to_string()).or_insert(0) += 1;
    }

    fn x(&self, tok: &str) -> String {
        self.doc.expand(tok)
    }

    /// Lower one superclass-position conjunct for `subject` (already expanded).
    fn lower_conjunct(&mut self, subject: &str, conj: &Expr) {
        match conj {
            Expr::Named(n) => {
                let n = self.x(n);
                self.ax(format!("SubClassOf <{subject}> <{n}>"));
            }
            Expr::Some { property, filler } => self.lower_existential(subject, property, filler, None),
            Expr::Exactly { property, n, filler } => {
                self.card(subject, property, *n, Some(*n));
                if *n >= 1 {
                    match filler.as_deref() {
                        Some(f) => self.lower_existential(subject, property, f, None),
                        None => self.skip("expr:bare-cardinality"),
                    }
                } else {
                    self.skip("expr:max0");
                }
            }
            Expr::Min { property, n, filler } => {
                if *n > 1 {
                    self.card(subject, property, *n, None);
                }
                if *n >= 1 {
                    match filler.as_deref() {
                        Some(f) => self.lower_existential(subject, property, f, None),
                        None => self.skip("expr:bare-cardinality"),
                    }
                } else {
                    self.skip("expr:min0");
                }
            }
            Expr::Max { property, n, .. } => {
                self.card(subject, property, 0, Some(*n));
                self.skip(if *n == 0 { "expr:max0" } else { "expr:max" });
            }
            Expr::Only { .. } => self.skip("expr:only"),
            Expr::HasValue { .. } => self.skip("expr:value"),
            Expr::Not(_) => self.skip("expr:not"),
            Expr::Or(_) => self.skip("expr:or"),
            Expr::OneOf(_) => self.skip("expr:oneof"),
            Expr::And(_) => {
                // a nested And at conjunct position only occurs under parens that the
                // caller has already flattened; distribute anyway (entailed)
                for c in conj.conjuncts() {
                    self.lower_conjunct(subject, c);
                }
            }
        }
    }

    /// `subject ⊑ ∃property.filler` when the filler is NAMED; else skipped (a nested
    /// filler still entails ∃r.Cᵢ per conjunct, but the Python twin skips these —
    /// parity first, coverage ratchets move BOTH lowerings together).
    fn lower_existential(&mut self, subject: &str, property: &str, filler: &Expr, _n: Option<u32>) {
        match filler {
            Expr::Named(f) => {
                let p = self.x(property);
                let f_x = self.x(f);
                self.ax(format!("SubClassOfExistential <{subject}> <{p}> <{f_x}>"));
                if f.starts_with("xsd:") || f_x.starts_with(XSD_NS) {
                    let key = (subject.to_string(), p.clone());
                    if self.seen_attrs.insert(key) {
                        self.ann(format!("@Attribute <{subject}> <{p}> <{f_x}>"));
                    }
                }
            }
            _ => self.skip("expr:nested"),
        }
    }

    fn card(&mut self, subject: &str, property: &str, min: u32, max: Option<u32>) {
        let p = self.x(property);
        let key = (subject.to_string(), p.clone());
        if self.seen_cards.insert(key) {
            let mx = max.map_or("*".to_string(), |m| m.to_string());
            self.ann(format!("@Cardinality <{subject}> <{p}> {min} {mx}"));
        }
    }

    fn label(&mut self, subject: &str, text: &str) {
        if !quotable(text) {
            self.skip("label:unquotable");
            return;
        }
        if self.seen_labels.insert(subject.to_string()) {
            self.ann(format!("@Label <{subject}> \"{text}\""));
        }
    }
}

/// Lower a parsed document to tiered KFS.
pub fn lower(doc: &Document) -> Lowering {
    let mut ctx = Ctx {
        doc,
        axioms: Vec::new(),
        annotations: Vec::new(),
        ax_lines: Vec::new(),
        ann_lines: Vec::new(),
        cur_line: 0,
        skipped: BTreeMap::new(),
        seen_labels: BTreeSet::new(),
        seen_attrs: BTreeSet::new(),
        seen_cards: BTreeSet::new(),
        seen_enums: BTreeSet::new(),
    };

    // top-level DisjointClasses blocks — n-ary lowers to all pairs (entailed)
    for block in &doc.disjoint_blocks {
        ctx.cur_line = block.line;
        let atoms: Vec<String> = block.atoms.iter().map(|a| ctx.x(a)).collect();
        for (i, a) in atoms.iter().enumerate() {
            for b in &atoms[i + 1..] {
                ctx.ax(format!("DisjointClasses <{a}> <{b}>"));
            }
        }
    }

    for frame in &doc.frames {
        let subject = ctx.x(&frame.subject);
        ctx.cur_line = frame.line;
        for (prop, text) in &frame.annotations {
            if is_label_prop(prop, doc) {
                ctx.label(&subject, text);
            } else if frame.kind == FrameKind::DataProperty && is_definition_prop(prop, doc) {
                // a DataProperty definition enumerating a closed value set → @Enum
                // (dormant on artifacts whose definitions live outside the omn — the
                // deriver carrying skos:definition into the realized omn activates it)
                if let Some(vals) = parse_enum_from_definition(text) {
                    let vals: Vec<String> = vals.into_iter().filter(|v| quotable(v)).collect();
                    if vals.len() >= 2 && ctx.seen_enums.insert(subject.clone()) {
                        let quoted: Vec<String> = vals.iter().map(|v| format!("\"{v}\"")).collect();
                        ctx.ann(format!("@Enum <{subject}> {}", quoted.join(" ")));
                    }
                }
            }
        }
        match frame.kind {
            FrameKind::Class => {
                for section in &frame.sections {
                    ctx.cur_line = section.line;
                    match section.keyword.as_str() {
                        "SubClassOf" | "EquivalentTo" => {
                            for item in &section.items {
                                for conj in item.conjuncts() {
                                    ctx.lower_conjunct(&subject, conj);
                                }
                            }
                        }
                        "DisjointWith" => {
                            for item in &section.items {
                                if let Expr::Named(n) = item {
                                    let n = ctx.x(n);
                                    ctx.ax(format!("DisjointClasses <{subject}> <{n}>"));
                                } else {
                                    ctx.skip("disjoint:non-atomic");
                                }
                            }
                        }
                        "Annotations" => {}
                        other => ctx.skip(&format!("section:{other}")),
                    }
                }
            }
            FrameKind::ObjectProperty => {
                for section in &frame.sections {
                    ctx.cur_line = section.line;
                    match section.keyword.as_str() {
                        kw @ ("Domain" | "Range") => {
                            for item in &section.items {
                                if let Expr::Named(n) = item {
                                    let n = ctx.x(n);
                                    let form = if kw == "Domain" {
                                        "PropertyDomain"
                                    } else {
                                        "PropertyRange"
                                    };
                                    ctx.ax(format!("{form} <{subject}> <{n}>"));
                                } else {
                                    ctx.skip(&format!("{}:non-atomic", kw.to_lowercase()));
                                }
                            }
                        }
                        "Annotations" => {}
                        other => ctx.skip(&format!("section:{other}")),
                    }
                }
            }
            FrameKind::Individual => {
                for section in &frame.sections {
                    ctx.cur_line = section.line;
                    match section.keyword.as_str() {
                        "Types" => {
                            for item in &section.items {
                                if let Expr::Named(n) = item {
                                    let n = ctx.x(n);
                                    ctx.ax(format!("ClassAssertion <{n}> <{subject}>"));
                                } else {
                                    ctx.skip("types:non-atomic");
                                }
                            }
                        }
                        "Annotations" => {}
                        other => ctx.skip(&format!("section:{other}")),
                    }
                }
            }
            FrameKind::DataProperty | FrameKind::AnnotationProperty | FrameKind::Datatype => {
                ctx.skip(&format!("frame:{}", frame.kind.keyword()));
            }
        }
    }

    let n_axioms = ctx.axioms.len();
    let n_annotations = ctx.annotations.len();
    let mut kfs = ctx.axioms.join("\n");
    if !ctx.annotations.is_empty() {
        kfs.push('\n');
        kfs.push_str(&ctx.annotations.join("\n"));
    }
    kfs.push('\n');
    let mut src_lines = ctx.ax_lines;
    src_lines.extend_from_slice(&ctx.ann_lines);
    Lowering {
        kfs,
        n_axioms,
        n_annotations,
        src_lines,
        skipped: ctx.skipped,
    }
}

#[cfg(test)]
mod tests {
    use super::super::parse_document;
    use super::*;

    #[test]
    fn tiered_lowering_end_to_end() {
        let doc_text = "\
Prefix: sdg: <https://signals.zndx.org/sdg#>
Prefix: bfo: <http://purl.obolibrary.org/obo/BFO_>
Prefix: xsd: <http://www.w3.org/2001/XMLSchema#>
Class: bfo:0000002 SubClassOf: bfo:0000001
DisjointClasses: bfo:0000002, bfo:0000003
Class: sdg:Role SubClassOf: bfo:0000023, sdg:inheresIn exactly 1 sdg:Bearer, sdg:realizes some sdg:Act
Class: <https://signals.zndx.org/sdg#Role> SubClassOf: sdg:hasEncoding some xsd:string
Class: sdg:Role
    Annotations: rdfs:label \"role\"
ObjectProperty: sdg:inheresIn
    Domain: sdg:Role
Individual: sdg:i_role_01
    Types: sdg:Role
";
        let (doc, issues) = parse_document(doc_text);
        assert!(issues.is_empty(), "{issues:?}");
        let low = lower(&doc);
        let lines: Vec<&str> = low.kfs.lines().collect();
        // canonicalization: the prefixed and full-IRI Role frames merged on one name
        let role = "https://signals.zndx.org/sdg#Role";
        assert!(lines.contains(&format!("SubClassOf <{role}> <http://purl.obolibrary.org/obo/BFO_0000023>").as_str()));
        // exactly 1 → existential (weakened) + true bounds in the tier
        assert!(lines.iter().any(|l| l.starts_with(&format!("SubClassOfExistential <{role}> <https://signals.zndx.org/sdg#inheresIn>"))));
        assert!(lines.contains(&format!("@Cardinality <{role}> <https://signals.zndx.org/sdg#inheresIn> 1 1").as_str()));
        // xsd filler → @Attribute + existential
        assert!(lines.contains(&format!("@Attribute <{role}> <https://signals.zndx.org/sdg#hasEncoding> <http://www.w3.org/2001/XMLSchema#string>").as_str()));
        // label, domain, types, disjoint pair
        assert!(lines.contains(&format!("@Label <{role}> \"role\"").as_str()));
        assert!(lines.iter().any(|l| l.starts_with("PropertyDomain <https://signals.zndx.org/sdg#inheresIn>")));
        assert!(lines.iter().any(|l| l.starts_with("ClassAssertion ")));
        assert!(lines.iter().any(|l| l.starts_with("DisjointClasses ")));
        assert_eq!(low.n_axioms + low.n_annotations, lines.len());
    }

    #[test]
    fn enum_extraction_ports_the_python_rules() {
        assert_eq!(
            parse_enum_from_definition("Current state (pending / running / complete / failed)."),
            Some(vec!["pending".into(), "running".into(), "complete".into(), "failed".into()])
        );
        assert_eq!(
            parse_enum_from_definition("The status: open, closed, or archived"),
            Some(vec!["open".into(), "closed".into(), "archived".into()])
        );
        // illustrative parentheticals never fire
        assert_eq!(parse_enum_from_definition("A standard identifier (e.g. ISO, RFC)."), None);
        assert_eq!(parse_enum_from_definition("A free-text note."), None);
    }

    #[test]
    fn dataprop_definition_emits_enum_annotation() {
        let (doc, _) = parse_document(
            "Prefix: sdg: <https://x.org/sdg#>\nDataProperty: sdg:hasStatus\n    Annotations: skos:definition \"Lifecycle state (draft / final / retired)\"\n",
        );
        let low = lower(&doc);
        assert!(low.kfs.contains("@Enum <https://x.org/sdg#hasStatus> \"draft\" \"final\" \"retired\""),
            "{}", low.kfs);
    }

    #[test]
    fn refused_shapes_are_counted_never_silent() {
        let (doc, _) = parse_document(
            "Class: A SubClassOf: B or C, p only D, p some (q some R)\n",
        );
        let low = lower(&doc);
        assert_eq!(low.n_axioms, 0);
        assert_eq!(low.skipped.get("expr:or"), Some(&1));
        assert_eq!(low.skipped.get("expr:only"), Some(&1));
        assert_eq!(low.skipped.get("expr:nested"), Some(&1));
    }
}
