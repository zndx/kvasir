//! OWL Manchester Syntax front-end — the TOOL's ingestion layer (never the kernel's).
//!
//! Target ruling (aegir 2026-07-04): kvasir's external ingestion is CONFINED to the
//! Manchester syntax DeepOnto/OWLAPI consumes (the W3C Manchester grammar). This module
//! parses a Manchester document and LOWERS it to tiered KFS — reasoning-tier axioms
//! (sound for refutation: emitted lines are ENTAILED; skips only miss clashes) plus
//! `@`-sigiled annotation-tier facts (labels, attribute typing, true cardinality bounds).
//!
//! Containment: this lives in `kvasir-cli` (the tool). `kvasir-core`/`kvasir-check`
//! never grow a Manchester dependency; the calculus sees only gated KFS.
//!
//! Parse posture: per-SECTION containment, never silent. A section whose body the
//! grammar cannot parse becomes a loud [`ParseIssue`] (line + reason) and the rest of
//! the document proceeds; the lowering separately counts constructs it entails nothing
//! from. A strict mode (refuse the document on any issue) arrives with HOCON config.
//!
//! Known boundary (map §7): OWLAPI is lenient where a strict parser is not — acceptance
//! is differentially validated against the Python `kvasir_bridge.lower_manchester`
//! lowering (the retained twin) and the DeepOnto harness on real files.

pub mod expr;
pub mod frames;
pub mod lexer;
pub mod lower;

pub use frames::parse_document;
pub use lower::lower;

/// A parsed OWL class (or datatype) expression — the recursive core of the grammar.
///
/// Expression parsing is adapted from OxiRS (`oxirs-rule/src/manchester/`), Apache-2.0 —
/// see NOTICE. Extended here with full-IRI (`<…>`) primaries and comma-separated lists.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// A named entity: prefixed (`bfo:0000015`) or full IRI (angles stripped).
    Named(String),
    /// `A and B and …`
    And(Vec<Expr>),
    /// `A or B or …`
    Or(Vec<Expr>),
    /// `not C`
    Not(Box<Expr>),
    /// `{ i1 i2 … }`
    OneOf(Vec<String>),
    /// `p some C`
    Some { property: String, filler: Box<Expr> },
    /// `p only C`
    Only { property: String, filler: Box<Expr> },
    /// `p min n [C]`
    Min { property: String, n: u32, filler: Option<Box<Expr>> },
    /// `p max n [C]`
    Max { property: String, n: u32, filler: Option<Box<Expr>> },
    /// `p exactly n [C]`
    Exactly { property: String, n: u32, filler: Option<Box<Expr>> },
    /// `p value i`
    HasValue { property: String, individual: String },
}

impl Expr {
    /// Top-level conjuncts (an `And` flattens one level; anything else is itself).
    pub fn conjuncts(&self) -> Vec<&Expr> {
        match self {
            Expr::And(parts) => parts.iter().collect(),
            other => vec![other],
        }
    }
}

/// Frame kinds the document layer recognizes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameKind {
    Class,
    ObjectProperty,
    DataProperty,
    AnnotationProperty,
    Datatype,
    Individual,
}

impl FrameKind {
    pub fn keyword(self) -> &'static str {
        match self {
            FrameKind::Class => "Class",
            FrameKind::ObjectProperty => "ObjectProperty",
            FrameKind::DataProperty => "DataProperty",
            FrameKind::AnnotationProperty => "AnnotationProperty",
            FrameKind::Datatype => "Datatype",
            FrameKind::Individual => "Individual",
        }
    }
}

/// One frame section (`SubClassOf: A, p some B`) with its comma items parsed.
/// `line` is the citation anchor kvasir-ddl's per-element proof citations consume.
#[derive(Debug, Clone)]
pub struct Section {
    pub keyword: String,
    #[allow(dead_code)] // citation anchor — consumed by the ddl module (next increment)
    pub line: usize,
    pub items: Vec<Expr>,
}

/// One frame (`Class: sdg:X …`) with merged sections and string-valued annotations.
#[derive(Debug, Clone)]
pub struct Frame {
    pub kind: FrameKind,
    pub subject: String,
    #[allow(dead_code)] // citation anchor — consumed by the ddl module (next increment)
    pub line: usize,
    pub sections: Vec<Section>,
    /// `(property, literal)` pairs from `Annotations:` sections (string literals only;
    /// language tags / datatype suffixes are consumed and dropped).
    pub annotations: Vec<(String, String)>,
}

/// A top-level `DisjointClasses: a, b, …` axiom block.
#[derive(Debug, Clone)]
pub struct DisjointBlock {
    #[allow(dead_code)] // citation anchor — consumed by the ddl module (next increment)
    pub line: usize,
    pub atoms: Vec<String>,
}

/// A parsed Manchester document.
#[derive(Debug, Clone, Default)]
pub struct Document {
    /// `prefix:` → namespace URI, from the document's own declarations.
    pub prefixes: Vec<(String, String)>,
    pub frames: Vec<Frame>,
    pub disjoint_blocks: Vec<DisjointBlock>,
}

impl Document {
    /// Expand a token to its full IRI via the document's declared prefixes
    /// (the canonicalization contract shared with the Python lowering: prefix
    /// declarations are document semantics; expansion is a correctness merge).
    pub fn expand(&self, tok: &str) -> String {
        for (p, uri) in &self.prefixes {
            if let Some(local) = tok.strip_prefix(p.as_str()) {
                return format!("{uri}{local}");
            }
        }
        tok.to_string()
    }
}

/// A loud, per-section parse containment record (line + reason), never silent.
#[derive(Debug, Clone)]
pub struct ParseIssue {
    pub line: usize,
    pub context: String,
    pub message: String,
}

impl std::fmt::Display for ParseIssue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}: {} — {}", self.line, self.context, self.message)
    }
}

/// Lexer/expression errors (position is a byte offset within the section body).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ManchesterError {
    Lex { pos: usize, msg: String },
    Parse { pos: usize, msg: String },
}

impl std::fmt::Display for ManchesterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ManchesterError::Lex { pos, msg } => write!(f, "lex error at byte {pos}: {msg}"),
            ManchesterError::Parse { pos, msg } => write!(f, "parse error at token {pos}: {msg}"),
        }
    }
}

impl std::error::Error for ManchesterError {}
