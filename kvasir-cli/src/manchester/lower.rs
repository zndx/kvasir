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
//!   - `max`/`only` with a named class filler → `@Relation` (a schema-real but NOT
//!     existentially-forced object relation — an optional FK; without this such
//!     relations vanish from the DDL entirely, a projection leak)
//!   - DataProperty `skos:definition` enumerating a closed set → `@Enum`
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
    /// Which lowering code paths the input exercised (`--stats` coverage; the upstream
    /// derive agent reads the DORMANT complement as its complexity brief).
    pub constructs: BTreeMap<String, usize>,
    /// PARSE-TIME REFUTATION SIGNALS: contradictions detectable syntactically — e.g. the
    /// same (class, property) carrying incompatible cardinality bounds (min 2 vs max 1
    /// = ⊥, which then ∃-⊥-cascades; measured poisoning 1,489 classes at corpus scale
    /// before HermiT named it in 341s — this catches it in microseconds).
    pub conflicts: Vec<String>,
}

const XSD_STRING: &str = "http://www.w3.org/2001/XMLSchema#string";
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
    seen_cards: BTreeMap<(String, String), (u32, Option<u32>)>,
    seen_card_ann: BTreeSet<(String, String)>,
    seen_enums: BTreeSet<String>,
    seen_rels: BTreeSet<(String, String)>,
    seen_keys: BTreeSet<String>,
    identifier_props: BTreeSet<String>,
    oneof_classes: BTreeMap<String, Vec<String>>,
    constructs: BTreeMap<String, usize>,
    conflicts: Vec<String>,
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

    fn stat(&mut self, key: &str) {
        *self.constructs.entry(key.to_string()).or_insert(0) += 1;
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
                let fname = filler.as_deref().and_then(|f| if let Expr::Named(x) = f { Some(x.clone()) } else { None });
                self.card(subject, property, *n, Some(*n), fname);
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
                    let fname = filler.as_deref().and_then(|f| if let Expr::Named(x) = f { Some(x.clone()) } else { None });
                    self.card(subject, property, *n, None, fname);
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
            Expr::Max { property, n, filler } => {
                let fname = filler.as_deref().and_then(|f| if let Expr::Named(x) = f { Some(x.clone()) } else { None });
                self.card(subject, property, 0, Some(*n), fname);
                // a max relation is schema-real (an optional/nullable FK) but not
                // existentially forced — the annotation tier carries it so the DDL
                // planner renders the column (leak-2 fix: without this the relation
                // vanished entirely). max 0 asserts absence: no relation.
                if *n > 0 {
                    if let Some(Expr::Named(f)) = filler.as_deref() {
                        self.relation(subject, property, f);
                    }
                }
                self.skip(if *n == 0 { "expr:max0" } else { "expr:max" });
            }
            Expr::Only { property, filler } => {
                // an all-values-from restriction types an (optional) relation; carry it
                // as a schema-real nullable FK too.
                if let Expr::Named(f) = filler.as_ref() {
                    self.relation(subject, property, f);
                }
                self.skip("expr:only");
            }
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
                if let Some(vals) = self.oneof_classes.get(&f_x).cloned() {
                    // K4: the filler is an enumeration class ({a b c}) — a closed VALUE SET,
                    // not an entity. Lower as attribute + enum ONLY (no relation axiom), so
                    // the planner renders a lookup table, never an entity/reference table.
                    let key = (subject.to_string(), p.clone());
                    if self.seen_attrs.insert(key) {
                        self.ann(format!("@Attribute <{subject}> <{p}> <{XSD_STRING}>"));
                    }
                    if self.seen_enums.insert(p.clone()) {
                        let quoted: Vec<String> =
                            vals.iter().filter(|v| quotable(v)).map(|v| format!("\"{v}\"")).collect();
                        if quoted.len() >= 2 {
                            self.ann(format!("@Enum <{p}> {}", quoted.join(" ")));
                            self.stat("k4_oneof_enum");
                        }
                    }
                    return;
                }
                self.ax(format!("SubClassOfExistential <{subject}> <{p}> <{f_x}>"));
                if f.starts_with("xsd:") || f_x.starts_with(XSD_NS) {
                    let key = (subject.to_string(), p.clone());
                    if self.seen_attrs.insert(key) {
                        self.ann(format!("@Attribute <{subject}> <{p}> <{f_x}>"));
                        self.stat("data_restriction");
                    }
                    // K3: an identifier-vocabulary property restricted on this class IS its
                    // declared natural key — the wild idiom for owl:hasKey (first one wins).
                    if self.identifier_props.contains(&p)
                        && self.seen_keys.insert(subject.to_string())
                    {
                        self.ann(format!("@Key <{subject}> <{p}>"));
                        self.stat("k3_identifier_key");
                    }
                }
            }
            _ => self.skip("expr:nested"),
        }
    }

    /// A schema-real but non-existential object relation (from `max`/`only`) → @Relation.
    /// xsd fillers are attributes, not relations, and never reach here.
    fn relation(&mut self, subject: &str, property: &str, filler: &str) {
        let p = self.x(property);
        let f = self.x(filler);
        if f.starts_with("xsd:") || f.starts_with(XSD_NS) {
            return;
        }
        if self.seen_rels.insert((subject.to_string(), p.clone())) {
            self.ann(format!("@Relation <{subject}> <{p}> <{f}>"));
            self.stat("relation_optional");
        }
    }

    fn card(&mut self, subject: &str, property: &str, min: u32, max: Option<u32>,
            filler: Option<String>) {
        let p = self.x(property);
        // CONFLICT key includes the FILLER: qualified bounds over DIFFERENT fillers are
        // compatible (exactly-1-University + min-2-Course is 3 successors, satisfiable —
        // HermiT-verified; the fillerless key falsely refuted it, violating kvasir's
        // sound-for-refutation contract). Unqualified bounds (filler None) constrain the
        // TOTAL and conflict with any same-prop bound.
        let fkey = filler.map(|f| self.x(&f)).unwrap_or_default();
        let key = (subject.to_string(), format!("{p}|{fkey}"));
        // local min>max is ⊥ outright
        if max.map_or(false, |m| min > m) {
            self.conflicts.push(format!(
                "<{subject}> <{p}>: min {min} > max {} — unsatisfiable bound",
                max.unwrap()
            ));
        }
        match self.seen_cards.get(&key) {
            None => {
                self.seen_cards.insert(key.clone(), (min, max));
                let ann_key = (subject.to_string(), p.clone());
                if self.seen_card_ann.insert(ann_key) {
                    let mx = max.map_or("*".to_string(), |m| m.to_string());
                    self.ann(format!("@Cardinality <{subject}> <{p}> {min} {mx}"));
                    self.stat(if min > 1 || max.map_or(false, |m| m > 1) {
                        "cardinality_many"
                    } else {
                        "cardinality_one"
                    });
                }
            }
            Some(&(pmin, pmax)) if pmin != min || pmax != max => {
                // two restrictions, incompatible bounds: the combined min is max(mins),
                // combined max is min(maxes) — empty interval ⇒ the class is ⊥ (and the
                // ∃-⊥ cascade spreads it to everything requiring a successor here).
                let cmin = pmin.max(min);
                let cmax = match (pmax, max) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (a, b) => a.or(b),
                };
                if cmax.map_or(false, |m| cmin > m) {
                    self.conflicts.push(format!(
                        "<{subject}> <{p}>: conflicting bounds ({pmin}..{}) vs ({min}..{}) \
                         — combined interval empty ⇒ class unsatisfiable",
                        pmax.map_or("*".into(), |m: u32| m.to_string()),
                        max.map_or("*".into(), |m: u32| m.to_string())
                    ));
                }
            }
            _ => {}
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
        seen_cards: BTreeMap::new(),
        seen_card_ann: BTreeSet::new(),
        seen_enums: BTreeSet::new(),
        seen_rels: BTreeSet::new(),
        seen_keys: BTreeSet::new(),
        identifier_props: BTreeSet::new(),
        oneof_classes: BTreeMap::new(),
        constructs: BTreeMap::new(),
        conflicts: Vec::new(),
    };

    // ── the NATURAL key-election ladder pre-pass (K2/K3/K4) ─────────────────────────
    // Real-world ontologies rarely assert owl:hasKey; identity arrives through naturally
    // occurring constructs instead. Collected here, elected during the main walk:
    //   K2  InverseFunctional object property  → @Unique (FK column UNIQUE)
    //   K3  identifier-vocabulary data property (dcterms:identifier / skos:notation /
    //       schema:identifier / IAO_0000578, own IRI or SubPropertyOf-closure) → @Key
    //   K4  EquivalentTo: { i1 i2 … } enumeration class → @Enum on relations targeting it
    const ID_VOCAB: &[&str] = &[
        "http://purl.org/dc/terms/identifier",
        "http://purl.org/dc/elements/1.1/identifier",
        "http://www.w3.org/2004/02/skos/core#notation",
        "https://schema.org/identifier",
        "http://schema.org/identifier",
        "http://purl.obolibrary.org/obo/IAO_0000578",
    ];
    let mut subprop: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for frame in &doc.frames {
        let subject = ctx.x(&frame.subject);
        match frame.kind {
            FrameKind::DataProperty => {
                for section in &frame.sections {
                    if section.keyword == "SubPropertyOf" {
                        for item in &section.items {
                            if let Expr::Named(n) = item {
                                subprop.entry(subject.clone()).or_default().push(ctx.x(n));
                            }
                        }
                    }
                }
            }
            FrameKind::ObjectProperty => {
                for section in &frame.sections {
                    if section.keyword == "Characteristics" {
                        for item in &section.items {
                            if matches!(item, Expr::Named(n) if n == "InverseFunctional") {
                                ctx.ann(format!("@Unique <{subject}>"));
                                ctx.stat("k2_inverse_functional");
                            } else if matches!(item, Expr::Named(n) if n == "Functional") {
                                ctx.stat("functional_characteristic");
                            }
                        }
                    }
                }
            }
            FrameKind::Class => {
                for section in &frame.sections {
                    if section.keyword == "EquivalentTo" {
                        for item in &section.items {
                            if let Expr::OneOf(inds) = item {
                                let vals: Vec<String> = inds
                                    .iter()
                                    .map(|i| {
                                        let full = ctx.x(i);
                                        full.rsplit(['#', '/']).next().unwrap_or(&full).to_string()
                                    })
                                    .collect();
                                ctx.oneof_classes.insert(subject.clone(), vals);
                                ctx.stat("oneof_class");
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    // identifier closure: own IRI in the vocabulary, or reaches it over SubPropertyOf edges
    let is_id = |iri: &str, sp: &BTreeMap<String, Vec<String>>| -> bool {
        if ID_VOCAB.contains(&iri) {
            return true;
        }
        let mut stack = vec![iri.to_string()];
        let mut seen: BTreeSet<String> = BTreeSet::new();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur.clone()) {
                continue;
            }
            if ID_VOCAB.contains(&cur.as_str()) {
                return true;
            }
            if let Some(supers) = sp.get(&cur) {
                stack.extend(supers.iter().cloned());
            }
        }
        false
    };
    let all_props: BTreeSet<String> = subprop.keys().cloned().collect();
    for prop in &all_props {
        if is_id(prop, &subprop) {
            ctx.identifier_props.insert(prop.clone());
        }
    }

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
                        "HasKey" => {
                            let mut props: Vec<String> = Vec::new();
                            for item in &section.items {
                                if let Expr::Named(n) = item {
                                    props.push(ctx.x(n));
                                } else {
                                    ctx.skip("haskey:non-atomic");
                                }
                            }
                            if !props.is_empty() {
                                ctx.stat(if props.len() > 1 { "k1_haskey_composite" } else { "k1_haskey" });
                                let plist = props
                                    .iter()
                                    .map(|p| format!("<{p}>"))
                                    .collect::<Vec<_>>()
                                    .join(" ");
                                ctx.ann(format!("@Key <{subject}> {plist}"));
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
        constructs: ctx.constructs,
        conflicts: ctx.conflicts,
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
    fn max_and_only_relations_emit_relation_annotations() {
        let (doc, _) = parse_document(
            "Prefix: sdg: <https://x.org/sdg#>\nClass: sdg:A SubClassOf: sdg:derivedFrom max 1 sdg:B, sdg:typedAs only sdg:C\n",
        );
        let low = lower(&doc);
        assert!(low.kfs.contains("@Relation <https://x.org/sdg#A> <https://x.org/sdg#derivedFrom> <https://x.org/sdg#B>"), "{}", low.kfs);
        assert!(low.kfs.contains("@Relation <https://x.org/sdg#A> <https://x.org/sdg#typedAs> <https://x.org/sdg#C>"), "{}", low.kfs);
        // still no reasoning-tier existential for max/only (unsound to entail ∃)
        assert!(!low.kfs.contains("SubClassOfExistential"));
        // max 0 asserts absence → no relation
        let (doc0, _) = parse_document("Prefix: sdg: <https://x.org/sdg#>\nClass: sdg:A SubClassOf: sdg:p max 0 sdg:B\n");
        assert!(!lower(&doc0).kfs.contains("@Relation"));
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
