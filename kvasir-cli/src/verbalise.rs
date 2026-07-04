//! verbalise module — ontology→relational verbalisation over the OWNED Manchester AST.
//!
//! A second fold over the same parse tree the DDL lowering walks. Design lineage:
//! DeepOnto's `OntologyVerbaliser` (recursive bottom-up merge; the same-property
//! junction rewrite ∃r.A ⊓ ∃r.B → ∃r.(A⊓B); label-first vocabulary) — reimplemented
//! deterministically for the ontology→relational setting:
//!
//!   - MULTI-FRAME recomposition (aegir Comp 3: five distinct syntactic skeletons,
//!     seeded per-class subset — never one flat "X is a Y that…" for every class)
//!   - NO NLP model: property phrasing is rule-based (camel/snake → words); no spacy
//!   - TRUE-BOUND phrasing: `exactly 1` → "exactly one", `max 3` → "at most three-ish"
//!     ("at most 3") — the annotation tier carries what the reasoning weakening drops
//!   - VACUITY GUARD built in: unlabeled opaque locals (bfo numerics) never surface as
//!     head nouns; a class with nothing to say yields NO frames, never "X is a thing"
//!
//! Two consumers: `kvasir verbalise` (per-class frame sets, the corpus-side artifact)
//! and the ddl module (single clear table/column COMMENT sentences beside citations —
//! self-explaining proof-carrying DDL).

use std::collections::BTreeMap;

use serde::Serialize;

use crate::manchester::{Document, Expr, FrameKind};

/// IRI → preferred display name (label-first; built from the document's annotations).
pub type Vocab = BTreeMap<String, String>;

pub fn vocab_of(doc: &Document) -> Vocab {
    let mut v = Vocab::new();
    for frame in &doc.frames {
        let subject = doc.expand(&frame.subject);
        for (prop, text) in &frame.annotations {
            if prop == "rdfs:label" || doc.expand(prop).ends_with("rdf-schema#label") {
                v.entry(subject.clone()).or_insert_with(|| text.clone());
            }
        }
    }
    v
}

fn local(iri: &str) -> &str {
    iri.rsplit(['#', '/']).next().unwrap_or(iri)
}

/// camelCase / snake_case local name → lowercase words ("inheresIn" → "inheres in").
pub fn words(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    let mut prev_lower = false;
    for c in s.chars() {
        if c == '_' || c == '-' {
            out.push(' ');
            prev_lower = false;
        } else if c.is_ascii_uppercase() {
            if prev_lower {
                out.push(' ');
            }
            out.push(c.to_ascii_lowercase());
            prev_lower = false;
        } else {
            out.push(c);
            prev_lower = true;
        }
    }
    out.trim().to_string()
}

/// True when a local name is an opaque identifier that must never surface as prose —
/// the vacuity guard's first leg. Covers digit-leading locals (`0000031`) AND the
/// letter-prefixed numeric-ID form (`BFO_0000031`, `OBI_0000070`).
fn opaque(l: &str) -> bool {
    if l.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        return true;
    }
    let rest = l
        .trim_start_matches(|c: char| c.is_ascii_alphabetic())
        .trim_start_matches('_');
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

/// Display name for an entity: label first, else its local name as words; `None` for
/// an unlabeled opaque local (the caller drops it rather than verbalising a number).
pub fn name(vocab: &Vocab, iri: &str) -> Option<String> {
    if let Some(l) = vocab.get(iri) {
        return Some(l.clone());
    }
    let l = local(iri);
    if opaque(l) {
        None
    } else {
        Some(words(l))
    }
}

/// Property verb phrase: label first, else words ("records_patient_encounter" →
/// "records patient encounter"). Deterministic; no POS model.
pub fn verb(vocab: &Vocab, iri: &str) -> String {
    name(vocab, iri).unwrap_or_else(|| format!("relates via {}", local(iri)))
}

// ── quantifier phrasing (true bounds — beyond DeepOnto's reach) ────────────────
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quant {
    Some,
    Only,
    Exactly(u32),
    Min(u32),
    Max(u32),
}

pub fn count(q: Quant) -> String {
    match q {
        Quant::Some => "at least one".into(),
        Quant::Only => "only".into(),
        Quant::Exactly(1) => "exactly one".into(),
        Quant::Exactly(n) => format!("exactly {n}"),
        Quant::Min(n) => format!("at least {n}"),
        Quant::Max(n) => format!("at most {n}"),
    }
}

// ── recursive expression verbalisation (the DeepOnto-lineage core) ─────────────
pub fn verbalise_expr(vocab: &Vocab, doc: &Document, e: &Expr) -> String {
    match e {
        Expr::Named(n) => {
            let iri = doc.expand(n);
            name(vocab, &iri).unwrap_or_else(|| "something".into())
        }
        Expr::Not(inner) => format!("not {}", verbalise_expr(vocab, doc, inner)),
        Expr::And(parts) => junction(vocab, doc, parts, "and"),
        Expr::Or(parts) => junction(vocab, doc, parts, "or"),
        Expr::OneOf(inds) => {
            let names: Vec<String> = inds
                .iter()
                .map(|i| name(vocab, &doc.expand(i)).unwrap_or_else(|| words(local(i))))
                .collect();
            format!("one of {}", names.join(", "))
        }
        Expr::Some { property, filler } => restriction(vocab, doc, property, Quant::Some, Some(filler)),
        Expr::Only { property, filler } => restriction(vocab, doc, property, Quant::Only, Some(filler)),
        Expr::Exactly { property, n, filler } => {
            restriction(vocab, doc, property, Quant::Exactly(*n), filler.as_deref())
        }
        Expr::Min { property, n, filler } => {
            restriction(vocab, doc, property, Quant::Min(*n), filler.as_deref())
        }
        Expr::Max { property, n, filler } => {
            restriction(vocab, doc, property, Quant::Max(*n), filler.as_deref())
        }
        Expr::HasValue { property, individual } => {
            let p = verb(vocab, &doc.expand(property));
            let i = name(vocab, &doc.expand(individual)).unwrap_or_else(|| words(local(individual)));
            format!("something that {p} {i}")
        }
    }
}

fn restriction(vocab: &Vocab, doc: &Document, property: &str, q: Quant, filler: Option<&Expr>) -> String {
    let p = verb(vocab, &doc.expand(property));
    match filler {
        Some(f) => format!("something that {p} {} {}", count(q), verbalise_expr(vocab, doc, f)),
        None => format!("something that {p} {} thing", count(q)),
    }
}

/// The three-case junction logic with the SAME-PROPERTY MERGE (∃r.A ⊓ ∃r.B verbalises
/// as one clause over "A and B") — the DeepOnto design worth keeping, verbatim in
/// spirit, deterministic in implementation.
fn junction(vocab: &Vocab, doc: &Document, parts: &[Expr], conj: &str) -> String {
    // partition into named atoms and restrictions; merge restrictions by (prop, quant)
    let mut atoms: Vec<String> = Vec::new();
    let mut restrictions: Vec<(String, Quant, Vec<String>)> = Vec::new();
    let mut opaque_others: Vec<String> = Vec::new();
    for p in parts {
        match p {
            Expr::Named(n) => {
                if let Some(nm) = name(vocab, &doc.expand(n)) {
                    atoms.push(nm);
                }
            }
            Expr::Some { property, filler } => merge_r(vocab, doc, &mut restrictions, property, Quant::Some, filler),
            Expr::Only { property, filler } => merge_r(vocab, doc, &mut restrictions, property, Quant::Only, filler),
            Expr::Exactly { property, n, filler } => {
                if let Some(f) = filler.as_deref() {
                    merge_r(vocab, doc, &mut restrictions, property, Quant::Exactly(*n), f);
                }
            }
            Expr::Min { property, n, filler } => {
                if let Some(f) = filler.as_deref() {
                    merge_r(vocab, doc, &mut restrictions, property, Quant::Min(*n), f);
                }
            }
            Expr::Max { property, n, filler } => {
                if let Some(f) = filler.as_deref() {
                    merge_r(vocab, doc, &mut restrictions, property, Quant::Max(*n), f);
                }
            }
            other => opaque_others.push(verbalise_expr(vocab, doc, other)),
        }
    }
    let mut clauses: Vec<String> = Vec::new();
    if !atoms.is_empty() {
        clauses.push(atoms.join(&format!(" {conj} ")));
    }
    for (p, q, fillers) in &restrictions {
        clauses.push(format!("something that {p} {} {}", count(*q), fillers.join(" and ")));
    }
    clauses.extend(opaque_others);
    if clauses.is_empty() {
        "something".into()
    } else {
        clauses.join(&format!(" {conj} "))
    }
}

fn merge_r(
    vocab: &Vocab,
    doc: &Document,
    acc: &mut Vec<(String, Quant, Vec<String>)>,
    property: &str,
    q: Quant,
    filler: &Expr,
) {
    let p = verb(vocab, &doc.expand(property));
    let f = verbalise_expr(vocab, doc, filler);
    if let Some(slot) = acc.iter_mut().find(|(ap, aq, _)| *ap == p && *aq == q) {
        slot.2.push(f);
    } else {
        acc.push((p, q, vec![f]));
    }
}

// ── class-frame multi-frame recomposition (Comp 3 ported) ──────────────────────
#[derive(Debug, Clone)]
pub struct Constraint {
    pub prop: String,   // verb phrase
    pub filler: String, // verbalised filler
    pub quant: Quant,
}

#[derive(Debug, Clone, Default)]
pub struct Parts {
    pub subject: String,
    pub supers: Vec<String>, // named, non-opaque heads only (the vacuity guard)
    pub constraints: Vec<Constraint>,
}

/// Decompose a Class frame's SubClassOf/EquivalentTo items into verbalisation parts.
pub fn parts_of(vocab: &Vocab, doc: &Document, frame: &crate::manchester::Frame) -> Option<Parts> {
    if frame.kind != FrameKind::Class {
        return None;
    }
    let subject_iri = doc.expand(&frame.subject);
    let subject = name(vocab, &subject_iri)?;
    let mut parts = Parts { subject, ..Default::default() };
    for section in &frame.sections {
        if section.keyword != "SubClassOf" && section.keyword != "EquivalentTo" {
            continue;
        }
        for item in &section.items {
            for conj in item.conjuncts() {
                match conj {
                    Expr::Named(n) => {
                        if let Some(nm) = name(vocab, &doc.expand(n)) {
                            if !parts.supers.contains(&nm) {
                                parts.supers.push(nm);
                            }
                        }
                    }
                    Expr::Some { property, filler } => push_c(vocab, doc, &mut parts, property, Quant::Some, filler),
                    Expr::Only { property, filler } => push_c(vocab, doc, &mut parts, property, Quant::Only, filler),
                    Expr::Exactly { property, n, filler } => {
                        if let Some(f) = filler.as_deref() {
                            push_c(vocab, doc, &mut parts, property, Quant::Exactly(*n), f);
                        }
                    }
                    Expr::Min { property, n, filler } => {
                        if let Some(f) = filler.as_deref() {
                            push_c(vocab, doc, &mut parts, property, Quant::Min(*n), f);
                        }
                    }
                    Expr::Max { property, n, filler } => {
                        if let Some(f) = filler.as_deref() {
                            push_c(vocab, doc, &mut parts, property, Quant::Max(*n), f);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    if parts.supers.is_empty() && parts.constraints.is_empty() {
        return None; // nothing to say — say nothing (the vacuity guard's second leg)
    }
    Some(parts)
}

fn push_c(vocab: &Vocab, doc: &Document, parts: &mut Parts, property: &str, q: Quant, filler: &Expr) {
    let prop = verb(vocab, &doc.expand(property));
    let f = verbalise_expr(vocab, doc, filler);
    // same-property merge at the frame level too
    if let Some(c) = parts
        .constraints
        .iter_mut()
        .find(|c| c.prop == prop && c.quant == q)
    {
        c.filler = format!("{} and {}", c.filler, f);
    } else {
        parts.constraints.push(Constraint { prop, filler: f, quant: q });
    }
}

fn head(parts: &Parts) -> String {
    if parts.supers.is_empty() {
        "entity".into()
    } else {
        parts.supers.join(" and ")
    }
}

fn art(noun: &str) -> &'static str {
    match noun.chars().next() {
        Some('a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U') => "an",
        _ => "a",
    }
}

/// Compose up to `k` distinct-skeleton frames (subsumptive always first for
/// continuity; the tail rotates by an FNV-1a hash of `seed_key` so the corpus-wide
/// skeleton distribution flattens instead of concentrating).
pub fn frames(parts: &Parts, k: usize, seed_key: &str) -> Vec<String> {
    let s = &parts.subject;
    let h = head(parts);
    let a_h = format!("{} {}", art(&h), h);
    let pool: Vec<String> = if parts.constraints.is_empty() {
        vec![
            format!("{s} is a kind of {h}."),
            format!("{s} is a type of {h}."),
            format!("Every {s} is {a_h}."),
            format!("{s} denotes {a_h}."),
            format!("Any {s} qualifies as {a_h}."),
        ]
    } else {
        let that: Vec<String> = parts
            .constraints
            .iter()
            .map(|c| format!("{} {} {}", c.prop, count(c.quant), c.filler))
            .collect();
        let bears: Vec<String> = parts
            .constraints
            .iter()
            .map(|c| format!("the {} relation to {} {}", c.prop, count(c.quant), c.filler))
            .collect();
        let via: Vec<String> = parts
            .constraints
            .iter()
            .map(|c| format!("to {} {} via {}", count(c.quant), c.filler, c.prop))
            .collect();
        vec![
            format!("{s} is {a_h} that {}.", that.join(" and ")),
            format!("Each {s} is defined as {a_h} which {}.", that.join(" and ")),
            format!("For an entity to count as {s}, it must bear {}.", bears.join(" and ")),
            format!("Every {s} stands in {}.", bears.join(" and ")),
            format!("Any {s} necessarily relates {}.", via.join(" and ")),
        ]
    };
    let mut out: Vec<String> = Vec::with_capacity(k.min(pool.len()));
    out.push(pool[0].clone());
    let mut tail: Vec<String> = pool[1..].to_vec();
    if !tail.is_empty() {
        let rot = (fnv(seed_key) as usize) % tail.len();
        tail.rotate_left(rot);
    }
    out.extend(tail);
    out.truncate(k);
    out
}

fn fnv(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.as_bytes() {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

// ── the `kvasir verbalise` payload ─────────────────────────────────────────────
#[derive(Debug, Serialize)]
pub struct ClassVerbalisation {
    pub class: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    pub frames: Vec<String>,
}

/// Verbalise every Class frame in a document (merged by subject IRI; frames beyond
/// the first for a subject contribute their sections through the merge in parts_of
/// running per-frame — v0 verbalises per frame occurrence and merges by subject).
pub fn verbalise_document(doc: &Document, k: usize) -> Vec<ClassVerbalisation> {
    let vocab = vocab_of(doc);
    let mut merged: BTreeMap<String, Parts> = BTreeMap::new();
    for frame in &doc.frames {
        let Some(p) = parts_of(&vocab, doc, frame) else { continue };
        let iri = doc.expand(&frame.subject);
        match merged.get_mut(&iri) {
            None => {
                merged.insert(iri, p);
            }
            Some(existing) => {
                for s in p.supers {
                    if !existing.supers.contains(&s) {
                        existing.supers.push(s);
                    }
                }
                for c in p.constraints {
                    if !existing
                        .constraints
                        .iter()
                        .any(|e| e.prop == c.prop && e.quant == c.quant && e.filler == c.filler)
                    {
                        existing.constraints.push(c);
                    }
                }
            }
        }
    }
    merged
        .into_iter()
        .map(|(class, parts)| ClassVerbalisation {
            label: vocab.get(&class).cloned(),
            frames: frames(&parts, k, &class),
            class,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manchester::parse_document;

    const DOC: &str = "\
Prefix: sdg: <https://signals.zndx.org/sdg#>
Prefix: bfo: <http://purl.obolibrary.org/obo/BFO_>
Class: bfo:0000023
    Annotations: rdfs:label \"role\"
Class: sdg:ParentingRole SubClassOf: bfo:0000023, sdg:inheresIn exactly 1 sdg:DisabledAdult, sdg:realizes some sdg:ParentingActivity
Class: sdg:DisabledAdult
    Annotations: rdfs:label \"disabled adult\"
Class: sdg:ParentingActivity
    Annotations: rdfs:label \"parenting activity\"
Class: sdg:Mystery SubClassOf: bfo:0000031
Class: sdg:Blend SubClassOf: sdg:consumes some sdg:CoffeeBean and sdg:consumes some sdg:Water
Class: sdg:CoffeeBean
Class: sdg:Water
";

    #[test]
    fn true_bounds_and_labels_verbalise() {
        let (doc, _) = parse_document(DOC);
        let out = verbalise_document(&doc, 5);
        let role = out.iter().find(|c| c.class.ends_with("ParentingRole")).unwrap();
        let first = &role.frames[0];
        assert!(first.contains("exactly one disabled adult"), "true bounds: {first}");
        assert!(first.contains("at least one parenting activity"), "{first}");
        assert!(first.contains("is a role that"), "label-first head: {first}");
        assert!(role.frames.len() == 5);
        // distinct skeletons
        assert!(role.frames.iter().any(|f| f.starts_with("For an entity to count as")));
    }

    #[test]
    fn vacuity_guard_unlabeled_opaque_head_yields_no_head_noun() {
        let (doc, _) = parse_document(DOC);
        let out = verbalise_document(&doc, 3);
        // Mystery ⊑ bfo:0000031 (unlabeled, opaque local) → no supers, no constraints → NO frames
        assert!(!out.iter().any(|c| c.class.ends_with("Mystery")));
    }

    #[test]
    fn same_property_conjuncts_merge_into_one_clause() {
        let (doc, _) = parse_document(DOC);
        let out = verbalise_document(&doc, 1);
        let blend = out.iter().find(|c| c.class.ends_with("Blend")).unwrap();
        let f = &blend.frames[0];
        assert!(
            f.contains("consumes at least one coffee bean and water"),
            "same-property merge: {f}"
        );
        assert_eq!(f.matches("consumes").count(), 1, "one clause, not two: {f}");
    }
}
