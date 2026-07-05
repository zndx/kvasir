//! shapes module — SHACL Core EMISSION + INGESTION (`kvasir shapes` / `kvasir ddl --shapes`).
//!
//! SHACL ruling (aegir map §9): shapes are NOT optional — explicit when user-provided,
//! IMPLICIT when kvasir completes the constraints itself to render DDL. This module is
//! both halves: [`emit`] derives the shapes graph from the tiered facts the ddl module
//! consumes; [`parse`] reads a shapes graph BACK into those facts, so a shapes file is a
//! first-class DDL constraint source and users can hand-author/extend the standard syntax.
//!
//! DENORMALIZED BY DESIGN: each targeted class carries its ROLLED constraints (own +
//! inherited), so no entailment regime is assumed — a plain SHACL Core validator sees
//! exactly what the DDL realizes. Emission is canonical (sorted classes, sorted property
//! paths): same input, same bytes.
//!
//! The tier↔SHACL correspondence this makes literal:
//!   @Attribute  ≡ sh:path + sh:datatype        @Cardinality ≡ sh:minCount/sh:maxCount
//!   @Enum       ≡ sh:in                        existential  ≡ sh:path + sh:class + sh:minCount≥1
//!   @Relation   ≡ sh:path + sh:class (no minCount — the optional/nullable FK)
//!
//! CONTAINMENT NOTE (2026-07-04): the rudof `shacl` crate (the standards validator) pulls
//! 567 crates incl. reqwest/hyper/tokio even with default-features=false — an HTTP+async
//! stack for a Turtle parser, exactly the sprawl the containment ruling refuses. So
//! [`parse`] is a LEAN reader of the SHACL-Core Turtle subset (the shape this tool emits
//! and a conformant author would write) — the same judgement as sqlparser-for-self-check
//! vs polyglot-as-authority. It proves the FIXPOINT (own emitted shapes → identical DDL)
//! and ingests hand-authored Core shapes; robust arbitrary-graph ingestion (full RDF,
//! blank-node graphs, alt lexical forms) is a separately-justified later increment.

use std::collections::BTreeMap;

use kvasir_core::{Annotation, Axiom};

const XSD_NS: &str = "http://www.w3.org/2001/XMLSchema#";

#[derive(Default)]
struct PropShape {
    datatype: Option<String>,
    class: Option<String>,
    min: Option<u32>,
    max: Option<u32>,
    values: Option<Vec<String>>,
}

/// Emit a SHACL Core shapes graph (Turtle) from the tiered facts. Same election as
/// the ddl module: a NodeShape per class with ≥1 rolled attribute or existential.
pub fn emit(axioms: &[Axiom], annotations: &[Annotation]) -> String {
    // told edges + per-class own facts. (prop, target, is_existential): an existential
    // is NOT NULL → sh:minCount≥1; a pure @Relation is optional → no minCount. Pushed
    // existentials-first so per-path dedup keeps the NOT NULL when both co-name a prop.
    let mut sub: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut exts: BTreeMap<&str, Vec<(&str, &str, bool)>> = BTreeMap::new();
    for ax in axioms {
        match ax {
            Axiom::SubClassOf { sub: s, sup } => sub.entry(s).or_default().push(sup),
            Axiom::EquivalentToIntersection { class, parts } => {
                for p in parts {
                    sub.entry(class).or_default().push(p);
                }
            }
            Axiom::SubClassOfExistential { sub: s, role, filler } => {
                if !filler.starts_with(XSD_NS) && !filler.starts_with("xsd:") {
                    exts.entry(s).or_default().push((role, filler, true));
                }
            }
            _ => {}
        }
    }
    let mut attrs: BTreeMap<&str, Vec<(&str, &str)>> = BTreeMap::new();
    let mut cards: BTreeMap<(&str, &str), (u32, Option<u32>)> = BTreeMap::new();
    let mut enums: BTreeMap<&str, &Vec<String>> = BTreeMap::new();
    let mut key_of: BTreeMap<&str, &Vec<String>> = BTreeMap::new();
    let mut unique_props: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    for an in annotations {
        match an {
            Annotation::Attribute { class, prop, xsd } => {
                attrs.entry(class).or_default().push((prop, xsd));
            }
            Annotation::Cardinality { class, prop, min, max } => {
                cards.insert((class, prop), (*min, *max));
            }
            Annotation::Enum { prop, values } => {
                enums.insert(prop, values);
            }
            Annotation::Label { .. } => {}
            Annotation::Key { class, props } => {
                key_of.insert(class, props);
            }
            Annotation::Unique { prop } => {
                unique_props.insert(prop.as_str());
            }
            Annotation::Relation { class, prop, target } => {
                // a schema-real non-existential relation → sh:class, no minCount
                // (optional). Pushed after existentials so the NOT NULL wins on dedup.
                exts.entry(class).or_default().push((prop, target, false));
            }
        }
    }

    fn ancestors_of<'a>(sub: &BTreeMap<&'a str, Vec<&'a str>>, start: &'a str) -> Vec<&'a str> {
        let mut seen: Vec<&'a str> = vec![start];
        let mut queue: Vec<&'a str> = vec![start];
        while let Some(cur) = queue.pop() {
            for sup in sub.get(cur).map(|v| v.as_slice()).unwrap_or(&[]) {
                if !seen.contains(sup) {
                    seen.push(sup);
                    queue.push(sup);
                }
            }
        }
        seen
    }

    // rolled property shapes per class (own wins; BTreeMap keyed by path → canonical order)
    let mut all_classes: Vec<&str> = sub.keys().chain(exts.keys()).chain(attrs.keys()).copied().collect();
    all_classes.sort_unstable();
    all_classes.dedup();

    let mut out = String::from(
        "@prefix sh: <http://www.w3.org/ns/shacl#> .\n@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n@prefix kvasir: <https://kvasir.zndx.org/ns#> .\n\n",
    );
    for class in &all_classes {
        let mut props: BTreeMap<&str, PropShape> = BTreeMap::new();
        for holder in ancestors_of(&sub, class) {
            for (p, x) in attrs.get(holder).map(|v| v.as_slice()).unwrap_or(&[]) {
                let entry = props.entry(p).or_default();
                if entry.datatype.is_none() && entry.class.is_none() {
                    entry.datatype = Some((*x).to_string());
                    entry.values = enums.get(p).map(|v| (*v).clone());
                    if let Some((mn, mx)) = cards.get(&(holder, *p)) {
                        entry.min = Some(*mn);
                        entry.max = *mx;
                    }
                }
            }
            // WINNER-PER-(class,prop) — the SAME deterministic rule as the ddl rollup
            // (existential first, then lexicographic target): a multi-filler property
            // collapses identically on both sides, so the fixpoint holds.
            let holder_exts = exts.get(holder).map(|v| v.as_slice()).unwrap_or(&[]);
            let mut by_prop: BTreeMap<&str, Vec<&(&str, &str, bool)>> = BTreeMap::new();
            for e in holder_exts {
                by_prop.entry(e.0).or_default().push(e);
            }
            for (p, mut group) in by_prop {
                group.sort_by_key(|e| (!e.2, e.1));
                let (_, t, is_ex) = group[0];
                let entry = props.entry(p).or_default();
                if entry.datatype.is_none() && entry.class.is_none() {
                    entry.class = Some((*t).to_string());
                    // an existential defaults to minCount 1 (NOT NULL); a pure @Relation
                    // to 0 (optional). An explicit @Cardinality overrides either — but a
                    // multi-filler property's bounds are ambiguous by construction, so the
                    // winner's default applies there.
                    let (mn, mx) = if group.len() == 1 {
                        cards
                            .get(&(holder, p))
                            .copied()
                            .unwrap_or((if *is_ex { 1 } else { 0 }, None))
                    } else {
                        (if *is_ex { 1 } else { 0 }, None)
                    };
                    entry.min = Some(mn);
                    entry.max = mx;
                }
            }
        }
        if props.is_empty() {
            continue; // same election as ddl: nothing evidenced, no shape
        }
        out.push_str(&format!("<{class}Shape>\n    a sh:NodeShape ;\n    sh:targetClass <{class}> ;\n"));
        // kvasir:key — NOT SHACL Core (Core cannot express cross-node uniqueness); an
        // emitted, documented annotation so a third-party toolchain reproduces the SAME
        // DDL from the shapes graph alone (the fixpoint invariant carries key election).
        if let Some(kprops) = key_of.get(*class) {
            let plist = kprops.iter().map(|k| format!("<{k}>")).collect::<Vec<_>>().join(" ");
            out.push_str(&format!("    kvasir:key ( {plist} ) ;\n"));
        }
        for (path, ps) in &props {
            out.push_str(&format!("    sh:property [\n        sh:path <{path}> ;\n"));
            if unique_props.contains(&path[..]) {
                out.push_str("        kvasir:unique true ;\n");
            }
            if let Some(dt) = &ps.datatype {
                let dt_short = dt
                    .strip_prefix(XSD_NS)
                    .map(|l| format!("xsd:{l}"))
                    .unwrap_or_else(|| format!("<{dt}>"));
                out.push_str(&format!("        sh:datatype {dt_short} ;\n"));
            }
            if let Some(c) = &ps.class {
                out.push_str(&format!("        sh:class <{c}> ;\n"));
            }
            if let Some(vals) = &ps.values {
                let list = vals
                    .iter()
                    .map(|v| format!("\"{v}\""))
                    .collect::<Vec<_>>()
                    .join(" ");
                out.push_str(&format!("        sh:in ({list}) ;\n"));
            }
            if let Some(mn) = ps.min {
                if mn > 0 {
                    out.push_str(&format!("        sh:minCount {mn} ;\n"));
                }
            }
            if let Some(mx) = ps.max {
                out.push_str(&format!("        sh:maxCount {mx} ;\n"));
            }
            out.push_str("    ] ;\n");
        }
        // terminate the NodeShape: swap the final " ;" for " ."
        out.truncate(out.len() - 2);
        out.push_str(".\n\n");
    }
    out
}

// ── INGESTION: SHACL Core Turtle → tiered facts (the lean reader) ──────────────
#[derive(Default)]
struct InProp {
    path: Option<String>,
    unique: bool,
    datatype: Option<String>,
    class: Option<String>,
    min: Option<u32>,
    max: Option<u32>,
    values: Vec<String>,
}

fn expand_xsd(tok: &str) -> String {
    tok.strip_prefix("xsd:")
        .map(|l| format!("{XSD_NS}{l}"))
        .unwrap_or_else(|| tok.trim_start_matches('<').trim_end_matches('>').to_string())
}

fn quoted_list(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '"' {
            let mut v = String::new();
            for x in chars.by_ref() {
                if x == '"' {
                    break;
                }
                v.push(x);
            }
            out.push(v);
        }
    }
    out
}

/// Parse a SHACL-Core shapes graph (the Turtle subset [`emit`] produces / a conformant
/// author writes) back into tiered facts. The inverse of emission: `sh:class` +
/// `sh:minCount≥1` → existential (reasoning tier); `sh:class` without a positive
/// minCount → `@Relation` (nullable); `sh:datatype` → `@Attribute`; `sh:in` → `@Enum`;
/// non-trivial bounds (min>1 or any max) → `@Cardinality` — exactly the forms the omn
/// lowering emits, so the ddl planner is source-agnostic and the round-trip is exact.
pub fn parse(ttl: &str) -> (Vec<Axiom>, Vec<Annotation>) {
    let mut axioms: Vec<Axiom> = Vec::new();
    let mut annotations: Vec<Annotation> = Vec::new();
    let mut enums_seen: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut cur_class: Option<String> = None;
    let mut cur_prop: Option<InProp> = None;

    let angle = |s: &str| s.trim().trim_start_matches('<').trim_end_matches('>').to_string();

    let flush = |p: InProp,
                 class: &str,
                 axioms: &mut Vec<Axiom>,
                 annotations: &mut Vec<Annotation>,
                 enums_seen: &mut BTreeMap<String, Vec<String>>| {
        let Some(path) = p.path else { return };
        if p.unique {
            annotations.push(Annotation::Unique { prop: path.clone() });
        }
        let card_worth = p.min.map(|m| m > 1).unwrap_or(false) || p.max.is_some();
        if let Some(dt) = p.datatype {
            annotations.push(Annotation::Attribute {
                class: class.to_string(),
                prop: path.clone(),
                xsd: dt,
            });
            if !p.values.is_empty() {
                enums_seen.entry(path.clone()).or_insert(p.values);
            }
        } else if let Some(cls) = p.class {
            if p.min.unwrap_or(0) >= 1 {
                axioms.push(Axiom::SubClassOfExistential {
                    sub: class.to_string(),
                    role: path.clone(),
                    filler: cls,
                });
            } else {
                annotations.push(Annotation::Relation {
                    class: class.to_string(),
                    prop: path.clone(),
                    target: cls,
                });
            }
        }
        if card_worth {
            annotations.push(Annotation::Cardinality {
                class: class.to_string(),
                prop: path,
                min: p.min.unwrap_or(0),
                max: p.max,
            });
        }
    };

    for raw in ttl.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('@') || line.starts_with('#') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("sh:targetClass") {
            cur_class = Some(angle(rest.trim_end_matches([';', '.']).trim()));
        } else if let Some(rest) = line.strip_prefix("kvasir:key") {
            if let Some(cls) = cur_class.as_deref() {
                let props: Vec<String> = rest
                    .trim_end_matches([';', '.'])
                    .trim()
                    .trim_start_matches('(')
                    .trim_end_matches(')')
                    .split_whitespace()
                    .map(|t| angle(t))
                    .collect();
                if !props.is_empty() {
                    annotations.push(Annotation::Key { class: cls.to_string(), props });
                }
            }
        } else if line.contains("sh:property") && line.contains('[') {
            cur_prop = Some(InProp::default());
        } else if let Some(p) = cur_prop.as_mut() {
            let body = line.trim_end_matches([';', '.']).trim();
            if let Some(v) = body.strip_prefix("sh:path") {
                p.path = Some(angle(v.trim()));
            } else if let Some(v) = body.strip_prefix("sh:datatype") {
                p.datatype = Some(expand_xsd(v.trim()));
            } else if let Some(v) = body.strip_prefix("sh:class") {
                p.class = Some(angle(v.trim()));
            } else if let Some(v) = body.strip_prefix("sh:minCount") {
                p.min = v.trim().parse().ok();
            } else if let Some(v) = body.strip_prefix("sh:maxCount") {
                p.max = v.trim().parse().ok();
            } else if let Some(v) = body.strip_prefix("sh:in") {
                p.values = quoted_list(v);
            } else if body.strip_prefix("kvasir:unique").is_some() {
                p.unique = true;
            } else if body.starts_with(']') {
                if let (Some(pr), Some(cls)) = (cur_prop.take(), cur_class.as_deref()) {
                    flush(pr, cls, &mut axioms, &mut annotations, &mut enums_seen);
                }
            }
        }
    }
    for (prop, values) in enums_seen {
        annotations.push(Annotation::Enum { prop, values });
    }
    (axioms, annotations)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kvasir_core::parse_kfs_tiered;

    #[test]
    fn shapes_carry_the_tier_and_the_rollup() {
        let kfs = "\
SubClassOf <s#NurseRole> <s#Role>
SubClassOfExistential <s#Role> <s#inheresIn> <s#Bearer>
@Attribute <s#Role> <s#hasStatus> <http://www.w3.org/2001/XMLSchema#string>
@Cardinality <s#Role> <s#inheresIn> 1 1
@Enum <s#hasStatus> \"active\" \"retired\"
";
        let (axioms, annotations) = parse_kfs_tiered(kfs).unwrap();
        let ttl = emit(&axioms, &annotations);
        assert!(ttl.contains("<s#RoleShape>"));
        assert!(ttl.contains("sh:targetClass <s#Role>"));
        assert!(ttl.contains("sh:class <s#Bearer>"));
        assert!(ttl.contains("sh:minCount 1"));
        assert!(ttl.contains("sh:maxCount 1"));
        assert!(ttl.contains("sh:in (\"active\" \"retired\")"));
        // denormalized rollup: NurseRole carries the inherited constraints itself
        assert!(ttl.contains("<s#NurseRoleShape>"));
        let nurse = ttl.split("<s#NurseRoleShape>").nth(1).unwrap();
        assert!(nurse.contains("sh:path <s#inheresIn>"));
        assert!(nurse.contains("sh:datatype xsd:string"));
        // deterministic: same input, same bytes
        assert_eq!(ttl, emit(&axioms, &annotations));
    }

    // The FIXPOINT invariant (RH ruling): shapes are explicit-or-implicit, and feeding
    // kvasir's own emitted shapes back must realize the SAME DDL. Here: omn facts →
    // emit → parse → re-emit must be a fixed point, and the parsed facts must plan to
    // the same tables/FKs (proven byte-exact on the CLI; this locks the module contract).
    #[test]
    fn emitted_shapes_round_trip_to_the_same_facts() {
        let kfs = "\
SubClassOf <s#Blood> <s#Sample>
SubClassOfExistential <s#Sample> <s#storedIn> <s#Freezer>
SubClassOfExistential <s#Sample> <s#testedIn> <s#Assay>
@Attribute <s#Sample> <s#hasBarcode> <http://www.w3.org/2001/XMLSchema#string>
@Cardinality <s#Sample> <s#testedIn> 2 *
@Relation <s#Sample> <s#derivedFrom> <s#Subject>
@Cardinality <s#Sample> <s#derivedFrom> 0 1
@Enum <s#hasBarcode> \"a\" \"b\"
";
        let (ax, an) = parse_kfs_tiered(kfs).unwrap();
        let ttl1 = emit(&ax, &an);
        let (ax2, an2) = parse(&ttl1);
        let ttl2 = emit(&ax2, &an2);
        assert_eq!(ttl1, ttl2, "emit∘parse∘emit must be a fixed point");
        // the storedIn existential survives as NOT NULL (min 1); derivedFrom stays a
        // nullable @Relation; testedIn stays a many (min 2)
        assert!(ax2.iter().any(|a| matches!(a, Axiom::SubClassOfExistential { role, .. } if role.ends_with("storedIn"))));
        assert!(an2.iter().any(|a| matches!(a, Annotation::Relation { prop, .. } if prop.ends_with("derivedFrom"))));
        assert!(an2.iter().any(|a| matches!(a, Annotation::Cardinality { prop, min: 2, .. } if prop.ends_with("testedIn"))));
    }
}
