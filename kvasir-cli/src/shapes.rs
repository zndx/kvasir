//! shapes module — the IMPLICIT SHACL Core emission (`kvasir shapes <file.omn>`).
//!
//! SHACL ruling (aegir map §9): shapes are NOT optional — explicit when user-provided,
//! IMPLICIT when kvasir completes the constraints itself to render DDL. This module is
//! the implicit half: derive the shapes graph from the same entailments + annotation
//! tier the ddl module consumes, and EMIT it so users have the standard syntax to
//! extend — and so a third-party conformant SHACL toolchain can realize the same DDL
//! from (ontology + emitted shapes). Ingestion (the explicit case, via the rudof
//! `shacl` crate, default-features=false → Core only) and the fixpoint invariant
//! (own emitted shapes fed back → byte-identical DDL) are the follow-on increment.
//!
//! DENORMALIZED BY DESIGN: each targeted class carries its ROLLED constraints (own +
//! inherited), so no entailment regime is assumed — a plain SHACL Core validator sees
//! exactly what the DDL realizes. Emission is canonical (sorted classes, sorted
//! property paths): same input, same bytes.
//!
//! The tier↔SHACL correspondence this makes literal:
//!   @Attribute  ≡ sh:path + sh:datatype        @Cardinality ≡ sh:minCount/sh:maxCount
//!   @Enum       ≡ sh:in                        existential  ≡ sh:path + sh:class + sh:minCount 1

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
    // told edges + per-class own facts
    let mut sub: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut exts: BTreeMap<&str, Vec<(&str, &str)>> = BTreeMap::new();
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
                    exts.entry(s).or_default().push((role, filler));
                }
            }
            _ => {}
        }
    }
    let mut attrs: BTreeMap<&str, Vec<(&str, &str)>> = BTreeMap::new();
    let mut cards: BTreeMap<(&str, &str), (u32, Option<u32>)> = BTreeMap::new();
    let mut enums: BTreeMap<&str, &Vec<String>> = BTreeMap::new();
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
        "@prefix sh: <http://www.w3.org/ns/shacl#> .\n@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\n",
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
            for (p, t) in exts.get(holder).map(|v| v.as_slice()).unwrap_or(&[]) {
                let entry = props.entry(p).or_default();
                if entry.datatype.is_none() && entry.class.is_none() {
                    entry.class = Some((*t).to_string());
                    let (mn, mx) = cards.get(&(holder, *p)).copied().unwrap_or((1, None));
                    entry.min = Some(mn);
                    entry.max = mx;
                }
            }
        }
        if props.is_empty() {
            continue; // same election as ddl: nothing evidenced, no shape
        }
        out.push_str(&format!("<{class}Shape>\n    a sh:NodeShape ;\n    sh:targetClass <{class}> ;\n"));
        for (path, ps) in &props {
            out.push_str(&format!("    sh:property [\n        sh:path <{path}> ;\n"));
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
}
