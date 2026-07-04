//! ddl module — certified entailments + annotations → PROOF-CARRYING semantic DDL.
//!
//! Every emitted element (table, column, FK, junction, lookup) carries `cites`: the
//! SOURCE line numbers (the user's .omn when lowered internally; the .kfs lines
//! otherwise) of the axioms/annotations that JUSTIFY it. The tool cites; it never
//! proves — `kvasir-core` saturates first and an inconsistent ontology REFUSES DDL
//! emission with the refutation as the reason (schema from falsehood is no schema).
//!
//! v0 rules (design of record: aegir map §7, "ddl module v0 decisions"):
//!   - table per class with ≥1 rolled-up attribute or outgoing existential; bare
//!     id-only reference tables for FK targets not otherwise elected
//!   - told-closure rollup: subclasses inherit superclass @Attributes + existentials
//!     (entailed), deduped by property, own declaration wins; cites carry the
//!     subsumption path
//!   - `some`/`exactly 1`/`min 1` → FK column NOT NULL; `max 1` → nullable FK;
//!     bounds beyond 1 → junction table; `@Enum` → lookup table + FK rewrite
//!   - `PropertyRange` cites join the FK; a mis-domained FK is a WARNING w/ citation
//!   - SEMANTIC register only (IRI-local snake_case); worldly renames stay downstream
//!   - every rendered statement must parse under sqlparser (GenericDialect) before
//!     leaving the process — the self-check-before-verdict doctrine on this output

use std::collections::{BTreeMap, BTreeSet};

use kvasir_core::{Annotation, Axiom};
use serde::Serialize;

#[derive(Debug, Serialize)]
pub struct Column {
    pub name: String,
    pub sql_type: String,
    pub nullable: bool,
    pub pk: bool,
    /// The property IRI this column realizes (absent for the surrogate id).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prop: Option<String>,
    /// Human-legible COMMENT payload (verbalised beside the citation — the comment is
    /// the citation's readable rendering, never a replacement for it).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<String>,
    pub cites: Vec<usize>,
}

#[derive(Debug, Serialize)]
pub struct Fk {
    pub column: String,
    pub target_class: String,
    pub target_table: String,
    pub cites: Vec<usize>,
}

#[derive(Debug, Serialize)]
pub struct Table {
    pub class: String,
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<String>,
    pub columns: Vec<Column>,
    pub fks: Vec<Fk>,
    pub cites: Vec<usize>,
}

#[derive(Debug, Serialize)]
pub struct Junction {
    pub name: String,
    pub subject_class: String,
    pub subject_table: String,
    pub target_class: String,
    pub target_table: String,
    pub prop: String,
    pub cites: Vec<usize>,
}

#[derive(Debug, Serialize)]
pub struct Lookup {
    pub name: String,
    pub prop: String,
    pub values: Vec<String>,
    pub cites: Vec<usize>,
}

#[derive(Debug, Serialize)]
pub struct Plan {
    pub tables: Vec<Table>,
    pub junctions: Vec<Junction>,
    pub lookups: Vec<Lookup>,
    pub warnings: Vec<String>,
    pub n_reference_tables: usize,
    pub sql_valid: bool,
}

// ── naming (semantic register) ─────────────────────────────────────────────────
fn local(iri: &str) -> &str {
    iri.rsplit(['#', '/']).next().unwrap_or(iri)
}

fn snake(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    let mut prev_lower = false;
    for c in s.chars() {
        if c.is_ascii_uppercase() {
            if prev_lower {
                out.push('_');
            }
            out.push(c.to_ascii_lowercase());
            prev_lower = false;
        } else if c.is_ascii_alphanumeric() {
            prev_lower = c.is_ascii_lowercase() || c.is_ascii_digit();
            out.push(c);
        } else {
            if !out.ends_with('_') && !out.is_empty() {
                out.push('_');
            }
            prev_lower = false;
        }
    }
    let trimmed = out.trim_matches('_').to_string();
    if trimmed.is_empty() {
        "t".to_string()
    } else if trimmed.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        format!("t_{trimmed}")
    } else {
        trimmed
    }
}

fn prop_col(iri: &str) -> String {
    let l = local(iri);
    let stripped = l
        .strip_prefix("has")
        .or_else(|| l.strip_prefix("is"))
        .filter(|r| r.chars().next().is_some_and(|c| c.is_ascii_uppercase() || c == '_'))
        .unwrap_or(l);
    snake(stripped)
}

fn sql_type(xsd: &str) -> &'static str {
    match local(xsd) {
        "dateTime" => "TIMESTAMP",
        "date" => "DATE",
        "decimal" => "DECIMAL(38,9)",
        "double" | "float" => "DOUBLE",
        "integer" | "int" => "INTEGER",
        "long" => "BIGINT",
        "boolean" => "BOOLEAN",
        _ => "VARCHAR(255)",
    }
}

const XSD_NS: &str = "http://www.w3.org/2001/XMLSchema#";

/// Label-first display name for comments (falls back to the local name as words).
fn display(labels: &BTreeMap<&str, (&str, usize)>, iri: &str) -> String {
    labels
        .get(iri)
        .map(|(l, _)| (*l).to_string())
        .unwrap_or_else(|| crate::verbalise::words(local(iri)))
}

fn bound_phrase(min: u32, max: Option<u32>) -> String {
    match (min, max) {
        (m, Some(x)) if m == x => format!("exactly {m}"),
        (0, Some(x)) => format!("at most {x}"),
        (m, None) => format!("at least {m}"),
        (m, Some(x)) => format!("{m} to {x}"),
    }
}

// ── the planner ────────────────────────────────────────────────────────────────
/// Build the semantic DDL plan. `ax_cite[i]` / `ann_cite[j]` are the source lines of
/// the i-th axiom / j-th annotation (the citation provenance).
pub fn plan(
    axioms: &[Axiom],
    annotations: &[Annotation],
    ax_cite: &[usize],
    ann_cite: &[usize],
) -> Plan {
    // ── indexes (everything keyed by full IRI, carrying its citation) ──────────
    let mut sub: BTreeMap<&str, Vec<(&str, usize)>> = BTreeMap::new();
    // (prop, target, cite, is_existential) — an existential relation is NOT NULL (min≥1);
    // an @Relation (max/only) is optional. When a property has BOTH, dedup keeps the
    // existential (it is pushed first, from the axiom loop) so the NOT NULL wins.
    let mut exts: BTreeMap<&str, Vec<(&str, &str, usize, bool)>> = BTreeMap::new();
    let mut ranges: BTreeMap<&str, (&str, usize)> = BTreeMap::new();
    let mut domains: BTreeMap<&str, (&str, usize)> = BTreeMap::new();
    for (i, ax) in axioms.iter().enumerate() {
        let c = ax_cite.get(i).copied().unwrap_or(0);
        match ax {
            Axiom::SubClassOf { sub: s, sup } => sub.entry(s).or_default().push((sup, c)),
            Axiom::EquivalentToIntersection { class, parts } => {
                for p in parts {
                    sub.entry(class).or_default().push((p, c));
                }
            }
            Axiom::SubClassOfExistential { sub: s, role, filler } => {
                if !filler.starts_with(XSD_NS) && !filler.starts_with("xsd:") {
                    exts.entry(s).or_default().push((role, filler, c, true));
                }
            }
            Axiom::PropertyRange { role, range } => {
                ranges.insert(role, (range, c));
            }
            Axiom::PropertyDomain { role, domain } => {
                domains.insert(role, (domain, c));
            }
            _ => {}
        }
    }
    let mut attrs: BTreeMap<&str, Vec<(&str, &str, usize)>> = BTreeMap::new();
    let mut cards: BTreeMap<(&str, &str), (u32, Option<u32>, usize)> = BTreeMap::new();
    let mut enums: BTreeMap<&str, (&Vec<String>, usize)> = BTreeMap::new();
    let mut labels: BTreeMap<&str, (&str, usize)> = BTreeMap::new();
    for (j, an) in annotations.iter().enumerate() {
        let c = ann_cite.get(j).copied().unwrap_or(0);
        match an {
            Annotation::Attribute { class, prop, xsd } => {
                attrs.entry(class).or_default().push((prop, xsd, c));
            }
            Annotation::Cardinality { class, prop, min, max } => {
                cards.insert((class, prop), (*min, *max, c));
            }
            Annotation::Enum { prop, values } => {
                enums.insert(prop, (values, c));
            }
            Annotation::Label { entity, text } => {
                labels.entry(entity).or_insert((text, c));
            }
            Annotation::Relation { class, prop, target } => {
                // a schema-real, non-existential relation (max/only) — an OPTIONAL FK.
                // Pushed after the existentials so rollup's per-property dedup keeps an
                // existential (NOT NULL) when both name the property. Nullability is
                // driven by is_existential (below), NOT by a cardinality entry — a
                // co-present `some` must not be nullified by an `only`.
                exts.entry(class).or_default().push((prop, target, c, false));
            }
        }
    }

    // ── reflexive-transitive told closure with edge-cite paths ──────────────────
    // ancestors(c) = [(ancestor, path_cites)] — BFS, cycle-safe, deterministic order
    let ancestors = |start: &str| -> Vec<(String, Vec<usize>)> {
        let mut out: Vec<(String, Vec<usize>)> = Vec::new();
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut queue: Vec<(String, Vec<usize>)> = vec![(start.to_string(), Vec::new())];
        seen.insert(start.to_string());
        while let Some((cur, path)) = queue.pop() {
            for (sup, cite) in sub.get(cur.as_str()).map(|v| v.as_slice()).unwrap_or(&[]) {
                if seen.insert((*sup).to_string()) {
                    let mut p = path.clone();
                    p.push(*cite);
                    out.push(((*sup).to_string(), p.clone()));
                    queue.push(((*sup).to_string(), p));
                }
            }
        }
        out
    };

    // ── election: classes with own-or-inherited structure ──────────────────────
    let mut all_classes: BTreeSet<&str> = BTreeSet::new();
    all_classes.extend(sub.keys().copied());
    all_classes.extend(exts.keys().copied());
    all_classes.extend(attrs.keys().copied());

    struct Rolled<'a> {
        attrs: Vec<(&'a str, &'a str, Vec<usize>)>, // prop, xsd, cites
        // prop, target, cites, HOLDER (the class the existential was declared on — the
        // @Cardinality annotation is keyed there, so a subclass's inherited relation
        // must resolve its bound at the holder, not at the subclass; else min-2 etc.
        // silently downgrades to a single FK on every subclass — the projection leak
        // the falsification test caught), is_existential (NOT NULL vs optional FK).
        exts: Vec<(&'a str, &'a str, Vec<usize>, &'a str, bool)>,
    }
    let mut rolled: BTreeMap<&str, Rolled> = BTreeMap::new();
    for class in &all_classes {
        let mut seen_prop: BTreeSet<&str> = BTreeSet::new();
        let mut r = Rolled { attrs: Vec::new(), exts: Vec::new() };
        for (p, x, c) in attrs.get(class).map(|v| v.as_slice()).unwrap_or(&[]) {
            if seen_prop.insert(p) {
                r.attrs.push((p, x, vec![*c]));
            }
        }
        for (p, t, c, is_ex) in exts.get(class).map(|v| v.as_slice()).unwrap_or(&[]) {
            if seen_prop.insert(p) {
                r.exts.push((p, t, vec![*c], class, *is_ex));
            }
        }
        for (anc, path) in ancestors(class) {
            let key: &str = all_classes.get(anc.as_str()).copied().unwrap_or_default();
            if key.is_empty() {
                continue;
            }
            for (p, x, c) in attrs.get(key).map(|v| v.as_slice()).unwrap_or(&[]) {
                if seen_prop.insert(p) {
                    let mut cites = vec![*c];
                    cites.extend(&path);
                    r.attrs.push((p, x, cites));
                }
            }
            for (p, t, c, is_ex) in exts.get(key).map(|v| v.as_slice()).unwrap_or(&[]) {
                if seen_prop.insert(p) {
                    let mut cites = vec![*c];
                    cites.extend(&path);
                    r.exts.push((p, t, cites, key, *is_ex));
                }
            }
        }
        // canonical column order: sort by property IRI so the emitted schema is
        // SOURCE-INDEPENDENT (an omn and its own emitted shapes yield byte-identical
        // DDL — the fixpoint invariant; and any two runs agree regardless of rollup path).
        r.attrs.sort_by(|a, b| a.0.cmp(b.0));
        r.exts.sort_by(|a, b| a.0.cmp(b.0));
        rolled.insert(class, r);
    }

    let elected: BTreeSet<&str> = rolled
        .iter()
        .filter(|(_, r)| !r.attrs.is_empty() || !r.exts.is_empty())
        .map(|(c, _)| *c)
        .collect();

    // FK targets need a table to point at; un-elected targets become bare reference tables
    let mut reference: BTreeSet<&str> = BTreeSet::new();
    for class in &elected {
        for (_, t, _, _, _) in &rolled[class].exts {
            if !elected.contains(t) {
                reference.insert(t);
            }
        }
    }

    // ── table names (collision-deduped, deterministic) ─────────────────────────
    let mut names: BTreeMap<&str, String> = BTreeMap::new();
    let mut used: BTreeSet<String> = BTreeSet::new();
    let mut warnings: Vec<String> = Vec::new();
    for class in elected.iter().chain(reference.iter()) {
        let base = snake(local(class));
        let mut name = base.clone();
        let mut k = 2;
        while !used.insert(name.clone()) {
            name = format!("{base}_{k}");
            k += 1;
        }
        if name != base {
            warnings.push(format!("table name collision: {class} -> {name}"));
        }
        names.insert(class, name);
    }

    // ── emission ────────────────────────────────────────────────────────────────
    let mut tables: Vec<Table> = Vec::new();
    let mut junctions: Vec<Junction> = Vec::new();
    let mut lookups: BTreeMap<&str, Lookup> = BTreeMap::new();

    for class in &elected {
        let r = &rolled[class];
        let tname = names[class].clone();
        let mut columns = vec![Column {
            name: "id".into(),
            sql_type: "VARCHAR(255)".into(),
            nullable: false,
            pk: true,
            prop: None,
            comment: None,
            cites: Vec::new(),
        }];
        let mut fks: Vec<Fk> = Vec::new();
        let mut used_cols: BTreeSet<String> = BTreeSet::new();
        used_cols.insert("id".into());
        let uniq = |used: &mut BTreeSet<String>, base: String| -> String {
            let mut n = base.clone();
            let mut k = 2;
            while !used.insert(n.clone()) {
                n = format!("{base}_{k}");
                k += 1;
            }
            n
        };

        for (p, x, cites) in &r.attrs {
            let col = uniq(&mut used_cols, prop_col(p));
            if let Some((values, ec)) = enums.get(*p) {
                let lut_name = format!("{}_lut", prop_col(p));
                lookups.entry(p).or_insert_with(|| Lookup {
                    name: lut_name.clone(),
                    prop: (*p).to_string(),
                    values: (*values).clone(),
                    cites: vec![*ec],
                });
                let mut fk_cites = cites.clone();
                fk_cites.push(*ec);
                fks.push(Fk {
                    column: col.clone(),
                    target_class: (*p).to_string(),
                    target_table: lut_name,
                    cites: fk_cites,
                });
                columns.push(Column {
                    name: col,
                    sql_type: "VARCHAR(64)".into(),
                    nullable: true,
                    pk: false,
                    prop: Some((*p).to_string()),
                    comment: Some(format!(
                        "the {} of this {} (closed value set)",
                        crate::verbalise::words(local(p)),
                        display(&labels, class),
                    )),
                    cites: cites.clone(),
                });
            } else {
                columns.push(Column {
                    name: col,
                    sql_type: sql_type(x).into(),
                    nullable: true,
                    pk: false,
                    prop: Some((*p).to_string()),
                    comment: Some(format!(
                        "the {} of this {} ({})",
                        crate::verbalise::words(local(p)),
                        display(&labels, class),
                        local(x),
                    )),
                    cites: cites.clone(),
                });
            }
        }

        for (p, t, cites, holder, is_ex) in &r.exts {
            let mut cites = cites.clone();
            if let Some((rng, rc)) = ranges.get(*p) {
                cites.push(*rc);
                let _ = rng;
            }
            if let Some((dom, dc)) = domains.get(*p) {
                let dom_ok = *class == *dom
                    || ancestors(class).iter().any(|(a, _)| a == dom);
                if !dom_ok {
                    warnings.push(format!(
                        "mis-domained FK: {class} via {p} but domain is {dom} (cite {dc})"
                    ));
                }
            }
            // resolve the bound at the HOLDER (leak-1 fix): a subclass inherits the
            // parent's @Cardinality, so min-2 stays a junction on the subclass too.
            let bounds = cards
                .get(&(*holder, *p))
                .copied()
                .unwrap_or((1, None, 0));
            let (min, max, bc) = bounds;
            if bc != 0 {
                cites.push(bc);
            }
            // nullability is the EXISTENTIAL question, not the cardinality one: a `some`
            // is NOT NULL even if an `only`/`max` co-names the property (the fixpoint
            // caught this). A pure @Relation's effective min is 0 for display/nullable.
            let eff_min = if *is_ex { min.max(1) } else { 0 };
            // junction iff GENUINE multiplicity — min>1 or max>1. `some`/`min 1`/`exactly 1`
            // are all minCount 1 in a shapes graph (∃ IS min 1), so they must realize
            // identically (single FK) or the round-trip cannot recover the distinction —
            // the fixpoint forces the principled rule.
            let many = min > 1 || max.is_some_and(|m| m > 1);
            let single = !many;
            if single {
                let col = uniq(&mut used_cols, prop_col(p));
                columns.push(Column {
                    name: col.clone(),
                    sql_type: "VARCHAR(255)".into(),
                    nullable: !is_ex,
                    pk: false,
                    prop: Some((*p).to_string()),
                    comment: Some(format!(
                        "references the {} this {} {} ({})",
                        display(&labels, t),
                        display(&labels, class),
                        crate::verbalise::words(local(p)),
                        bound_phrase(eff_min, max),
                    )),
                    cites: cites.clone(),
                });
                fks.push(Fk {
                    column: col,
                    target_class: (*t).to_string(),
                    target_table: names[t].clone(),
                    cites,
                });
            } else {
                junctions.push(Junction {
                    name: format!("{}_{}", tname, prop_col(p)),
                    subject_class: (*class).to_string(),
                    subject_table: tname.clone(),
                    target_class: (*t).to_string(),
                    target_table: names[t].clone(),
                    prop: (*p).to_string(),
                    cites,
                });
            }
        }

        let mut cites: Vec<usize> = Vec::new();
        let label = labels.get(*class).map(|(l, lc)| {
            cites.push(*lc);
            (*l).to_string()
        });
        let comment = Some(format!("one row per {}", display(&labels, class)));
        tables.push(Table {
            class: (*class).to_string(),
            name: tname,
            label,
            comment,
            columns,
            fks,
            cites,
        });
    }

    for class in &reference {
        let label = labels.get(*class).map(|(l, _)| (*l).to_string());
        tables.push(Table {
            class: (*class).to_string(),
            name: names[class].clone(),
            label,
            comment: Some(format!("reference: one row per {}", display(&labels, class))),
            columns: vec![Column {
                name: "id".into(),
                sql_type: "VARCHAR(255)".into(),
                nullable: false,
                pk: true,
                prop: None,
                comment: None,
                cites: Vec::new(),
            }],
            fks: Vec::new(),
            cites: Vec::new(),
        });
    }

    Plan {
        tables,
        junctions,
        lookups: lookups.into_values().collect(),
        warnings,
        n_reference_tables: reference.len(),
        sql_valid: false, // set by render_and_check
    }
}

// ── SQL rendering + the sqlparser self-check ───────────────────────────────────
/// Render CREATE TABLE statements for the plan and self-check EVERY statement
/// through sqlparser (GenericDialect). Returns (statements, all_valid).
pub fn render_and_check(p: &Plan) -> (Vec<String>, bool) {
    let mut stmts: Vec<String> = Vec::new();
    for lut in &p.lookups {
        stmts.push(format!(
            "CREATE TABLE {} (\n  code VARCHAR(64),\n  PRIMARY KEY (code)\n)",
            lut.name
        ));
    }
    for t in &p.tables {
        let mut lines: Vec<String> = Vec::new();
        for c in &t.columns {
            let nn = if c.nullable { "" } else { " NOT NULL" };
            lines.push(format!("  {} {}{}", c.name, c.sql_type, nn));
        }
        lines.push("  PRIMARY KEY (id)".to_string());
        for fk in &t.fks {
            let target_col = if fk.target_table.ends_with("_lut") { "code" } else { "id" };
            lines.push(format!(
                "  FOREIGN KEY ({}) REFERENCES {}({})",
                fk.column, fk.target_table, target_col
            ));
        }
        stmts.push(format!("CREATE TABLE {} (\n{}\n)", t.name, lines.join(",\n")));
    }
    for j in &p.junctions {
        stmts.push(format!(
            "CREATE TABLE {} (\n  {}_id VARCHAR(255) NOT NULL,\n  {}_id VARCHAR(255) NOT NULL,\n  PRIMARY KEY ({}_id, {}_id),\n  FOREIGN KEY ({}_id) REFERENCES {}(id),\n  FOREIGN KEY ({}_id) REFERENCES {}(id)\n)",
            j.name,
            j.subject_table, j.target_table,
            j.subject_table, j.target_table,
            j.subject_table, j.subject_table,
            j.target_table, j.target_table,
        ));
    }
    let dialect = sqlparser::dialect::GenericDialect {};
    let all_valid = stmts
        .iter()
        .all(|s| sqlparser::parser::Parser::parse_sql(&dialect, s).is_ok());
    (stmts, all_valid)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kvasir_core::parse_kfs_tiered;

    const KFS: &str = "\
SubClassOf <s#Role> <b#Continuant>
SubClassOfExistential <s#Role> <s#inheresIn> <s#Bearer>
SubClassOfExistential <s#Role> <s#realizes> <s#Act>
SubClassOfExistential <s#Act> <s#hasCount> <xsd:integer>
SubClassOf <s#NurseRole> <s#Role>
PropertyDomain <s#inheresIn> <s#Role>
@Attribute <s#Role> <s#hasStatus> <http://www.w3.org/2001/XMLSchema#string>
@Cardinality <s#Role> <s#inheresIn> 1 1
@Cardinality <s#Role> <s#realizes> 2 *
@Enum <s#hasStatus> \"active\" \"retired\"
@Label <s#Role> \"role\"
";

    #[test]
    fn plan_emits_cited_tables_fks_junctions_lookups() {
        let (axioms, annotations) = parse_kfs_tiered(KFS).unwrap();
        let ax_c: Vec<usize> = (1..=axioms.len()).collect();
        let ann_c: Vec<usize> = (100..100 + annotations.len()).collect();
        let p = plan(&axioms, &annotations, &ax_c, &ann_c);
        let role = p.tables.iter().find(|t| t.name == "role").expect("role table");
        assert_eq!(role.label.as_deref(), Some("role"));
        // exactly-1 relation → single NOT NULL FK column, cited
        let fk = role.fks.iter().find(|f| f.column == "inheres_in").expect("fk");
        assert!(!fk.cites.is_empty());
        // 1..* relation → junction
        assert!(p.junctions.iter().any(|j| j.prop.ends_with("realizes")));
        // enum → lookup + FK rewrite
        assert_eq!(p.lookups.len(), 1);
        assert!(role.fks.iter().any(|f| f.target_table == "status_lut"));
        // inheritance rollup: NurseRole inherits the attribute + relations, cites carry the path
        let nurse = p.tables.iter().find(|t| t.name == "nurse_role").expect("nurse");
        let status = nurse.columns.iter().find(|c| c.name == "status").expect("inherited");
        assert!(status.cites.len() >= 2, "attribute cite + subsumption path");
        // xsd existential is an attribute, not an FK target: no table for xsd:integer
        assert!(!p.tables.iter().any(|t| t.class.contains("XMLSchema")));
        // reference table for Bearer (FK target without own structure)
        assert!(p.tables.iter().any(|t| t.name == "bearer" && t.columns.len() == 1));
        let (stmts, ok) = render_and_check(&p);
        assert!(ok, "sqlparser must accept every rendered statement:\n{}", stmts.join(";\n"));
    }

    // The falsification test made permanent: EVERY upstream richness form must project
    // through the toolchain — else "adds no width by design" is false (RH, 2026-07-04).
    const ENRICHED: &str = "\
SubClassOf <s#Blood> <s#Sample>
SubClassOfExistential <s#Sample> <s#storedIn> <s#Freezer>
@Attribute <s#Sample> <s#hasBarcode> <http://www.w3.org/2001/XMLSchema#string>
@Cardinality <s#Sample> <s#storedIn> 1 1
@Cardinality <s#Sample> <s#testedIn> 2 *
SubClassOfExistential <s#Sample> <s#testedIn> <s#Assay>
@Relation <s#Sample> <s#derivedFrom> <s#Subject>
@Cardinality <s#Sample> <s#derivedFrom> 0 1
";

    #[test]
    fn leak1_cardinality_rolls_up_through_inheritance() {
        // min-2 on the parent must stay a JUNCTION on the subclass, not downgrade to a FK
        let (ax, an) = parse_kfs_tiered(ENRICHED).unwrap();
        let p = plan(&ax, &an, &(1..=ax.len()).collect::<Vec<_>>(), &(1..=an.len()).collect::<Vec<_>>());
        assert!(p.junctions.iter().any(|j| j.subject_table == "sample" && j.prop.ends_with("testedIn")));
        assert!(
            p.junctions.iter().any(|j| j.subject_table == "blood" && j.prop.ends_with("testedIn")),
            "the subclass must inherit the many-to-many as a junction, not a single FK"
        );
        assert!(!p.tables.iter().any(|t| t.name == "blood" && t.columns.iter().any(|c| c.name == "tested_in")));
    }

    #[test]
    fn leak2_max_only_relations_render_as_nullable_fks() {
        // @Relation (max/only — schema-real, not existentially forced) → a NULLABLE FK,
        // inherited by the subclass; without this the relation vanished entirely
        let (ax, an) = parse_kfs_tiered(ENRICHED).unwrap();
        let p = plan(&ax, &an, &(1..=ax.len()).collect::<Vec<_>>(), &(1..=an.len()).collect::<Vec<_>>());
        for tbl in ["sample", "blood"] {
            let t = p.tables.iter().find(|t| t.name == tbl).unwrap();
            let df = t.columns.iter().find(|c| c.name == "derived_from")
                .unwrap_or_else(|| panic!("{tbl} must carry the max-1 relation as a column"));
            assert!(df.nullable, "a max-1 relation is an OPTIONAL FK");
            assert!(t.fks.iter().any(|f| f.column == "derived_from" && f.target_table == "subject"));
        }
        let (_, ok) = render_and_check(&p);
        assert!(ok);
    }
}
