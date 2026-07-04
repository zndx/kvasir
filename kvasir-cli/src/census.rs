//! census — the PREFLIGHT instrument (`kvasir census <file>`).
//!
//! Tells an ontology author what their ontology can support BEFORE they run ddl:
//! the width-potential distribution (what class_to_table would emit), the
//! out-of-fragment residue (every construct the grammar/fragment could not use,
//! named — the survey posture: refuse comprehensively, report comprehensively),
//! annotation-tier inventory (label coverage drives verbalisation quality), and
//! the saturation verdict as a FIELD rather than a refusal — the census is
//! diagnostic; `ddl` is where inconsistency refuses.
//!
//! Honest-expectations doctrine: BFO/CCO-style ontologies are class/relation-rich
//! and DataProperty-poor; this instrument makes that visible up front instead of
//! letting a thin schema read as a tool defect. Stat names match aegir's
//! `profiles.census` (median/p90/p99/max/ge5_ratio) for cross-instrument reads.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::ddl::Plan;

#[derive(Debug, Serialize)]
pub struct Width {
    pub median: usize,
    pub p90: usize,
    pub p99: usize,
    pub max: usize,
    pub ge5_ratio: f64,
}

#[derive(Debug, Serialize)]
pub struct Census {
    /// `false` means the v0 refutation subset found a clash — `ddl` will refuse.
    pub fragment_no_clash: bool,
    pub n_unsat_classes: usize,
    pub n_tables: usize,
    pub n_elected: usize,
    pub n_reference: usize,
    pub n_junctions: usize,
    pub n_lookups: usize,
    /// Column-width distribution over ELECTED tables (id + attributes + FK columns).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub width: Option<Width>,
    /// Elected tables carrying NO data attribute (only id + FKs) — the property-poverty
    /// signal; the number phase-B-style accretion (or a richer source ontology) moves.
    pub attr_zero_ratio: f64,
    pub label_coverage: f64,
    pub n_warnings: usize,
    /// Out-of-fragment / out-of-grammar residue, named per construct.
    pub residue: BTreeMap<String, usize>,
    pub n_parse_issues: usize,
}

fn pct(sorted: &[usize], q: f64) -> usize {
    if sorted.is_empty() {
        return 0;
    }
    sorted[((q * sorted.len() as f64) as usize).min(sorted.len() - 1)]
}

pub fn census(
    plan: &Plan,
    residue: &BTreeMap<String, usize>,
    n_parse_issues: usize,
    fragment_no_clash: bool,
    n_unsat_classes: usize,
) -> Census {
    let elected: Vec<_> = plan.tables.iter().filter(|t| t.columns.len() > 1).collect();
    let mut widths: Vec<usize> = elected.iter().map(|t| t.columns.len()).collect();
    widths.sort_unstable();
    let width = (!widths.is_empty()).then(|| Width {
        median: pct(&widths, 0.5),
        p90: pct(&widths, 0.9),
        p99: pct(&widths, 0.99),
        max: *widths.last().unwrap(),
        ge5_ratio: widths.iter().filter(|w| **w >= 5).count() as f64 / widths.len() as f64,
    });
    let attr_zero = elected
        .iter()
        .filter(|t| {
            let fk_cols: BTreeSet<&str> = t.fks.iter().map(|f| f.column.as_str()).collect();
            !t.columns
                .iter()
                .any(|c| c.prop.is_some() && !fk_cols.contains(c.name.as_str()))
        })
        .count();
    Census {
        fragment_no_clash,
        n_unsat_classes,
        n_tables: plan.tables.len(),
        n_elected: elected.len(),
        n_reference: plan.n_reference_tables,
        n_junctions: plan.junctions.len(),
        n_lookups: plan.lookups.len(),
        width,
        attr_zero_ratio: if elected.is_empty() {
            0.0
        } else {
            attr_zero as f64 / elected.len() as f64
        },
        label_coverage: if plan.tables.is_empty() {
            0.0
        } else {
            plan.tables.iter().filter(|t| t.label.is_some()).count() as f64
                / plan.tables.len() as f64
        },
        n_warnings: plan.warnings.len(),
        residue: residue.clone(),
        n_parse_issues,
    }
}
