//! The pinned fragment: AST + the FRAGMENT GATE.
//!
//! Doctrine rule 1 — refuse, don't approximate. The gate is the engine's first act on any input:
//! constructs outside the pinned fragment are rejected loudly with the offending construct named,
//! never silently weakened. Out-of-fragment inputs belong to the general oracle (HermiT).
//!
//! The KFS v0 surface syntax is deliberately trivial (one axiom per line) so that differential
//! engines cannot diverge at the parser — parser skew is itself a soundness hazard (measured
//! upstream: a prefix-form `Types:` silently degraded an entire Manchester document to a vacuous
//! 11-axiom parse that was "trivially consistent").

use serde::{Deserialize, Serialize};

/// An interned entity name (IRI or local name — the gate does not interpret it).
pub type Name = String;

/// The pinned-fragment axiom forms. Everything the engine reasons about is one of these; there is
/// no "other" variant by design — anything else fails the gate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Axiom {
    /// `c ⊑ d`
    SubClassOf { sub: Name, sup: Name },
    /// `c ≡ a₁ ⊓ a₂ ⊓ …` (genus–differentia definitions; the told direction `c ⊑ aᵢ` is v0-active)
    EquivalentToIntersection { class: Name, parts: Vec<Name> },
    /// `c ⊑ ∃r.d` — admitted by the gate, inert at v0 (sound for refutation: fewer derivations
    /// can only miss clashes, never invent them). Active in the T3 EL⁺ rule set.
    SubClassOfExistential { sub: Name, role: Name, filler: Name },
    /// `Disjoint(a, b)` (pairwise)
    DisjointClasses { a: Name, b: Name },
    /// `i : c` — a Types-only ABox assertion (no role assertions between individuals at v0;
    /// this is the machine-checked precondition of the upstream decomposition theorem)
    ClassAssertion { class: Name, individual: Name },
}

/// A loud, named rejection. The gate never guesses.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct OutOfFragment {
    pub line: usize,
    pub construct: String,
    pub detail: String,
}

impl std::fmt::Display for OutOfFragment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "out of fragment at line {}: {} — {} (kvasir refuses; route to the general oracle)",
            self.line, self.construct, self.detail
        )
    }
}

impl std::error::Error for OutOfFragment {}

/// Constructs we RECOGNIZE and refuse by name — the known-expensive shapes from the tractability
/// audit (nominals, inverses, transitivity, unbounded cardinality, unions) plus role assertions
/// (which would void the ABox decomposition precondition).
const REFUSED: &[(&str, &str)] = &[
    (
        "InverseObjectProperties",
        "inverse roles force pairwise blocking",
    ),
    (
        "TransitiveObjectProperty",
        "transitivity expands concept closure",
    ),
    ("ObjectHasValue", "nominal (hasValue)"),
    ("ObjectOneOf", "nominal (oneOf)"),
    (
        "ObjectUnionOf",
        "covering disjunctions fan out the label space",
    ),
    (
        "ObjectComplementOf",
        "general negation is outside the Horn fragment",
    ),
    (
        "ObjectMinCardinality",
        "cardinality clausification is O(n²)",
    ),
    (
        "ObjectMaxCardinality",
        "cardinality clausification is O(n²)",
    ),
    (
        "ObjectExactCardinality",
        "cardinality clausification is O(n²)",
    ),
    (
        "ObjectPropertyAssertion",
        "role assertions void the Types-only ABox decomposition",
    ),
    (
        "SameIndividual",
        "individual equality voids the disjoint-union amalgamation",
    ),
    (
        "DifferentIndividuals",
        "individual inequality is out of the v0 ABox shape",
    ),
];

/// Parse one KFS line through the gate. `Ok(None)` = blank/comment.
pub fn parse_line(line_no: usize, raw: &str) -> Result<Option<Axiom>, OutOfFragment> {
    let line = raw.split('#').next().unwrap_or("").trim();
    if line.is_empty() {
        return Ok(None);
    }
    let mut toks = line.split_whitespace();
    let head = toks.next().unwrap_or("");
    let args: Vec<String> = toks.map(strip_angles).collect();
    let arity = |n: usize, form: &str| -> Result<(), OutOfFragment> {
        if args.len() == n {
            Ok(())
        } else {
            Err(OutOfFragment {
                line: line_no,
                construct: head.to_string(),
                detail: format!("{form} expects {n} argument(s), got {}", args.len()),
            })
        }
    };
    match head {
        "SubClassOf" => {
            arity(2, "SubClassOf <sub> <sup>")?;
            Ok(Some(Axiom::SubClassOf {
                sub: args[0].clone(),
                sup: args[1].clone(),
            }))
        }
        "EquivalentToIntersection" => {
            if args.len() < 2 {
                return Err(OutOfFragment {
                    line: line_no,
                    construct: head.to_string(),
                    detail: "expects <class> then ≥1 conjunct".to_string(),
                });
            }
            Ok(Some(Axiom::EquivalentToIntersection {
                class: args[0].clone(),
                parts: args[1..].to_vec(),
            }))
        }
        "SubClassOfExistential" => {
            arity(3, "SubClassOfExistential <sub> <role> <filler>")?;
            Ok(Some(Axiom::SubClassOfExistential {
                sub: args[0].clone(),
                role: args[1].clone(),
                filler: args[2].clone(),
            }))
        }
        "DisjointClasses" => {
            arity(2, "DisjointClasses <a> <b>")?;
            Ok(Some(Axiom::DisjointClasses {
                a: args[0].clone(),
                b: args[1].clone(),
            }))
        }
        "ClassAssertion" => {
            arity(2, "ClassAssertion <class> <individual>")?;
            Ok(Some(Axiom::ClassAssertion {
                class: args[0].clone(),
                individual: args[1].clone(),
            }))
        }
        other => {
            let detail = REFUSED
                .iter()
                .find(|(name, _)| *name == other)
                .map(|(_, why)| (*why).to_string())
                .unwrap_or_else(|| "unknown construct".to_string());
            Err(OutOfFragment {
                line: line_no,
                construct: other.to_string(),
                detail,
            })
        }
    }
}

/// Parse a whole KFS document; the FIRST out-of-fragment line aborts the run (refuse-loud).
pub fn parse_kfs(text: &str) -> Result<Vec<Axiom>, OutOfFragment> {
    let mut out = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        if let Some(ax) = parse_line(i + 1, raw)? {
            out.push(ax);
        }
    }
    Ok(out)
}

fn strip_angles(t: &str) -> String {
    t.trim_start_matches('<').trim_end_matches('>').to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admits_the_fragment() {
        let doc = "\
# the dual-grounding shape
SubClassOf <process> <occurrent>
EquivalentToIntersection <dual> <process> <continuant>
SubClassOfExistential <role> <realized_in> <process>
DisjointClasses <continuant> <occurrent>
ClassAssertion <dual> <i_sample_01>
";
        let axs = parse_kfs(doc).expect("in-fragment doc must parse");
        assert_eq!(axs.len(), 5);
    }

    #[test]
    fn refuses_known_expensive_constructs_by_name() {
        for (construct, _) in REFUSED {
            let doc = format!("{construct} <a> <b>");
            let err = parse_kfs(&doc).expect_err("must refuse");
            assert_eq!(&err.construct, construct);
            assert!(!err.detail.is_empty(), "refusal must carry its reason");
        }
    }

    #[test]
    fn refuses_unknown_constructs_loudly() {
        let err = parse_kfs("HasKey <a> <p>").expect_err("must refuse");
        assert_eq!(err.construct, "HasKey");
    }

    #[test]
    fn arity_errors_are_out_of_fragment() {
        assert!(parse_kfs("SubClassOf <a>").is_err());
        assert!(parse_kfs("DisjointClasses <a> <b> <c>").is_err());
    }
}
