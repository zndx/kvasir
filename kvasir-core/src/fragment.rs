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
    /// `c ⊑ ∃r.d` — ACTIVE since P0: feeds R-domain (subject typing) and the ∃-⊥ family
    /// (a required successor in an empty class refutes the subject).
    SubClassOfExistential { sub: Name, role: Name, filler: Name },
    /// `Disjoint(a, b)` (pairwise)
    DisjointClasses { a: Name, b: Name },
    /// `i : c` — a Types-only ABox assertion (no role assertions between individuals at v0;
    /// this is the machine-checked precondition of the upstream decomposition theorem)
    ClassAssertion { class: Name, individual: Name },
    /// `range(r) ⊑ c` — every r-successor is a c (P0; participates in the ∃-⊥ family:
    /// a filler jointly unsatisfiable with the range empties the successor).
    PropertyRange { role: Name, range: Name },
    /// `domain(r) ⊑ c` — every r-subject is a c (P0; R-domain derives `sub ⊑ c` from any
    /// `sub ⊑ ∃r.d`, feeding the told closure and the disjointness clash join).
    PropertyDomain { role: Name, domain: Name },
}

/// The ANNOTATION TIER — worldly structure DDL needs but the calculus refuses (cardinality
/// bounds, attribute typing, enumerations, labels). A visible fragment WIDENING with two named
/// consumers (kvasir-ddl, the differential harness), never a silent leak into reasoning:
/// `@`-sigiled forms route here and are UNREPRESENTABLE in proofs by construction — `saturate`
/// and `kvasir-check` take `Vec<Axiom>` only. The reasoning gate is unchanged: a bare
/// cardinality construct stays refused by name; an unknown `@`-form is refused exactly like an
/// unknown bare form. (Design: aegir kvasir-ddl map §3, 2026-07-04.)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Annotation {
    /// `@Attribute <class> <prop> <xsd>` — a typed data attribute (a column candidate)
    Attribute { class: Name, prop: Name, xsd: Name },
    /// `@Cardinality <class> <prop> <min> <max|*>` — TRUE bounds; the reasoning lowering weakens
    /// `exactly n` to `some`, the DDL source must not (`exactly 1` → `1 1`)
    Cardinality {
        class: Name,
        prop: Name,
        min: u32,
        max: Option<u32>,
    },
    /// `@Enum <prop> "v" …` — a closed value set (lookup-table fuel)
    Enum { prop: Name, values: Vec<String> },
    /// `@Unique <prop>` — an InverseFunctional object property (the FOAF-mbox identity
    /// idiom): the referencing FK column carries a UNIQUE constraint in the DDL lowering.
    Unique { prop: Name },
    /// `@Key <class> <prop> [<prop>…]` — an OWL 2 `HasKey` axiom: the properties identify
    /// instances of the class. A SINGLE-prop key elects the natural PRIMARY KEY in the DDL
    /// lowering (the SchemaPile-real alternative to a synthesized surrogate `id`).
    Key { class: Name, props: Vec<Name> },
    /// `@Label <entity> "text"` — display text (semantic-register COMMENT payload only)
    Label { entity: Name, text: String },
    /// `@Relation <class> <prop> <target>` — an object-property relation that is NOT
    /// existentially forced (a `max`/`only` restriction). The relation is schema-real
    /// (an optional/nullable FK) but carries no `∃`, so it cannot ride the reasoning
    /// tier's `SubClassOfExistential`; the annotation tier is exactly where
    /// schema-real-but-not-reasoning-forced facts belong.
    Relation { class: Name, prop: Name, target: Name },
}

/// One parsed KFS line, tier-tagged. The reasoning view (`parse_kfs`) sees only `Axiom`s.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Line {
    Axiom(Axiom),
    Annotation(Annotation),
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
///
/// A comment starts at a `#` at line start or preceded by whitespace — NOT inside a token:
/// IRIs (`<https://…#LocalName>`) are the actual payload of upstream fact streams, and a naive
/// split-on-`#` truncates every one of them into an arity error (measured: the founding-artifact
/// lowering, 8,099 axioms, 100% refused).
pub fn parse_line(line_no: usize, raw: &str) -> Result<Option<Line>, OutOfFragment> {
    let comment_at = raw.char_indices().find_map(|(i, c)| {
        (c == '#' && (i == 0 || raw[..i].ends_with(char::is_whitespace))).then_some(i)
    });
    let line = raw[..comment_at.unwrap_or(raw.len())].trim();
    if line.is_empty() {
        return Ok(None);
    }
    if let Some(rest) = line.strip_prefix('@') {
        return parse_annotation(line_no, rest).map(|a| Some(Line::Annotation(a)));
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
            Ok(Some(Line::Axiom(Axiom::SubClassOf {
                sub: args[0].clone(),
                sup: args[1].clone(),
            })))
        }
        "EquivalentToIntersection" => {
            if args.len() < 2 {
                return Err(OutOfFragment {
                    line: line_no,
                    construct: head.to_string(),
                    detail: "expects <class> then ≥1 conjunct".to_string(),
                });
            }
            Ok(Some(Line::Axiom(Axiom::EquivalentToIntersection {
                class: args[0].clone(),
                parts: args[1..].to_vec(),
            })))
        }
        "SubClassOfExistential" => {
            arity(3, "SubClassOfExistential <sub> <role> <filler>")?;
            Ok(Some(Line::Axiom(Axiom::SubClassOfExistential {
                sub: args[0].clone(),
                role: args[1].clone(),
                filler: args[2].clone(),
            })))
        }
        "DisjointClasses" => {
            arity(2, "DisjointClasses <a> <b>")?;
            Ok(Some(Line::Axiom(Axiom::DisjointClasses {
                a: args[0].clone(),
                b: args[1].clone(),
            })))
        }
        "ClassAssertion" => {
            arity(2, "ClassAssertion <class> <individual>")?;
            Ok(Some(Line::Axiom(Axiom::ClassAssertion {
                class: args[0].clone(),
                individual: args[1].clone(),
            })))
        }
        "PropertyRange" => {
            arity(2, "PropertyRange <role> <class>")?;
            Ok(Some(Line::Axiom(Axiom::PropertyRange {
                role: args[0].clone(),
                range: args[1].clone(),
            })))
        }
        "PropertyDomain" => {
            arity(2, "PropertyDomain <role> <class>")?;
            Ok(Some(Line::Axiom(Axiom::PropertyDomain {
                role: args[0].clone(),
                domain: args[1].clone(),
            })))
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

/// Parse one `@`-sigiled annotation-tier line (the `@` already stripped). Strict per form;
/// an unknown `@`-form or a malformed one is out-of-fragment — the tier widens the FORMAT,
/// never the gate's posture.
fn parse_annotation(line_no: usize, rest: &str) -> Result<Annotation, OutOfFragment> {
    let (head, tail) = rest
        .split_once(char::is_whitespace)
        .unwrap_or((rest, ""));
    let err = |detail: String| OutOfFragment {
        line: line_no,
        construct: format!("@{head}"),
        detail,
    };
    match head {
        "Attribute" => {
            let args: Vec<String> = tail.split_whitespace().map(strip_angles).collect();
            if args.len() != 3 {
                return Err(err(format!(
                    "@Attribute <class> <prop> <xsd> expects 3 arguments, got {}",
                    args.len()
                )));
            }
            Ok(Annotation::Attribute {
                class: args[0].clone(),
                prop: args[1].clone(),
                xsd: args[2].clone(),
            })
        }
        "Cardinality" => {
            let args: Vec<String> = tail.split_whitespace().map(strip_angles).collect();
            if args.len() != 4 {
                return Err(err(format!(
                    "@Cardinality <class> <prop> <min> <max|*> expects 4 arguments, got {}",
                    args.len()
                )));
            }
            let min: u32 = args[2]
                .parse()
                .map_err(|_| err(format!("min bound {:?} is not a u32", args[2])))?;
            let max: Option<u32> = if args[3] == "*" {
                None
            } else {
                Some(
                    args[3]
                        .parse()
                        .map_err(|_| err(format!("max bound {:?} is not a u32 or '*'", args[3])))?,
                )
            };
            if let Some(m) = max {
                if min > m {
                    return Err(err(format!("min {min} exceeds max {m}")));
                }
            }
            Ok(Annotation::Cardinality {
                class: args[0].clone(),
                prop: args[1].clone(),
                min,
                max,
            })
        }
        "Unique" => {
            let args: Vec<String> = tail.split_whitespace().map(strip_angles).collect();
            if args.len() != 1 {
                return Err(err(format!("@Unique <prop> expects 1 argument, got {}", args.len())));
            }
            Ok(Annotation::Unique { prop: args[0].clone() })
        }
        "Key" => {
            let args: Vec<String> = tail.split_whitespace().map(strip_angles).collect();
            if args.len() < 2 {
                return Err(err(format!(
                    "@Key <class> <prop> [<prop>…] expects ≥2 arguments, got {}",
                    args.len()
                )));
            }
            Ok(Annotation::Key {
                class: args[0].clone(),
                props: args[1..].to_vec(),
            })
        }
        "Enum" => {
            let (prop, vals_raw) = tail
                .trim()
                .split_once(char::is_whitespace)
                .ok_or_else(|| err("@Enum <prop> \"v\" … expects a prop then ≥1 quoted value".into()))?;
            let values = quoted_values(line_no, head, vals_raw)?;
            if values.is_empty() {
                return Err(err("@Enum expects ≥1 quoted value".into()));
            }
            Ok(Annotation::Enum {
                prop: strip_angles(prop),
                values,
            })
        }
        "Label" => {
            let (entity, text_raw) = tail
                .trim()
                .split_once(char::is_whitespace)
                .ok_or_else(|| err("@Label <entity> \"text\" expects an entity then one quoted string".into()))?;
            let mut vals = quoted_values(line_no, head, text_raw)?;
            if vals.len() != 1 {
                return Err(err(format!(
                    "@Label expects exactly one quoted string, got {}",
                    vals.len()
                )));
            }
            Ok(Annotation::Label {
                entity: strip_angles(entity),
                text: vals.remove(0),
            })
        }
        "Relation" => {
            let args: Vec<String> = tail.split_whitespace().map(strip_angles).collect();
            if args.len() != 3 {
                return Err(err(format!(
                    "@Relation <class> <prop> <target> expects 3 arguments, got {}",
                    args.len()
                )));
            }
            Ok(Annotation::Relation {
                class: args[0].clone(),
                prop: args[1].clone(),
                target: args[2].clone(),
            })
        }
        other => Err(OutOfFragment {
            line: line_no,
            construct: format!("@{other}"),
            detail: "unknown annotation form — the tier admits only @Attribute/@Cardinality/@Enum/@Label/@Relation"
                .to_string(),
        }),
    }
}

/// Strict quoted-value scanner: a whitespace-separated sequence of `"…"` strings, no escapes
/// (values are vocabulary tokens; the emitter refuses embedded quotes upstream). Anything
/// unquoted or unterminated is out-of-fragment.
fn quoted_values(line_no: usize, head: &str, raw: &str) -> Result<Vec<String>, OutOfFragment> {
    let mut vals = Vec::new();
    let mut chars = raw.trim().chars();
    while let Some(c) = chars.next() {
        if c.is_whitespace() {
            continue;
        }
        if c != '"' {
            return Err(OutOfFragment {
                line: line_no,
                construct: format!("@{head}"),
                detail: format!("values must be double-quoted; found {c:?}"),
            });
        }
        let mut s = String::new();
        loop {
            match chars.next() {
                Some('"') => break,
                Some(ch) => s.push(ch),
                None => {
                    return Err(OutOfFragment {
                        line: line_no,
                        construct: format!("@{head}"),
                        detail: "unterminated quoted value".to_string(),
                    })
                }
            }
        }
        vals.push(s);
    }
    Ok(vals)
}

/// Parse a whole KFS document into BOTH tiers; the FIRST out-of-fragment line aborts the run
/// (refuse-loud). The reasoning engine and the kernel consume only the axioms; kvasir-ddl and
/// the differential harness consume both.
pub fn parse_kfs_tiered(text: &str) -> Result<(Vec<Axiom>, Vec<Annotation>), OutOfFragment> {
    let mut axioms = Vec::new();
    let mut annotations = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        match parse_line(i + 1, raw)? {
            Some(Line::Axiom(ax)) => axioms.push(ax),
            Some(Line::Annotation(an)) => annotations.push(an),
            None => {}
        }
    }
    Ok((axioms, annotations))
}

/// The REASONING view of a document: annotation-tier lines route past it (they are
/// unrepresentable in `Vec<Axiom>` and therefore in any proof), unknown constructs still
/// refuse loudly. Callers needing the annotations use [`parse_kfs_tiered`].
pub fn parse_kfs(text: &str) -> Result<Vec<Axiom>, OutOfFragment> {
    parse_kfs_tiered(text).map(|(axioms, _)| axioms)
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
    fn iri_fragments_are_not_comments() {
        // '#' inside a token is payload (IRIs); only line-start / whitespace-preceded '#' comments
        let doc = "\
SubClassOf <https://signals.zndx.org/sdg#A> <https://signals.zndx.org/sdg#B>  # trailing comment
# full-line comment
DisjointClasses <https://signals.zndx.org/sdg#B> <https://signals.zndx.org/sdg#C>
";
        let axs = parse_kfs(doc).expect("IRI fragments must survive the comment stripper");
        assert_eq!(axs.len(), 2);
        assert!(matches!(&axs[0], Axiom::SubClassOf { sub, sup }
            if sub.contains("sdg#A") && sup.contains("sdg#B")));
    }

    #[test]
    fn arity_errors_are_out_of_fragment() {
        assert!(parse_kfs("SubClassOf <a>").is_err());
        assert!(parse_kfs("DisjointClasses <a> <b> <c>").is_err());
    }

    #[test]
    fn annotation_tier_routes_not_admits() {
        let doc = "\
SubClassOf <a> <b>
@Attribute <a> <sdg:hasEncoding> <xsd:string>
@Cardinality <a> <sdg:inheresIn> 1 1
@Enum <sdg:hasStatus> \"pending\" \"in progress\" \"complete\"
@Label <a> \"ablation process\"
DisjointClasses <a> <c>
";
        let (axioms, annotations) = parse_kfs_tiered(doc).expect("tiered doc must parse");
        assert_eq!(axioms.len(), 2);
        assert_eq!(annotations.len(), 4);
        // the reasoning view sees ONLY the axioms — annotations are unrepresentable in proofs
        assert_eq!(parse_kfs(doc).unwrap().len(), 2);
        assert!(matches!(
            &annotations[1],
            Annotation::Cardinality { min: 1, max: Some(1), .. }
        ));
        assert!(
            matches!(&annotations[2], Annotation::Enum { values, .. } if values[1] == "in progress")
        );
    }

    #[test]
    fn relation_annotation_routes_like_the_rest() {
        let doc = "SubClassOf <a> <b>\n@Relation <a> <sdg:derivedFrom> <c>\n";
        let (axioms, annotations) = parse_kfs_tiered(doc).unwrap();
        assert_eq!(axioms.len(), 1); // reasoning tier unchanged
        assert!(matches!(
            &annotations[0],
            Annotation::Relation { class, target, .. } if class == "a" && target == "c"
        ));
        assert!(parse_kfs("@Relation <a> <p>").is_err()); // arity
    }

    #[test]
    fn unknown_annotation_forms_refuse_loudly() {
        let err = parse_kfs("@Widget <a> <b>").expect_err("must refuse");
        assert_eq!(err.construct, "@Widget");
        assert!(!err.detail.is_empty());
    }

    #[test]
    fn bare_cardinality_stays_refused_the_tier_does_not_soften_the_gate() {
        assert!(parse_kfs("ObjectExactCardinality <a> <b>").is_err());
    }

    #[test]
    fn malformed_annotations_refuse() {
        assert!(parse_kfs("@Cardinality <a> <p> 2 1").is_err()); // min > max
        assert!(parse_kfs("@Cardinality <a> <p> 1 x").is_err()); // non-numeric max
        assert!(parse_kfs("@Enum <p> pending").is_err()); // unquoted value
        assert!(parse_kfs("@Label <a> \"unterminated").is_err());
        assert!(parse_kfs("@Attribute <a> <p>").is_err()); // arity
    }

    #[test]
    fn cardinality_star_is_unbounded() {
        let (_, anns) = parse_kfs_tiered("@Cardinality <a> <p> 2 *").unwrap();
        assert!(matches!(
            &anns[0],
            Annotation::Cardinality { min: 2, max: None, .. }
        ));
    }
}
