//! kvasir-check — the small trusted kernel (De Bruijn criterion: trust the checker, not the prover).
//!
//! Validates a proof DAG independently of the engine's search: every step's conclusion must follow
//! from its premises under its named rule, input citations must match the input axioms verbatim,
//! and the DAG must be topologically ordered. This crate is deliberately tiny and dependency-light —
//! it is the piece a skeptic audits (or, on the formal-methods horizon, the piece that gets
//! mechanized; verifying a ~200-line checker is tractable, verifying a reasoner is a research career).

use kvasir_core::{Axiom, Fact, Proof, Rule};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckError {
    pub step: usize,
    pub reason: String,
}

impl std::fmt::Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "proof step {} invalid: {}", self.step, self.reason)
    }
}

impl std::error::Error for CheckError {}

/// Validate a proof DAG against the input axioms. Returns the number of validated steps.
pub fn check_proof(axioms: &[Axiom], proof: &Proof) -> Result<usize, CheckError> {
    let steps = &proof.steps;
    for (i, step) in steps.iter().enumerate() {
        if step.id != i {
            return Err(err(i, "step ids must be dense and ordered"));
        }
        for &p in &step.premises {
            if p >= i {
                return Err(err(
                    i,
                    "premise does not precede the step (not a DAG order)",
                ));
            }
        }
        let premise = |k: usize| -> &Fact { &steps[step.premises[k]].conclusion };
        match step.rule {
            Rule::Input => {
                let ai = step
                    .axiom
                    .ok_or_else(|| err(i, "Input step must cite an axiom"))?;
                let ax = axioms
                    .get(ai)
                    .ok_or_else(|| err(i, "axiom index out of range"))?;
                if !input_matches(ax, &step.conclusion) {
                    return Err(err(i, "Input conclusion does not match the cited axiom"));
                }
            }
            Rule::REq => {
                let ai = step
                    .axiom
                    .ok_or_else(|| err(i, "R-eq must cite its ≡ axiom"))?;
                let ax = axioms
                    .get(ai)
                    .ok_or_else(|| err(i, "axiom index out of range"))?;
                let Fact::Sub { sub, sup } = &step.conclusion else {
                    return Err(err(i, "R-eq must conclude a Sub fact"));
                };
                let Axiom::EquivalentToIntersection { class, parts } = ax else {
                    return Err(err(i, "R-eq must cite an EquivalentToIntersection axiom"));
                };
                if sub != class || !parts.contains(sup) {
                    return Err(err(
                        i,
                        "R-eq conclusion is not a told conjunct of the ≡ axiom",
                    ));
                }
            }
            Rule::RTrans => {
                if step.premises.len() != 2 {
                    return Err(err(i, "R-trans takes exactly 2 premises"));
                }
                let (Fact::Sub { sub: c, sup: d1 }, Fact::Sub { sub: d2, sup: e }) =
                    (premise(0), premise(1))
                else {
                    return Err(err(i, "R-trans premises must both be Sub facts"));
                };
                let Fact::Sub { sub, sup } = &step.conclusion else {
                    return Err(err(i, "R-trans must conclude a Sub fact"));
                };
                if d1 != d2 || sub != c || sup != e {
                    return Err(err(i, "R-trans premises do not chain to the conclusion"));
                }
            }
            Rule::RDisj => {
                let Fact::Unsat { class } = &step.conclusion else {
                    return Err(err(i, "R-disj must conclude an Unsat fact"));
                };
                let Some(Fact::Disjoint { a, b }) = step.premises.first().map(|_| premise(0))
                else {
                    return Err(err(i, "R-disj's first premise must be a Disjoint fact"));
                };
                // remaining premises establish class ⊑ a / class ⊑ b; a missing premise is only
                // admissible when the class IS that side (the reflexive edge).
                let mut have_a = class == a;
                let mut have_b = class == b;
                for k in 1..step.premises.len() {
                    match premise(k) {
                        Fact::Sub { sub, sup } if sub == class && sup == a => have_a = true,
                        Fact::Sub { sub, sup } if sub == class && sup == b => have_b = true,
                        _ => return Err(err(i, "R-disj side premise is not class ⊑ a|b")),
                    }
                }
                if !(have_a && have_b) {
                    return Err(err(i, "R-disj does not establish both disjoint sides"));
                }
            }
            Rule::RInst => {
                if step.premises.len() != 2 {
                    return Err(err(i, "R-inst takes exactly 2 premises"));
                }
                let (
                    Fact::Assert {
                        class: ca,
                        individual,
                    },
                    Fact::Unsat { class: cu },
                ) = (premise(0), premise(1))
                else {
                    return Err(err(i, "R-inst premises must be Assert then Unsat"));
                };
                let Fact::KbRefuted {
                    individual: ri,
                    class: rc,
                } = &step.conclusion
                else {
                    return Err(err(i, "R-inst must conclude KbRefuted"));
                };
                if ca != cu || ri != individual || rc != ca {
                    return Err(err(i, "R-inst premises do not support the refutation"));
                }
            }
            Rule::RDomain => {
                if step.premises.len() != 2 {
                    return Err(err(i, "R-domain takes exactly 2 premises"));
                }
                let (Fact::Ex { sub, role, .. }, Fact::Domain { role: dr, domain }) =
                    (premise(0), premise(1))
                else {
                    return Err(err(i, "R-domain premises must be Ex then Domain"));
                };
                let Fact::Sub { sub: cs, sup } = &step.conclusion else {
                    return Err(err(i, "R-domain must conclude a Sub fact"));
                };
                if role != dr || cs != sub || sup != domain {
                    return Err(err(i, "R-domain premises do not type the subject"));
                }
            }
            Rule::RConjUnsat => {
                let Fact::PairUnsat { a: d, b: e } = &step.conclusion else {
                    return Err(err(i, "R-conj-unsat must conclude PairUnsat"));
                };
                if step.premises.len() == 1 {
                    // one-sided: Unsat(d) or Unsat(e) empties the pair
                    let Fact::Unsat { class } = premise(0) else {
                        return Err(err(i, "single-premise R-conj-unsat needs an Unsat premise"));
                    };
                    if class != d && class != e {
                        return Err(err(
                            i,
                            "R-conj-unsat's Unsat premise is neither pair member",
                        ));
                    }
                } else {
                    // disjointness-sided: Disjoint(a,b) + (d ⊑ a, e ⊑ b) in either orientation,
                    // reflexive sides admissible (mirrors R-disj's checker)
                    let Some(Fact::Disjoint { a, b }) = step.premises.first().map(|_| premise(0))
                    else {
                        return Err(err(i, "R-conj-unsat's first premise must be Disjoint"));
                    };
                    let side_subs: Vec<&Fact> = (1..step.premises.len()).map(&premise).collect();
                    let holds = |x: &String, y: &String| -> bool {
                        // x ⊑ y via a side premise, or reflexively
                        x == y
                            || side_subs.iter().any(
                                |f| matches!(f, Fact::Sub { sub, sup } if sub == x && sup == y),
                            )
                    };
                    let ok = (holds(d, a) && holds(e, b)) || (holds(d, b) && holds(e, a));
                    if !ok {
                        return Err(err(
                            i,
                            "R-conj-unsat does not establish the pair under the disjointness",
                        ));
                    }
                    for f in side_subs {
                        if !matches!(f, Fact::Sub { .. }) {
                            return Err(err(i, "R-conj-unsat side premises must be Sub facts"));
                        }
                    }
                }
            }
            Rule::RExistBot => {
                if step.premises.len() != 2 {
                    return Err(err(i, "R-exist-⊥ takes exactly 2 premises"));
                }
                let (Fact::Ex { sub, filler, .. }, Fact::Unsat { class }) =
                    (premise(0), premise(1))
                else {
                    return Err(err(i, "R-exist-⊥ premises must be Ex then Unsat"));
                };
                let Fact::Unsat { class: cu } = &step.conclusion else {
                    return Err(err(i, "R-exist-⊥ must conclude Unsat"));
                };
                if class != filler || cu != sub {
                    return Err(err(i, "R-exist-⊥ filler/subject do not line up"));
                }
            }
            Rule::RExistRangeBot => {
                if step.premises.len() != 3 {
                    return Err(err(i, "R-exist-range-⊥ takes exactly 3 premises"));
                }
                let (
                    Fact::Ex { sub, role, filler },
                    Fact::Range { role: rr, range },
                    Fact::PairUnsat { a, b },
                ) = (premise(0), premise(1), premise(2))
                else {
                    return Err(err(
                        i,
                        "R-exist-range-⊥ premises must be Ex, Range, PairUnsat",
                    ));
                };
                let Fact::Unsat { class: cu } = &step.conclusion else {
                    return Err(err(i, "R-exist-range-⊥ must conclude Unsat"));
                };
                let pair_ok = (a == filler && b == range) || (a == range && b == filler);
                if role != rr || !pair_ok || cu != sub {
                    return Err(err(i, "R-exist-range-⊥ does not empty this successor set"));
                }
            }
            Rule::RSubUnsat => {
                if step.premises.len() != 2 {
                    return Err(err(i, "R-sub-unsat takes exactly 2 premises"));
                }
                let (Fact::Sub { sub, sup }, Fact::Unsat { class }) = (premise(0), premise(1))
                else {
                    return Err(err(i, "R-sub-unsat premises must be Sub then Unsat"));
                };
                let Fact::Unsat { class: cu } = &step.conclusion else {
                    return Err(err(i, "R-sub-unsat must conclude Unsat"));
                };
                if class != sup || cu != sub {
                    return Err(err(i, "R-sub-unsat does not propagate down the told edge"));
                }
            }
        }
    }
    Ok(steps.len())
}

fn input_matches(ax: &Axiom, fact: &Fact) -> bool {
    match (ax, fact) {
        (Axiom::SubClassOf { sub, sup }, Fact::Sub { sub: fs, sup: fp }) => sub == fs && sup == fp,
        (Axiom::DisjointClasses { a, b }, Fact::Disjoint { a: fa, b: fb }) => a == fa && b == fb,
        (
            Axiom::ClassAssertion { class, individual },
            Fact::Assert {
                class: fc,
                individual: fi,
            },
        ) => class == fc && individual == fi,
        (
            Axiom::SubClassOfExistential { sub, role, filler },
            Fact::Ex {
                sub: fs,
                role: fr,
                filler: ff,
            },
        ) => sub == fs && role == fr && filler == ff,
        (
            Axiom::PropertyRange { role, range },
            Fact::Range {
                role: fr,
                range: fc,
            },
        ) => role == fr && range == fc,
        (
            Axiom::PropertyDomain { role, domain },
            Fact::Domain {
                role: fr,
                domain: fc,
            },
        ) => role == fr && domain == fc,
        _ => false,
    }
}

fn err(step: usize, reason: &str) -> CheckError {
    CheckError {
        step,
        reason: reason.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kvasir_core::{check, Verdict};

    #[test]
    fn validates_the_engines_own_proofs() {
        let doc = "\
SubClassOf <process> <occurrent>
DisjointClasses <continuant> <occurrent>
EquivalentToIntersection <dual> <process> <continuant>
ClassAssertion <dual> <i_sample_01>
";
        let (axioms, verdict) = check(doc).unwrap();
        let Verdict::Refuted { proof, .. } = verdict else {
            panic!("expected Refuted")
        };
        let n = check_proof(&axioms, &proof).expect("engine proof must check");
        assert!(n >= 4);
    }

    #[test]
    fn validates_p0_rule_proofs() {
        // exercises RDomain, RConjUnsat (both shapes), RExistBot, RExistRangeBot, RSubUnsat
        for doc in [
            // R-domain → closure → R-disj
            "SubClassOfExistential <role> <inheres_in> <person>\n\
             PropertyDomain <inheres_in> <dependent>\n\
             SubClassOf <dependent> <continuant>\n\
             SubClassOf <role> <occurrent>\n\
             DisjointClasses <continuant> <occurrent>\n",
            // R-exist-⊥ + R-sub-unsat
            "SubClassOf <d> <a>\nSubClassOf <d> <b>\nDisjointClasses <a> <b>\n\
             SubClassOfExistential <c> <r> <d>\nSubClassOf <c2> <c>\n",
            // R-conj-unsat (disjoint-sided) + R-exist-range-⊥ (the JIE shape)
            "SubClassOfExistential <jie> <part_of> <service>\n\
             PropertyRange <part_of> <material>\n\
             SubClassOf <service> <immaterial>\n\
             DisjointClasses <material> <immaterial>\n",
            // R-conj-unsat (one-sided, unsat range class)
            "SubClassOf <e> <a>\nSubClassOf <e> <b>\nDisjointClasses <a> <b>\n\
             PropertyRange <r> <e>\nSubClassOfExistential <c> <r> <x>\n",
        ] {
            let (axioms, verdict) = check(doc).unwrap();
            let Verdict::Refuted { proof, .. } = verdict else {
                panic!("expected Refuted for:\n{doc}")
            };
            check_proof(&axioms, &proof).unwrap_or_else(|e| panic!("proof must check: {e}\n{doc}"));
        }
    }

    #[test]
    fn rejects_a_tampered_p0_proof() {
        let doc = "\
SubClassOfExistential <jie> <part_of> <service>
PropertyRange <part_of> <material>
SubClassOf <service> <immaterial>
DisjointClasses <material> <immaterial>
";
        let (axioms, verdict) = check(doc).unwrap();
        let Verdict::Refuted { mut proof, .. } = verdict else {
            panic!("expected Refuted")
        };
        for s in &mut proof.steps {
            if let Fact::PairUnsat { a, .. } = &mut s.conclusion {
                *a = "innocent_bystander".to_string();
            }
        }
        assert!(
            check_proof(&axioms, &proof).is_err(),
            "tampered PairUnsat must be rejected"
        );
    }

    #[test]
    fn rejects_a_tampered_proof() {
        let doc = "\
SubClassOf <process> <occurrent>
DisjointClasses <continuant> <occurrent>
EquivalentToIntersection <dual> <process> <continuant>
ClassAssertion <dual> <i_sample_01>
";
        let (axioms, verdict) = check(doc).unwrap();
        let Verdict::Refuted { mut proof, .. } = verdict else {
            panic!("expected Refuted")
        };
        // tamper: swap one conclusion's class name
        for s in &mut proof.steps {
            if let Fact::Unsat { class } = &mut s.conclusion {
                *class = "innocent_bystander".to_string();
            }
        }
        assert!(
            check_proof(&axioms, &proof).is_err(),
            "tampered proof must be rejected"
        );
    }
}
