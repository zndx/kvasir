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
