//! Semi-naive saturation over the v0 sound-refutation rule set (R-eq, R-trans, R-disj, R-inst).
//!
//! Doctrine rule 4 — a proven calculus, implemented: this is the told-subsumption fixpoint plus
//! disjointness clash detection, the trivially-sound core of the consequence-based EL family
//! (Baader–Brandt–Lutz 2005). Existential axioms are inert here — sound for refutation (fewer
//! derivations can only MISS clashes, never invent them). Every derived fact carries its proof step;
//! the engine's answer is always (verdict, proof DAG), and the DAG is the boundary signal.

use std::collections::HashMap;

use crate::fragment::{Axiom, Name};
use crate::verdict::{Fact, Proof, Rule, Step, Verdict};

/// Saturate the axioms and return the verdict with its proof.
pub fn saturate(axioms: &[Axiom]) -> Verdict {
    let mut proof = Proof::default();
    let mut fact_ids: HashMap<Fact, usize> = HashMap::new();

    let add = |proof: &mut Proof,
                   fact_ids: &mut HashMap<Fact, usize>,
                   rule: Rule,
                   premises: Vec<usize>,
                   axiom: Option<usize>,
                   fact: Fact|
     -> Option<usize> {
        if fact_ids.contains_key(&fact) {
            return None; // first derivation wins; the DAG stays minimal-ish
        }
        let id = proof.steps.len();
        proof.steps.push(Step {
            id,
            rule,
            premises,
            axiom,
            conclusion: fact.clone(),
        });
        fact_ids.insert(fact, id);
        Some(id)
    };

    // ── load: input axioms → base facts (R-eq inline for the told direction) ─────────
    for (ai, ax) in axioms.iter().enumerate() {
        match ax {
            Axiom::SubClassOf { sub, sup } => {
                add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::Input,
                    vec![],
                    Some(ai),
                    Fact::Sub {
                        sub: sub.clone(),
                        sup: sup.clone(),
                    },
                );
            }
            Axiom::EquivalentToIntersection { class, parts } => {
                for part in parts {
                    add(
                        &mut proof,
                        &mut fact_ids,
                        Rule::REq,
                        vec![],
                        Some(ai),
                        Fact::Sub {
                            sub: class.clone(),
                            sup: part.clone(),
                        },
                    );
                }
            }
            Axiom::DisjointClasses { a, b } => {
                add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::Input,
                    vec![],
                    Some(ai),
                    Fact::Disjoint {
                        a: a.clone(),
                        b: b.clone(),
                    },
                );
            }
            Axiom::ClassAssertion { class, individual } => {
                add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::Input,
                    vec![],
                    Some(ai),
                    Fact::Assert {
                        class: class.clone(),
                        individual: individual.clone(),
                    },
                );
            }
            Axiom::SubClassOfExistential { .. } => { /* inert at v0 — see module doc */ }
        }
    }

    // reflexive told subsumption (c ⊑ c) is implicit; we materialize only what rules need.

    // ── R-trans: semi-naive transitive closure over Sub ───────────────────────────────
    // delta-driven: newly derived Sub facts are joined against told edges until fixpoint.
    let mut sup_of: HashMap<Name, Vec<(Name, usize)>> = HashMap::new(); // sub → [(sup, step)]
    for (fact, id) in fact_ids.clone() {
        if let Fact::Sub { sub, sup } = fact {
            sup_of.entry(sub).or_default().push((sup, id));
        }
    }
    let mut delta: Vec<(Name, Name, usize)> = sup_of
        .iter()
        .flat_map(|(sub, sups)| {
            sups.iter()
                .map(move |(sup, id)| (sub.clone(), sup.clone(), *id))
        })
        .collect();
    while !delta.is_empty() {
        let mut next = Vec::new();
        for (c, d, id_cd) in delta.drain(..) {
            let d_sups: Vec<(Name, usize)> = sup_of.get(&d).cloned().unwrap_or_default();
            for (e, id_de) in d_sups {
                let fact = Fact::Sub {
                    sub: c.clone(),
                    sup: e.clone(),
                };
                if let Some(id) = add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::RTrans,
                    vec![id_cd, id_de],
                    None,
                    fact,
                ) {
                    sup_of.entry(c.clone()).or_default().push((e.clone(), id));
                    next.push((c.clone(), e, id));
                }
            }
        }
        delta = next;
    }

    // ── R-disj: c ⊑ a, c ⊑ b, Disjoint(a,b) ⇒ Unsat(c) ────────────────────────────────
    let disjoints: Vec<(Name, Name, usize)> = fact_ids
        .iter()
        .filter_map(|(f, id)| match f {
            Fact::Disjoint { a, b } => Some((a.clone(), b.clone(), *id)),
            _ => None,
        })
        .collect();
    let mut unsat: Vec<(Name, usize)> = Vec::new();
    let subs: Vec<(Name, Name, usize)> = fact_ids
        .iter()
        .filter_map(|(f, id)| match f {
            Fact::Sub { sub, sup } => Some((sub.clone(), sup.clone(), *id)),
            _ => None,
        })
        .collect();
    let mut sups_with_id: HashMap<&Name, HashMap<&Name, usize>> = HashMap::new();
    for (sub, sup, id) in &subs {
        sups_with_id.entry(sub).or_default().insert(sup, *id);
    }
    let mut classes: Vec<&Name> = sups_with_id.keys().copied().collect();
    classes.sort(); // deterministic verdict order (doctrine rule 6)
    for c in classes {
        let sups = &sups_with_id[c];
        for (a, b, id_ab) in &disjoints {
            // a class is also a told subclass of itself — include the reflexive edge in the join
            let id_ca = if c == a {
                None
            } else {
                sups.get(a).copied().map(Some).unwrap_or(None)
            };
            let id_cb = if c == b {
                None
            } else {
                sups.get(b).copied().map(Some).unwrap_or(None)
            };
            let hit_a = c == a || id_ca.is_some();
            let hit_b = c == b || id_cb.is_some();
            if hit_a && hit_b {
                let mut premises: Vec<usize> = vec![*id_ab];
                premises.extend(id_ca);
                premises.extend(id_cb);
                if let Some(id) = add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::RDisj,
                    premises,
                    None,
                    Fact::Unsat { class: c.clone() },
                ) {
                    unsat.push((c.clone(), id));
                }
            }
        }
    }

    // ── R-inst: i : c, Unsat(c) ⇒ KB refuted via i ─────────────────────────────────────
    let mut refuted_individuals = Vec::new();
    let asserts: Vec<(Name, Name, usize)> = fact_ids
        .iter()
        .filter_map(|(f, id)| match f {
            Fact::Assert { class, individual } => Some((class.clone(), individual.clone(), *id)),
            _ => None,
        })
        .collect();
    for (class, individual, id_assert) in &asserts {
        if let Some((_, id_unsat)) = unsat.iter().find(|(c, _)| c == class) {
            add(
                &mut proof,
                &mut fact_ids,
                Rule::RInst,
                vec![*id_assert, *id_unsat],
                None,
                Fact::KbRefuted {
                    individual: individual.clone(),
                    class: class.clone(),
                },
            );
            refuted_individuals.push(individual.clone());
        }
    }

    if unsat.is_empty() {
        return Verdict::no_clash();
    }
    let mut unsat_classes: Vec<Name> = unsat.into_iter().map(|(c, _)| c).collect();
    unsat_classes.sort();
    unsat_classes.dedup();
    refuted_individuals.sort();
    refuted_individuals.dedup();
    Verdict::Refuted {
        unsat_classes,
        refuted_individuals,
        proof,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragment::parse_kfs;

    /// The founding differential vector: the dual-grounding collision from the upstream realize
    /// (a class ≡ process ⊓ continuant under continuant ⊥ occurrent). HermiT's verdict on the
    /// equivalent OWL: DualGroundedThing unsatisfiable. kvasir must agree, with proof.
    #[test]
    fn refutes_dual_grounding_with_proof() {
        let doc = "\
SubClassOf <process> <occurrent>
DisjointClasses <continuant> <occurrent>
EquivalentToIntersection <dual> <process> <continuant>
ClassAssertion <dual> <i_sample_01>
";
        let axioms = parse_kfs(doc).unwrap();
        match saturate(&axioms) {
            Verdict::Refuted {
                unsat_classes,
                refuted_individuals,
                proof,
            } => {
                assert_eq!(unsat_classes, vec!["dual".to_string()]);
                assert_eq!(refuted_individuals, vec!["i_sample_01".to_string()]);
                assert!(!proof.steps.is_empty());
                // the DAG must actually reach the refutation
                assert!(proof
                    .steps
                    .iter()
                    .any(|s| matches!(&s.conclusion, Fact::KbRefuted { .. })));
            }
            v => panic!("expected Refuted, got {v:?}"),
        }
    }

    #[test]
    fn no_clash_is_not_a_certificate() {
        let doc = "\
SubClassOf <a> <b>
SubClassOf <b> <c>
DisjointClasses <c> <d>
";
        let axioms = parse_kfs(doc).unwrap();
        match saturate(&axioms) {
            Verdict::NoClashFound { note } => {
                assert!(note.contains("NOT a consistency certificate"));
            }
            v => panic!("expected NoClashFound, got {v:?}"),
        }
    }

    #[test]
    fn transitive_clash_found_through_a_chain() {
        // a ⊑ b ⊑ c, a ⊑ d, Disjoint(c, d) ⇒ Unsat(a)
        let doc = "\
SubClassOf <a> <b>
SubClassOf <b> <c>
SubClassOf <a> <d>
DisjointClasses <c> <d>
";
        let axioms = parse_kfs(doc).unwrap();
        match saturate(&axioms) {
            Verdict::Refuted { unsat_classes, .. } => {
                assert!(unsat_classes.contains(&"a".to_string()));
            }
            v => panic!("expected Refuted, got {v:?}"),
        }
    }

    #[test]
    fn existentials_are_inert_and_sound() {
        // an existential must not create a clash on its own
        let doc = "\
SubClassOfExistential <role> <realized_in> <process>
SubClassOf <process> <occurrent>
DisjointClasses <continuant> <occurrent>
";
        let axioms = parse_kfs(doc).unwrap();
        assert!(matches!(saturate(&axioms), Verdict::NoClashFound { .. }));
    }
}
