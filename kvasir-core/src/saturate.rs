//! Semi-naive saturation over the sound-refutation rule set:
//! v0 core — R-eq, R-trans, R-disj, R-inst (told subsumption + disjointness clash);
//! P0 loop-refuter — R-domain, R-conj-unsat, R-exist-⊥, R-exist-range-⊥, R-sub-unsat
//! (subject typing from domains; required successors in empty classes refute the subject;
//! ⊥ propagates down the told hierarchy).
//!
//! Doctrine rule 4 — a proven calculus, implemented: the consequence-based EL⁺⊥-with-range/domain
//! family (Baader–Brandt–Lutz 2005). Every rule is OWL-entailed, so a derived clash is a genuine
//! inconsistency; missing rules can only MISS clashes, never invent them (sound for refutation).
//! Every derived fact carries its proof step; the engine's answer is always (verdict, proof DAG),
//! and the DAG is the boundary signal.
//!
//! Rule staging (why no global fixpoint is needed): `Ex`/`Range`/`Domain` facts are input-only —
//! no rule derives new ones — so R-domain fires exhaustively BEFORE the transitive closure and its
//! conclusions participate in it. Unsat-generating rules run after the closure as their own
//! worklist fixpoint (new `Unsat` facts trigger only Unsat-generating rules).

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
    // side collections in axiom order (deterministic): the P0 rules join over these
    let mut ex_facts: Vec<(usize, Name, Name, Name)> = Vec::new(); // (step, sub, role, filler)
    let mut ranges: Vec<(usize, Name, Name)> = Vec::new(); // (step, role, range)
    let mut domains: Vec<(usize, Name, Name)> = Vec::new(); // (step, role, domain)
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
            Axiom::SubClassOfExistential { sub, role, filler } => {
                if let Some(id) = add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::Input,
                    vec![],
                    Some(ai),
                    Fact::Ex {
                        sub: sub.clone(),
                        role: role.clone(),
                        filler: filler.clone(),
                    },
                ) {
                    ex_facts.push((id, sub.clone(), role.clone(), filler.clone()));
                }
            }
            Axiom::PropertyRange { role, range } => {
                if let Some(id) = add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::Input,
                    vec![],
                    Some(ai),
                    Fact::Range {
                        role: role.clone(),
                        range: range.clone(),
                    },
                ) {
                    ranges.push((id, role.clone(), range.clone()));
                }
            }
            Axiom::PropertyDomain { role, domain } => {
                if let Some(id) = add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::Input,
                    vec![],
                    Some(ai),
                    Fact::Domain {
                        role: role.clone(),
                        domain: domain.clone(),
                    },
                ) {
                    domains.push((id, role.clone(), domain.clone()));
                }
            }
        }
    }

    // ── R-domain: c ⊑ ∃r.d, domain(r) ⊑ e ⇒ c ⊑ e ────────────────────────────────────
    // fires exhaustively here (Ex/Domain are input-only) so its Sub conclusions join the closure
    for (id_ex, sub, role, _filler) in &ex_facts {
        for (id_dom, drole, dclass) in &domains {
            if role == drole {
                add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::RDomain,
                    vec![*id_ex, *id_dom],
                    None,
                    Fact::Sub {
                        sub: sub.clone(),
                        sup: dclass.clone(),
                    },
                );
            }
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

    // ── the ⊥ fixpoint (P0): R-conj-unsat / R-exist-⊥ / R-exist-range-⊥ / R-sub-unsat ──
    // Sub/Ex/Range/Disjoint facts are final here; only Unsat (and PairUnsat) grow, so a
    // worklist over newly-unsat classes reaches the fixpoint.
    let mut sub_rev: HashMap<&Name, Vec<(&Name, usize)>> = HashMap::new(); // sup → [(sub, step)]
    for (sub, sup, id) in &subs {
        sub_rev.entry(sup).or_default().push((sub, *id));
    }
    for v in sub_rev.values_mut() {
        v.sort(); // deterministic derivation order
    }
    let ranges_by_class: HashMap<&Name, Vec<(usize, &Name)>> = {
        let mut m: HashMap<&Name, Vec<(usize, &Name)>> = HashMap::new();
        for (id, role, range) in &ranges {
            m.entry(range).or_default().push((*id, role));
        }
        m
    };

    // seed: statically-disjoint filler⊓range pairs (the conjunction-probe shape, derived natively)
    for (id_ex, sub, role, filler) in &ex_facts {
        for (id_range, rrole, range) in &ranges {
            if role != rrole || filler == range {
                continue;
            }
            // find Disjoint(a,b) with filler ⊑ a ∧ range ⊑ b (either orientation; reflexive ok)
            let sups_of = |c: &Name| -> HashMap<&Name, usize> {
                let mut m: HashMap<&Name, usize> = HashMap::new();
                for (s, p, id) in &subs {
                    if s == c {
                        m.insert(p, *id);
                    }
                }
                m
            };
            let (f_sups, r_sups) = (sups_of(filler), sups_of(range));
            let side =
                |c: &Name, sups: &HashMap<&Name, usize>, x: &Name| -> Option<Option<usize>> {
                    if c == x {
                        Some(None) // reflexive — no premise needed
                    } else {
                        sups.get(x).map(|id| Some(*id))
                    }
                };
            let mut derived = None;
            for (a, b, id_ab) in &disjoints {
                let hit = side(filler, &f_sups, a)
                    .zip(side(range, &r_sups, b))
                    .or_else(|| side(filler, &f_sups, b).zip(side(range, &r_sups, a)));
                if let Some((fa, rb)) = hit {
                    let mut premises = vec![*id_ab];
                    premises.extend(fa);
                    premises.extend(rb);
                    derived = Some((premises, *id_range));
                    break;
                }
            }
            if let Some((premises, id_range)) = derived {
                let pf = Fact::PairUnsat {
                    a: filler.clone(),
                    b: range.clone(),
                };
                // get-or-add: a pair shared by several existentials is derived once but cited by all
                let id_pair = add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::RConjUnsat,
                    premises,
                    None,
                    pf.clone(),
                )
                .or_else(|| fact_ids.get(&pf).copied());
                if let Some(id_pair) = id_pair {
                    if let Some(id) = add(
                        &mut proof,
                        &mut fact_ids,
                        Rule::RExistRangeBot,
                        vec![*id_ex, id_range, id_pair],
                        None,
                        Fact::Unsat { class: sub.clone() },
                    ) {
                        unsat.push((sub.clone(), id));
                    }
                }
            }
        }
    }

    let mut worklist: Vec<(Name, usize)> = unsat.clone();
    while let Some((x, id_x)) = worklist.pop() {
        // R-sub-unsat: c ⊑ x, Unsat(x) ⇒ Unsat(c)
        if let Some(children) = sub_rev.get(&x) {
            let children = children.clone();
            for (c, id_sub) in children {
                if let Some(id) = add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::RSubUnsat,
                    vec![id_sub, id_x],
                    None,
                    Fact::Unsat { class: c.clone() },
                ) {
                    unsat.push((c.clone(), id));
                    worklist.push((c.clone(), id));
                }
            }
        }
        // R-exist-⊥: c ⊑ ∃r.x, Unsat(x) ⇒ Unsat(c)
        for (id_ex, sub, _role, filler) in &ex_facts {
            if filler == &x {
                if let Some(id) = add(
                    &mut proof,
                    &mut fact_ids,
                    Rule::RExistBot,
                    vec![*id_ex, id_x],
                    None,
                    Fact::Unsat { class: sub.clone() },
                ) {
                    unsat.push((sub.clone(), id));
                    worklist.push((sub.clone(), id));
                }
            }
        }
        // range side: Unsat(e) with range(r) ⊑ e ⇒ every r-successor set is empty
        if let Some(rs) = ranges_by_class.get(&x) {
            let rs: Vec<(usize, Name)> = rs.iter().map(|(id, r)| (*id, (*r).clone())).collect();
            for (id_range, rrole) in rs {
                for (id_ex, sub, role, filler) in &ex_facts {
                    if role != &rrole {
                        continue;
                    }
                    let pf = Fact::PairUnsat {
                        a: filler.clone(),
                        b: x.clone(),
                    };
                    let id_pair = add(
                        &mut proof,
                        &mut fact_ids,
                        Rule::RConjUnsat,
                        vec![id_x],
                        None,
                        pf.clone(),
                    )
                    .or_else(|| fact_ids.get(&pf).copied());
                    if let Some(id_pair) = id_pair {
                        if let Some(id) = add(
                            &mut proof,
                            &mut fact_ids,
                            Rule::RExistRangeBot,
                            vec![*id_ex, id_range, id_pair],
                            None,
                            Fact::Unsat { class: sub.clone() },
                        ) {
                            unsat.push((sub.clone(), id));
                            worklist.push((sub.clone(), id));
                        }
                    }
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
    fn a_satisfiable_existential_is_sound() {
        // an existential with a satisfiable successor set must not create a clash
        let doc = "\
SubClassOfExistential <role> <realized_in> <process>
SubClassOf <process> <occurrent>
DisjointClasses <continuant> <occurrent>
";
        let axioms = parse_kfs(doc).unwrap();
        assert!(matches!(saturate(&axioms), Verdict::NoClashFound { .. }));
    }

    /// R-domain: the subject of an existential is typed by the role's domain, and that typing
    /// participates in the disjointness join.
    #[test]
    fn domain_typing_refutes_the_subject() {
        // role ⊑ ∃inheres_in.person; domain(inheres_in) ⊑ dependent; dependent ⊑ continuant;
        // role ⊑ occurrent; Disjoint(continuant, occurrent) ⇒ Unsat(role)
        let doc = "\
SubClassOfExistential <role> <inheres_in> <person>
PropertyDomain <inheres_in> <dependent>
SubClassOf <dependent> <continuant>
SubClassOf <role> <occurrent>
DisjointClasses <continuant> <occurrent>
";
        let axioms = parse_kfs(doc).unwrap();
        match saturate(&axioms) {
            Verdict::Refuted { unsat_classes, .. } => {
                assert!(unsat_classes.contains(&"role".to_string()));
            }
            v => panic!("expected Refuted via R-domain, got {v:?}"),
        }
    }

    /// R-exist-⊥: a required successor in an empty class refutes the subject, and the
    /// refutation propagates down the told hierarchy (R-sub-unsat).
    #[test]
    fn empty_filler_refutes_the_subject_and_its_subclasses() {
        // d is unsat (disjoint supers); c ⊑ ∃r.d ⇒ Unsat(c); c2 ⊑ c ⇒ Unsat(c2)
        let doc = "\
SubClassOf <d> <a>
SubClassOf <d> <b>
DisjointClasses <a> <b>
SubClassOfExistential <c> <r> <d>
SubClassOf <c2> <c>
";
        let axioms = parse_kfs(doc).unwrap();
        match saturate(&axioms) {
            Verdict::Refuted { unsat_classes, .. } => {
                for want in ["d", "c", "c2"] {
                    assert!(
                        unsat_classes.contains(&want.to_string()),
                        "missing {want} in {unsat_classes:?}"
                    );
                }
            }
            v => panic!("expected Refuted via R-exist-⊥/R-sub-unsat, got {v:?}"),
        }
    }

    /// R-exist-range-⊥: the JointInformationEnvironment shape — the filler is jointly
    /// unsatisfiable with the role's range, so the required successor set is empty.
    #[test]
    fn filler_range_conjunction_clash_refutes_the_subject() {
        // jie ⊑ ∃part_of.service; range(part_of) ⊑ material; service ⊑ immaterial;
        // Disjoint(material, immaterial) ⇒ successors ∈ service ⊓ material = ∅ ⇒ Unsat(jie)
        let doc = "\
SubClassOfExistential <jie> <part_of> <service>
PropertyRange <part_of> <material>
SubClassOf <service> <immaterial>
DisjointClasses <material> <immaterial>
";
        let axioms = parse_kfs(doc).unwrap();
        match saturate(&axioms) {
            Verdict::Refuted { unsat_classes, .. } => {
                assert_eq!(unsat_classes, vec!["jie".to_string()]);
            }
            v => panic!("expected Refuted via R-exist-range-⊥, got {v:?}"),
        }
    }

    /// The one-sided pair: an unsat RANGE class empties every successor set of the role.
    #[test]
    fn unsat_range_class_refutes_all_subjects_of_the_role() {
        let doc = "\
SubClassOf <e> <a>
SubClassOf <e> <b>
DisjointClasses <a> <b>
PropertyRange <r> <e>
SubClassOfExistential <c> <r> <anything>
";
        let axioms = parse_kfs(doc).unwrap();
        match saturate(&axioms) {
            Verdict::Refuted { unsat_classes, .. } => {
                assert!(unsat_classes.contains(&"c".to_string()));
                assert!(unsat_classes.contains(&"e".to_string()));
            }
            v => panic!("expected Refuted via one-sided R-conj-unsat, got {v:?}"),
        }
    }
}
