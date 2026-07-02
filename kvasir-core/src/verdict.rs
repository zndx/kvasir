//! Verdicts and the proof DAG.
//!
//! Doctrine rule 2 — v0 is a SOUND REFUTER, not a certifier. `Refuted` is definitive and carries a
//! machine-checkable proof. `NoClashFound` is explicitly NOT a consistency certificate while the rule
//! set is incomplete: a verifier must never emit vacuous confidence (the upstream pipeline was burned
//! twice in one day by "trivially consistent" — kvasir's type system makes that verdict unrepresentable).

use serde::{Deserialize, Serialize};

use crate::fragment::Name;

/// One derivation step. `premises` index into the proof's `steps`; `axiom` indexes the input
/// axiom list when the step cites an input directly. The independent checker (`kvasir-check`)
/// re-derives `conclusion` from the premises under `rule` — trust the checker, not the prover.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Step {
    pub id: usize,
    pub rule: Rule,
    pub premises: Vec<usize>,
    pub axiom: Option<usize>,
    pub conclusion: Fact,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Rule {
    /// An input axiom cited verbatim.
    Input,
    /// `EquivalentToIntersection(c, [.. aᵢ ..])` ⇒ `c ⊑ aᵢ` (the told direction).
    REq,
    /// `c ⊑ d`, `d ⊑ e` ⇒ `c ⊑ e`.
    RTrans,
    /// `c ⊑ a`, `c ⊑ b`, `Disjoint(a, b)` ⇒ `Unsat(c)`.
    RDisj,
    /// `i : c`, `Unsat(c)` ⇒ `KB refuted via i`.
    RInst,
}

/// The derived-fact language (deliberately tiny).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Fact {
    Sub { sub: Name, sup: Name },
    Disjoint { a: Name, b: Name },
    Assert { class: Name, individual: Name },
    Unsat { class: Name },
    KbRefuted { individual: Name, class: Name },
}

/// A proof DAG: topologically ordered steps (every premise id < the step's own id).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proof {
    pub steps: Vec<Step>,
}

/// The v0 verdict. There is no `Consistent` variant — by construction.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "verdict")]
pub enum Verdict {
    /// Definitive: the KB (or the named classes) are refuted, with proof.
    Refuted {
        unsat_classes: Vec<Name>,
        refuted_individuals: Vec<Name>,
        proof: Proof,
    },
    /// NOT a certificate. The v0 rule set found no clash; completeness (and with it the authority
    /// to certify) arrives with the full saturation calculus + a differential-clean record.
    NoClashFound { note: String },
}

impl Verdict {
    pub fn no_clash() -> Self {
        Verdict::NoClashFound {
            note: "v0 sound-refutation subset found no clash — NOT a consistency certificate; \
                   certification authority remains with the general oracle (HermiT)"
                .to_string(),
        }
    }
}
