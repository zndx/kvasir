//! kvasir-core — fragment gate, semi-naive saturation, proof-DAG emission.
//!
//! Doctrine (see the repository README): refuse-don't-approximate; v0 is a sound refuter, never a
//! certifier; every verdict ships a proof the independent checker (`kvasir-check`) re-derives;
//! the calculus is cited, not invented; differential testing against HermiT/ELK is the trust bridge.

pub mod fragment;
pub mod saturate;
pub mod verdict;

pub use fragment::{parse_kfs, Axiom, OutOfFragment};
pub use saturate::saturate;
pub use verdict::{Fact, Proof, Rule, Step, Verdict};

/// Gate + saturate in one call: the whole v0 engine.
pub fn check(kfs_text: &str) -> Result<(Vec<Axiom>, Verdict), OutOfFragment> {
    let axioms = parse_kfs(kfs_text)?;
    let verdict = saturate(&axioms);
    Ok((axioms, verdict))
}
