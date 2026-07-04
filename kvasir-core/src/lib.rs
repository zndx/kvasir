//! kvasir-core — fragment gate, semi-naive saturation, proof-DAG emission.
//!
//! Doctrine (see the repository README): refuse-don't-approximate; v0 is a sound refuter, never a
//! certifier; every verdict ships a proof the independent checker (`kvasir-check`) re-derives;
//! the calculus is cited, not invented; differential testing against HermiT/ELK is the trust bridge.
//!
//! `unsafe` is denied crate-wide and allowed ONLY in the flatc-generated accessors (whose unsafe is
//! the FlatBuffers runtime's verified-buffer contract, exercised behind `flatbuffers::root`'s verifier).

#![deny(unsafe_code)]

pub mod fragment;
pub mod kfsb;
pub mod saturate;
pub mod verdict;

#[allow(unsafe_code, unused_imports, clippy::all, clippy::pedantic)]
#[path = "generated/kfs_generated.rs"]
pub(crate) mod kfs_generated;

pub use fragment::{parse_kfs, parse_kfs_tiered, Annotation, Axiom, Line, OutOfFragment};
pub use saturate::saturate;
pub use verdict::{Fact, Proof, Rule, Step, Verdict};

/// Gate + saturate in one call: the whole v0 engine (text front-end).
pub fn check(kfs_text: &str) -> Result<(Vec<Axiom>, Verdict), OutOfFragment> {
    let axioms = parse_kfs(kfs_text)?;
    let verdict = saturate(&axioms);
    Ok((axioms, verdict))
}

/// Gate + saturate for the binary front-end (`.kfsb`, FlatBuffers — see `schemas/kfs.fbs`).
pub fn check_kfsb(buf: &[u8]) -> Result<(Vec<Axiom>, Verdict), OutOfFragment> {
    let axioms = kfsb::read(buf)?;
    let verdict = saturate(&axioms);
    Ok((axioms, verdict))
}
