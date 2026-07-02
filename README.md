# kvasir

A fragment-gated, proof-emitting OWL reasoner in Rust — built to keep pace with a growing,
substantively-curated ontology on modern hardware.

*Kvasir: born of the truce between two clans of gods, the wisest of beings.* This engine is born of the
truce between **speed** and **trust** — it is fast only where it can prove it is right.

## Why

Battle-tested tableau reasoners (HermiT) implement full-SROIQ generality in single-threaded, GC-managed
code designed two hardware generations ago. Our workload — a BFO/CCO-grounded, content-derived domain
ontology with a rich ≡-definition layer and a large Types-only ABox — occupies a far simpler fragment and
pays generality costs it never uses, pinning one core while dozens idle. Measured upstream (aegir,
2026-07-02): TBox consistency 480 s; +248 Types-only individuals → the monolithic check exceeded every
budget, while a *sound shape-aware decomposition* of the same certification ran in seconds with HermiT as
the per-check oracle. Kvasir generalizes that move into an engine.

## Doctrine (non-negotiable)

1. **Refuse, don't approximate.** The first act on any input is the **fragment gate**: constructs outside
   the pinned fragment are rejected loudly, never silently weakened. Complete for the fragment, silent for
   nothing. Out-of-fragment inputs belong to the general oracle (HermiT).
2. **v0 is a sound refuter, not a certifier.** `Refuted` verdicts carry machine-checkable proofs and are
   definitive. `NoClashFound` is explicitly **not** a consistency certificate while the rule set is
   incomplete — a verifier must never emit vacuous confidence. Certification authority arrives only with
   the complete saturation calculus *and* a differential-clean record.
3. **De Bruijn criterion: trust the checker, not the prover.** Every verdict ships its proof DAG;
   `kvasir-check` — a small, independent kernel — re-derives every step. Don't verify the big engine;
   verify the small checker.
4. **A proven calculus, implemented — not invented.** Consequence-based saturation for EL⁺/ALCH-class
   fragments (Baader–Brandt–Lutz 2005; Kazakov–Krötzsch–Simančík 2014; Simančík–Kazakov–Horrocks 2011).
   We cite and implement; the novelty budget is spent on engineering, not logic.
5. **Differential testing is the trust bridge.** Every commit re-verifies against HermiT (and ELK where
   the profile fits) over a regression corpus that grows with every upstream release. HermiT keeps signing
   published certificates until kvasir earns co-signing through a long differential-clean record.
6. **Deterministic and pinned.** Reproducible verdicts; upstream certificates record the exact kvasir
   commit. Provenance for the verifier itself.

## Architecture

```
kvasir-core   fragment AST · fragment gate · semi-naive saturation · proof DAG emission
kvasir-check  the small trusted kernel: validates proof DAGs step-by-step (independent of core's search)
kvasir-cli    `kvasir check <file.kfs> [--json]` — process-isolated; budgets are plain process deadlines
```

Process isolation is a feature: a JVM tableau cannot be interrupted in-process (the upstream watchdog is
`os._exit`); a kvasir run is killed or deadlined like any process, cleanly.

### v0 rule set (sound-refutation subset)

- `R-eq` — `EquivalentToIntersection(c, [a…])` ⇒ `c ⊑ aᵢ` (the told direction)
- `R-trans` — told-subsumption transitive closure (semi-naive)
- `R-disj` — `c ⊑ a`, `c ⊑ b`, `DisjointClasses(a,b)` ⇒ `Unsat(c)` (with proof)
- `R-inst` — `ClassAssertion(c, i)`, `Unsat(c)` ⇒ `KB refuted` (with proof)

Existential restrictions are **admitted by the gate and inert at v0** — ignoring derivations is sound for
refutation (fewer derivations ⇒ fewer clashes found; anything refuted is genuinely refuted). The full EL⁺
existential rules are the T3 milestone.

### Input: KFS v0 (kvasir fact stream)

A deliberately minimal, canonical line format the upstream emits deterministically (parser skew between
differential engines is itself a soundness hazard; a shared trivial syntax removes it). One axiom per
line, `#` comments:

```
SubClassOf <c> <d>
EquivalentToIntersection <c> <a> <b> ...
SubClassOfExistential <c> <r> <d>        # admitted; inert at v0
DisjointClasses <a> <b>
ClassAssertion <c> <i>
```

`horned-owl` ingestion of the upstream `.owl` (RDF/XML) is the planned second front-end; the gate remains
the arbiter either way.

### Integration: KFS binary (FlatBuffers payload)

`schemas/kfs.fbs` defines the **payload-layer** integration point, in keeping with Apache Kudu's
direction (KUDU-1261: FlatBuffers for bulk cell payloads inside the protobuf envelope — benchmarked
~7–8× faster ser/de than protobuf, buffer reuse without reallocation). Envelope protocols stay wherever
they are (the upstream engine speaks gRPC/protobuf); the fact stream itself is zero-copy:

- **The schema is the fragment.** The `AxiomKind` union can only represent pinned-fragment constructs —
  an out-of-fragment axiom is *unrepresentable* in a well-formed buffer. For binary input the gate moves
  to the writer (refuse to serialize what the schema cannot say); text KFS keeps the reader-side gate.
  Widening the union is a visible, reviewed act.
- **Names interned once**, axioms carry `u32` indexes — the reader gets integer facts (what the
  saturation core wants) with no parse. Out-of-range indexes are loud errors, never defaults.
- **Verified reads** (`flatbuffers::root` runs the verifier); corrupt buffers fail loudly (tested).
- **Cross-language by generation**: `flatc --rust` (checked into `kvasir-core/src/generated/`) and
  `flatc --python` (`bindings/python/`) from the one `.fbs` — no hand parser on either side, so
  differential engines cannot diverge at the parse. Proven: Python writes, Rust refutes, verdicts agree.
- `kvasir check file.kfsb` (extension-dispatched) · `kvasir convert in.kfs out.kfsb`.

Verdicts + proof DAGs as FlatBuffers (mmap-able stored artifacts — proofs as data-plane citizens) is the
natural next table in the same schema.

## Roadmap

- **T2** (upstream aegir #132): exact fragment measurement of the live ontology; ELK where the EL profile
  fits; the differential harness as founding CI.
- **T3**: complete EL⁺/ALCH consequence-based saturation (rayon-parallel; join-heavy core is
  GPU-amenable later); classification; conjunction-satisfiability service for the decomposed ABox
  certification; daemon mode (tonic) mirroring the upstream capability-engine layering.

## License

Apache-2.0.
