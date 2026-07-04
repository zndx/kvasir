# Parity Roadmap — Konclude ∪ HermiT, ordered by aegir acceleration

**Intent (2026-07-02):** feature parity with BOTH Konclude and HermiT, with the implementation schedule
ordered by acceleration value to the aegir pipeline — not by logical prestige. Parity is the floor;
kvasir already exceeds both parents on the trust axis (see "Where kvasir leads").

**License discipline:** Konclude is **LGPLv3** (with GPLv3-bundled Qt-container variants). This roadmap
derives from a clean-room *feature inventory* (config-key registry ~660 keys, directory/CLI/README
surfaces, bundled test assets) — no code was read at the algorithm level and none may be transcribed.
HermiT's feature surface derives from Motik–Shearer–Horrocks (JAIR 2009) and production use upstream.
Techniques are implemented from public literature (Baader–Brandt–Lutz; Kazakov–Krötzsch–Simančík;
Simančík–Kazakov–Horrocks; Horrocks et al. on absorption) — cited, not invented, never lifted.

## The parity matrix

| Feature area | Konclude | HermiT | kvasir v0 | Phase |
|---|---|---|---|---|
| Sound refutation w/ proofs | — | — (bolt-on BlackBox, slow) | **✓ native proof DAGs + kernel** | ✓ |
| Vacuity-proof verdict types | — | — | **✓ `Consistent` unrepresentable at v0** | ✓ |
| Process-isolated budgets | — | — (uninterruptible tableau) | **✓ deadline = kill** | ✓ |
| Fragment gate (refuse, don't approximate) | — (accepts all, pays generality) | — | **✓ named refusals** | ✓ |
| Zero-copy payload (FlatBuffers) | — | — | **✓ KFS/kfsb** | ✓ |
| Range/domain + ∃-propagation refutation | (subsumed) | (subsumed) | **✓ landed 2026-07-03** | ✓ (P0) |
| Proof-carrying ontology→DDL lowering | — | — | **✓ landed 2026-07-04** — `kvasir ddl` (tool MODULE, not a crate — containment): Manchester/KFS → gated (refuses inconsistent input), cited (source-line provenance), sqlparser-self-checked semantic DDL | ✓ (production cutover rides aegir R1) |
| Ontology→relational verbalisation | — | — | **✓ landed 2026-07-04** — `kvasir verbalise`: multi-frame recomposition over the owned AST (DeepOnto-lineage recursive merge + same-property rewrite; true-bound phrasing; vacuity guard; no NLP model); populates DDL COMMENT payloads beside citations | ✓ |
| Told classification + sat/unsat caching | `SatisfiableCache*`, `UnsatisfiableCache*`, `ComputedTypesCaching` | limited | — | **P1** |
| Incremental reasoning (delta re-check) | `Revision.IncrementalRebuild` family, versioned KB | **none** | — | **P1** |
| ⊥-locality module extraction | — (entity extraction only) | — (via OWLAPI) | — | **P1** |
| Complete fragment saturation (EL⁺⊥+r/d) | saturation-approximation stage (`ConceptSaturation`, `SaturationCaching`) | — (tableau only) | — | **P2** |
| Native justifications for ALL verdicts | **none** | bolt-on only | v0: refutations only | **P2** |
| Absorption family (GCI, ≡→⊑, disjunction→implication) | **richest area** (`GCIAbsorption`, `EquivalentDefinitionToSubclassImplicationAbsorption`, …) | clausification-era absorption | — | **P3** |
| Task-granular parallelism | parallel subsumption/realization/precompute/query (`MaximumParallel*`) | **none (single-threaded)** | — | **P4** (rayon) |
| ABox at scale (backend/neighbour expansion, KP-set realization) | `BackendCriticalNeighbourExpansion*`, `OptimizedKPSetOntologyConceptRealizer` | realization, no scale machinery | decomposed cert upstream | **P5** |
| Daemon/server mode + KB sessions | `owllinkserver`, `sparqlserver` | none | CLI only | **P6** (gRPC, constellation idiom) |
| Property/role classification + role realization | first-class (CLI-reachable) | supported | — | **P7** |
| Datatypes (facets/restrictions) | "almost complete" | OWL 2 datatype map | gate-refused | **P8** |
| Full SROIQ residue (nominals/inverse/card/⊔) | tableau-completion stage | hypertableau | gate-refused → HermiT | **P9** (hybrid) |
| Classification traversal (known/possible sets) | `OptimizedKPSet{Class,Role}SubsumptionClassifier` | known/possible subsumers | — | P2/P4 |
| Conjunctive/SPARQL answering | absorption-based CQ engine + SPARQL | none | — | post-P9, demand-gated |
| SWRL rules | none (nominal schemas instead) | DL-safe rules | — | not scheduled (aegir unused) |
| Explanation of *inferences* (not just unsat) | none | none | — | rides P2 proofs |

## The schedule, with aegir-acceleration rationale

- **P0 — the loop refuter** *(slotted, aegir #135, ~1–2 days)*: `PropertyRange`/`PropertyDomain` forms +
  R-range / R-domain / R-exist-⊥ + checker rules; sound-for-refutation KFS lowering upstream;
  `fast_refute()` inside agent-loop rounds. Covers 100% of the empirically-observed clash class in
  milliseconds vs ~510 s/round; proof DAGs replace black-box explanation on the covered class.
  *Accelerates: every membrane round, immediately; R1's loops most of all.*
- **P1 — memory between calls**: told-classification service; satisfiable/unsatisfiable caching;
  **incremental delta-check** (re-derive only what changed axioms touch — the Konclude Revision idea,
  absent in HermiT); ⊥-locality modules (the losslessness instrument upstream already cites).
  *Accelerates: multi-round loops (rounds share 99% of the doc), lineup ancestry queries, promote gates.*
- **P2 — fragment-complete saturation**: EL⁺⊥ + range/domain rules, complete for the pinned fragment
  (Baader et al.), all verdicts proof-carrying; certification-grade *in fragment* pending the
  differential record — the ~480 s pass falls here; HermiT co-signs at publish.
  *Accelerates: the realize certification; unlocks `Consistent`-in-fragment as an earned verdict type.*
- **P3 — absorption**: GCI + ≡-definition-to-implication + disjunction-to-implication absorption —
  Konclude's richest preprocessing family, and our TBox is ≡-heavy by design (381/433 and growing).
  *Accelerates: keeps P2 linear as R1 multiplies definitions.*
- **P4 — task-granular parallelism**: rayon work-stealing over per-class satisfiability, saturation
  partitions, parallel realization tests — the Konclude pattern (parallel *tasks*, not one big lock),
  which HermiT never had. *Accelerates: everything O(classes); 24 idle cores.*
- **P5 — ABox at scale**: saturation-based instance checking + neighbour-expansion-style batching for
  large ABoxes + KP-set realization. *Accelerates: mode #6 at 10⁴–10⁵ individuals; realization for
  CPA/lineup instance panels.*
- **P6 — daemon + sessions**: gRPC service (constellation idiom; Konclude's server mode is the
  precedent), loaded-KB sessions, incremental Tell/Retract, budget-as-deadline native.
  *Accelerates: amortizes load across membrane calls; the federation's verification capability.*
- **P7 — property hierarchies**: role classification/realization (first-class in Konclude).
  *Accelerates: the property-reuse membrane's metrics + the lineup property navigator (the 87%
  single-use finding needs a property taxonomy to reuse against).*
- **P8 — datatypes**: facets/value-space checks. *Aegir's xsd-typed data properties are logically light
  today; scheduled when they stop being.*
- **P9 — the SROIQ residue, hybrid**: saturation feeds a tableau-completion backstop for
  nominals/inverse/cardinality/⊔ — the Konclude architecture, arrived at last because aegir's own gate
  refuses these constructs and HermiT remains resident for routing. This is full logical parity.
- **Continuous — the differential harness**: every upstream HermiT certification silently scores
  kvasir's verdict (the co-signing record accrues from production); GALEN + LUBM (Konclude's bundled
  stress vectors) join our own corpus as regression fixtures; an ORE-style eval mode mirrors Konclude's
  competition harness.

## Where kvasir leads (parity is the floor)

Neither parent has: native machine-checkable proofs with an independent kernel (De Bruijn), verdict
types that make vacuous confidence unrepresentable, process-isolated budgets, a refuse-don't-approximate
fragment gate, or a zero-copy payload boundary. These are not scheduled — they are shipped, and every
phase above must preserve them.
