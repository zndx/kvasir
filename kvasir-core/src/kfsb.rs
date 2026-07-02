//! KFS binary (FlatBuffers) — the payload-layer integration point (see `schemas/kfs.fbs`).
//!
//! Kudu-style layering (KUDU-1261): FlatBuffers carries the bulk fact stream; envelope protocols stay
//! wherever they are. The buffer is verified (`flatbuffers::root` runs the verifier) and read in place;
//! names are interned at write time so axioms arrive as integer facts. THE SCHEMA IS THE FRAGMENT —
//! out-of-fragment constructs are unrepresentable, so the binary reader's remaining duties are
//! structural: verifier-clean buffer, in-range name indexes, non-degenerate axioms. Any violation is a
//! loud error, never a default.

use crate::fragment::{Axiom, OutOfFragment};
use crate::kfs_generated::kvasir::kfs as fb;

/// Read a `.kfsb` buffer into fragment axioms. Errors are reported as [`OutOfFragment`] with the
/// buffer position in `line` (0 for whole-buffer failures) — the same loud contract as the text gate.
pub fn read(buf: &[u8]) -> Result<Vec<Axiom>, OutOfFragment> {
    let fs = flatbuffers::root::<fb::FactStream>(buf).map_err(|e| OutOfFragment {
        line: 0,
        construct: "FactStream".to_string(),
        detail: format!("buffer failed verification: {e}"),
    })?;
    let names = fs.names();
    let name = |ix: u32, at: usize| -> Result<String, OutOfFragment> {
        if (ix as usize) < names.len() {
            Ok(names.get(ix as usize).to_string())
        } else {
            Err(OutOfFragment {
                line: at + 1,
                construct: "name-index".to_string(),
                detail: format!("index {ix} out of range ({} interned names)", names.len()),
            })
        }
    };
    let mut out = Vec::with_capacity(fs.axioms().len());
    for (i, ax) in fs.axioms().iter().enumerate() {
        let bad = |what: &str| OutOfFragment {
            line: i + 1,
            construct: "Axiom".to_string(),
            detail: what.to_string(),
        };
        let parsed = match ax.kind_type() {
            fb::AxiomKind::SubClassOf => {
                let t = ax
                    .kind_as_sub_class_of()
                    .ok_or_else(|| bad("union/kind mismatch"))?;
                Axiom::SubClassOf {
                    sub: name(t.sub(), i)?,
                    sup: name(t.sup(), i)?,
                }
            }
            fb::AxiomKind::EquivalentToIntersection => {
                let t = ax
                    .kind_as_equivalent_to_intersection()
                    .ok_or_else(|| bad("union/kind mismatch"))?;
                let parts = t.parts();
                if parts.is_empty() {
                    return Err(bad("EquivalentToIntersection with no conjuncts"));
                }
                let mut ps = Vec::with_capacity(parts.len());
                for p in parts.iter() {
                    ps.push(name(p, i)?);
                }
                Axiom::EquivalentToIntersection {
                    class: name(t.lhs(), i)?,
                    parts: ps,
                }
            }
            fb::AxiomKind::SubClassOfExistential => {
                let t = ax
                    .kind_as_sub_class_of_existential()
                    .ok_or_else(|| bad("union/kind mismatch"))?;
                Axiom::SubClassOfExistential {
                    sub: name(t.sub(), i)?,
                    role: name(t.role(), i)?,
                    filler: name(t.filler(), i)?,
                }
            }
            fb::AxiomKind::DisjointClasses => {
                let t = ax
                    .kind_as_disjoint_classes()
                    .ok_or_else(|| bad("union/kind mismatch"))?;
                Axiom::DisjointClasses {
                    a: name(t.a(), i)?,
                    b: name(t.b(), i)?,
                }
            }
            fb::AxiomKind::ClassAssertion => {
                let t = ax
                    .kind_as_class_assertion()
                    .ok_or_else(|| bad("union/kind mismatch"))?;
                Axiom::ClassAssertion {
                    class: name(t.cls(), i)?,
                    individual: name(t.individual(), i)?,
                }
            }
            other => {
                return Err(OutOfFragment {
                    line: i + 1,
                    construct: format!("{other:?}"),
                    detail: "unknown union variant (schema drift?)".to_string(),
                })
            }
        };
        out.push(parsed);
    }
    Ok(out)
}

/// Serialize fragment axioms into a `.kfsb` buffer (names interned; deterministic given input order).
pub fn write(axioms: &[Axiom], source: &str) -> Vec<u8> {
    use std::collections::HashMap;
    let mut fbb = flatbuffers::FlatBufferBuilder::new();
    // interning pass — first-seen order is the dictionary order (deterministic); owned strings,
    // no unsafe (this crate denies unsafe_code; only the flatc-generated accessors are exempt)
    let mut ix: HashMap<String, u32> = HashMap::new();
    let mut names: Vec<String> = Vec::new();
    let intern = |n: &mut HashMap<String, u32>, names: &mut Vec<String>, s: &str| -> u32 {
        if let Some(&i) = n.get(s) {
            return i;
        }
        let i = names.len() as u32;
        names.push(s.to_string());
        n.insert(s.to_string(), i);
        i
    };
    // collect (kind, field indexes) first so the builder writes tables after the dictionary
    enum K {
        Sub(u32, u32),
        Eq(u32, Vec<u32>),
        Ex(u32, u32, u32),
        Dis(u32, u32),
        Assert(u32, u32),
    }
    let ks: Vec<K> = axioms
        .iter()
        .map(|ax| match ax {
            Axiom::SubClassOf { sub, sup } => K::Sub(
                intern(&mut ix, &mut names, sub),
                intern(&mut ix, &mut names, sup),
            ),
            Axiom::EquivalentToIntersection { class, parts } => K::Eq(
                intern(&mut ix, &mut names, class),
                parts
                    .iter()
                    .map(|p| intern(&mut ix, &mut names, p))
                    .collect(),
            ),
            Axiom::SubClassOfExistential { sub, role, filler } => K::Ex(
                intern(&mut ix, &mut names, sub),
                intern(&mut ix, &mut names, role),
                intern(&mut ix, &mut names, filler),
            ),
            Axiom::DisjointClasses { a, b } => K::Dis(
                intern(&mut ix, &mut names, a),
                intern(&mut ix, &mut names, b),
            ),
            Axiom::ClassAssertion { class, individual } => K::Assert(
                intern(&mut ix, &mut names, class),
                intern(&mut ix, &mut names, individual),
            ),
        })
        .collect();

    let name_offs: Vec<_> = names.iter().map(|s| fbb.create_string(s)).collect();
    let names_vec = fbb.create_vector(&name_offs);

    let mut axiom_offs = Vec::with_capacity(ks.len());
    for k in &ks {
        let (kind_type, kind) = match k {
            K::Sub(sub, sup) => {
                let t = fb::SubClassOf::create(
                    &mut fbb,
                    &fb::SubClassOfArgs {
                        sub: *sub,
                        sup: *sup,
                    },
                );
                (fb::AxiomKind::SubClassOf, t.as_union_value())
            }
            K::Eq(lhs, parts) => {
                let pv = fbb.create_vector(parts);
                let t = fb::EquivalentToIntersection::create(
                    &mut fbb,
                    &fb::EquivalentToIntersectionArgs {
                        lhs: *lhs,
                        parts: Some(pv),
                    },
                );
                (fb::AxiomKind::EquivalentToIntersection, t.as_union_value())
            }
            K::Ex(sub, role, filler) => {
                let t = fb::SubClassOfExistential::create(
                    &mut fbb,
                    &fb::SubClassOfExistentialArgs {
                        sub: *sub,
                        role: *role,
                        filler: *filler,
                    },
                );
                (fb::AxiomKind::SubClassOfExistential, t.as_union_value())
            }
            K::Dis(a, b) => {
                let t = fb::DisjointClasses::create(
                    &mut fbb,
                    &fb::DisjointClassesArgs { a: *a, b: *b },
                );
                (fb::AxiomKind::DisjointClasses, t.as_union_value())
            }
            K::Assert(cls, individual) => {
                let t = fb::ClassAssertion::create(
                    &mut fbb,
                    &fb::ClassAssertionArgs {
                        cls: *cls,
                        individual: *individual,
                    },
                );
                (fb::AxiomKind::ClassAssertion, t.as_union_value())
            }
        };
        axiom_offs.push(fb::Axiom::create(
            &mut fbb,
            &fb::AxiomArgs {
                kind_type,
                kind: Some(kind),
            },
        ));
    }
    let axioms_vec = fbb.create_vector(&axiom_offs);
    let source_off = fbb.create_string(source);
    let root = fb::FactStream::create(
        &mut fbb,
        &fb::FactStreamArgs {
            version: 1,
            names: Some(names_vec),
            axioms: Some(axioms_vec),
            source: Some(source_off),
        },
    );
    fbb.finish(root, Some("KFS0"));
    fbb.finished_data().to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragment::parse_kfs;
    use crate::saturate::saturate;
    use crate::verdict::Verdict;

    const VECTOR: &str = "\
SubClassOf <process> <occurrent>
SubClassOf <function> <continuant>
DisjointClasses <continuant> <occurrent>
EquivalentToIntersection <DualGroundedThing> <process> <continuant>
SubClassOfExistential <ExecutiveDirectorRole> <realized_in> <function>
ClassAssertion <DualGroundedThing> <i_sample_01>
";

    #[test]
    fn round_trip_preserves_axioms_and_verdict() {
        let axioms = parse_kfs(VECTOR).unwrap();
        let buf = write(&axioms, "test-vector");
        assert_eq!(&buf[4..8], b"KFS0", "file identifier must be present");
        let back = read(&buf).expect("round trip must read");
        assert_eq!(axioms, back, "binary round trip must be identity on axioms");
        let (v1, v2) = (saturate(&axioms), saturate(&back));
        assert!(matches!(v1, Verdict::Refuted { .. }));
        match (v1, v2) {
            (
                Verdict::Refuted {
                    unsat_classes: a, ..
                },
                Verdict::Refuted {
                    unsat_classes: b, ..
                },
            ) => assert_eq!(a, b),
            _ => panic!("verdicts must agree across the wire"),
        }
    }

    #[test]
    fn corrupt_buffer_is_a_loud_error_not_a_default() {
        let axioms = parse_kfs(VECTOR).unwrap();
        let mut buf = write(&axioms, "test-vector");
        let mid = buf.len() / 2;
        let end = (mid + 8).min(buf.len());
        for b in &mut buf[mid..end] {
            *b ^= 0xFF;
        }
        // either the verifier rejects it, or reading surfaces a structural error;
        // silence is the one forbidden outcome
        match read(&buf) {
            Err(_) => {}
            Ok(back) => assert_eq!(
                back, axioms,
                "a corrupt buffer that still verifies must not silently change the axioms"
            ),
        }
    }

    #[test]
    fn interning_dedupes_names() {
        let axioms = parse_kfs(VECTOR).unwrap();
        let buf = write(&axioms, "t");
        let fs = flatbuffers::root::<fb::FactStream>(&buf).unwrap();
        // 9 distinct names across 6 axioms (process, occurrent, function, continuant,
        // DualGroundedThing, ExecutiveDirectorRole, realized_in, i_sample_01) — no duplicates
        let n = fs.names().len();
        let mut seen = std::collections::HashSet::new();
        for i in 0..n {
            assert!(
                seen.insert(fs.names().get(i).to_string()),
                "names must be interned once"
            );
        }
        assert_eq!(n, 8);
    }
}
