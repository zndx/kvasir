//! kvasir CLI —
//!   `kvasir check <file.kfs|file.kfsb> [--json]`   gate + saturate + self-checked verdict
//!   `kvasir convert <in.kfs> <out.kfsb>`           text → FlatBuffers payload (KFS binary)
//!   `kvasir lower <file.omn> [--json]`             Manchester → tiered KFS on stdout
//!                                                  (--json: stats to stdout instead)
//!
//! Exit codes (stable interface for the upstream membrane):
//!   0  no clash found (NOT a certificate — see README doctrine rule 2)
//!   1  REFUTED, with a self-checked proof (the proof is validated by kvasir-check before exit)
//!   2  out of fragment (refused loudly; route to the general oracle)
//!   3  internal error / proof failed self-check (a verdict without a valid proof is no verdict)
//!
//! Process isolation is the budget story: the caller deadlines or kills this process; there is no
//! uninterruptible in-process tableau. `.kfsb` is the payload-layer FlatBuffers front-end (Kudu-style:
//! bulk data zero-copy; envelope protocols unchanged) — dispatched by extension.

mod census;
mod ddl;
mod shapes;
mod manchester;
mod verbalise;

use std::process::ExitCode;

use kvasir_core::{check, check_kfsb, kfsb, parse_kfs, parse_kfs_tiered, saturate, Verdict};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("check") => cmd_check(&args),
        Some("convert") => cmd_convert(&args),
        Some("lower") => cmd_lower(&args),
        Some("ddl") => cmd_ddl(&args),
        Some("verbalise") => cmd_verbalise(&args),
        Some("census") => cmd_census(&args),
        Some("shapes") => cmd_shapes(&args),
        _ => {
            eprintln!("usage: kvasir check <file.kfs|file.kfsb> [--json]");
            eprintln!("       kvasir convert <in.kfs> <out.kfsb>");
            eprintln!("       kvasir lower <file.omn> [--json]");
            eprintln!("       kvasir ddl <file.omn|file.kfs> [--sql]");
            eprintln!("       kvasir verbalise <file.omn>");
            eprintln!("       kvasir census <file.omn|file.kfs>");
            eprintln!("       kvasir shapes <file.omn|file.kfs>");
            ExitCode::from(3)
        }
    }
}

/// The IMPLICIT shapes emission: SHACL Core (Turtle) derived from the same tiered
/// facts the ddl module consumes — the standard syntax users extend, and the artifact
/// a third-party conformant toolchain realizes the same DDL from. Denormalized per
/// class (no entailment regime assumed); canonical byte order.
fn cmd_shapes(args: &[String]) -> ExitCode {
    let Some(path) = args.get(2).filter(|a| !a.starts_with("--")).cloned() else {
        eprintln!("usage: kvasir shapes <file.omn|file.kfs>");
        return ExitCode::from(3);
    };
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("kvasir: cannot read {path}: {e}");
            return ExitCode::from(3);
        }
    };
    let kfs = if path.ends_with(".omn") || path.ends_with(".owl") {
        let (doc, issues) = manchester::parse_document(&text);
        for issue in &issues {
            eprintln!("kvasir shapes: {issue}");
        }
        manchester::lower(&doc).kfs
    } else {
        text
    };
    let (axioms, annotations) = match parse_kfs_tiered(&kfs) {
        Ok(t) => t,
        Err(oof) => {
            eprintln!("kvasir: {oof}");
            return ExitCode::from(2);
        }
    };
    print!("{}", shapes::emit(&axioms, &annotations));
    ExitCode::SUCCESS
}

/// The PREFLIGHT instrument: what this ontology can support, before running ddl.
/// Diagnostic posture — inconsistency is a REPORTED FIELD here, not a refusal.
fn cmd_census(args: &[String]) -> ExitCode {
    let Some(path) = args.get(2).filter(|a| !a.starts_with("--")).cloned() else {
        eprintln!("usage: kvasir census <file.omn|file.kfs>");
        return ExitCode::from(3);
    };
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("kvasir: cannot read {path}: {e}");
            return ExitCode::from(3);
        }
    };
    let (kfs, src, n_issues) = if path.ends_with(".omn") || path.ends_with(".owl") {
        let (doc, issues) = manchester::parse_document(&text);
        for issue in &issues {
            eprintln!("kvasir census: {issue}");
        }
        let low = manchester::lower(&doc);
        (low.kfs, low.src_lines, issues.len())
    } else {
        (text.clone(), Vec::new(), 0)
    };
    let (axioms, annotations) = match parse_kfs_tiered(&kfs) {
        Ok(t) => t,
        Err(oof) => {
            eprintln!("kvasir: {oof}");
            return ExitCode::from(2);
        }
    };
    let (no_clash, n_unsat) = match saturate(&axioms) {
        Verdict::Refuted { unsat_classes, .. } => (false, unsat_classes.len()),
        Verdict::NoClashFound { .. } => (true, 0),
    };
    // residue: re-derive the lowering skip counts for .omn; .kfs has no lowering residue
    let residue = if path.ends_with(".omn") || path.ends_with(".owl") {
        let (doc, _) = manchester::parse_document(&text);
        manchester::lower(&doc).skipped
    } else {
        Default::default()
    };
    let (ax_cite, ann_cite) = src.split_at(axioms.len().min(src.len()));
    let plan = ddl::plan(&axioms, &annotations, ax_cite, ann_cite);
    let c = census::census(&plan, &residue, n_issues, no_clash, n_unsat);
    println!("{}", serde_json::to_string_pretty(&c).unwrap());
    ExitCode::SUCCESS
}

/// Manchester → per-class multi-frame verbalisations (JSON). The corpus-side artifact;
/// the ddl plan carries the single-sentence COMMENT payloads separately.
fn cmd_verbalise(args: &[String]) -> ExitCode {
    let Some(path) = args.get(2).filter(|a| !a.starts_with("--")).cloned() else {
        eprintln!("usage: kvasir verbalise <file.omn>");
        return ExitCode::from(3);
    };
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("kvasir: cannot read {path}: {e}");
            return ExitCode::from(3);
        }
    };
    let (doc, issues) = manchester::parse_document(&text);
    for issue in &issues {
        eprintln!("kvasir verbalise: {issue}");
    }
    let out = verbalise::verbalise_document(&doc, 5);
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
    ExitCode::SUCCESS
}

/// Manchester or tiered KFS → proof-carrying semantic DDL plan (JSON; `--sql` renders
/// statements). Gate first: an inconsistent ontology REFUSES emission (exit 1) with the
/// refutation named — no schema from falsehood. Rendered SQL must pass the sqlparser
/// self-check before leaving the process (exit 3 otherwise).
fn cmd_ddl(args: &[String]) -> ExitCode {
    let sql_out = args.iter().any(|a| a == "--sql");
    let Some(path) = args.get(2).filter(|a| !a.starts_with("--")).cloned() else {
        eprintln!("usage: kvasir ddl <file.omn|file.kfs> [--sql]");
        return ExitCode::from(3);
    };
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("kvasir: cannot read {path}: {e}");
            return ExitCode::from(3);
        }
    };
    // (kfs, per-emitted-line source citations): .omn lowers internally and cites the
    // user's omn lines; a .kfs file cites its own line numbers.
    let (kfs, src) = if path.ends_with(".omn") || path.ends_with(".owl") {
        let (doc, issues) = manchester::parse_document(&text);
        for issue in &issues {
            eprintln!("kvasir ddl: {issue}");
        }
        let low = manchester::lower(&doc);
        (low.kfs, low.src_lines)
    } else {
        let mut src: Vec<usize> = Vec::new();
        let mut ann: Vec<usize> = Vec::new();
        for (i, raw) in text.lines().enumerate() {
            let comment_at = raw.char_indices().find_map(|(k, c)| {
                (c == '#' && (k == 0 || raw[..k].ends_with(char::is_whitespace))).then_some(k)
            });
            let line = raw[..comment_at.unwrap_or(raw.len())].trim();
            if line.is_empty() {
                continue;
            }
            if line.starts_with('@') {
                ann.push(i + 1);
            } else {
                src.push(i + 1);
            }
        }
        src.extend(ann);
        (text.clone(), src)
    };
    let (axioms, annotations) = match parse_kfs_tiered(&kfs) {
        Ok(t) => t,
        Err(oof) => {
            eprintln!("kvasir: {oof}");
            return ExitCode::from(2);
        }
    };
    if let Verdict::Refuted { unsat_classes, .. } = saturate(&axioms) {
        eprintln!(
            "kvasir ddl: REFUSED — ontology is inconsistent (unsat: {unsat_classes:?}); \
             no schema is emitted from a falsified source"
        );
        return ExitCode::from(1);
    }
    let (ax_cite, ann_cite) = src.split_at(axioms.len().min(src.len()));
    let mut plan = ddl::plan(&axioms, &annotations, ax_cite, ann_cite);
    let (stmts, ok) = ddl::render_and_check(&plan);
    plan.sql_valid = ok;
    if !ok {
        eprintln!("kvasir ddl: INTERNAL — rendered SQL failed the sqlparser self-check");
        return ExitCode::from(3);
    }
    if sql_out {
        for s in &stmts {
            println!("{s};\n");
        }
    } else {
        println!("{}", serde_json::to_string_pretty(&plan).unwrap());
    }
    ExitCode::SUCCESS
}

/// Manchester → tiered KFS. Parse issues go to stderr (loud containment, exit stays 0
/// so the differential can proceed); IO errors exit 3. `--json` prints stats instead
/// of the KFS text.
fn cmd_lower(args: &[String]) -> ExitCode {
    let json = args.iter().any(|a| a == "--json");
    let Some(path) = args.get(2).filter(|a| *a != "--json").cloned() else {
        eprintln!("usage: kvasir lower <file.omn> [--json]");
        return ExitCode::from(3);
    };
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("kvasir: cannot read {path}: {e}");
            return ExitCode::from(3);
        }
    };
    let (doc, issues) = manchester::parse_document(&text);
    for issue in &issues {
        eprintln!("kvasir lower: {issue}");
    }
    let low = manchester::lower(&doc);
    if json {
        println!(
            "{}",
            serde_json::json!({
                "n_axioms": low.n_axioms,
                "n_annotations": low.n_annotations,
                "n_issues": issues.len(),
                "skipped": low.skipped,
            })
        );
    } else {
        print!("{}", low.kfs);
    }
    ExitCode::SUCCESS
}

fn cmd_check(args: &[String]) -> ExitCode {
    let json = args.iter().any(|a| a == "--json");
    let Some(path) = args.get(2).filter(|a| *a != "--json").cloned() else {
        eprintln!("usage: kvasir check <file.kfs|file.kfsb> [--json]");
        return ExitCode::from(3);
    };
    let result = if path.ends_with(".kfsb") {
        match std::fs::read(&path) {
            Ok(buf) => check_kfsb(&buf),
            Err(e) => {
                eprintln!("kvasir: cannot read {path}: {e}");
                return ExitCode::from(3);
            }
        }
    } else {
        match std::fs::read_to_string(&path) {
            Ok(text) => check(&text),
            Err(e) => {
                eprintln!("kvasir: cannot read {path}: {e}");
                return ExitCode::from(3);
            }
        }
    };
    match result {
        Err(oof) => {
            eprintln!("kvasir: {oof}");
            ExitCode::from(2)
        }
        Ok((axioms, verdict)) => {
            if let Verdict::Refuted { proof, .. } = &verdict {
                // a verdict without a valid proof is no verdict (De Bruijn: the checker gates the exit)
                if let Err(e) = kvasir_check::check_proof(&axioms, proof) {
                    eprintln!("kvasir: INTERNAL — emitted proof failed self-check: {e}");
                    return ExitCode::from(3);
                }
            }
            if json {
                println!("{}", serde_json::to_string_pretty(&verdict).unwrap());
            } else {
                match &verdict {
                    Verdict::Refuted {
                        unsat_classes,
                        refuted_individuals,
                        proof,
                    } => {
                        println!(
                            "REFUTED  unsat_classes={unsat_classes:?} refuted_individuals={refuted_individuals:?} proof_steps={}",
                            proof.steps.len()
                        );
                    }
                    Verdict::NoClashFound { note } => println!("NO-CLASH-FOUND  ({note})"),
                }
            }
            match verdict {
                Verdict::Refuted { .. } => ExitCode::from(1),
                Verdict::NoClashFound { .. } => ExitCode::SUCCESS,
            }
        }
    }
}

fn cmd_convert(args: &[String]) -> ExitCode {
    let (Some(input), Some(output)) = (args.get(2), args.get(3)) else {
        eprintln!("usage: kvasir convert <in.kfs> <out.kfsb>");
        return ExitCode::from(3);
    };
    let text = match std::fs::read_to_string(input) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("kvasir: cannot read {input}: {e}");
            return ExitCode::from(3);
        }
    };
    // the writer-side gate: text passes the fragment gate BEFORE serialization — the schema cannot
    // represent out-of-fragment constructs, and we refuse rather than approximate on the way in.
    let axioms = match parse_kfs(&text) {
        Ok(a) => a,
        Err(oof) => {
            eprintln!("kvasir: {oof}");
            return ExitCode::from(2);
        }
    };
    let buf = kfsb::write(&axioms, input);
    if let Err(e) = std::fs::write(output, &buf) {
        eprintln!("kvasir: cannot write {output}: {e}");
        return ExitCode::from(3);
    }
    println!(
        "wrote {} axioms ({} bytes) -> {output}",
        axioms.len(),
        buf.len()
    );
    ExitCode::SUCCESS
}
