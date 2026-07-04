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

mod manchester;

use std::process::ExitCode;

use kvasir_core::{check, check_kfsb, kfsb, parse_kfs, Verdict};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("check") => cmd_check(&args),
        Some("convert") => cmd_convert(&args),
        Some("lower") => cmd_lower(&args),
        _ => {
            eprintln!("usage: kvasir check <file.kfs|file.kfsb> [--json]");
            eprintln!("       kvasir convert <in.kfs> <out.kfsb>");
            eprintln!("       kvasir lower <file.omn> [--json]");
            ExitCode::from(3)
        }
    }
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
