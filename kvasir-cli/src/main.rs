//! kvasir CLI — `kvasir check <file.kfs> [--json]`
//!
//! Exit codes (stable interface for the upstream membrane):
//!   0  no clash found (NOT a certificate — see README doctrine rule 2)
//!   1  REFUTED, with a self-checked proof (the proof is validated by kvasir-check before exit)
//!   2  out of fragment (refused loudly; route to the general oracle)
//!   3  internal error / proof failed self-check (a verdict without a valid proof is no verdict)
//!
//! Process isolation is the budget story: the caller deadlines or kills this process; there is no
//! uninterruptible in-process tableau.

use std::process::ExitCode;

use kvasir_core::{check, Verdict};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let (path, json) = match parse_args(&args) {
        Some(p) => p,
        None => {
            eprintln!("usage: kvasir check <file.kfs> [--json]");
            return ExitCode::from(3);
        }
    };
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("kvasir: cannot read {path}: {e}");
            return ExitCode::from(3);
        }
    };
    match check(&text) {
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

fn parse_args(args: &[String]) -> Option<(String, bool)> {
    if args.len() < 3 || args[1] != "check" {
        return None;
    }
    let json = args.iter().any(|a| a == "--json");
    args.get(2)
        .filter(|a| *a != "--json")
        .map(|p| (p.clone(), json))
}
