//! `truth strength-comparisons [COMPARISON] [--registered]` and
//! `truth strength-report [--output FILE] [--build-input | --check-input]`:
//! Python `corpus.py strength-comparisons` and `strength-report`.
//!
//! `strength-comparisons` live-verifies the registered comparisons (or one,
//! named by its exact id as Python matches it) and prints one status line
//! each, or the reports as JSON; `--registered` prints the provenance-only
//! projection without running Lean. `strength-report` live-verifies every
//! comparison and atomically writes the `.cache` bundle, byte for byte as
//! Python writes it; `--check-input` validates an existing bundle's
//! freshness and projection without rerunning proofs. `--recorded-exporters
//! DIR` replays recorded Lean exporter outputs for the parity harness; it
//! skips Lake and `scripts/verify-result.sh` and is never a verification.

use super::structure::{checkout, on_large_stack};
use super::{Accepts, Args, Command, Failure, Output, corpus_error, load, raw, usage};
use std::path::{Path, PathBuf};
use truth::{
    pyjson::Ordered,
    strength::{self, Data, Exporters},
    structure::Records,
};

pub const COMPARISONS: Command = Command {
    name: "strength-comparisons",
    run: |args, operands| on_large_stack(args, operands, run_comparisons),
};

pub const REPORT: Command = Command {
    name: "strength-report",
    run: |args, operands| on_large_stack(args, operands, run_report),
};

/// The prologue both commands share: operand count, then the options that
/// do not apply (`--registered` applies only to `strength-comparisons`).
fn prologue(args: &Args, operands: &[&str], most: usize, registered: bool) -> Result<(), Failure> {
    args.reject_research()?;
    if operands.len() > most || args.bridge_flags {
        return Err(usage(super::HELP));
    }
    args.check_options(Accepts {
        configuration: true,
        ..Accepts::default()
    })?;
    let configuration = &args.configuration;
    if configuration.case.is_some()
        || configuration.seed.is_some()
        || !configuration.premises.is_empty()
        || configuration.check.is_some()
        || configuration.argument.is_some()
        || configuration.verify
        || configuration.max_atoms.is_some()
        || (configuration.registered && !registered)
    {
        return Err(usage(if registered {
            "strength-comparisons accepts only --registered and --json"
        } else {
            "strength-report accepts only --output, --build-input, --check-input and --json"
        }));
    }
    if !args.structure.unfold.is_empty() || args.structure.extractor_json.is_some() {
        return Err(usage(
            "--unfold and --extractor-json apply only to structure and structure-report",
        ));
    }
    Ok(())
}

/// The checkout, its records and the Python `context` data.
fn context(
    args: &Args,
) -> Result<(PathBuf, truth::Corpus, truth::identity::Aliases, Data), Failure> {
    let root = checkout(args)?;
    let (corpus, aliases, _) = load(args)?;
    let records = Records::load(&root).map_err(corpus_error)?;
    let data = Data::load(&root, &records).map_err(corpus_error)?;
    Ok((root, corpus, aliases, data))
}

/// The environment variable that must be `1` for `--recorded-exporters`.
const REPLAY_GATE: &str = "TRUTH_PARITY_REPLAY";

/// Lean, or the recorded exporter outputs of `--recorded-exporters`, which
/// the parity harness alone may use: it needs `TRUTH_PARITY_REPLAY=1`, and a
/// replayed bundle is never written to the trusted presentation path the
/// explorer reads ([`strength::DEFAULT_OUTPUT`]), because replay runs
/// neither Lake nor Comparator.
fn exporters<'a>(args: &'a Args, output: Option<&Path>) -> Result<Exporters<'a>, Failure> {
    let Some(directory) = &args.recorded_exporters else {
        return Ok(Exporters::Lean);
    };
    if std::env::var(REPLAY_GATE).as_deref() != Ok("1") {
        return Err(usage(format!(
            "--recorded-exporters is a parity-test replay without Lean or Comparator; it needs {REPLAY_GATE}=1"
        )));
    }
    if output.and_then(Path::file_name) == Path::new(strength::DEFAULT_OUTPUT).file_name() {
        return Err(usage(format!(
            "a replayed bundle is not live-verified and may not be written as {}",
            strength::DEFAULT_OUTPUT
        )));
    }
    Ok(Exporters::Recorded(Path::new(directory)))
}

fn run_comparisons(args: &Args, operands: &[&str]) -> Output {
    prologue(args, operands, 1, true)?;
    let (root, corpus, aliases, data) = context(args)?;
    let selected: Vec<Ordered> = match operands.first() {
        Some(id) => {
            let selected: Vec<Ordered> = data
                .comparisons
                .iter()
                .filter(|relation| matches!(relation.get("id"), Some(Ordered::String(rid)) if rid == id))
                .cloned()
                .collect();
            if selected.is_empty() {
                return Err(corpus_error(format!("unknown registered comparison: {id}")));
            }
            selected
        }
        None => data.comparisons.clone(),
    };
    let reports = if args.configuration.registered {
        selected
            .iter()
            .map(|relation| strength::projection(relation, &data, None, false))
            .collect::<Result<Vec<_>, _>>()
    } else {
        strength::verify(&root, &corpus, &data, &selected, &exporters(args, None)?)
    }
    .map_err(corpus_error)?;
    if args.machine {
        return Err(raw(0, Ordered::Array(reports).dumps(None) + "\n"));
    }
    let text: String = reports
        .iter()
        .map(|report| {
            let field = |key: &str| match report.get(key) {
                Some(Ordered::String(text)) => text.clone(),
                Some(other) => other.dumps(None),
                None => String::new(),
            };
            format!(
                "{}: {}; {}; converse {}\n",
                field("id"),
                field("comparison_status"),
                field("delta_status"),
                field("converse_status")
            )
        })
        .collect();
    Err(raw(0, aliases.humanize(&text)))
}

fn run_report(args: &Args, operands: &[&str]) -> Output {
    prologue(args, operands, 0, false)?;
    let (root, corpus, _, data) = context(args)?;
    let output = root.join(
        args.structure
            .output
            .as_deref()
            .unwrap_or(strength::DEFAULT_OUTPUT),
    );
    let check = args.structure.check_input;
    let bundle = if check {
        strength::read_bundle(&root, &output, &data)
    } else {
        strength::write_bundle(
            &root,
            &output,
            &corpus,
            &data,
            &exporters(args, Some(&output))?,
        )
    }
    .map_err(corpus_error)?;
    if args.machine {
        return Err(raw(0, strength::without_inputs(&bundle).dumps(None) + "\n"));
    }
    let count = match bundle.get("comparisons") {
        Some(Ordered::Array(reports)) => reports.len(),
        _ => 0,
    };
    let digest = match bundle
        .get("producer")
        .and_then(|producer| producer.get("input_digest"))
    {
        Some(Ordered::String(digest)) => digest.clone(),
        Some(other) => other.dumps(None),
        None => String::new(),
    };
    Err(raw(
        0,
        format!(
            "strength report: {count} comparisons; {digest}\n{}\n",
            if check {
                "Producer freshness validated; no fresh proof execution."
            } else {
                "Existing result verifiers and complete application binding passed."
            }
        ),
    ))
}
