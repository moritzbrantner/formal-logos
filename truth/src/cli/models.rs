//! `truth models [--check STATEMENT | --argument ARGUMENT] [--premise
//! STATEMENT]... [--verify]`: Python `corpus.py models` (#954 slices B2 and
//! A6). `--check`, `--argument` and `--verify` Lean-check every registered
//! model's exact evaluations, finite carriers and zero axioms
//! ([`bind_check::verify_models`]) after `lake build`.

use super::{
    Accepts, Args, Command, Output, configurations::corpus_error, load, resolve_in,
    resolve_statement, usage, with_identity,
};
use serde_json::Value;
use std::collections::BTreeSet;
use truth::{bind_check, finite_models};

pub const COMMAND: Command = Command {
    name: "models",
    run,
};

/// The registered models, their classification against a target and
/// premise set, and their co-failure candidates; a `--premise` needs a
/// target.
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        configuration: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let options = &args.configuration;
    if options.case.is_some()
        || options.seed.is_some()
        || options.registered
        || options.max_atoms.is_some()
    {
        return Err(usage(
            "--case, --seed, --registered and --max-atoms do not apply to models",
        ));
    }
    let (corpus, aliases, _) = load(args)?;
    let mut check = options
        .check
        .as_deref()
        .map(|token| resolve_statement(&aliases, token))
        .transpose()?;
    let mut premises = options
        .premises
        .iter()
        .map(|token| resolve_statement(&aliases, token))
        .collect::<Result<Vec<_>, _>>()?;
    let argument = options
        .argument
        .as_deref()
        .map(|token| resolve_in(&aliases, token, &["arguments"]))
        .transpose()?;
    if let Some(id) = &argument {
        let Some(record) = corpus.get("arguments", id) else {
            return Err(corpus_error(format!("unknown argument {id}")));
        };
        let conclusion = record
            .fields
            .get("conclusion_statement_id")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_owned();
        if check.as_ref().is_some_and(|check| *check != conclusion) {
            return Err(corpus_error("--argument conclusion must match --check"));
        }
        check = Some(conclusion);
        let mut all: BTreeSet<String> = premises.into_iter().collect();
        all.extend(
            record
                .fields
                .get("premise_statement_ids")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned),
        );
        premises = all.into_iter().collect();
    }
    if !premises.is_empty() && check.is_none() {
        return Err(corpus_error("--premise requires --check or --argument"));
    }
    for sid in check.iter().chain(&premises) {
        if corpus.get("statements", sid).is_none() {
            return Err(corpus_error(format!("unknown statement {sid}")));
        }
    }
    truth::check::registered_models(&args.root).map_err(corpus_error)?;
    let premise_ids: Vec<&str> = premises.iter().map(String::as_str).collect();
    let mut report =
        finite_models::model_report(&corpus.records("models"), check.as_deref(), &premise_ids);
    report["argument_id"] = argument.map_or(Value::Null, Value::String);
    let mut text = finite_models::format_models(&report);
    if options.verify || check.is_some() {
        let verification = bind_check::verify_models(&args.root, &corpus).map_err(corpus_error)?;
        // Python prints the dictionary in its insertion order.
        text.push_str(&format!(
            "\nmodel-check: {{'models': {}, 'certificates': {}, 'axioms': []}}",
            verification["models"], verification["certificates"]
        ));
        report["verification"] = verification;
    }
    let text = aliases.humanize(&text);
    Ok((with_identity(&report, &corpus), Some(text)))
}
