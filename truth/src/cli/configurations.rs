//! `truth configurations [--registered]`: Python `corpus.py configurations`
//! (#954 slices B2 and A6). Without `--registered` every selected case is
//! verified live in Lean ([`configuration_live::verified_reports`]).

use super::{Accepts, Args, Command, Failure, Output, load, resolve_in, resolve_statement, usage};
use serde_json::{Value, json};
use truth::{
    configuration_live,
    configurations::{self, Context},
};

pub const COMMAND: Command = Command {
    name: "configurations",
    run,
};

/// A Python `CorpusError`: `corpus error: …` and exit code 2.
pub fn corpus_error(message: impl Into<String>) -> Failure {
    (
        2,
        json!({"code": "corpus_error", "message": message.into()}),
    )
}

/// The registered projection with `--registered`; otherwise Lean builds the
/// selected modules, checks the certificates and models, replays the cores
/// and binds the original theorems before any report is printed.
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        configuration: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let options = &args.configuration;
    if options.check.is_some()
        || options.argument.is_some()
        || options.verify
        || options.max_atoms.is_some()
    {
        return Err(usage(
            "--check, --argument, --verify and --max-atoms do not apply to configurations",
        ));
    }
    truth::check::registered_configurations(&args.root).map_err(corpus_error)?;
    let (corpus, aliases, _) = load(args)?;
    let context = Context::new(&corpus);
    let case = options
        .case
        .as_deref()
        .map(|token| resolve_in(&aliases, token, &["configurations"]))
        .transpose()?;
    let seed = options
        .seed
        .as_deref()
        .map(|token| resolve_statement(&aliases, token))
        .transpose()?;
    let premises = options
        .premises
        .iter()
        .map(|token| resolve_statement(&aliases, token))
        .collect::<Result<Vec<_>, _>>()?;
    let mut cases = context.cases.clone();
    if let Some(case) = &case {
        cases.retain(|record| record.get("id").and_then(Value::as_str) == Some(case));
        if cases.is_empty() {
            return Err(corpus_error(format!("unknown configuration case {case}")));
        }
    }
    if let Some(seed) = &seed {
        if !context.statements.contains_key(seed.as_str()) {
            return Err(corpus_error(format!("unknown statement {seed}")));
        }
        cases
            .retain(|record| record.get("seed_statement_id").and_then(Value::as_str) == Some(seed));
    }
    if !premises.is_empty() && cases.len() != 1 {
        return Err(corpus_error("--premise requires exactly one selected case"));
    }
    let mut selections = Vec::new();
    for case in cases {
        let selection = if premises.is_empty() {
            None
        } else {
            let applications = case
                .get("semantics")
                .and_then(|semantics| semantics.get("applications"))
                .and_then(Value::as_object);
            let unique = premises
                .iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len()
                == premises.len();
            if !unique
                || premises.iter().any(|sid| {
                    !applications.is_some_and(|applications| applications.contains_key(sid))
                })
            {
                return Err(corpus_error(
                    "premises must be unique explicit statement IDs in this profile",
                ));
            }
            Some(premises.iter().map(String::as_str).collect::<Vec<_>>())
        };
        selections.push((case, selection));
    }
    let reports = if options.registered {
        let mut reports = Vec::new();
        for (case, selection) in &selections {
            let mut report = configurations::configuration_report(
                case,
                &context.results,
                &context.arguments,
                &context.models,
                false,
                selection.as_ref().map(|ids| ("selection", ids.to_vec())),
            )
            .map_err(corpus_error)?;
            report["verification"] = Value::Null;
            reports.push(report);
        }
        reports
    } else {
        configuration_live::verified_reports(&args.root, &corpus, &context, &selections)
            .map_err(corpus_error)?
    };
    let text = configurations::format_configurations(&reports);
    // Python prints nothing at all for no selected case.
    let text = (!reports.is_empty()).then(|| aliases.humanize(&text));
    Ok((Value::Array(reports), text))
}
