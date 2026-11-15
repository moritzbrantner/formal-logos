//! `truth models`: Python `corpus.py models` without the Lean model check
//! (#954 slice B2).

use super::{
    Accepts, Args, Command, Output, configurations::corpus_error, load, usage, with_identity,
};
use truth::finite_models;

pub const COMMAND: Command = Command {
    name: "models",
    run,
};

/// The registered models and their co-failure candidates. `--check`,
/// `--argument` and `--verify` Lean-check every registered model in Python
/// (`verify_models`), which stays Python's until slice A6; a `--premise`
/// needs one of the first two.
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
    if options.check.is_some() || options.argument.is_some() || options.verify {
        return Err(usage(
            "models --check, --argument and --verify Lean-check the registered models; use `python3 scripts/corpus.py models`",
        ));
    }
    if !options.premises.is_empty() {
        return Err(corpus_error("--premise requires --check or --argument"));
    }
    truth::check::registered_models(&args.root).map_err(corpus_error)?;
    let (corpus, aliases, _) = load(args)?;
    let mut report = finite_models::model_report(&corpus.records("models"), None, &[]);
    report["argument_id"] = serde_json::Value::Null;
    let text = aliases.humanize(&finite_models::format_models(&report));
    Ok((with_identity(&report, &corpus), Some(text)))
}
