//! `truth configuration-report (--output PATH | --check PATH |
//! --build-input)`: Python `corpus.py configuration-report` (#954 slice A6).
//!
//! `--output` live-verifies every case in Lean (`lake`, `verify-result.sh`
//! and the bind exporter, as Python runs them) and atomically writes the
//! disposable `.cache` bundle byte for byte as Python does, plus the
//! producer fingerprint; `--check` and `--build-input` validate an existing
//! bundle's freshness without running Lean.

use super::{Accepts, Args, Command, Output, corpus_error, load, raw, usage};
use serde_json::Value;
use std::{fs, path::PathBuf};
use truth::{
    configuration_explorer::{self as explorer, CACHE_PATH},
    configuration_live,
    configurations::Context,
    structure::os_error,
};

pub const COMMAND: Command = Command {
    name: "configuration-report",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        configuration: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let options = &args.configuration;
    let structure = &args.structure;
    if options.case.is_some()
        || options.seed.is_some()
        || !options.premises.is_empty()
        || options.registered
        || options.argument.is_some()
        || options.verify
        || options.max_atoms.is_some()
        || !structure.unfold.is_empty()
        || structure.check_input
        || structure.extractor_json.is_some()
    {
        return Err(usage(
            "configuration-report takes exactly one of --output PATH, --check PATH and --build-input",
        ));
    }
    let modes = [
        structure.output.is_some(),
        options.check.is_some(),
        structure.build_input,
    ];
    if modes.iter().filter(|given| **given).count() != 1 {
        return Err(usage(
            "configuration-report takes exactly one of --output PATH, --check PATH and --build-input",
        ));
    }
    let root =
        fs::canonicalize(&args.root).map_err(|error| corpus_error(os_error(&error, &args.root)))?;
    let absolute = |path: &str| -> PathBuf {
        let path = PathBuf::from(path);
        if path.is_absolute() {
            path
        } else {
            root.join(path)
        }
    };
    let context_of = |corpus| -> Result<Context, super::Failure> {
        truth::check::registered_configurations(&root).map_err(corpus_error)?;
        Ok(Context::new(corpus))
    };
    let bundle = if structure.build_input {
        let Some(artifact) =
            std::env::var_os("TRUTH_CORE_CONFIGURATION_REPORT").filter(|value| !value.is_empty())
        else {
            if std::env::var("TRUTH_CORE_REQUIRE_CONFIGURATION_REPORT").as_deref() == Ok("true") {
                return Err(corpus_error(
                    "certified build requires TRUTH_CORE_CONFIGURATION_REPORT".into(),
                ));
            }
            let text = if args.machine {
                "{\"mode\": \"registered-only\"}"
            } else {
                "configuration build input: registered-only development"
            };
            return Err(raw(0, format!("{text}\n")));
        };
        let path = absolute(&artifact.to_string_lossy());
        if explorer::resolve(&path) != explorer::resolve(&root.join(CACHE_PATH)) {
            return Err(corpus_error(
                "certified build report must use .cache/configuration-explorer.json for cache invalidation".into(),
            ));
        }
        let (corpus, _, _) = load(args)?;
        let context = context_of(&corpus)?;
        explorer::read_bundle(&root, &path, &context).map_err(corpus_error)?
    } else if let Some(check) = &options.check {
        let (corpus, _, _) = load(args)?;
        let context = context_of(&corpus)?;
        explorer::read_bundle(&root, &absolute(check), &context).map_err(corpus_error)?
    } else {
        let requested = absolute(structure.output.as_deref().unwrap_or_default());
        let initial = explorer::input_manifest(&root).map_err(corpus_error)?;
        let (corpus, _, _) = load(args)?;
        let context = context_of(&corpus)?;
        // Python checks the output path only after verifying; checking it
        // first spares a long Lean run that could not be written.
        let output = explorer::output_path(&root, &requested).map_err(corpus_error)?;
        let selections: Vec<_> = context.cases.iter().map(|case| (*case, None)).collect();
        let reports = configuration_live::verified_reports(&root, &corpus, &context, &selections)
            .map_err(corpus_error)?;
        explorer::write_bundle(&root, &output, &context, &reports, &initial)
            .map_err(corpus_error)?
    };
    let text = if args.machine {
        // Input hashes stay server-side; the UI needs source identity and data.
        let mut projection = bundle;
        if let Some(producer) = projection["producer"].as_object_mut() {
            producer.remove("inputs");
        }
        explorer::dumps(&projection)
    } else {
        let producer = &bundle["producer"];
        let cases = bundle["cases"].as_array().map_or(0, Vec::len);
        let text = |value: &Value| value.as_str().unwrap_or_default().to_owned();
        format!(
            "configuration report: {cases} cases; source {}; input digest {}\n{}",
            text(&producer["source_head"]),
            text(&producer["input_digest"]),
            if structure.output.is_some() {
                "Live verification completed; disposable producer output written."
            } else {
                "Validated producer output freshness; this check is not fresh proof execution."
            }
        )
    };
    Err(raw(0, text + "\n"))
}
