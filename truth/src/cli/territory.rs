//! `truth territory`: Python `corpus.py territory` (#954 slice B2).

use super::{
    Accepts, Args, Command, Output, configurations::corpus_error, load, usage, validate_first,
    with_identity,
};
use serde_json::Value;
use truth::{
    configurations::Index,
    frontier,
    territory::{self, Bounds, Inputs},
};

pub const COMMAND: Command = Command {
    name: "territory",
    run,
};

/// Emergent positions and the territory matrix; writes no record. Python
/// validates the corpus first; the frontier root is `--frontier-root` here
/// (Python `--root`).
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        configuration: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let options = &args.configuration;
    if options.case.is_some()
        || options.seed.is_some()
        || !options.premises.is_empty()
        || options.registered
        || options.check.is_some()
        || options.argument.is_some()
        || options.verify
    {
        return Err(usage(
            "only --frontier-root and --max-atoms apply to territory",
        ));
    }
    validate_first(&args.root)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let report = frontier::current_frontier(&args.root, &corpus, &frontier_root, false, false);
    if report["root_known"] != true {
        return Err(corpus_error(format!(
            "unknown root statement: {frontier_root}"
        )));
    }
    let index = |kind: &str| -> Index {
        corpus
            .records(kind)
            .into_iter()
            .map(|record| {
                (
                    record.get("id").and_then(Value::as_str).unwrap_or_default(),
                    record,
                )
            })
            .collect()
    };
    let array = |value: &Value| value.as_array().cloned().unwrap_or_default();
    let inputs = Inputs {
        statements: index("statements"),
        arguments: index("arguments"),
        results: index("results").into_iter().collect(),
        relations: corpus.records("relations"),
        claims: corpus.records("claims"),
        sources: index("sources"),
        models: corpus.records("models"),
        // A map from result ID to its transcription kind.
        transcription_results: report["transcription_results"]
            .as_object()
            .map(|kinds| kinds.keys().cloned().collect())
            .unwrap_or_default(),
        seeds: array(&report["items"])
            .iter()
            .filter(|item| !item["path_to_root"].is_null())
            .map(|item| {
                (
                    item["statement_id"].as_str().unwrap_or_default().to_owned(),
                    item["transitive_dependent_arguments"]
                        .as_array()
                        .map_or(0, Vec::len),
                )
            })
            .collect(),
        routes: array(&report["routes"]["routes"]),
    };
    let bounds = Bounds {
        max_atoms: options.max_atoms.unwrap_or(Bounds::default().max_atoms),
        ..Bounds::default()
    };
    let mut territory = territory::territory_report(&inputs, &bounds);
    territory.report["root"] = Value::String(frontier_root);
    if args.machine && territory.count_unrepresentable() {
        // Python prints the exact (unbounded) int; serde_json has no exact
        // number beyond u64 here, so refuse instead of misreporting it.
        let count = territory.global_count.as_ref().map(|count| count.decimal());
        return Err((
            1,
            serde_json::json!({"code": "unrepresentable_count", "message": format!(
                "the global position count {} exceeds the JSON integers truth prints; use `python3 scripts/corpus.py territory --json`",
                count.unwrap_or_default())}),
        ));
    }
    let text = aliases.humanize(&territory::format_territory(&territory));
    Ok((with_identity(&territory.report, &corpus), Some(text)))
}
