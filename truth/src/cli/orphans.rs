//! `truth orphans [--by module|family] [--senses]`: verified work that does
//! not reach the frontier root. `truth orphans --base REV`: the change of its
//! count from a base revision (Python `scripts/orphan_summary.py --base`).

use super::{Accepts, Args, Command, Output, load, usage};
use serde_json::Value;
use serde_json::json;
use truth::orphans;
use truth::{Corpus, identity::Aliases};

pub const COMMAND: Command = Command {
    name: "orphans",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        orphans: true,
        base: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    if args.frontier.base.is_some() && (args.senses || args.group_by.is_some()) {
        return Err(usage("--base and --by/--senses are alternatives"));
    }
    let (corpus, aliases, frontier_root) = load(args)?;
    if let Some(base) = args.frontier.base.as_deref() {
        return Ok(count_delta(args, &corpus, &aliases, &frontier_root, base));
    }
    let (mut output, text) = if args.senses {
        let report = orphans::sense_report(&args.root, &corpus, &frontier_root);
        let text = orphans::format_senses(&report);
        (report, text)
    } else {
        let by = args.group_by.unwrap_or(orphans::GroupBy::Module);
        let report = orphans::report(&args.root, &corpus, &frontier_root, by);
        let text = orphans::format(&report);
        (report, text)
    };
    output["schema_version"] = json!(1);
    output["input_identity"] = json!(corpus.input_identity());
    Ok((output, Some(aliases.humanize(&text))))
}

/// Python `scripts/orphan_summary.py --base REV`: the disconnected count at
/// the head (the working tree; its failure fails the command) and at `base`.
/// A base that cannot be read or computed is reported as unavailable on
/// stderr and in the output, never as a zero baseline, and does not fail.
fn count_delta(
    args: &Args,
    corpus: &Corpus,
    aliases: &Aliases,
    frontier_root: &str,
    base: &str,
) -> (Value, Option<String>) {
    let head = orphans::disconnected_count(&args.root, corpus, frontier_root);
    let root = args.frontier_root_set().then_some(frontier_root);
    let (previous, engine, error) = match orphans::revision_count(&args.root, base, root) {
        Ok((count, engine)) => (Some(count), Some(engine), None),
        Err(error) => {
            eprintln!("Orphan baseline unavailable: {error}");
            (None, None, Some(error))
        }
    };
    let legacy_root = aliases.legacy(frontier_root);
    let text = orphans::format_count_summary(legacy_root, base, head, previous);
    let output = json!({
        "schema_version": 1,
        "root": frontier_root,
        "base": base,
        "base_count": previous,
        "head_count": head,
        "delta": previous.map(|previous| head as i64 - previous as i64),
        "base_error": error,
        "engines": {"base": engine, "head": "rust"},
        "input_identity": corpus.input_identity(),
    });
    (output, Some(text))
}
