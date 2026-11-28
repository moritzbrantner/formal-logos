//! `truth orphans [--by module|family] [--all] [--senses]`: verified work
//! that does not reach the frontier root, with each result's placement state
//! (`--all` lists every disconnected result; by default only unplaced ones).
//! `truth orphans --base REV`: the change of its count from a base revision
//! (Python `scripts/orphan_summary.py --base`). `truth orphans --base REV
//! --gate`: the placement gate; it fails (exit 1) when a result new since the
//! base, or whose argument changed or placement was lost, is unplaced.

use super::{Accepts, Args, Command, HELP, Output, load, raw, usage};
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
    // `--all` is the one research option `orphans` reads.
    let research = &args.research;
    if research.limit.is_some() || research.related.is_some() || research.frontier.is_some() {
        return Err(usage(
            "--limit, --related and --frontier-json apply only to related, dossier and context",
        ));
    }
    if !operands.is_empty() || args.bridge_flags {
        return Err(usage(HELP));
    }
    args.check_options(accepts)?;
    if args.frontier.base.is_some() && (args.senses || args.group_by.is_some() || research.all) {
        return Err(usage("--base and --by/--senses/--all are alternatives"));
    }
    if args.gate && args.frontier.base.is_none() {
        return Err(usage("--gate requires --base REV"));
    }
    if args.senses && research.all {
        return Err(usage("--senses and --all are alternatives"));
    }
    let (corpus, aliases, frontier_root) = load(args)?;
    if let Some(base) = args.frontier.base.as_deref() {
        if args.gate {
            return gate(args, &corpus, &aliases, &frontier_root, base);
        }
        return Ok(count_delta(args, &corpus, &aliases, &frontier_root, base));
    }
    let (mut output, text) = if args.senses {
        let report = orphans::sense_report(&args.root, &corpus, &frontier_root);
        let text = orphans::format_senses(&report);
        (report, text)
    } else {
        let by = args.group_by.unwrap_or(orphans::GroupBy::Module);
        let report = orphans::report(&args.root, &corpus, &frontier_root, by);
        let text = orphans::format(&report, research.all);
        (report, text)
    };
    output["schema_version"] = json!(1);
    output["input_identity"] = json!(corpus.input_identity());
    Ok((output, Some(aliases.humanize(&text))))
}

/// The placement gate against `base` ("head rules on base data"). An
/// unreadable base is a `revision_error` (exit 1), as for `connectivity
/// --base`: a gate that cannot judge must not pass silently.
fn gate(
    args: &Args,
    corpus: &Corpus,
    aliases: &Aliases,
    frontier_root: &str,
    base: &str,
) -> Output {
    let root = args.frontier_root_set().then_some(frontier_root);
    let mut output = orphans::revision_gate(&args.root, corpus, frontier_root, base, root)
        .map_err(|message| (1, json!({"code": "revision_error", "message": message})))?;
    output["schema_version"] = json!(1);
    output["input_identity"] = json!(corpus.input_identity());
    let text = aliases.humanize(&orphans::format_gate(&output));
    if output["passed"] == true {
        return Ok((output, Some(text)));
    }
    Err(if args.machine {
        output["code"] = json!("placement_gate");
        output["message"] = json!(text);
        (1, output)
    } else {
        raw(1, format!("{text}\n"))
    })
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
    let legacy_root = aliases.legacy(frontier_root);
    let root = args.frontier_root_set().then_some(frontier_root);
    let (previous, engine, error) = match orphans::revision_count(&args.root, base, root) {
        Ok(count) => (Some(count), Some("rust"), None),
        Err(error) => {
            eprintln!("Orphan baseline unavailable: {error}");
            (None, None, Some(error))
        }
    };
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
