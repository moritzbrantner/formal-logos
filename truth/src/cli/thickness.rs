//! `truth thickness [--queue] [--base REV]`: Python `corpus.py thickness
//! [--queue] [--base REV]`.

use super::{Accepts, Args, Command, Failure, Output, load};
use serde_json::json;
use truth::{frontier, thickness};

pub const COMMAND: Command = Command {
    name: "thickness",
    run,
};

/// JSON as `scripts/corpus.py thickness --json` prints it (plus
/// `input_identity`, and with `--base` the `engines` that computed base and
/// head), and the same text as the Python command.
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        queue: true,
        frontier_root: true,
        base: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let records = thickness::Records::from_corpus(&corpus);
    let flags = frontier::transcription_flags(&args.root, &records);
    let frontier = thickness::frontier_inputs(&frontier_root, &records, &flags);
    let report = thickness::thickness_report(&frontier, &records);
    let base = args.frontier.base.as_deref();
    let (output, text) = if args.queue {
        if base.is_some() {
            return Err(corpus_error("thickness --queue does not take --base"));
        }
        let queue = thickness::thickness_queue(&frontier, &report, &records);
        let text = thickness::format_thickness_queue(&frontier_root, &queue);
        (
            json!({"root": frontier_root, "queue": queue, "input_identity": corpus.input_identity()}),
            text,
        )
    } else if let Some(revision) = base {
        let legacy_root = aliases.legacy(&frontier_root);
        let (base_report, engine) =
            thickness::revision_thickness(&args.root, revision, &frontier_root, legacy_root)
                .map_err(corpus_error)?;
        let delta = thickness::thickness_delta(&base_report, &report);
        let text = thickness::format_thickness(&report, Some(&delta));
        (
            json!({"report": report, "delta": delta,
                   "engines": {"base": engine, "head": "rust"},
                   "input_identity": corpus.input_identity()}),
            text,
        )
    } else {
        let text = thickness::format_thickness(&report, None);
        (
            json!({"report": report, "delta": null, "input_identity": corpus.input_identity()}),
            text,
        )
    };
    Ok((output, Some(aliases.humanize(&text))))
}

/// A Python `CorpusError`: `corpus error: MESSAGE` on stderr, exit 2.
fn corpus_error(message: impl Into<String>) -> Failure {
    (
        2,
        json!({"code": "corpus_error", "message": message.into()}),
    )
}
