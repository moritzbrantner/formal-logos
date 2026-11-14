//! `truth thickness [--queue]`: Python `corpus.py thickness [--queue]`.

use super::{Accepts, Args, Command, Output, load};
use serde_json::json;
use truth::{frontier, thickness};

pub const COMMAND: Command = Command {
    name: "thickness",
    run,
};

/// JSON as `scripts/corpus.py thickness --json` prints it (plus
/// `input_identity`), and the same text as the Python command.
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        queue: true,
        frontier_root: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let records = thickness::Records::from_corpus(&corpus);
    let flags = frontier::transcription_flags(&args.root, &records);
    let frontier = thickness::frontier_inputs(&frontier_root, &records, &flags);
    let report = thickness::thickness_report(&frontier, &records);
    let (output, text) = if args.queue {
        let queue = thickness::thickness_queue(&frontier, &report, &records);
        let text = thickness::format_thickness_queue(&frontier_root, &queue);
        (
            json!({"root": frontier_root, "queue": queue, "input_identity": corpus.input_identity()}),
            text,
        )
    } else {
        let text = thickness::format_thickness(&report);
        (
            json!({"report": report, "delta": null, "input_identity": corpus.input_identity()}),
            text,
        )
    };
    Ok((output, Some(aliases.humanize(&text))))
}
