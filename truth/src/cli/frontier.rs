//! `truth frontier [--reaching-root] [--routes] [--fixture FILE]`: Python
//! `corpus.py frontier`, or Python `frontier_report` on a fixture.

use super::{Accepts, Args, Command, Failure, Output, load, resolve_statement};
use serde_json::{Value, json};
use std::io::Read;
use truth::frontier;

pub const COMMAND: Command = Command {
    name: "frontier",
    run,
};

/// JSON as `scripts/corpus.py frontier --json` prints it (plus
/// `input_identity`; `next_steps` only without `--routes`, as in Python), and
/// the same text as the Python command. Only the requested form is computed.
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        frontier: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let options = &args.frontier;
    let machine = args.machine;
    let next_steps = machine && !options.routes;
    let (report, identity, aliases) = match &options.fixture {
        Some(path) => {
            let (fixture, identity) = read_fixture(path)?;
            let aliases = fixture.aliases();
            let frontier_root = resolve_statement(&aliases, &args.frontier_root)?;
            let report = fixture.report(&frontier_root, options.reaching_root, next_steps);
            (report, identity, aliases)
        }
        None => {
            let (corpus, aliases, frontier_root) = load(args)?;
            let report = frontier::current_frontier(
                &args.root,
                &corpus,
                &frontier_root,
                options.reaching_root,
                next_steps,
            );
            (report, corpus.input_identity(), aliases)
        }
    };
    let identity = json!(identity);
    let (output, text) = if options.routes {
        let mut routes = report["routes"].clone();
        let text = if machine {
            String::new()
        } else {
            frontier::format_routes(&routes)
        };
        routes["input_identity"] = identity;
        (routes, text)
    } else {
        let text = if machine {
            String::new()
        } else {
            frontier::format_frontier(&report)
        };
        let mut report = report;
        report["input_identity"] = identity;
        (report, text)
    };
    Ok((output, Some(aliases.humanize(&text))))
}

fn fixture_error(message: String) -> Failure {
    (1, json!({"code": "fixture_error", "message": message}))
}

/// The fixture at `path` (`-`: stdin) and its input identity: the FNV-1a
/// hash of its bytes, in the form `Corpus::input_identity` prints.
fn read_fixture(path: &str) -> Result<(frontier::Fixture, String), Failure> {
    let mut bytes = Vec::new();
    let read = if path == "-" {
        std::io::stdin().read_to_end(&mut bytes).map(|_| ())
    } else {
        std::fs::read(path).map(|content| bytes = content)
    };
    read.map_err(|error| fixture_error(format!("cannot read frontier fixture {path}: {error}")))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| fixture_error(format!("frontier fixture {path} is not JSON: {error}")))?;
    let fixture = frontier::Fixture::parse(&value)
        .map_err(|message| fixture_error(format!("frontier fixture {path}: {message}")))?;
    let mut state = truth::FNV1A64_OFFSET;
    truth::fnv1a64_update(&mut state, &bytes);
    Ok((fixture, format!("fnv1a64:{state:016x}")))
}
