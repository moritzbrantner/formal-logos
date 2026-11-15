//! `truth index …`: the disposable SQLite/FTS5 lookup index (#954 slice B7),
//! Python `scripts/research_index.py` (see `truth::index`).
//!
//! - `build` — rebuild `.cache/truth-index.sqlite` now;
//! - `search WORDS [--limit N]` — records containing every word, by FTS5 rank;
//! - `show ID` — one record (`kind:ID` when an ID names several) and the
//!   records that reference it;
//! - `duplicates`, `summary` — exact duplicate argument bundles, inventory;
//! - `parity` — every corpus file and record against the index;
//! - `export PATH` — one indexed corpus file's original bytes;
//! - `bundle --case ID [--premise S]...`, `compare --case ID [--left S]...
//!   [--right S]...` — registered-only configuration views.
//!
//! Every query first reuses the index when it is bound to the current corpus
//! and otherwise rebuilds it (Python's query commands reject a stale index
//! instead). Output is Python's JSON: indented without `--json`, compact
//! with it. Errors exit 1, usage errors 2.

use super::{Accepts, Args, Command, Failure, Output, raw, usage};
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use truth::index;

pub const COMMAND: Command = Command { name: "index", run };

const SUBCOMMANDS: &str =
    "index requires build, search, show, duplicates, summary, parity, export, bundle or compare";

fn error(message: impl Into<String>) -> Failure {
    (1, json!({"code": "index_error", "message": message.into()}))
}

fn printed(value: Value) -> Output {
    let text = serde_json::to_string_pretty(&value).unwrap_or_default();
    Ok((value, Some(text)))
}

fn root(args: &Args) -> Result<PathBuf, Failure> {
    std::fs::canonicalize(&args.root)
        .map_err(|failure| error(format!("{}: {failure}", args.root.display())))
}

fn run(args: &Args, operands: &[&str]) -> Output {
    let Some((sub, rest)) = operands.split_first() else {
        return Err(usage(SUBCOMMANDS));
    };
    let configuration = matches!(*sub, "bundle" | "compare");
    args.check_options(Accepts {
        configuration,
        ..Accepts::default()
    })?;
    let options = &args.configuration;
    if configuration
        && (options.seed.is_some()
            || options.registered
            || options.check.is_some()
            || options.argument.is_some()
            || options.verify
            || options.max_atoms.is_some())
    {
        return Err(usage(
            "index bundle and compare take --case, --premise, --left and --right only",
        ));
    }
    if *sub != "bundle" && !options.premises.is_empty() {
        return Err(usage("--premise applies only to index bundle"));
    }
    if *sub != "compare" && args.index.flags {
        return Err(usage("--left and --right apply only to index compare"));
    }
    let research = &args.research;
    if research.all || research.related.is_some() || research.frontier.is_some() {
        return Err(usage(
            "index takes --limit N (search only), not --all, --related or --frontier-json",
        ));
    }
    if *sub != "search" && research.limit.is_some() {
        return Err(usage("--limit applies only to index search"));
    }
    if args.write || args.queue || args.bridge_flags {
        return Err(usage(SUBCOMMANDS));
    }
    let root = root(args)?;
    match (*sub, rest) {
        ("build", []) => {
            let path = index::database(&root);
            index::build(&root, &path).map_err(error)?;
            printed(json!({"index": path.display().to_string(), "mode": "derived lookup only"}))
        }
        ("search", words) if !words.is_empty() => {
            let db = open(&root)?;
            let limit = research.limit.unwrap_or(20);
            printed(index::search(&db, &words.join(" "), limit).map_err(error)?)
        }
        ("show", [id]) => printed(index::show(&open(&root)?, id).map_err(error)?),
        ("duplicates", []) => printed(json!(index::duplicates(&open(&root)?).map_err(error)?)),
        ("summary", []) => printed(index::summary(&open(&root)?).map_err(error)?),
        ("parity", []) => {
            let report = index::parity(&open(&root)?, &root).map_err(error)?;
            if report["issues"]
                .as_array()
                .is_some_and(|issues| !issues.is_empty())
            {
                return Err(error(report.to_string()));
            }
            printed(report)
        }
        ("export", [path]) => {
            let bytes = index::export(&open(&root)?, path).map_err(error)?;
            let text = String::from_utf8(bytes)
                .map_err(|_| error(format!("{path}: indexed bytes are not UTF-8")))?;
            Err(raw(0, text))
        }
        ("bundle", []) => {
            let db = open(&root)?;
            let token = options
                .case
                .as_deref()
                .ok_or_else(|| usage("index bundle requires --case ID"))?;
            let case = index::case(&db, token).map_err(error)?;
            let tables = index::Tables::load(&db).map_err(error)?;
            let premises = index::statements(&db, &options.premises).map_err(error)?;
            printed(index::bundle(&case, &tables, &premises).map_err(error)?)
        }
        ("compare", []) => {
            let db = open(&root)?;
            let token = options
                .case
                .as_deref()
                .ok_or_else(|| usage("index compare requires --case ID"))?;
            let case = index::case(&db, token).map_err(error)?;
            let tables = index::Tables::load(&db).map_err(error)?;
            let left = index::statements(&db, &args.index.left).map_err(error)?;
            let right = index::statements(&db, &args.index.right).map_err(error)?;
            printed(index::compare(token, &case, &tables, &left, &right).map_err(error)?)
        }
        _ => Err(usage(SUBCOMMANDS)),
    }
}

/// The fresh index, rebuilt first when it is missing or stale.
fn open(root: &Path) -> Result<rusqlite::Connection, Failure> {
    index::open(root).map(|(db, _)| db).map_err(error)
}
