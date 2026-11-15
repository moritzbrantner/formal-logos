//! Command-line dispatch: one module per subcommand, found through
//! [`COMMANDS`].
//!
//! [`args::parse`] reads every shared option in token order, as before the
//! split, so option errors keep their precedence. The first positional
//! argument names the command; its `run` receives the parsed options and the
//! remaining positional operands, checks which options apply, and returns the
//! JSON value and text that [`main`] prints. Adding a command is one new
//! module plus one [`COMMANDS`] line (see `truth/README.md`).

use serde_json::{Value, json};
use std::{ffi::OsString, path::Path, process::ExitCode};
use truth::{
    Corpus,
    identity::{Aliases, Unresolved},
};

mod args;
mod bind_check;
mod bridges;
mod check;
mod configurations;
mod context;
mod dossier;
mod frontier;
mod frontier_diff;
mod ids;
mod inspect;
mod lexicon;
mod models;
mod next;
mod next_steps;
mod orphans;
mod related;
mod research;
mod sort_lists;
mod status;
mod territory;
mod thickness;

pub use args::{Accepts, Args};

pub const HELP: &str = "Usage: truth [--root PATH] [--json] status
       truth [--root PATH] [--json] check
       truth [--root PATH] [--json] inspect ID
       truth [--root PATH] [--json] thickness [--queue] [--frontier-root STATEMENT]
       truth [--root PATH] [--json] frontier [--reaching-root] [--routes] [--frontier-root STATEMENT]
       truth [--root PATH] [--json] frontier-diff --base REV [--head REV] [--frontier-root STATEMENT]
       truth [--root PATH] [--json] orphans [--frontier-root STATEMENT] [--by module|family] [--senses]
       truth [--root PATH] [--json] bridges --constants FILE (--queue-file FILE | --target ID)...
             [--targets N] [--top K] [--pool M]
       truth [--root PATH] [--json] related STATEMENT [--limit N]
       truth [--root PATH] [--json] dossier (STATEMENT | --all) [--frontier-json FILE] [--limit N]
       truth [--root PATH] [--json] context TARGET [--frontier-json FILE] [--limit N] [--related N]
       truth [--root PATH] [--json] next
       truth [--root PATH] [--json] next-steps [--frontier-root STATEMENT]
       truth [--root PATH] [--json] arguments
       truth [--root PATH] [--json] results
       truth [--root PATH] [--json] sort-lists
       truth [--root PATH] [--json] lexicon (show WORD | untraced | coverage | check | bootstrap | allowlist | ratchet --base REV) [--limit N] [--write]
       truth [--root PATH] [--json] configurations --registered [--case ID] [--seed STATEMENT] [--premise STATEMENT]...
       truth [--root PATH] [--json] models
       truth [--root PATH] [--json] territory [--frontier-root STATEMENT] [--max-atoms N]
       truth [--root PATH] [--json] bind-check [--result RESULT]... [--affected --base REV [--head REV]]
             [--lean-json FILE] [--print-lean-input]

An ID, STATEMENT, TARGET or --target may be a uuid, a legacy id (STMT-...) or a label.
dossier and context compute the frontier in-process, or read it from FILE, written by
`python3 scripts/corpus.py frontier --json [--root STATEMENT]` on the same checkout.";

/// An error: exit code and the JSON error object (`code`, `message`, ...).
pub type Failure = (u8, Value);

/// A command's output: the `--json` value and the text printed without
/// `--json` (`None` prints nothing).
pub type Output = Result<(Value, Option<String>), Failure>;

/// One subcommand.
pub struct Command {
    /// The first positional argument that selects it.
    pub name: &'static str,
    /// Runs it with the parsed options and the positional operands after
    /// `name`; it rejects the options that do not apply to it.
    pub run: fn(&Args, &[&str]) -> Output,
}

/// Every subcommand. A new command adds its module and one line here.
pub const COMMANDS: &[Command] = &[
    status::COMMAND,
    check::COMMAND,
    inspect::COMMAND,
    thickness::COMMAND,
    frontier::COMMAND,
    frontier_diff::COMMAND,
    orphans::COMMAND,
    bridges::COMMAND,
    related::COMMAND,
    dossier::COMMAND,
    context::COMMAND,
    next::COMMAND,
    next_steps::COMMAND,
    ids::ARGUMENTS,
    ids::RESULTS,
    sort_lists::COMMAND,
    lexicon::COMMAND,
    configurations::COMMAND,
    models::COMMAND,
    territory::COMMAND,
    bind_check::COMMAND,
];

/// Parses `args` and runs the command it names.
pub fn run(args: &[OsString]) -> Output {
    let args = args::parse(args)?;
    let positional: Vec<&str> = args.positional.iter().map(String::as_str).collect();
    match positional.split_first() {
        Some((name, operands)) => match COMMANDS.iter().find(|command| command.name == *name) {
            Some(command) if args.bind.flags && command.name != "bind-check" => Err(usage(
                "--result, --affected, --lean-json and --print-lean-input apply only to bind-check",
            )),
            Some(command) => (command.run)(&args, operands),
            None => Err(args.shape_error()),
        },
        None => Err(args.shape_error()),
    }
}

/// The process entry point: `--help`, then the command, printed as JSON on
/// `--json` and as text otherwise; errors go to stderr with their exit code.
pub fn main(args: &[OsString]) -> ExitCode {
    if matches!(args, [arg] if arg == "--help" || arg == "-h") {
        println!("{HELP}");
        return ExitCode::SUCCESS;
    }
    let machine = args.iter().any(|arg| arg == "--json");
    match run(args) {
        Ok((output, text)) => {
            if machine {
                println!("{output}");
            } else if let Some(text) = text {
                // `check` text: stderr part, then the stdout summary.
                if let Some(rest) = text.strip_prefix('\u{0}') {
                    let (stderr, stdout) = rest.split_once('\u{0}').unwrap_or((rest, ""));
                    if !stderr.is_empty() {
                        eprintln!("{stderr}");
                    }
                    println!("{stdout}");
                } else {
                    println!("{text}");
                }
            }
            ExitCode::SUCCESS
        }
        Err((code, error)) if error["code"] == "raw_output" => {
            print!("{}", error["stdout"].as_str().unwrap_or_default());
            ExitCode::from(code)
        }
        Err((code, error)) => {
            if machine {
                eprintln!("{}", json!({"schema_version":1,"error":error}));
            } else if error["stdout"] == true {
                // A Python report that prints its outcome to stdout and
                // exits nonzero (`next` without candidates).
                println!("{}", error["message"].as_str().unwrap_or_default());
            } else if error["code"] == "corpus_error" {
                eprintln!(
                    "corpus error: {}",
                    error["message"].as_str().unwrap_or_default()
                );
            } else if let Some(path) = error["path"].as_str() {
                eprintln!(
                    "truth: {path}: {}",
                    error["message"].as_str().unwrap_or_default()
                );
            } else {
                eprintln!("truth: {}", error["message"].as_str().unwrap_or_default());
            }
            ExitCode::from(code)
        }
    }
}

/// A command whose stdout must be byte-identical to Python's in both modes
/// (`bind-check`'s sorted, indented JSON and its text) and whose exit code
/// may be nonzero on success: `main` prints `stdout` exactly and exits `code`.
pub fn raw(code: u8, stdout: String) -> Failure {
    (code, json!({"code": "raw_output", "stdout": stdout}))
}

/// A Python `CorpusError`: `corpus error: …`, exit code 2.
pub fn corpus_error(message: String) -> Failure {
    (2, json!({"code": "corpus_error", "message": message}))
}

pub fn usage(message: impl Into<String>) -> Failure {
    (2, json!({"code":"usage", "message": message.into()}))
}

pub fn unknown(message: &str) -> Failure {
    (3, json!({"code":"unknown_id", "message":message}))
}

pub fn invalid_target(message: &str) -> Failure {
    (2, json!({"code":"invalid_target", "message":message}))
}

pub fn input_error(path: &str, message: String) -> Failure {
    (
        1,
        json!({"code":"invalid_input", "path":path, "message":message}),
    )
}

pub fn read_json(path: &str) -> Result<Value, Failure> {
    let bytes = std::fs::read(path).map_err(|error| {
        (
            1,
            json!({"code":"read_error", "path":path, "message":error.to_string()}),
        )
    })?;
    serde_json::from_slice(&bytes).map_err(|error| {
        (
            1,
            json!({"code":"invalid_json", "path":path, "message":error.to_string()}),
        )
    })
}

/// `value` as a JSON object with the corpus `input_identity` added.
pub fn with_identity(value: impl serde::Serialize, corpus: &Corpus) -> Value {
    let mut value = serde_json::to_value(value).unwrap_or(Value::Null);
    if let Some(object) = value.as_object_mut() {
        object.insert("input_identity".into(), json!(corpus.input_identity()));
    }
    value
}

/// The uuid `token` names (uuid, legacy id, label, case-insensitive label),
/// `None` when it names no record; naming several records is an error.
pub fn resolve(
    aliases: &Aliases,
    token: &str,
    kinds: Option<&[&str]>,
) -> Result<Option<String>, Failure> {
    match aliases.resolve(token, kinds) {
        Ok(id) => Ok(Some(id)),
        Err(Unresolved::Unknown) => Ok(None),
        Err(Unresolved::Ambiguous(candidates)) => Err((
            3,
            json!({"code": "unknown_id", "id": token,
                   "message": format!("{token:?} names several records: {}; pass a uuid",
                                      aliases.describe(&candidates)),
                   "candidates": candidates.iter()
                       .map(|(kind, id)| json!({"kind": kind, "id": id, "label": aliases.label(id)}))
                       .collect::<Vec<_>>()}),
        )),
    }
}

/// A command-line token as the uuid it names, trying `kinds` in order
/// (Python `resolve_id`); an unknown token stays as given so the command
/// reports it.
pub fn resolve_in(aliases: &Aliases, token: &str, kinds: &[&str]) -> Result<String, Failure> {
    for kind in kinds {
        if let Some(id) = resolve(aliases, token, Some(&[kind]))? {
            return Ok(id);
        }
    }
    Ok(token.to_owned())
}

/// A statement token as its uuid; an unknown token stays as given.
pub fn resolve_statement(aliases: &Aliases, token: &str) -> Result<String, Failure> {
    resolve_in(aliases, token, &["statements"])
}

/// The structurally loaded corpus at `--root`, its aliases and the resolved
/// `--frontier-root`.
pub fn load(args: &Args) -> Result<(Corpus, Aliases, String), Failure> {
    let corpus = Corpus::load(&args.root).map_err(|error| {
        (
            1,
            json!({"code":error.code, "path":error.path, "message":error.message}),
        )
    })?;
    let aliases = corpus.aliases();
    let frontier_root = resolve_statement(&aliases, &args.frontier_root)?;
    Ok((corpus, aliases, frontier_root))
}

/// Validate first: runs the full `truth check` validation (Python
/// `validate()`) on the checkout at `root` and fails as Python's
/// `corpus.py` does on a broken corpus, with its first `corpus error: …`
/// and exit code 2, before a ported report command does its own work.
///
/// Python's `bind-check`, `next`, the ID-list commands, `status`,
/// `thickness`, `frontier` and `dossier --all` call `validate()` first; a
/// Rust port of such a command that must keep that behaviour calls this
/// before [`load`]. Warnings are not printed (Python prints them only for
/// `check`). `next`, `next-steps`, `arguments`, `results`, `territory` and
/// `bind-check`
/// call it; the earlier ports perform only the structural load.
pub fn validate_first(root: &Path) -> Result<truth::check::Outcome, Failure> {
    truth::check::check(root)
        .map_err(|message| (2, json!({"code": "corpus_error", "message": message})))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_names_are_unique_and_documented() {
        for (index, command) in COMMANDS.iter().enumerate() {
            assert!(
                COMMANDS[..index]
                    .iter()
                    .all(|other| other.name != command.name),
                "{} registered twice",
                command.name
            );
            assert!(
                HELP.contains(&format!("[--json] {}", command.name)),
                "{} missing from HELP",
                command.name
            );
        }
    }

    #[test]
    fn validate_first_fails_like_python_on_a_broken_corpus() {
        let root =
            std::env::temp_dir().join(format!("truth-validate-first-{}", std::process::id()));
        let statements = root.join("corpus").join("statements");
        std::fs::create_dir_all(&statements).unwrap();
        std::fs::write(statements.join("a.json"), "[]").unwrap();
        let Err((code, error)) = validate_first(&root) else {
            panic!("a broken corpus validated")
        };
        std::fs::remove_dir_all(&root).unwrap();
        assert_eq!(code, 2);
        assert_eq!(error["code"], "corpus_error");
    }
}
