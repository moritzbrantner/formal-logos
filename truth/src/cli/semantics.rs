//! `truth semantics TARGET` and `truth semantics --premise … --conclusion …`:
//! the definitions, disambiguations and senses of a proposition or argument
//! with a per-term compatibility verdict for its connected arguments, and the
//! equivocation preflight of a candidate argument (`truth::semantics`).
//! Read-only.

use super::{Args, Command, Failure, HELP, Output, load, raw, research, unknown, usage};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use truth::semantics::{self, BridgeRequest, Semantics};

pub const COMMAND: Command = Command {
    name: "semantics",
    run,
};

fn error(message: String) -> Failure {
    (1, json!({"code": "semantics_error", "message": message}))
}

fn check(args: &Args) -> Result<(), Failure> {
    let configuration = &args.configuration;
    if args.bridge_flags
        || args.queue
        || args.frontier_flags()
        || args.frontier.fixture.is_some()
        || args.senses
        || args.group_by.is_some()
        || args.issues.own()
        || args.issues.issues_from.is_some()
        || args.research.all
        || args.research.related.is_some()
        || args.research.frontier.is_some()
        || args.write
        || configuration.case.is_some()
        || configuration.seed.is_some()
        || configuration.check.is_some()
        || configuration.argument.is_some()
        || configuration.registered
        || configuration.verify
        || configuration.max_atoms.is_some()
    {
        return Err(usage("an option does not apply to semantics"));
    }
    args.proof.only("semantics", &["--strict"])
}

fn limit(args: &Args) -> Result<usize, Failure> {
    match args.research.limit {
        None => Ok(semantics::DEFAULT_LIMIT),
        Some(limit) if (1..=200).contains(&limit) => Ok(limit as usize),
        Some(_) => Err(usage("--limit must be between 1 and 200")),
    }
}

/// `STATEMENT` or `STATEMENT@SENSE,SENSE`. The suffix names senses only when
/// both resolve; otherwise the whole token is the statement (a label may
/// contain '@'). A known statement with an unknown sense suffix exits 3.
fn bridge(
    aliases: &truth::identity::Aliases,
    loaded: &Semantics,
    token: &str,
) -> Result<BridgeRequest, Failure> {
    let statement = |token: &str| super::resolve(aliases, token, Some(&["statements"]));
    if let Some((head, suffix)) = token.rsplit_once('@')
        && let Some((from, to)) = suffix.split_once(',')
    {
        let (from, to) = (from.trim(), to.trim());
        let senses = loaded
            .resolve_sense(from)
            .and_then(|_| loaded.resolve_sense(to));
        match (statement(head)?, senses) {
            (Some(statement_id), Ok(_)) => {
                return Ok(BridgeRequest {
                    statement_id,
                    senses: Some((from.to_owned(), to.to_owned())),
                });
            }
            (Some(_), Err(message)) if statement(token)?.is_none() => {
                return Err(unknown(&format!("bridge {token}: {message}")));
            }
            _ => {}
        }
    }
    let statement_id =
        statement(token)?.ok_or_else(|| unknown(&format!("unknown bridge statement: {token}")))?;
    Ok(BridgeRequest {
        statement_id,
        senses: None,
    })
}

fn run(args: &Args, operands: &[&str]) -> Output {
    check(args)?;
    let limit = limit(args)?;
    let preflight = !args.configuration.premises.is_empty()
        || args.semantics.conclusion.is_some()
        || !args.semantics.definitions.is_empty();
    let (corpus, aliases, frontier_root) = load(args)?;
    let statement = |token: &str| -> Result<String, Failure> {
        super::resolve(&aliases, token, Some(&["statements"]))?
            .ok_or_else(|| unknown(&format!("unknown statement: {token}")))
    };
    if preflight {
        let Some(conclusion) = args.semantics.conclusion.as_deref() else {
            return Err(usage(
                "the semantics preflight (--premise, --definition) needs --conclusion STATEMENT",
            ));
        };
        if !operands.is_empty() {
            return Err(usage(
                "semantics takes either TARGET or --premise/--conclusion, not both",
            ));
        }
        if args.frontier_root_set() || args.research.limit.is_some() {
            return Err(usage(
                "--frontier-root and --limit do not apply to the semantics preflight",
            ));
        }
        let conclusion = statement(conclusion)?;
        let premises = args
            .configuration
            .premises
            .iter()
            .map(|token| statement(token))
            .collect::<Result<Vec<_>, _>>()?;
        let definitions = args
            .semantics
            .definitions
            .iter()
            .map(|token| {
                super::resolve(&aliases, token, Some(&["definitions"]))?
                    .ok_or_else(|| unknown(&format!("unknown definition: {token}")))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let loaded = Semantics::new(&args.root, &corpus).map_err(error)?;
        let bridges = args
            .semantics
            .bridges
            .iter()
            .map(|token| bridge(&aliases, &loaded, token))
            .collect::<Result<Vec<_>, _>>()?;
        let view = loaded
            .preflight(&premises, &conclusion, &definitions, &bridges)
            .map_err(error)?;
        let text = aliases.humanize(&semantics::format(&view));
        let value = super::with_identity(&view, &corpus);
        let mixed = view["unbridged"]
            .as_array()
            .is_some_and(|entries| !entries.is_empty());
        if args.proof.strict && mixed {
            let stdout = if args.machine {
                value.to_string()
            } else {
                text
            };
            return Err(raw(1, stdout + "\n"));
        }
        return Ok((value, Some(text)));
    }
    if args.semantics.flags || args.proof.strict {
        return Err(usage(
            "--bridge and --strict apply only to the semantics preflight (--conclusion …)",
        ));
    }
    let token = match operands {
        [token] if !token.is_empty() => *token,
        _ => return Err(usage(HELP)),
    };
    let mut found = None;
    for kind in ["statements", "arguments", "results"] {
        if let Some(id) = super::resolve(&aliases, token, Some(&[kind]))? {
            found = Some((kind, id));
            break;
        }
    }
    let (kind, id) =
        found.ok_or_else(|| unknown(&format!("unknown statement, argument or result: {token}")))?;
    let reaching = reaching_root(args, &corpus, &frontier_root)?;
    let mut loaded = Semantics::new(&args.root, &corpus).map_err(error)?;
    if let Some(reaching) = reaching {
        loaded = loaded.with_reaching_root(reaching);
    }
    let mut view = match kind {
        "statements" => loaded.statement_view(&id, limit),
        _ => {
            let argument = if kind == "results" {
                let result = &corpus.get("results", &id).expect("resolved result").fields;
                result
                    .get("argument_id")
                    .and_then(Value::as_str)
                    .filter(|argument| corpus.get("arguments", argument).is_some())
                    .ok_or_else(|| unknown(&format!("result {id} has no known argument")))?
                    .to_owned()
            } else {
                id.clone()
            };
            loaded.argument_view(&argument, limit)
        }
    };
    view["frontier_root"] = json!(frontier_root);
    if kind == "results" {
        view["requested"] = json!({"kind": kind, "id": id});
    }
    let text = aliases.humanize(&semantics::format(&view));
    Ok((super::with_identity(&view, &corpus), Some(text)))
}

/// The statements reaching the frontier root, or `None` when the default
/// root is not in this corpus (arguments then stay in file order). An
/// explicit `--frontier-root` must be known.
fn reaching_root(
    args: &Args,
    corpus: &truth::Corpus,
    frontier_root: &str,
) -> Result<Option<BTreeSet<String>>, Failure> {
    if args.frontier_root_set() {
        let view = research::frontier_view(args, corpus, frontier_root)?;
        return Ok(Some(view.reaching_root_statements));
    }
    if corpus.get("statements", frontier_root).is_none() {
        return Ok(None);
    }
    let report = truth::frontier::current_frontier(&args.root, corpus, frontier_root, false, false);
    Ok(Some(
        report["reaching_root_statements"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_owned)
            .collect(),
    ))
}
