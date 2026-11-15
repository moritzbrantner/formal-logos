//! `truth brief (TARGET | --question TEXT)` and `truth novelty (TEXT |
//! --statement ID)` (#1643): the evidence-linked research brief and the
//! advisory novelty check (`truth::brief`). Both read the corpus, the
//! frontier (in-process or `--frontier-json`), `docs/notes` through the
//! `truth index` projection, and an optional offline `--issues-from`
//! snapshot; neither calls GitHub or writes a corpus record.

use super::{Args, Command, Failure, HELP, Output, input_error, load, research, unknown, usage};
use serde_json::{Value, json};
use truth::brief::{self, Inputs, retrieval};

pub const BRIEF: Command = Command {
    name: "brief",
    run: run_brief,
};
pub const NOVELTY: Command = Command {
    name: "novelty",
    run: run_novelty,
};

fn error(message: String) -> Failure {
    (1, json!({"code": "brief_error", "message": message}))
}

/// Rejects the shared options neither command takes.
fn check(args: &Args, command: &str) -> Result<(), Failure> {
    if args.bridge_flags
        || args.configuration.flags
        || args.queue
        || args.frontier_flags()
        || args.senses
        || args.group_by.is_some()
        || args.issues.own()
        || args.research.all
        || args.research.related.is_some()
        || args.write
    {
        return Err(usage(format!("an option does not apply to {command}")));
    }
    if command == "brief" && args.brief.statement.is_some() {
        return Err(usage(
            "--statement applies only to novelty; brief takes the statement as TARGET",
        ));
    }
    if command == "novelty" && args.brief.question.is_some() {
        return Err(usage(
            "--question applies only to brief; novelty takes the text as its operand",
        ));
    }
    Ok(())
}

fn limit(args: &Args) -> Result<usize, Failure> {
    match args.research.limit {
        None => Ok(brief::DEFAULT_LIMIT),
        Some(limit) if (1..=200).contains(&limit) => Ok(limit as usize),
        Some(_) => Err(usage("--limit must be between 1 and 200")),
    }
}

/// The issue evidence: the snapshot at `--issues-from`, or explicitly missing.
fn issues(args: &Args, revision: &retrieval::Revision) -> Result<retrieval::Issues, Failure> {
    match args
        .issues
        .issues_from
        .as_deref()
        .filter(|path| !path.is_empty())
    {
        Some(path) => retrieval::read_snapshot(path, revision.committed_epoch)
            .map(retrieval::Issues::Snapshot)
            .map_err(|message| (2, json!({"code": "corpus_error", "message": message}))),
        None => Ok(retrieval::Issues::Missing {
            meaning: retrieval::MISSING_ISSUES,
        }),
    }
}

fn run_brief(args: &Args, operands: &[&str]) -> Output {
    check(args, "brief")?;
    let question = args.brief.question.as_deref();
    let target = match (operands, question) {
        ([target], None) if !target.is_empty() => Some(*target),
        ([], Some(_)) => None,
        _ => return Err(usage(HELP)),
    };
    let limit = limit(args)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let view = research::frontier_view(args, &corpus, &frontier_root)?;
    let revision = retrieval::Revision::of(&args.root);
    let issues = issues(args, &revision)?;
    let inputs = Inputs {
        root: &args.root,
        corpus: &corpus,
        aliases: &aliases,
        view: &view,
        issues: &issues,
        revision,
    };
    let value = match target {
        Some(token) => {
            let kinds = ["statements", "arguments", "results"];
            let mut found = None;
            for kind in kinds {
                if let Some(id) = super::resolve(&aliases, token, Some(&[kind]))? {
                    found = Some((kind, id));
                    break;
                }
            }
            let (kind, id) = found.ok_or_else(|| {
                unknown(&format!("unknown statement, argument or result: {token}"))
            })?;
            let sid = brief::target_statement(&corpus, kind, &id)
                .filter(|sid| corpus.get("statements", sid).is_some())
                .ok_or_else(|| {
                    unknown(&format!("{kind} {id} has no known conclusion statement"))
                })?;
            let requested = (kind != "statements").then(|| json!({"kind": kind, "id": id}));
            brief::statement_brief(&inputs, &sid, requested).map_err(error)?
        }
        None => {
            let root = std::fs::canonicalize(&args.root).map_err(|failure| {
                input_error(&args.root.display().to_string(), failure.to_string())
            })?;
            let (db, state) = retrieval::open_index(&root).map_err(error)?;
            brief::question_brief(&inputs, &db, state, question.unwrap_or_default(), limit)
                .map_err(error)?
        }
    };
    let text = brief::format_brief(&value, &aliases, limit);
    Ok((with_identity(value, &corpus), Some(text)))
}

fn with_identity(mut value: Value, corpus: &truth::Corpus) -> Value {
    value["input_identity"] = json!(corpus.input_identity());
    value
}

fn run_novelty(args: &Args, operands: &[&str]) -> Output {
    check(args, "novelty")?;
    let limit = limit(args)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let (text, exclude) = match (operands, args.brief.statement.as_deref()) {
        ([text], None) if !text.trim().is_empty() => ((*text).to_owned(), None),
        ([], Some(token)) => {
            let sid = super::resolve(&aliases, token, Some(&["statements"]))?
                .ok_or_else(|| unknown(&format!("unknown statement: {token}")))?;
            let record = &corpus
                .get("statements", &sid)
                .expect("resolved statement")
                .fields;
            let mut lean = retrieval::LeanSource::new(&args.root);
            let declaration = record.get("lean_declaration").and_then(Value::as_str);
            let own = declaration
                .and_then(|d| d.rsplit('.').next())
                .unwrap_or_default();
            let text = match declaration.and_then(|d| lean.block(d)) {
                // The statement's Lean vocabulary and connectives, without
                // its own name: what it says, not what it is called.
                Some((_, _, block)) => {
                    let query = retrieval::Query::parse(&block);
                    query
                        .items
                        .iter()
                        .filter(|item| {
                            (item.kind == "identifier" && item.text != own)
                                || item.kind == "operator"
                        })
                        .map(|item| item.text.clone())
                        .collect::<Vec<_>>()
                        .join(" ")
                }
                None => String::new(),
            };
            let text = if text.split_whitespace().count() >= 2 {
                text
            } else {
                record
                    .get("paraphrase")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                    .to_owned()
            };
            (text, Some(sid))
        }
        _ => return Err(usage(HELP)),
    };
    let view = research::frontier_view(args, &corpus, &frontier_root)?;
    let revision = retrieval::Revision::of(&args.root);
    let issues = issues(args, &revision)?;
    let inputs = Inputs {
        root: &args.root,
        corpus: &corpus,
        aliases: &aliases,
        view: &view,
        issues: &issues,
        revision,
    };
    let root = std::fs::canonicalize(&args.root)
        .map_err(|failure| input_error(&args.root.display().to_string(), failure.to_string()))?;
    let (db, state) = retrieval::open_index(&root).map_err(error)?;
    let report = brief::novelty::novelty(&inputs, &db, state, &text, exclude.as_deref(), limit)
        .map_err(error)?;
    let text = brief::novelty::format_novelty(&report, &aliases, limit);
    Ok((with_identity(report, &corpus), Some(text)))
}
