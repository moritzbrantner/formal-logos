//! Statement synthesis and discovery of scoped judgments for a question.
use super::{Args, Command, Output, input_error, load, resolve_statement, unknown, usage};
use serde_json::{Value, json};
use truth::{brief::assessment_search, support_graph, synthesis};

pub const COMMAND: Command = Command {
    name: "synthesis",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    args.check_options(Default::default())?;
    let question = args.brief.question.as_deref();
    if args.write
        || args.bridge_flags
        || args.research.related.is_some()
        || args.research.frontier.is_some()
        || args.research.all
        || args.brief.assessments_for.is_some()
        || args.brief.statement.is_some()
        || operands.len() > 1
        || question.is_some() && !operands.is_empty()
    {
        return Err(usage(
            "synthesis takes one statement or --question TEXT, optionally with --limit N",
        ));
    }
    if question.is_some_and(|q| q.trim().is_empty()) {
        return Err(usage("--question requires nonempty text"));
    }
    if args.research.limit.is_some_and(|limit| limit < 1) {
        return Err(usage("--limit must be positive"));
    }
    let (corpus, aliases, _) = load(args)?;
    if let Some(question) = question {
        let limit = args.research.limit.unwrap_or(5);
        let (value, text) =
            assessment_search::report_for_root(&args.root, &corpus, question, limit as usize)
                .map_err(|error| input_error("synthesis", error))?;
        return Ok((value, Some(text)));
    }
    let token = operands
        .first()
        .copied()
        .unwrap_or(support_graph::DEFAULT_TARGETS[0]);
    let target = resolve_statement(&aliases, token)?;
    let target = if let Some(record) = corpus.get("statements", &target) {
        record
    } else {
        let declarations: Vec<_> = corpus
            .records_by_id("statements")
            .filter_map(|(id, record)| {
                let decl = record.fields.get("lean_declaration")?.as_str()?;
                (decl == token || decl.rsplit('.').next() == Some(token))
                    .then_some((id, decl, record))
            })
            .collect();
        match declarations.as_slice() {
            [(_, _, record)] => *record,
            [] => return Err(unknown(&format!("unknown statement: {token}"))),
            several => {
                let candidates: Vec<Value> = several.iter().map(|(id, declaration, record)|
                    json!({"id":id,"lean_declaration":declaration,"paraphrase":record.fields["paraphrase"]})).collect();
                let choices = several
                    .iter()
                    .map(|(id, declaration, _)| format!("{declaration} — truth synthesis {id}"))
                    .collect::<Vec<_>>()
                    .join("\n");
                return Err((
                    3,
                    json!({"code":"unknown_id", "id":token, "candidates":candidates,
                    "message":format!("{token:?} matches several statement declarations. Choose a meaning:\n{choices}")}),
                ));
            }
        }
    };
    let report = synthesis::build(&args.root, &corpus, target)
        .map_err(|error| input_error("synthesis", error))?;
    let text = match args.research.limit {
        Some(limit) => report.reading(limit as usize).join("\n\n"),
        None => report.summary.join("\n\n"),
    };
    let json = serde_json::to_value(report).map_err(|e| input_error("synthesis", e.to_string()))?;
    Ok((json, Some(text)))
}
