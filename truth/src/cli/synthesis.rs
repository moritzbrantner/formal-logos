//! Statement synthesis and discovery of scoped judgments for a question.
use super::{
    Args, Command, Output, input_error, load, resolve_in, resolve_statement, unknown, usage,
};
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
            "synthesis takes one statement, argument, result or --question TEXT, optionally with --limit N",
        ));
    }
    if question.is_some_and(|q| q.trim().is_empty()) {
        return Err(usage("--question requires nonempty text"));
    }
    if args.research.limit.is_some_and(|limit| limit < 1) {
        return Err(usage("--limit must be positive"));
    }
    let (corpus, aliases, _) = load(args)?;
    let comparing = !args.without.is_empty() || args.compare_premises;
    if args.compare_premises && !args.without.is_empty() {
        return Err(usage(
            "choose --without for one scenario or --compare-premises for individual omissions",
        ));
    }
    if let Some(question) = question {
        if comparing {
            return Err(usage(
                "withholding premises requires an argument or its result",
            ));
        }
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
    let target = resolve_in(&aliases, token, &["statements", "arguments", "results"])?;
    let result = corpus.get("results", &target);
    let argument = if let Some(record) = result {
        let argument_id = record.fields["argument_id"].as_str().unwrap_or_default();
        Some(
            corpus
                .get("arguments", argument_id)
                .ok_or_else(|| unknown(&format!("result {target} has no known argument")))?,
        )
    } else {
        corpus.get("arguments", &target)
    };
    if let Some(argument) = argument {
        let without = args
            .without
            .iter()
            .map(|s| resolve_statement(&aliases, s))
            .collect::<Result<Vec<_>, _>>()?;
        let (value, text) = synthesis::argument::report(
            &args.root,
            &corpus,
            argument,
            result.map(|_| target.as_str()),
            &without,
            args.compare_premises,
            args.research.limit.unwrap_or(5) as usize,
        )
        .map_err(|error| input_error("synthesis", error))?;
        return Ok((value, Some(text)));
    }
    if comparing {
        return Err(usage(
            "withholding premises requires an argument or its result",
        ));
    }
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
            [] => {
                return Err(unknown(&format!(
                    "unknown statement, argument or result: {token}"
                )));
            }
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
