//! Exhaustive explicit evidence; ranking and display limits never affect traversal.
use super::{
    Accepts, Args, Command, Failure, Output, input_error, load, read_json, unknown, usage,
};
use serde_json::{Value, json};
use truth::{Corpus, evidence_graph::EvidenceGraph};

pub const COMMAND: Command = Command {
    name: "evidence",
    run,
};

pub fn expansion(args: &Args, corpus: &Corpus, seeds: &[String]) -> Result<Value, Failure> {
    let snapshot = args
        .issues
        .issues_from
        .as_deref()
        .map(read_json)
        .transpose()?;
    let graph = EvidenceGraph::build(&args.root, corpus, snapshot.as_ref())
        .map_err(|message| input_error("evidence", message))?;
    if !args.full_evidence
        && args
            .positional
            .first()
            .is_none_or(|value| value != "evidence")
    {
        return Ok(graph.expand(seeds).navigation());
    }
    serde_json::to_value(graph.expand(seeds))
        .map_err(|error| input_error("evidence", error.to_string()))
}

pub fn summary(value: &Value, limit: usize) -> String {
    let nodes = value["nodes"].as_array().map(Vec::as_slice).unwrap_or(&[]);
    let edges = value["edges"].as_array().map_or(0, Vec::len);
    let mut text = format!(
        "Explicit evidence: {} nodes, {edges} links (bidirectional reference traversal; not entailment).\n",
        nodes.len()
    );
    for node in nodes.iter().take(limit) {
        text.push_str(&format!(
            "  {}: {}\n",
            node["key"].as_str().unwrap_or_default(),
            node["label"].as_str().unwrap_or_default()
        ));
    }
    if nodes.len() > limit {
        text.push_str(&format!(
            "  {} more nodes; --json includes every node, edge and explanation path.\n",
            nodes.len() - limit
        ));
    }
    let unresolved = value["unresolved"].as_array().map_or(0, Vec::len);
    if unresolved > 0 {
        text.push_str(&format!(
            "  {unresolved} unresolved references are retained in --json.\n"
        ));
    }
    text
}

fn run(args: &Args, operands: &[&str]) -> Output {
    args.check_options(Accepts {
        issues_from: true,
        ..Accepts::default()
    })?;
    if args.research.all
        || args.research.frontier.is_some()
        || args.research.related.is_some()
        || args.write
        || args.bridge_flags
        || args.configuration.flags
    {
        return Err(usage(
            "evidence takes TARGET, --issues-from FILE and --limit N",
        ));
    }
    let [target] = operands else {
        return Err(usage("evidence requires one TARGET"));
    };
    let limit = args.research.limit.unwrap_or(12);
    if limit < 1 {
        return Err(usage("--limit must be positive"));
    }
    let (corpus, _, _) = load(args)?;
    let mut value = expansion(args, &corpus, &[(*target).to_owned()])?;
    if value["seeds"].as_array().is_none_or(Vec::is_empty) {
        return Err(unknown(&format!("unknown evidence target: {target}")));
    }
    value["input_identity"] = json!(corpus.input_identity());
    let text = summary(&value, usize::try_from(limit).unwrap_or(usize::MAX));
    Ok((value, Some(text)))
}
