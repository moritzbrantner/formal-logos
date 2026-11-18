//! `truth support-graph [STATEMENT ...]`: a complete registered-rule export.

use super::{Args, Command, Output, input_error, load, resolve_statement, unknown};
use serde_json::{Value, json};
use std::{path::Path, process::Command as ProcessCommand, time::Duration};
use truth::{subprocess, support_graph};

pub const COMMAND: Command = Command {
    name: "support-graph",
    run,
};

fn git_output(root: &Path, arguments: &[&str]) -> Option<String> {
    let mut command = ProcessCommand::new("git");
    command.args(arguments).current_dir(root);
    let output = subprocess::run_bounded(command, Duration::from_secs(10)).ok()??;
    if !output.success {
        return None;
    }
    Some(output.stdout.trim().to_owned())
}

fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, operands.len(), false, Default::default())?;
    let (corpus, aliases, _) = load(args)?;
    let operands = if operands.is_empty() {
        &support_graph::DEFAULT_TARGETS[..]
    } else {
        operands
    };
    let targets = operands
        .iter()
        .map(|token| resolve_statement(&aliases, token))
        .collect::<Result<Vec<_>, _>>()?;
    let graph = support_graph::build(&corpus, &targets).map_err(|error| match &error {
        support_graph::Error::UnknownTarget(_) => unknown(&error.to_string()),
        _ => input_error("support-graph", error.to_string()),
    })?;
    let mut lines = vec![format!(
        "Support graph: {} statements, {} result-backed argument rules, {} terminal inputs.",
        graph.statement_count, graph.rule_count, graph.terminal_statement_count
    )];
    for target in &graph.target_statement_ids {
        let direct = &graph.direct[target];
        lines.push(format!(
            "{}: {} immediate rules, {} conjunctions after literal absorption.",
            aliases.show(target),
            direct.rule_count,
            direct.minimal_conjunction_count
        ));
    }
    lines.push(support_graph::SCOPE.into());
    lines.push("--json exports the complete rule graph; no support combinations are enumerated by this command.".into());
    let mut value = serde_json::to_value(&graph)
        .map_err(|error| input_error("support-graph", error.to_string()))?;
    value["source_head"] =
        git_output(&args.root, &["rev-parse", "HEAD"]).map_or(Value::Null, Value::String);
    value["worktree_dirty"] = git_output(
        &args.root,
        &["status", "--porcelain", "--untracked-files=normal"],
    )
    .map_or(Value::Null, |status| json!(!status.is_empty()));
    Ok((value, Some(lines.join("\n"))))
}

#[cfg(test)]
mod tests {
    use std::{
        ffi::OsString,
        sync::atomic::{AtomicUsize, Ordering},
    };

    static NEXT: AtomicUsize = AtomicUsize::new(0);

    #[test]
    fn aliases_default_targets_unknown_ids_and_foreign_options() {
        let root = std::env::temp_dir().join(format!(
            "truth-support-graph-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(root.join("corpus/statements")).expect("fixture directory");
        for (id, alias) in truth::support_graph::DEFAULT_TARGETS
            .iter()
            .zip(["STMT-GOD-EXISTS", "STMT-NECESSARY-CLASSICAL-GOD-ROOT"])
        {
            std::fs::write(
                root.join(format!("corpus/statements/{id}.json")),
                serde_json::json!({"id":id,"legacy_id":alias,"paraphrase":alias}).to_string(),
            )
            .expect("fixture statement");
        }
        let run = |arguments: &[&str]| {
            let mut args = vec![OsString::from("--root"), root.clone().into_os_string()];
            args.extend(arguments.iter().map(OsString::from));
            super::super::run(&args)
        };
        let (both, _) = run(&["support-graph"]).expect("default graph");
        assert_eq!(
            both["target_statement_ids"]
                .as_array()
                .expect("targets")
                .len(),
            2
        );
        let (one, _) = run(&["support-graph", "STMT-GOD-EXISTS"]).expect("alias target");
        assert_eq!(
            one["target_statement_ids"],
            serde_json::json!([truth::support_graph::DEFAULT_TARGETS[0]])
        );
        assert_eq!(one["rule_count"], 0);
        assert_eq!(one["terminal_statement_count"], 1);
        let (code, _) = run(&["support-graph", "UNKNOWN"]).expect_err("unknown target");
        assert_eq!(code, 3);
        let (code, _) = run(&["support-graph", "--routes"]).expect_err("foreign option");
        assert_eq!(code, 2);
        std::fs::remove_dir_all(root).expect("cleanup");
    }
}
