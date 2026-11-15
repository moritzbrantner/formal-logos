//! `truth tree STATEMENT [--down N] [--up N] [--budget N]`: the argument
//! graph re-rooted at a statement, with its definitions (#1674). Statuses
//! come from the frontier computed with the statement as frontier root.
//!
//! `--materialize-edge KEY` writes, for one derived `contrapositive` edge of
//! the view, the batch spec, negation vocabulary and Solution that make it an
//! ordinary corpus argument (`truth::inversion`).

use super::{
    Args, Command, Output, input_error, load, resolve_statement, unknown, usage, with_identity,
};
use serde_json::json;
use truth::{frontier, inversion, thickness, tree};

pub const COMMAND: Command = Command { name: "tree", run };

fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 1, false, Default::default())?;
    let (corpus, aliases, _) = load(args)?;
    let root = resolve_statement(&aliases, operands[0])?;
    if corpus.get("statements", &root).is_none() {
        return Err(unknown(&format!("unknown statement: {}", operands[0])));
    }
    let options = tree::Options {
        down: args.tree.down.unwrap_or(tree::DEFAULT_DOWN),
        up: args.tree.up.unwrap_or(tree::DEFAULT_UP),
        budget: args.tree.budget.unwrap_or(tree::DEFAULT_BUDGET),
    };
    let report = frontier::current_frontier(&args.root, &corpus, &root, false, false);
    if report["root_known"] != true {
        return Err(input_error(
            "corpus",
            format!("unknown root statement: {root}"),
        ));
    }
    let view = tree::tree(&corpus, &report, &root, thickness::DEFAULT_ROOT, options)
        .map_err(|error| usage(format!("unknown statement: {}", error.0)))?;
    if let Some(key) = &args.tree.materialize_edge {
        return materialize(args, &corpus, &view, key);
    }
    let text = aliases.humanize(&tree::format_tree(&view));
    Ok((with_identity(&view, &corpus), Some(text)))
}

/// Write the files of one derived edge of the view (only `contrapositive`).
fn materialize(args: &Args, corpus: &truth::Corpus, view: &tree::Tree, key: &str) -> Output {
    let Some(edge) = view.edges.iter().find(|edge| {
        edge.inversion
            .as_ref()
            .is_some_and(|inversion| inversion.key == key)
    }) else {
        return Err(unknown(&format!(
            "no derived edge {key} in this view (keys are listed under the Inversions section and in --json)"
        )));
    };
    if edge.kind != "contrapositive" {
        return Err(usage(format!(
            "{key}: only contrapositive edges are materialized; an inverse_conditional edge rests on an unregistered exhaustiveness premise, which must be registered first"
        )));
    }
    let (Some(argument), Some(result)) = (&edge.argument_id, &edge.result_id) else {
        return Err(usage(format!("{key}: the edge has no argument or result")));
    };
    let plan = inversion::plan_contrapositive(&args.root, corpus, key, argument, &edge.to, result)
        .map_err(|message| input_error("lean", message))?;
    let written = inversion::write_plan(&args.root, &plan)
        .map_err(|message| input_error("materialize", message))?;
    let mut lines = vec![format!("Materialized {key} as {}:", plan.theorem)];
    lines.extend(
        written
            .iter()
            .map(|(path, status)| format!("  {status}: {path}")),
    );
    for (role, statement) in &plan.reused {
        lines.push(format!("  reused {role}: {statement}"));
    }
    lines.push("Next:".into());
    lines.extend(plan.commands.iter().map(|command| format!("  {command}")));
    let value = json!({
        "plan": plan,
        "written": written.iter().map(|(path, status)| json!({"path": path, "status": status})).collect::<Vec<_>>(),
    });
    Ok((with_identity(&value, corpus), Some(lines.join("\n"))))
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;

    fn run(args: &[&str]) -> super::Output {
        let args: Vec<OsString> = args.iter().map(OsString::from).collect();
        super::super::run(&args)
    }

    #[test]
    fn unknown_ids_and_foreign_options_fail() {
        let root = std::env::temp_dir().join(format!("truth-cli-tree-{}", std::process::id()));
        std::fs::create_dir_all(root.join("corpus").join("statements")).unwrap();
        let path = root.to_str().unwrap();
        let Err((code, error)) = run(&["--root", path, "tree", "STMT-NOPE"]) else {
            panic!("an unknown statement was accepted")
        };
        assert_eq!((code, error["code"].as_str()), (3, Some("unknown_id")));
        let Err((code, error)) = run(&["--root", path, "status", "--down", "2"]) else {
            panic!("--down was accepted by status")
        };
        assert_eq!(code, 2);
        assert!(
            error["message"]
                .as_str()
                .unwrap()
                .contains("apply only to tree")
        );
        let Err((code, _)) = run(&["--root", path, "tree", "X", "--up", "-1"]) else {
            panic!("a negative depth was accepted")
        };
        assert_eq!(code, 2);
        let Err((code, _)) = run(&["--root", path, "status", "--materialize-edge", "k"]) else {
            panic!("--materialize-edge was accepted by status")
        };
        assert_eq!(code, 2);
        std::fs::write(
            root.join("corpus").join("statements").join("X.json"),
            r#"{"id": "X", "paraphrase": "X holds."}"#,
        )
        .unwrap();
        let Err((code, error)) = run(&[
            "--root",
            path,
            "tree",
            "X",
            "--materialize-edge",
            "contrapositive:NOPE:X",
        ]) else {
            panic!("an unknown edge key was accepted")
        };
        assert_eq!((code, error["code"].as_str()), (3, Some("unknown_id")));
        std::fs::remove_dir_all(&root).unwrap();
    }
}
