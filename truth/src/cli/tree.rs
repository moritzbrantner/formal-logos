//! `truth tree STATEMENT [--down N] [--up N] [--budget N]`: the argument
//! graph re-rooted at a statement, with its definitions (#1674). Statuses
//! come from the frontier computed with the statement as frontier root.

use super::{
    Args, Command, Output, input_error, load, resolve_statement, unknown, usage, with_identity,
};
use truth::{frontier, thickness, tree};

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
    let text = aliases.humanize(&tree::format_tree(&view));
    Ok((with_identity(&view, &corpus), Some(text)))
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
        std::fs::remove_dir_all(&root).unwrap();
    }
}
