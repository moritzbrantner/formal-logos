//! "Head rules on base data" (owner decision for #954 R3, 2026-11-16):
//! `frontier-diff`, `thickness --base` and `orphans --base` read the base
//! revision's committed corpus and Lean sources from a `git archive` extract
//! and judge them with this binary's own rules. The base revision's own
//! tooling is never run: here its `scripts/corpus.py` fails if anything
//! executes it, and the base's data still yields a delta.

use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

const BINARY: &str = env!("CARGO_BIN_EXE_truth");
const ROOT: &str = "11111111-1111-4111-8111-111111111111";
const A: &str = "22222222-2222-4222-8222-222222222222";
const ARGUMENT: &str = "33333333-3333-4333-8333-333333333333";

/// A fresh temporary directory, removed on drop.
struct TempDir(PathBuf);

impl TempDir {
    fn new(name: &str) -> Self {
        let path =
            std::env::temp_dir().join(format!("truth-base-revision-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        TempDir(path)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn write(root: &Path, path: &str, text: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn git(root: &Path, args: &[&str]) {
    let status = Command::new("git")
        .args(["-c", "user.name=t", "-c", "user.email=t@example.invalid"])
        .args(["-c", "commit.gpgsign=false"])
        .args(args)
        .current_dir(root)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .status()
        .unwrap();
    assert!(status.success(), "git {args:?}");
}

/// BASE: ROOT and A, and a `scripts/corpus.py` that fails when run. HEAD
/// (committed as `HEAD`, and the working tree): a verified argument ROOT <- A.
fn fixture(directory: &Path) {
    git(directory, &["init", "-q"]);
    write(
        directory,
        "corpus/statements/root.json",
        &format!(r#"{{"id": "{ROOT}", "label": "ROOT", "paraphrase": "ROOT"}}"#),
    );
    write(
        directory,
        "corpus/statements/a.json",
        &format!(r#"{{"id": "{A}", "label": "A", "paraphrase": "A"}}"#),
    );
    write(
        directory,
        "scripts/corpus.py",
        "import sys\nsys.exit('the base revision tooling must not run')\n",
    );
    git(directory, &["add", "-A"]);
    git(directory, &["commit", "-qm", "base"]);
    git(directory, &["tag", "BASE"]);
    write(
        directory,
        "corpus/arguments/arg.json",
        &format!(
            r#"{{"id": "{ARGUMENT}", "label": "ROOT, from A", "premise_statement_ids": ["{A}"],
                "conclusion_statement_id": "{ROOT}", "inference_ids": ["INF"], "meaning": "m"}}"#
        ),
    );
    write(
        directory,
        "corpus/results/res.json",
        &format!(
            r#"{{"id": "44444444-4444-4444-8444-444444444444", "label": "ROOT, from A",
                "argument_id": "{ARGUMENT}", "status": "verified", "theorem": "X.t",
                "challenge_module": "X.Challenge", "solution_module": "X.Solution",
                "comparator_config": "c.json"}}"#
        ),
    );
    git(directory, &["add", "-A"]);
    git(directory, &["commit", "-qm", "head"]);
}

fn truth(root: &Path, args: &[&str]) -> Value {
    let output = Command::new(BINARY)
        .args(["--json", "--root"])
        .arg(root)
        .args(["--frontier-root", "ROOT"])
        .args(args)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "truth {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn base_revisions_are_judged_by_the_head_rules() {
    let directory = TempDir::new("rules");
    let root = directory.0.as_path();
    fixture(root);

    for head in [None, Some("HEAD")] {
        let mut args = vec!["frontier-diff", "--base", "BASE"];
        args.extend(head.iter().flat_map(|head| ["--head", *head]));
        let delta = truth(root, &args);
        assert_eq!(delta["engines"]["base"], "rust");
        assert_eq!(delta["engines"]["head"], "rust");
        assert_eq!(delta["base_counts"]["open"], 0);
        assert_eq!(delta["head_counts"]["open"], 1);
        assert_eq!(delta["bare_added"], serde_json::json!([A]));
        assert_eq!(delta["head_cheapest_route"]["argument_id"], ARGUMENT);
    }

    let thickness = truth(root, &["thickness", "--base", "BASE"]);
    assert_eq!(thickness["engines"]["base"], "rust");
    assert_eq!(
        thickness["delta"]["summary"]["derivation_count"],
        serde_json::json!([0, 1])
    );

    let orphans = truth(root, &["orphans", "--base", "BASE"]);
    assert_eq!(orphans["engines"]["base"], "rust");
    assert_eq!(orphans["base_count"], 0);
    assert!(orphans["base_error"].is_null());
}

/// The connectivity gate reads the base from Git like the other `--base`
/// commands: HEAD joins A to ROOT, so nothing new is disconnected; a new
/// unconnected statement in the working tree fails it (exit 1, listed as
/// `label [uuid8]`) until it records a connection plan.
#[test]
fn the_connectivity_gate_fails_on_new_disconnection_only() {
    let directory = TempDir::new("connectivity");
    let root = directory.0.as_path();
    fixture(root);
    let gate = truth(root, &["connectivity", "--base", "BASE"]);
    assert_eq!(gate["passed"], true);
    assert_eq!(gate["new_statements"], 0);

    const NEW: &str = "55555555-5555-4555-8555-555555555555";
    write(
        root,
        "corpus/statements/new.json",
        &format!(r#"{{"id": "{NEW}", "label": "NEW", "paraphrase": "NEW"}}"#),
    );
    // An attempt naming NEW together with the connected A is not typed
    // contact: the gate still fails.
    write(
        root,
        "corpus/attempts/attempt.json",
        &format!(
            r#"{{"id": "66666666-6666-4666-8666-666666666666", "statement_ids": ["{A}", "{NEW}"]}}"#
        ),
    );
    let output = Command::new(BINARY)
        .args(["--root"])
        .arg(root)
        .args(["--frontier-root", "ROOT", "connectivity", "--base", "BASE"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(
        text.contains(
            "NEW [55555555]: new statement outside the root component; no connection plan"
        ),
        "{text}"
    );

    // A plan with only a target (no bridge, no blocker) is not a valid plan,
    // although its target is in the root component: the gate still fails.
    write(
        root,
        "corpus/statements/new.json",
        &format!(
            r#"{{"id": "{NEW}", "label": "NEW", "paraphrase": "NEW",
                "connection_plan": {{"target_statement_id": "{A}"}}}}"#
        ),
    );
    let output = Command::new(BINARY)
        .args(["--root"])
        .arg(root)
        .args(["--frontier-root", "ROOT", "connectivity", "--base", "BASE"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(
        text.contains(
            "NEW [55555555]: new statement outside the root component; invalid connection plan: \
             connection_plan.missing_bridge must be a non-empty string"
        ),
        "{text}"
    );

    write(
        root,
        "corpus/statements/new.json",
        &format!(
            r#"{{"id": "{NEW}", "label": "NEW", "paraphrase": "NEW", "connection_plan": {{
                "target_statement_id": "{A}", "missing_bridge": "NEW implies A.",
                "blocker": "No shared vocabulary yet."}}}}"#
        ),
    );
    let gate = truth(root, &["connectivity", "--base", "BASE"]);
    assert_eq!(gate["passed"], true);
    assert_eq!(gate["judged"][0]["status"], "planned");
}

#[test]
fn an_unreadable_base_revision_is_a_revision_error() {
    let directory = TempDir::new("error");
    let root = directory.0.as_path();
    fixture(root);
    for command in ["frontier-diff", "connectivity"] {
        let output = Command::new(BINARY)
            .args(["--json", "--root"])
            .arg(root)
            .args([command, "--base", "NO-SUCH-REVISION"])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{command}");
        let error: Value = serde_json::from_slice(&output.stderr).unwrap();
        assert_eq!(error["error"]["code"], "revision_error", "{command}");
    }
}

/// The placement gate (`orphans --base REV --gate`) reads the base from Git:
/// HEAD's result reaches ROOT, so nothing is judged unplaced; a new verified
/// result in the working tree whose conclusion reaches nothing fails it
/// (exit 1, in text and in `--json`) until its conclusion records a
/// connection plan to a root-path statement.
#[test]
fn the_placement_gate_fails_on_new_unplaced_results() {
    let directory = TempDir::new("placement");
    let root = directory.0.as_path();
    fixture(root);
    let gate = truth(root, &["orphans", "--base", "BASE", "--gate"]);
    assert_eq!(gate["passed"], true);
    assert_eq!(gate["judged_state_counts"]["reaching"], 1);
    assert_eq!(gate["backlog_count"], 0);

    const NEW: &str = "55555555-5555-4555-8555-555555555555";
    const NEW_ARGUMENT: &str = "77777777-7777-4777-8777-777777777777";
    write(
        root,
        "corpus/statements/new.json",
        &format!(r#"{{"id": "{NEW}", "label": "NEW", "paraphrase": "NEW"}}"#),
    );
    write(
        root,
        "corpus/arguments/new.json",
        &format!(
            r#"{{"id": "{NEW_ARGUMENT}", "label": "NEW, from A", "premise_statement_ids": ["{A}"],
                "conclusion_statement_id": "{NEW}", "inference_ids": ["INF"], "meaning": "m"}}"#
        ),
    );
    write(
        root,
        "corpus/results/new.json",
        &format!(
            r#"{{"id": "88888888-8888-4888-8888-888888888888", "label": "NEW, from A",
                "argument_id": "{NEW_ARGUMENT}", "status": "verified", "theorem": "Y.t",
                "challenge_module": "Y.Challenge", "solution_module": "Y.Solution",
                "comparator_config": "c.json"}}"#
        ),
    );
    let run = |json: bool| {
        let mut command = Command::new(BINARY);
        if json {
            command.arg("--json");
        }
        command
            .arg("--root")
            .arg(root)
            .args([
                "--frontier-root",
                "ROOT",
                "orphans",
                "--base",
                "BASE",
                "--gate",
            ])
            .output()
            .unwrap()
    };
    let output = run(false);
    assert_eq!(output.status.code(), Some(1));
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(text.contains(": FAILED"), "{text}");
    assert!(
        text.contains("  NEW [55555555] (result NEW, from A [88888888]; new result)"),
        "{text}"
    );
    assert!(text.contains("Contrived edges and tautological bridges are not acceptable"));
    let output = run(true);
    assert_eq!(output.status.code(), Some(1));
    let error: Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(error["error"]["code"], "placement_gate");
    assert_eq!(error["error"]["passed"], false);
    assert_eq!(
        error["error"]["offending"][0]["conclusion_statement_id"],
        NEW
    );
    assert_eq!(error["error"]["offending"][0]["change"], "new");

    write(
        root,
        "corpus/statements/new.json",
        &format!(
            r#"{{"id": "{NEW}", "label": "NEW", "paraphrase": "NEW", "connection_plan": {{
                "target_statement_id": "{A}", "missing_bridge": "NEW implies A.",
                "blocker": "No shared vocabulary yet."}}}}"#
        ),
    );
    let gate = truth(root, &["orphans", "--base", "BASE", "--gate"]);
    assert_eq!(gate["passed"], true);
    assert_eq!(gate["judged_state_counts"]["planned"], 1);

    let output = run_args(root, &["orphans", "--base", "NO-SUCH-REVISION", "--gate"]);
    assert_eq!(output.status.code(), Some(1));
    let error: Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(error["error"]["code"], "revision_error");

    for (args, message) in [
        (&["orphans", "--gate"][..], "--gate requires --base REV"),
        (
            &["orphans", "--base", "BASE", "--all"][..],
            "--base and --by/--senses/--all are alternatives",
        ),
        (
            &["connectivity", "--base", "BASE", "--gate"][..],
            "--gate applies only to orphans --base",
        ),
    ] {
        let output = run_args(root, args);
        assert_eq!(output.status.code(), Some(2), "{args:?}");
        let error: Value = serde_json::from_slice(&output.stderr).unwrap();
        assert_eq!(error["error"]["code"], "usage", "{args:?}");
        assert_eq!(error["error"]["message"], message, "{args:?}");
    }
}

/// `truth --json --root ROOT ARGS...`, whatever its exit code.
fn run_args(root: &Path, args: &[&str]) -> std::process::Output {
    Command::new(BINARY)
        .args(["--json", "--root"])
        .arg(root)
        .args(args)
        .output()
        .unwrap()
}
