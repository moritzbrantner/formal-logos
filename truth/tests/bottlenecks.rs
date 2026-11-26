//! `truth bottlenecks` end to end on the frozen `research` golden base
//! (`tests/golden/research/test_fixture.json`), rooted at its statement C:
//! the option parsing, the in-process frontier and the attempt authors that
//! the unit tests in `truth::bottlenecks` take as given.

use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

const BINARY: &str = env!("CARGO_BIN_EXE_truth");
const STATEMENT_A: &str = "a8459a54-228d-545e-9e81-bf462fcca7a6";
const ATTEMPT: &str = "corpus/attempts/00-ATTEMPT-ONE.json";

/// A fresh temporary directory, removed on drop.
struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// The golden base, with one `author` worker entry on its attempt about A.
fn fixture(name: &str) -> Scratch {
    let root =
        std::env::temp_dir().join(format!("truth-bottlenecks-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    let golden =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden/research/test_fixture.json");
    let golden: Value = serde_json::from_str(&fs::read_to_string(golden).expect("research golden"))
        .expect("golden JSON");
    for (relative, content) in golden["base"].as_object().expect("base files") {
        let text = match content {
            Value::String(text) => text.clone(),
            other => other.to_string(),
        };
        let path = root.join(relative);
        fs::create_dir_all(path.parent().expect("parent")).expect("directory");
        fs::write(path, text).expect("write fixture file");
    }
    let path = root.join(ATTEMPT);
    let mut attempt: Value =
        serde_json::from_str(&fs::read_to_string(&path).expect("attempt")).expect("JSON");
    assert_eq!(
        attempt["statement_ids"][0], STATEMENT_A,
        "the golden base changed"
    );
    attempt["workers"] = serde_json::json!([{"role": "author", "provider": "codex",
        "model": "sol", "date": "2026-11-26"}]);
    fs::write(&path, attempt.to_string()).expect("write attempt");
    Scratch(root)
}

fn run(root: &Path, args: &[&str]) -> Output {
    Command::new(BINARY)
        .arg("--root")
        .arg(root)
        .args(args)
        .output()
        .expect("run truth")
}

fn json(root: &Path, args: &[&str]) -> Value {
    let output = run(
        root,
        &[
            &["--json", "bottlenecks", "--frontier-root", "STMT-C"],
            args,
        ]
        .concat(),
    );
    assert!(
        output.status.success(),
        "truth bottlenecks {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("bottlenecks JSON")
}

fn listed(report: &Value) -> Vec<&str> {
    report["premises"]
        .as_array()
        .expect("premises")
        .iter()
        .map(|row| row["statement_id"].as_str().expect("statement id"))
        .collect()
}

#[test]
fn bottlenecks_lists_shared_open_premises_with_their_authors() {
    let scratch = fixture("list");
    let root = &scratch.0;
    // A is the one open premise reaching C; ARG-AB and ARG-AD consume it.
    let all = json(root, &[]);
    assert_eq!(listed(&all), [STATEMENT_A], "{all:#}");
    let a = &all["premises"][0];
    assert_eq!(a["consuming_arguments"], 2, "{all:#}");
    assert_eq!(a["authored_by"], serde_json::json!(["sol"]));
    assert!(all["input_identity"].is_string() || all["input_identity"].is_object());
    assert_eq!(
        listed(&json(root, &["--authored-only-by", "sol"])),
        [STATEMENT_A]
    );
    assert!(listed(&json(root, &["--authored-only-by", "astra"])).is_empty());
    assert!(listed(&json(root, &["--min-arguments", "3"])).is_empty());
    // The fixture has no stage conclusions.
    assert!(listed(&json(root, &["--stage", "1"])).is_empty());

    let text = run(root, &["bottlenecks", "--frontier-root", "STMT-C"]);
    let text = String::from_utf8(text.stdout).expect("UTF-8");
    assert!(text.contains("A [a8459a54]"), "{text}");
    assert!(text.contains("not philosophical merit"), "{text}");
}

#[test]
fn bottleneck_options_apply_only_where_documented() {
    let scratch = fixture("options");
    let root = &scratch.0;
    for (args, message) in [
        (&["bottlenecks", "--open"][..], "--open only to workers"),
        (
            &["workers", "--stage", "1"][..],
            "apply only to bottlenecks",
        ),
        (&["bottlenecks", "--limit", "0"][..], "positive integer"),
        (&["bottlenecks", "--stage", "x"][..], "positive integer"),
        (
            &["bottlenecks", "--min-routes", "-1"][..],
            "non-negative integer",
        ),
    ] {
        let output = run(root, args);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{args:?}: {stderr}");
        assert!(stderr.contains(message), "{args:?}: {stderr}");
    }
}
