//! End-to-end smoke test of the worker retrieval path (#954 I1): one
//! fixture query goes through `index search` → `brief` → `novelty` →
//! `dossier` → `context`, each step consuming the identifiers the previous
//! one returned, as `AGENTS.md` ("Premise dossiers and attempts") and the
//! `proposition-reuse` skill direct. Offline and deterministic: the
//! fixture checkout is the frozen `research` golden base (no Git, no Lean
//! build, no issue snapshot) plus one statement paraphrase and one research
//! note written here.

use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

const BINARY: &str = env!("CARGO_BIN_EXE_truth");
const STATEMENT_B: &str = "3be459bf-458d-516d-84b8-483b47465286";
const ARGUMENT_BC: &str = "79139f8b-4871-5213-9292-b73e0ee11a7d";
const PARAPHRASE: &str = "Every mover moves only insofar as it is in act.";
const NOTE: &str = "docs/notes/mover-act.md";

/// A fresh temporary directory, removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let path =
            std::env::temp_dir().join(format!("truth-retrieval-smoke-{}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("scratch directory");
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn write(root: &Path, relative: &str, text: &str) {
    let path = root.join(relative);
    fs::create_dir_all(path.parent().expect("parent")).expect("directory");
    fs::write(path, text).expect("write fixture file");
}

fn fixture(root: &Path) {
    let golden =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden/research/test_fixture.json");
    let golden: Value = serde_json::from_str(&fs::read_to_string(golden).expect("research golden"))
        .expect("golden JSON");
    for (relative, content) in golden["base"].as_object().expect("base files") {
        let text = match content {
            Value::String(text) => text.clone(),
            other => other.to_string(),
        };
        write(root, relative, &text);
    }
    let path = "corpus/statements/01-STMT-B.json";
    let mut statement: Value =
        serde_json::from_str(&fs::read_to_string(root.join(path)).expect("STMT-B")).expect("JSON");
    assert_eq!(statement["id"], STATEMENT_B, "the golden base changed");
    statement["paraphrase"] = Value::String(PARAPHRASE.into());
    write(
        root,
        path,
        &serde_json::to_string_pretty(&statement).expect("JSON"),
    );
    write(
        root,
        NOTE,
        "# Mover and act\n\n## Open question\n\nWhether a mover in act must itself be unmoved is \
         open; `STMT-B` states the narrower claim.\n",
    );
}

fn truth(root: &Path, args: &[&str]) -> Value {
    let output = Command::new(BINARY)
        .arg("--root")
        .arg(root)
        .arg("--json")
        .args(args)
        .output()
        .expect("run truth");
    assert!(
        output.status.success(),
        "truth {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| panic!("truth {args:?}: {error}"))
}

fn ids(values: &Value, field: &str) -> Vec<String> {
    values
        .as_array()
        .map(|items| {
            items
                .iter()
                .filter_map(|item| item[field].as_str().map(str::to_owned))
                .collect()
        })
        .unwrap_or_default()
}

#[test]
fn index_brief_novelty_dossier_context() {
    let scratch = Scratch::new();
    let root = scratch.0.as_path();
    fixture(root);

    // 1. Discovery without a seed: the statement first, then the note
    //    section that names it (#952).
    let hits = truth(root, &["index", "search", "mover act"]);
    let hits = hits.as_array().expect("search hits");
    let statement = hits
        .iter()
        .find(|hit| hit["kind"] == "statements")
        .and_then(|hit| hit["id"].as_str())
        .expect("a statement hit")
        .to_owned();
    assert_eq!(statement, STATEMENT_B);
    let note = hits
        .iter()
        .find(|hit| {
            hit["kind"] == "note"
                && hit["path"] == NOTE
                && !hit["links"].as_array().unwrap().is_empty()
        })
        .expect("a linked note hit");
    assert_eq!(note["links"][0], format!("statements:{STATEMENT_B}"));
    assert!(root.join(".cache/truth-index.sqlite").is_file());

    // 2. Brief on the discovered statement: frontier status, the arguments
    //    using it and the note mentioning it, with the evidence boundary.
    let brief = truth(root, &["brief", &statement, "--frontier-root", "STMT-C"]);
    assert_eq!(brief["mode"], "statement");
    assert_eq!(brief["statement"]["id"], STATEMENT_B);
    assert_eq!(brief["formal_status"]["closure"], "proved");
    assert_eq!(brief["formal_status"]["established"], false);
    let premise_of = ids(&brief["arguments"]["premise_of"], "id");
    assert!(
        premise_of.contains(&ARGUMENT_BC.to_owned()),
        "{premise_of:?}"
    );
    assert_eq!(brief["notes"]["sections"][0]["path"], NOTE);
    assert!(
        brief["boundary"]
            .as_str()
            .unwrap()
            .contains("not evidence that no prior work exists")
    );
    assert_eq!(brief["issues"]["source"]["availability"], "missing");

    // Compact navigation retains every node and valid explanation paths;
    // requesting raw evidence changes presentation, never discovery.
    let compact = &brief["evidence_graph"]["expansion"];
    let full = truth(
        root,
        &[
            "brief",
            &statement,
            "--full-evidence",
            "--frontier-root",
            "STMT-C",
        ],
    );
    let full = &full["evidence_graph"]["expansion"];
    assert_eq!(ids(&compact["nodes"], "key"), ids(&full["nodes"], "key"));
    assert!(compact["nodes"][0].get("content").is_none());
    assert!(full["nodes"][0].get("content").is_some());
    let edges = compact["edges"].as_array().unwrap();
    let predecessors = compact["predecessors"].as_object().unwrap();
    for node in compact["nodes"].as_array().unwrap() {
        let mut key = node["key"].as_str().unwrap();
        let mut steps = 0;
        while let Some(step) = predecessors.get(key) {
            let edge = &edges[step["edge"].as_u64().unwrap() as usize];
            assert!(edge["from"] == key || edge["to"] == key);
            key = step["predecessor"].as_str().unwrap();
            steps += 1;
            assert!(steps <= predecessors.len(), "explanation must be acyclic");
        }
        assert!(
            compact["seeds"]
                .as_array()
                .unwrap()
                .iter()
                .any(|seed| seed == key)
        );
    }

    // 3. Novelty of the claim's own words: already recorded, by that
    //    statement; without a snapshot, issue history is reported unknown.
    let novelty = truth(root, &["novelty", PARAPHRASE, "--frontier-root", "STMT-C"]);
    assert_eq!(novelty["classification"], "already-recorded");
    assert_eq!(novelty["hits"][0]["id"], STATEMENT_B);
    assert!(novelty["hit_counts"]["notes"].as_u64().unwrap() >= 1);
    assert!(
        novelty["caveats"][0]
            .as_str()
            .unwrap()
            .contains("issue and PR history is unknown")
    );

    // 4. Dossier of the same statement: the argument the brief named, and
    //    the note mention.
    let dossier = truth(root, &["dossier", &statement, "--frontier-root", "STMT-C"]);
    assert_eq!(dossier["statement"]["id"], STATEMENT_B);
    let arguments: Vec<String> = dossier["argument_ids"]
        .as_array()
        .expect("argument_ids")
        .iter()
        .filter_map(|id| id.as_str().map(str::to_owned))
        .collect();
    assert!(arguments.contains(&ARGUMENT_BC.to_owned()), "{arguments:?}");
    assert_eq!(dossier["note_mentions"][0]["path"], NOTE);

    // 5. Context of that argument: its frozen Lean theorem and the premise
    //    the search started from.
    let context = truth(root, &["context", ARGUMENT_BC, "--frontier-root", "STMT-C"]);
    assert_eq!(context["argument_id"], ARGUMENT_BC);
    assert_eq!(ids(&context["premises"], "statement_id"), [STATEMENT_B]);
    assert_eq!(context["lean"][0]["theorem"], "TruthCore.Fix.fixBC");
    assert_eq!(context["lean"][0]["status"], "verified");
}
