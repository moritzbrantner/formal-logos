//! The shared transcription-closure fixture (rule (d)) of
//! `scripts/testdata/frontier-transcription-closure.json`, which the
//! Explorer's `proposition-graph.test.ts` also checks, so both
//! implementations agree. It replaces the retired Python
//! `test_corpus_frontier.py` case (#954 R3).

use serde_json::{Map, Value, json};
use std::{
    collections::BTreeMap,
    io::Write,
    path::PathBuf,
    process::{Command, Stdio},
};

const BINARY: &str = env!("CARGO_BIN_EXE_truth");

fn fixture() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../scripts/testdata/frontier-transcription-closure.json");
    serde_json::from_str(&std::fs::read_to_string(path).expect("shared fixture")).expect("JSON")
}

fn reversed(value: &Value, reverse: bool) -> Value {
    let mut items = value.as_array().cloned().unwrap_or_default();
    if reverse {
        items.reverse();
    }
    Value::Array(items)
}

fn frontier(input: &Value) -> Value {
    let mut child = Command::new(BINARY)
        .args([
            "--json",
            "frontier",
            "--fixture",
            "-",
            "--frontier-root",
            "TOP",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run truth");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(input.to_string().as_bytes())
        .expect("write fixture");
    let output = child.wait_with_output().expect("truth output");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("frontier JSON")
}

#[test]
fn shared_transcription_closure_fixture_in_either_order() {
    let fixture = fixture();
    let results = fixture["results"].as_array().expect("results");
    let flags: Vec<Value> = fixture["transcription_result_ids"]
        .as_array()
        .expect("transcription_result_ids")
        .iter()
        .map(|id| {
            let argument = results
                .iter()
                .find(|result| result["id"] == *id)
                .map(|result| result["argument_id"].clone())
                .expect("transcription result");
            json!({"result_id": id, "argument_id": argument, "proof_steps": 1,
                   "single_application_of": "hBridge", "goal_consequent_premises": []})
        })
        .collect();
    for reverse in [false, true] {
        let mut input = Map::new();
        for key in ["statements", "arguments", "results", "relations", "claims"] {
            input.insert(key.into(), reversed(&fixture[key], reverse));
        }
        input.insert(
            "transcription_flags".into(),
            reversed(&Value::Array(flags.clone()), reverse),
        );
        let report = frontier(&Value::Object(input));
        let items = report["items"].as_array().expect("items");
        let mut ids: Vec<&str> = items
            .iter()
            .map(|item| item["statement_id"].as_str().unwrap())
            .collect();
        ids.sort();
        assert_eq!(
            json!(ids),
            fixture["expected_frontier"],
            "reverse={reverse}"
        );
        let depths: BTreeMap<&str, &Value> = items
            .iter()
            .map(|item| (item["statement_id"].as_str().unwrap(), &item["depth"]))
            .collect();
        assert_eq!(
            json!(depths),
            fixture["expected_depth"],
            "reverse={reverse}"
        );
        let via: BTreeMap<&str, &Value> = report["closed_via_transcription"]
            .as_array()
            .expect("closed_via_transcription")
            .iter()
            .map(|item| (item["statement_id"].as_str().unwrap(), &item["result_id"]))
            .collect();
        assert_eq!(
            json!(via),
            fixture["expected_closed_via_transcription"],
            "reverse={reverse}"
        );
    }
}

/// A `tests` relation (a control, model or countermodel naming what it
/// tests) carries no warrant: adding such relations to the shared fixture
/// leaves `truth --json frontier` unchanged apart from the input fingerprint.
#[test]
fn tests_relations_leave_frontier_json_unchanged() {
    let fixture = fixture();
    let mut input = Map::new();
    for key in ["statements", "arguments", "results", "relations", "claims"] {
        input.insert(key.into(), fixture[key].clone());
    }
    let mut plain = frontier(&Value::Object(input.clone()));
    let relations = input["relations"].as_array().cloned().unwrap_or_default();
    let tests = [
        ("argument", "ARG-REF", "statement", "OPEN"),
        ("argument", "ARG-PROVED", "statement", "TOP"),
        ("argument", "ARG-T1", "argument", "ARG-T2"),
        ("argument", "ARG-REF2", "statement", "DEF2"),
    ]
    .into_iter()
    .enumerate()
    .map(|(index, (subject_kind, subject, object_kind, object))| {
        json!({"id": format!("REL-TESTS-{index}"), "subject_kind": subject_kind,
               "subject_id": subject, "predicate": "tests", "object_kind": object_kind,
               "object_id": object, "note": "a control of this node"})
    });
    input.insert(
        "relations".into(),
        Value::Array(relations.into_iter().chain(tests).collect()),
    );
    let mut tested = frontier(&Value::Object(input));
    for report in [&mut plain, &mut tested] {
        report
            .as_object_mut()
            .expect("report")
            .remove("input_identity");
    }
    assert_eq!(tested, plain);
}
