//! Exact-bundle CLI routing through the existing search, filtering and
//! certification pipeline. The subprocess fixture supplies synthetic Lean
//! responses: these tests check the protocol, not proof validity.

use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

const BINARY: &str = env!("CARGO_BIN_EXE_truth");
const TARGET: &str = "11111111-1111-4111-8111-111111111111";
const BRIDGE: &str = "22222222-2222-4222-8222-222222222222";
const UNBOUND: &str = "33333333-3333-4333-8333-333333333333";

struct Fixture(PathBuf);

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn write(root: &Path, path: &str, value: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, value).unwrap();
}

fn premise(index: usize) -> String {
    format!("aaaaaaaa-aaaa-4aaa-8aaa-{index:012}")
}

fn fixture(name: &str) -> Fixture {
    let root = std::env::temp_dir().join(format!("truth-discover-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    write(
        &root,
        "corpus/statements/target.json",
        &json!({"id": TARGET, "label": "Target", "paraphrase": "target",
            "lean_declaration": "TruthCore.Target.Goal"})
        .to_string(),
    );
    for i in 0..10 {
        write(
            &root,
            &format!("corpus/statements/p{i}.json"),
            &json!({"id": premise(i), "label": format!("Premise {i}"), "paraphrase": "premise",
                "legacy_id": format!("STMT-P{i}"),
                "lean_declaration": format!("TruthCore.Premises.P{i}")})
            .to_string(),
        );
    }
    write(
        &root,
        "corpus/statements/bridge.json",
        &json!({"id": BRIDGE, "label": "Bridge", "paraphrase": "bridge",
            "lean_declaration": "TruthCore.Bridges.Link"})
        .to_string(),
    );
    write(
        &root,
        "corpus/statements/unbound.json",
        &json!({"id": UNBOUND, "label": "Unbound", "paraphrase": "unbound"}).to_string(),
    );
    write(
        &root,
        "corpus/disambiguations/term.json",
        &json!({"id": "term", "term": "term", "resolution": "distinct senses", "term_label": "TERM", "senses": [
            {"id": "first", "label": "TERM_1", "definition_id": "d1", "lean_parameters": [
                {"declaration": "TruthCore.Target.Goal", "parameter": "x"}]},
            {"id": "second", "label": "TERM_2", "definition_id": "d2", "lean_parameters": [
                {"declaration": "TruthCore.Premises.P0", "parameter": "x"}]}
        ]}).to_string(),
    );
    write(
        &root,
        "corpus/arguments/bridge.json",
        &json!({"id": "bridge-registration", "conclusion_statement_id": BRIDGE,
            "meaning": "bridge registration", "premise_statement_ids": [], "inference_ids": ["bridge-inference"],
            "sense_bridges": [
            {"term": "TERM", "from": "first", "to": "second", "statement_id": BRIDGE}
        ]}).to_string(),
    );
    write(&root, "scripts/Discover.lean", "import Lean\n");
    write(&root, "scripts/worker_env.py", WORKER);
    write(
        &root,
        "solver.json",
        &json!({"alone": null, "closed": {"used": [0], "axioms": ["Classical.choice"], "prover": "duper"},
            "minimal": [0], "proof": {"used": [0], "axioms": ["Classical.choice"], "prover": "duper"},
            "deletions": [], "vacuous": null,
            "witness": "synthetic response", "signature": ": True", "unfold": []}).to_string(),
    );
    Fixture(root)
}

const WORKER: &str = r#"import json
import shlex
import sys
from pathlib import Path

args = sys.argv[3:]
root = Path.cwd()
def record(stage, **fields):
    with (root / 'calls.jsonl').open('a') as f:
        f.write(json.dumps(dict(stage=stage, **fields)) + '\n')
if args[0] == 'build':
    record('build')
elif '--run' in args:
    declarations = Path(args[-1]).read_text().splitlines()
    record('export', declarations=declarations)
    missing = (root / 'missing.txt').read_text().strip() if (root / 'missing.txt').exists() else ''
    print(json.dumps([dict(declaration=d, module=d.rsplit('.', 1)[0], binders=['x'], constants=[])
                      for d in declarations if d != missing]))
elif Path(args[-1]).name == 'DiscoverCertify.lean':
    record('certify')
    for i, line in enumerate(Path(args[-1]).read_text().splitlines(), 1):
        if line.startswith('#print axioms '):
            error = (root / 'reject-certification').exists()
            print(json.dumps(dict(severity='error' if error else 'information', pos=dict(line=i),
                data='synthetic certification rejection' if error else
                     "'%s' depends on axioms: [Classical.choice]" % line.split()[-1])))
        if line.startswith('#discover_external '):
            outside = (root / 'outside.json').read_text() if (root / 'outside.json').exists() else '[]'
            print(json.dumps(dict(severity='information', pos=dict(line=i),
                data='discover-external: ' + outside.strip())))
else:
    for line in Path(args[-1]).read_text().splitlines():
        if line.startswith('#discover '):
            tokens = shlex.split(line)
            record('search', target=tokens[5], premises=tokens[7:])
            result = json.loads((root / 'solver.json').read_text())
            result['label'] = tokens[1]
            print('DISCOVER-JSON ' + json.dumps(result))
"#;

fn truth(root: &Path, args: &[&str]) -> Output {
    Command::new(BINARY)
        .args(["--root"])
        .arg(root)
        .args(["--json", "discover", "--target", "Target"])
        .args(args)
        .env_remove("TRUTH_ZIPPERPOSITION")
        .output()
        .unwrap()
}

fn report(output: &Output) -> Value {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn calls(root: &Path) -> Vec<Value> {
    fs::read_to_string(root.join("calls.jsonl"))
        .unwrap_or_default()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

#[test]
fn explicit_bundle_is_not_silently_replaced_by_retrieval() {
    let fixture = fixture("exact");
    let mut args = vec!["--module".to_owned(), "TruthCore.Target".to_owned()];
    for i in (0..10).rev() {
        args.extend(["--premise".into(), format!("STMT-P{i}")]);
    }
    args.extend(["--premise".into(), "Premise 0".into()]);
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let view = report(&truth(&fixture.0, &args));
    let expected: Vec<String> = (0..10).rev().map(premise).collect();
    assert_eq!(view["findings"].as_array().unwrap().len(), 1, "{view}");
    let finding = &view["findings"][0];
    assert_eq!(finding["candidates"], json!(expected));
    assert_eq!(view["options"]["premise_selection"], "exact");
    assert_eq!(view["options"]["premises"], json!(expected));
    assert!(view["options"]["premise_pool"].is_null());
    assert!(view["options"]["candidates"].is_null());
    assert_eq!(finding["kind"], "discovery");
    assert_eq!(finding["premises"][0]["statement_id"], premise(9));
    assert_eq!(finding["certified"]["ok"], true);
    let calls = calls(&fixture.0);
    assert!(calls.iter().any(|c| c["stage"] == "certify"));
    let search = calls.iter().find(|c| c["stage"] == "search").unwrap();
    assert_eq!(search["premises"].as_array().unwrap().len(), 10);
    assert!(
        !search["premises"]
            .as_array()
            .unwrap()
            .contains(&json!("TruthCore.Bridges.Link"))
    );
    let export = calls.iter().find(|c| c["stage"] == "export").unwrap();
    assert_eq!(export["declarations"].as_array().unwrap().len(), 11);
}

#[test]
fn exact_bundle_reuses_certification_and_rejection_filters() {
    let fixture = fixture("filters");
    write(&fixture.0, "reject-certification", "");
    let view = report(&truth(&fixture.0, &["--premise", "STMT-P0"]));
    let finding = &view["findings"][0];
    assert_eq!(finding["kind"], "filtered");
    assert_eq!(finding["filters"][0]["filter"], "certification");
    assert_eq!(finding["certified"]["ok"], false);

    let mut raw: Value =
        serde_json::from_str(&fs::read_to_string(fixture.0.join("solver.json")).unwrap()).unwrap();
    raw["domain_identified_by_name"] = json!(["P0.B = Goal.B"]);
    write(&fixture.0, "solver.json", &raw.to_string());
    let before = calls(&fixture.0)
        .iter()
        .filter(|c| c["stage"] == "certify")
        .count();
    let view = report(&truth(&fixture.0, &["--premise", "STMT-P0"]));
    assert_eq!(view["findings"][0]["kind"], "filtered");
    assert_eq!(
        view["findings"][0]["filters"][0]["filter"],
        "domain_by_name"
    );
    assert_eq!(
        calls(&fixture.0)
            .iter()
            .filter(|c| c["stage"] == "certify")
            .count(),
        before
    );
}

#[test]
fn a_portfolio_proof_resting_on_a_library_theorem_fails_certification() {
    let fixture = fixture("outside");
    let mut raw: Value =
        serde_json::from_str(&fs::read_to_string(fixture.0.join("solver.json")).unwrap()).unwrap();
    raw["closed"]["prover"] = json!("portfolio:simp_all");
    raw["proof"]["prover"] = json!("portfolio:simp_all");
    write(&fixture.0, "solver.json", &raw.to_string());
    // The search's own check found no outside theorem; the re-elaborated
    // certification text does (as a different library could supply one).
    write(&fixture.0, "outside.json", r#"["TruthCore.Lib.simpLemma"]"#);
    let view = report(&truth(&fixture.0, &["--premise", "STMT-P0"]));
    let finding = &view["findings"][0];
    assert_eq!(finding["kind"], "filtered", "{view}");
    assert_eq!(finding["filters"][0]["filter"], "outside_bundle");
    assert!(
        finding["filters"][0]["detail"]
            .as_str()
            .unwrap()
            .contains("TruthCore.Lib.simpLemma")
    );
    // The configuration carried prove-sweep's portfolio and its budget.
    assert_eq!(view["options"]["portfolio_heartbeats"], 20000);
    fs::remove_file(fixture.0.join("outside.json")).unwrap();
    let view = report(&truth(&fixture.0, &["--premise", "STMT-P0"]));
    assert_eq!(view["findings"][0]["kind"], "discovery", "{view}");
}

#[test]
fn invalid_exact_inputs_fail_before_building() {
    let fixture = fixture("invalid");
    for (args, code, message) in [
        (vec!["--premise", "missing"], 3, "unknown premise"),
        (vec!["--premise", ""], 2, "non-empty"),
        (vec!["--premise", "Unbound"], 2, "no lean_declaration"),
        (vec!["--premise", "Target"], 2, "target is also a premise"),
        (
            vec!["--premise", "STMT-P0", "--candidates", "1"],
            2,
            "--candidates",
        ),
        (
            vec!["--premise", "STMT-P0", "--premise-pool", "all"],
            2,
            "--premise-pool",
        ),
    ] {
        let output = truth(&fixture.0, &args);
        assert_eq!(
            output.status.code(),
            Some(code),
            "{args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(message),
            "{args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            calls(&fixture.0).is_empty(),
            "invalid input reached the build: {args:?}"
        );
    }
}

#[test]
fn unavailable_exact_declaration_is_an_error_not_a_skipped_goal() {
    let fixture = fixture("unavailable");
    write(&fixture.0, "missing.txt", "TruthCore.Premises.P0");
    let output = truth(&fixture.0, &["--premise", "STMT-P0"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("not in the built library"));
    assert!(!calls(&fixture.0).iter().any(|c| c["stage"] == "search"));
}
