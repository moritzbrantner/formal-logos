//! `truth semantics` on the sense fixture of the `check` golden
//! `test_conclusion_bridge_and_control_are_accepted`: statement C is
//! concluded by a bridged argument (ARG-BC, conclusion bridge T_1 -> T_2), an
//! allowlisted legacy mixing (ARG-BC-OLD) and a premise-free mixing control.
//! The preflight must reach exactly the verdict `truth check` gives the same
//! candidate written as a new argument file.

use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

const BINARY: &str = env!("CARGO_BIN_EXE_truth");
const GOLDEN: &str = "tests/golden/check/test_conclusion_bridge_and_control_are_accepted.json";
const CANDIDATE: &str = "corpus/arguments/05-candidate.json";

struct Fixture(PathBuf);

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn fixture(name: &str) -> Fixture {
    let golden: Value = serde_json::from_str(
        &fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(GOLDEN)).unwrap(),
    )
    .unwrap();
    let root = std::env::temp_dir().join(format!("truth-semantics-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    for (path, text) in golden["base"].as_object().unwrap() {
        let target = root.join(path);
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::write(target, text.as_str().unwrap()).unwrap();
    }
    Fixture(root)
}

fn truth(root: &Path, args: &[&str]) -> Output {
    Command::new(BINARY)
        .arg("--root")
        .arg(root)
        .args(args)
        .output()
        .unwrap()
}

fn json(root: &Path, args: &[&str]) -> Value {
    let mut all = vec!["--json"];
    all.extend(args);
    let output = truth(root, &all);
    assert!(
        output.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn verdicts(list: &Value) -> Vec<(String, String)> {
    list["shown"]
        .as_array()
        .unwrap()
        .iter()
        .map(|argument| {
            let term = &argument["terms"][0];
            (
                argument["label"].as_str().unwrap().to_owned(),
                format!(
                    "{}:{}",
                    term["term"].as_str().unwrap(),
                    term["verdict"].as_str().unwrap()
                ),
            )
        })
        .collect()
}

#[test]
fn statement_mode_reports_senses_and_verdicts() {
    let fixture = fixture("statement");
    let view = json(&fixture.0, &["semantics", "STMT-C"]);
    assert_eq!(view["mode"], "statement");
    assert!(
        view["input_identity"]
            .as_str()
            .unwrap()
            .starts_with("fnv1a64:")
    );
    let statement = &view["statement"];
    assert_eq!(statement["label"], "C");
    assert_eq!(statement["definitions"][0]["label"], "T_2: Second sense");
    assert_eq!(statement["definitions"][0]["basis"], "stipulative");
    assert_eq!(
        statement["definitions"][0]["formal_status"],
        "no_lean_declaration"
    );
    assert_eq!(statement["disambiguations"][0]["takes"][0], "T_2");
    let sense = &statement["senses_used"][0]["senses"][0];
    assert_eq!(sense["label"], "T_2");
    assert_eq!(sense["distinct_lean_declaration"], false);
    assert_eq!(
        verdicts(&view["arguments"]["concluding"]),
        [
            ("C, from B (2)".into(), "T:bridged".into()),
            ("C, from B".into(), "T:allowlisted_mixing".into()),
            ("control argument".into(), "T:mixing_control".into()),
        ]
    );
    let bridged = &view["arguments"]["concluding"]["shown"][0]["terms"][0];
    assert_eq!(bridged["bridges"][0]["label"], "C");
    assert_eq!(bridged["bridges"][0]["role"], "conclusion");
    // Which statement carries which sense.
    let legacy = &view["arguments"]["concluding"]["shown"][1]["terms"][0]["senses"];
    assert_eq!(legacy[0]["label"], "T_1");
    assert_eq!(legacy[0]["carriers"][0]["role"], "premise");
    assert_eq!(legacy[0]["carriers"][0]["label"], "B");
    assert_eq!(legacy[1]["carriers"][0]["role"], "conclusion");
    let summary = &view["summary"];
    assert_eq!(summary["term_uses"]["allowlisted_mixing"], 1);
    assert_eq!(summary["term_uses"]["bridged"], 1);
    assert_eq!(summary["term_uses"]["mixing_control"], 1);
    assert_eq!(summary["equivocation_risks_total"], 1);

    let text = truth(&fixture.0, &["semantics", "STMT-C", "--limit", "1"]);
    assert!(text.status.success());
    let text = String::from_utf8(text.stdout).unwrap();
    assert!(text.contains("Arguments concluding it (1 of 3):"), "{text}");
    assert!(text.contains("T_2 has no distinct Lean declaration: bind-check cannot catch"));
    assert!(text.contains("equivocation risks: 1 term use(s) in 1 argument(s)"));
}

#[test]
fn argument_and_result_modes() {
    let fixture = fixture("argument");
    let view = json(&fixture.0, &["semantics", "ARG-BC-OLD"]);
    assert_eq!(view["mode"], "argument");
    assert_eq!(
        view["argument"]["terms"][0]["verdict"],
        "allowlisted_mixing"
    );
    let roles: Vec<&str> = view["statements"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s["role"].as_str().unwrap())
        .collect();
    assert_eq!(roles, ["conclusion", "premise"]);
    // B is concluded by ARG-AB, whose statements use one sense.
    assert_eq!(view["ancestry"]["arguments"], 1);
    assert_eq!(view["ancestry"]["equivocation_risks_total"], 0);

    let view = json(&fixture.0, &["semantics", "RES-BC"]);
    assert_eq!(view["requested"]["kind"], "results");
    assert_eq!(view["argument"]["label"], "C, from B (2)");
    assert_eq!(view["argument"]["terms"][0]["verdict"], "bridged");
}

#[test]
fn unknown_target_exits_3() {
    let fixture = fixture("unknown");
    let output = truth(&fixture.0, &["semantics", "NO-SUCH-THING"]);
    assert_eq!(output.status.code(), Some(3));
    let output = truth(
        &fixture.0,
        &["semantics", "--premise", "NOPE", "--conclusion", "STMT-C"],
    );
    assert_eq!(output.status.code(), Some(3));
}

/// Writes the preflight's candidate as a new argument and runs `truth check`.
fn check_candidate(root: &Path, candidate: &Value) -> Output {
    let mut record = candidate.clone();
    record["id"] = "5e8b1c3a-4c2d-4f1e-9a7b-3c2d1e0f9a8b".into();
    record["label"] = "C, from B (candidate)".into();
    record["inference_ids"] = serde_json::json!(["3cdaf6ca-b69a-55db-a72e-32a15ab511aa"]);
    record["meaning"] = "m".into();
    fs::write(
        root.join(CANDIDATE),
        serde_json::to_string_pretty(&record).unwrap(),
    )
    .unwrap();
    let output = truth(root, &["check"]);
    fs::remove_file(root.join(CANDIDATE)).unwrap();
    output
}

#[test]
fn preflight_agrees_with_check_for_a_new_argument() {
    let fixture = fixture("preflight");
    let root = fixture.0.as_path();
    // Without a bridge: the same premises and conclusion as the allowlisted
    // ARG-BC-OLD, but a new argument gets no allowlist.
    let base = ["semantics", "--premise", "STMT-B", "--conclusion", "STMT-C"];
    let view = json(root, &base);
    assert_eq!(view["unbridged"][0]["term"], "T");
    assert_eq!(view["check"]["passes"], false);
    assert_eq!(view["agrees_with_check"], true);
    let output = check_candidate(root, &view["candidate"]);
    assert!(!output.status.success());
    let preflight = view["check"]["message"].as_str().unwrap();
    let suffix = preflight.strip_prefix("candidate argument: ").unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(&format!("{CANDIDATE}: {suffix}")),
        "check: {stderr}\npreflight: {preflight}"
    );
    let strict = truth(root, &[&base[..], &["--strict"]].concat());
    assert_eq!(strict.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&strict.stdout).contains("Unbridged mixing (1)"));

    // A conclusion bridge naming the senses: check accepts the argument.
    let bridged = [&base[..], &["--bridge", "STMT-C@T_1,T_2", "--strict"]].concat();
    let view = json(root, &bridged);
    assert_eq!(view["unbridged"], serde_json::json!([]));
    assert_eq!(view["check"]["passes"], true);
    assert_eq!(view["candidate"]["sense_bridges"][0]["role"], "conclusion");
    let output = check_candidate(root, &view["candidate"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    // C links only T_2, so without named senses it relates nothing.
    let view = json(root, &[&base[..], &["--bridge", "STMT-C"]].concat());
    assert_eq!(view["unbridged"][0]["term"], "T");
    assert_eq!(view["notes"].as_array().unwrap().len(), 1);
    assert_eq!(view["agrees_with_check"], true);
}
