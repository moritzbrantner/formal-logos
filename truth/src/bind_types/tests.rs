//! Fixture tests: a recorded `scripts/BindTypes.lean` output drives the
//! cache, and edits to its inputs make it stale.

use super::*;
use std::time::{SystemTime, UNIX_EPOCH};

const THEOREM: &str = "TruthCore.Fix.Solution.fixAB";

/// A recorded exporter output (shape of `lake env lean --run
/// scripts/BindTypes.lean`): one vocabulary parameter, a bound hypothesis,
/// an extra hypothesis, a theory bundle and the conclusion.
const RECORDED: &str = r#"[{"theorem": "TruthCore.Fix.Solution.fixAB",
  "binders": [
    {"name": "Being", "prop": false, "head": null, "core_head": null, "wrappers": [], "type": "Type"},
    {"name": "h", "prop": true, "head": "TruthCore.Fix.Vocab.FixA", "core_head": "TruthCore.Fix.Vocab.FixA",
     "wrappers": [], "type": "TruthCore.Fix.Vocab.FixA Being", "senses": []},
    {"name": "k", "prop": true, "head": "TruthCore.Fix.Vocab.FixE", "core_head": "TruthCore.Fix.Vocab.FixE",
     "wrappers": [], "type": "TruthCore.Fix.Vocab.FixE Being"},
    {"name": "T", "prop": true, "head": "TruthCore.Comparison.Theory", "core_head": "TruthCore.Comparison.Theory",
     "wrappers": [], "type": "TruthCore.Comparison.Theory Being",
     "bundle": [{"prop": true, "head": "TruthCore.Fix.Vocab.FixC", "core_head": "TruthCore.Fix.Vocab.FixC",
                 "wrappers": [], "type": "TruthCore.Fix.Vocab.FixC Being"}]}],
  "result": {"prop": true, "head": "TruthCore.Fix.Vocab.FixB", "core_head": "TruthCore.Fix.Vocab.FixB",
             "wrappers": [], "type": "TruthCore.Fix.Vocab.FixB Being", "senses": []},
  "expression_contract": {"encoding": "closed-expression-v1"}},
 {"sense_aliases": {}}]"#;

struct Fixture(PathBuf);

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn put(root: &Path, path: &str, text: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn fixture(name: &str) -> Fixture {
    let root = std::env::temp_dir().join(format!(
        "truth-bind-types-{name}-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos())
    ));
    for (id, declaration) in [
        ("STMT-A", "TruthCore.Fix.Vocab.FixA"),
        ("STMT-B", "TruthCore.Fix.Vocab.FixB"),
        ("STMT-C", "TruthCore.Fix.Vocab.FixC"),
        ("STMT-D", "TruthCore.Fix.Vocab.FixD"),
    ] {
        put(
            &root,
            &format!("corpus/statements/{id}.json"),
            &json!({"id": id, "label": id, "paraphrase": id, "lean_declaration": declaration})
                .to_string(),
        );
    }
    put(
        &root,
        "corpus/arguments/ARG-AB.json",
        &json!({"id": "ARG-AB", "label": "AB", "meaning": "A, C, D so B",
                "premise_statement_ids": ["STMT-A", "STMT-C", "STMT-D"],
                "conclusion_statement_id": "STMT-B", "inference_ids": ["INF-AB"]})
        .to_string(),
    );
    put(
        &root,
        "corpus/results/RES-AB.json",
        &json!({"id": "RES-AB", "label": "AB", "argument_id": "ARG-AB",
                "challenge_module": "TruthCore.Fix.Challenge",
                "solution_module": "TruthCore.Fix.Solution", "theorem": THEOREM,
                "comparator_config": "comparator/fix.json", "status": "verified"})
        .to_string(),
    );
    put(
        &root,
        "TruthCore/Fix/Solution.lean",
        "module\npublic import TruthCore.Fix.Vocab\n",
    );
    put(&root, "TruthCore/Fix/Vocab.lean", "module\n");
    put(&root, "lean-toolchain", "leanprover/lean4:v4.35.0\n");
    put(
        &root,
        ".lake/build/lib/lean/TruthCore/Fix/Vocab.olean.hash",
        "0123456789abcdef",
    );
    Fixture(root)
}

fn recorded() -> Vec<Value> {
    serde_json::from_str::<Value>(RECORDED)
        .unwrap()
        .as_array()
        .unwrap()
        .clone()
}

fn corpus(root: &Path) -> Corpus {
    Corpus::load(root).unwrap()
}

#[test]
fn absent_cache_is_one_notice() {
    let fx = fixture("absent");
    let (summary, found) = attach(&fx.0, &corpus(&fx.0), &["RES-AB"]);
    assert!(found.is_empty());
    assert_eq!(summary.missing, 1);
    assert_eq!(
        summary.notice.as_deref(),
        Some(
            "elaborated types: no bind-check cache at .cache/bind-types.json \
             (rerun `truth bind-check` after `lake build`; source text only)"
        )
    );
    // No results, no notice.
    assert_eq!(attach(&fx.0, &corpus(&fx.0), &[]).0.notice, None);
}

#[test]
fn recorded_output_gives_the_elaborated_binding() {
    let fx = fixture("fresh");
    let corpus = corpus(&fx.0);
    let (path, written) = write(&fx.0, &corpus, &recorded()).unwrap();
    assert_eq!((path, written), (fx.0.join(CACHE), 1));
    let (summary, found) = attach(&fx.0, &corpus, &["RES-AB"]);
    assert_eq!((summary.fresh, summary.notice), (1, None));
    let elaborated = &found["RES-AB"];
    assert_eq!(
        elaborated.statement,
        "theorem TruthCore.Fix.Solution.fixAB (Being : Type) (h : TruthCore.Fix.Vocab.FixA Being) \
         (k : TruthCore.Fix.Vocab.FixE Being) (T : TruthCore.Comparison.Theory Being) : \
         TruthCore.Fix.Vocab.FixB Being"
    );
    assert_eq!(
        elaborated.parameters,
        vec![Parameter {
            name: "Being".into(),
            lean_type: "Type".into()
        }]
    );
    let bindings: Vec<(&str, Option<&str>)> = elaborated
        .hypotheses
        .iter()
        .map(|h| (h.name.as_str(), h.statement_id.as_deref()))
        .collect();
    assert_eq!(
        bindings,
        vec![("h", Some("STMT-A")), ("k", None), ("T.1", Some("STMT-C"))]
    );
    assert_eq!(
        elaborated.conclusion.statement_id.as_deref(),
        Some("STMT-B")
    );
    assert_eq!(elaborated.missing_premises, vec!["STMT-D".to_owned()]);
    assert_eq!(elaborated.binding, "mismatch");
    // The cache keeps no contract, sense or wrapper data.
    let text = fs::read_to_string(fx.0.join(CACHE)).unwrap();
    assert!(!text.contains("expression_contract") && !text.contains("wrappers"));
}

#[test]
fn edited_inputs_make_the_entry_stale() {
    let edits: [(&str, &str); 4] = [
        ("TruthCore/Fix/Vocab.lean", "module\ndef x := 1\n"),
        ("TruthCore/Fix/Solution.lean", "module\n"),
        (
            ".lake/build/lib/lean/TruthCore/Fix/Vocab.olean.hash",
            "fedcba9876543210",
        ),
        ("lean-toolchain", "leanprover/lean4:v4.36.0\n"),
    ];
    for (path, text) in edits {
        let fx = fixture("stale");
        write(&fx.0, &corpus(&fx.0), &recorded()).unwrap();
        put(&fx.0, path, text);
        let (summary, found) = attach(&fx.0, &corpus(&fx.0), &["RES-AB"]);
        assert!(found.is_empty(), "{path}");
        assert_eq!(summary.stale, 1, "{path}");
        let notice = summary.notice.unwrap();
        assert!(
            notice.starts_with("elaborated types: 1 stale and 0 missing of 1 results")
                && notice.contains(&format!("RES-AB: {path} changed")),
            "{notice}"
        );
    }
}

#[test]
fn changed_records_and_missing_entries() {
    let fx = fixture("records");
    write(&fx.0, &corpus(&fx.0), &recorded()).unwrap();
    let result = fx.0.join("corpus/results/RES-AB.json");
    let mut record: Value = serde_json::from_slice(&fs::read(&result).unwrap()).unwrap();
    record["theorem"] = json!("TruthCore.Fix.Solution.other");
    fs::write(&result, record.to_string()).unwrap();
    let (summary, _) = attach(&fx.0, &corpus(&fx.0), &["RES-AB"]);
    assert!(
        summary
            .notice
            .unwrap()
            .contains("RES-AB: its theorem changed")
    );
    // An exporter output without the theorem writes nothing for it, and a
    // later scoped write keeps the other entries.
    let (_, written) = write(&fx.0, &corpus(&fx.0), &[]).unwrap();
    assert_eq!(written, 0);
    let (summary, _) = attach(&fx.0, &corpus(&fx.0), &["RES-AB"]);
    assert_eq!((summary.stale, summary.missing), (1, 0));
    fs::remove_file(fx.0.join(CACHE)).unwrap();
    write(&fx.0, &corpus(&fx.0), &[]).unwrap();
    let (summary, _) = attach(&fx.0, &corpus(&fx.0), &["RES-AB"]);
    assert_eq!((summary.stale, summary.missing), (0, 1));
}

#[test]
fn unreadable_cache_is_one_notice() {
    let fx = fixture("unreadable");
    put(&fx.0, CACHE, "{\"schema\": \"other\"}");
    let (summary, _) = attach(&fx.0, &corpus(&fx.0), &["RES-AB"]);
    assert_eq!(
        summary.notice.as_deref(),
        Some(
            "elaborated types: unreadable cache .cache/bind-types.json: not a \
             truth-bind-types-v1 cache (rerun `truth bind-check` after `lake build`; source text only)"
        )
    );
}
