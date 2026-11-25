//! Synthesis joins the current assessment scope to exact route inputs. Broader
//! attempt targets, nearby prose, and repeating a citation give no extra vote.
use serde_json::{Value, json};
use std::{fs, path::PathBuf, process::Command};

struct Fixture(PathBuf);

impl Fixture {
    fn write(&self, kind: &str, value: Value) {
        let dir = self.0.join("corpus").join(kind);
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join(format!("{}.json", value["id"].as_str().unwrap())),
            value.to_string(),
        )
        .unwrap();
    }
    fn statement(&self, id: &str) {
        self.write(
            "statements",
            json!({"id":id,"label":id,"paraphrase":format!("Statement {id}.")}),
        );
    }
    fn argument(&self, id: &str, premises: &[&str], conclusion: &str, transcription: bool) {
        self.write(
            "arguments",
            json!({"id":id,"label":id,"meaning":id,"premise_statement_ids":premises,
            "conclusion_statement_id":conclusion,"inference_ids":["inference"]}),
        );
        self.write("results", json!({"id":format!("result-{id}"),"argument_id":id,"challenge_module":"Challenge",
            "solution_module":"Solution","theorem":id,"comparator_config":"test","status":"solution-present","transcription":if transcription {"instantiation"} else {""}}));
    }
    fn assessment(&self, id: &str, scope: &[&str], wider: &[&str], judgment: &str, review: &str) {
        self.write("attempts", json!({"id":id,"statement_ids":wider,"summary":"Previous work",
            "current_assessment":{"statement_ids":scope,"scope":"The selected actual case.","assessment":judgment,
            "date":"2026-11-20","next_test":"Run the discriminator.","note":format!("docs/notes/topic.md#{id}"),
            "review":review,"publication":"published","reviewed_revision":"0".repeat(40),"evidence":"Review witness","supersedes":"None"}}));
    }
    fn run(&self, args: &[&str]) -> std::process::Output {
        Command::new(env!("CARGO_BIN_EXE_truth"))
            .arg("--root")
            .arg(&self.0)
            .arg("synthesis")
            .args(args)
            .output()
            .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn exact_argument_overlap_scoped_rivals_and_prior_work() {
    let fixture =
        Fixture(std::env::temp_dir().join(format!("truth-synthesis-{}", std::process::id())));
    for id in ["T", "P", "Q", "R", "S", "C"] {
        fixture.statement(id);
    }
    fixture.argument("a", &["P", "Q"], "T", false);
    fixture.argument("b", &["P", "R"], "T", true);
    fixture.argument("c", &["S"], "T", false);
    fixture.argument("downstream", &["T", "Q"], "C", false);
    let declaration = " theorem a (p q : Prop)\n    (hp : p) (hq : q) : And (a := p) (b := q)";
    fs::write(
        fixture.0.join("Challenge.lean"),
        format!("theorem companion : True := by trivial\n\n{declaration} := by sorry\n"),
    )
    .unwrap();
    fs::write(
        fixture.0.join("Solution.lean"),
        format!("{declaration} := ⟨hp, hq⟩\n"),
    )
    .unwrap();
    fixture.statement("U");
    fixture.write(
        "arguments",
        json!({
            "id":"proposed", "label":"proposed", "meaning":"Proposed route", "premise_statement_ids":["P"], "commitment_statement_ids":["Q"],
            "conclusion_statement_id":"U","inference_ids":["inference"]
        }),
    );
    fixture.assessment(
        "uncertified",
        &["U"],
        &["U"],
        "A plausible proposal.",
        "unreviewed",
    );
    fixture.assessment(
        "direct",
        &["T"],
        &["T"],
        "The case favors this interpretation. It does not establish the universal claim.",
        "accepted_qualified",
    );
    fixture.assessment(
        "competing",
        &["T"],
        &["T"],
        "The same case favors the competing interpretation.",
        "unreviewed",
    );
    fixture.assessment(
        "across",
        &["P", "S"],
        &["P", "S", "T"],
        "One investigation covers the actual witnesses.",
        "accepted_qualified",
    );
    fixture.assessment(
        "elsewhere",
        &["C"],
        &["T", "C"],
        "Separate research.",
        "accepted_qualified",
    );
    fixture.write("relations",json!({"id":"challenge","subject_kind":"statement","subject_id":"C",
        "predicate":"attacks","object_kind":"statement","object_id":"Q","note":"An objection to Q."}));

    let machine = fixture.run(&["T", "--json"]);
    assert!(
        machine.status.success(),
        "{:?}",
        String::from_utf8_lossy(&machine.stderr)
    );
    let value: Value = serde_json::from_slice(&machine.stdout).unwrap();
    assert_eq!(value["formal_status"]["closure"], "proved");
    assert_eq!(value["formal_status"]["established"], false);
    assert_eq!(value["routes"][1]["status"], "transcription");
    assert_eq!(
        value["target_assessment_ids"],
        json!(["competing", "direct"])
    );
    assert_eq!(value["assessments"].as_object().unwrap().len(), 3);
    assert_eq!(value["premises"]["P"]["assessment_ids"], json!(["across"]));
    assert_eq!(value["premises"]["Q"]["assessment_ids"], json!([]));
    assert_eq!(
        value["shared_premises"],
        json!([{"statement_id":"P","argument_ids":["a","b"]}])
    );
    assert_eq!(
        value["shared_assessments"],
        json!([{"attempt_id":"across","statement_ids":["P","S"],"argument_ids":["a","b","c"]}])
    );
    assert_eq!(
        value["consumers"][0]["premise_statement_ids"],
        json!(["T", "Q"])
    );
    assert_eq!(
        value["related_statements"]["C"]["paraphrase"],
        "Statement C."
    );
    assert_eq!(value["objections"][0]["object_id"], "Q");
    assert_eq!(value["premises"]["Q"]["formal_status"]["refuted"], false);
    let result = &value["results"]["result-a"];
    assert_eq!(result["status"], "solution-present");
    assert_eq!(result["challenge_path"], "Challenge.lean");
    assert_eq!(result["solution_path"], "Solution.lean");
    assert_eq!(
        result["advertised_statement"],
        json!({"name":"a","line":3,"statement":declaration})
    );
    assert!(value["results"]["result-c"]["advertised_statement"].is_null());
    let human = String::from_utf8(fixture.run(&["T"]).stdout).unwrap();
    let first_judgment = human.find("The case favors this interpretation.").unwrap();
    let formal_evidence = &human[..first_judgment];
    assert!(formal_evidence.contains(declaration));
    assert!(formal_evidence.contains("Challenge.lean:3"));
    assert!(formal_evidence.contains("Solution.lean"));
    assert!(formal_evidence.contains("solution-present, solution registered"));
    assert!(!formal_evidence.contains("theorem companion"));
    let unresolved = String::from_utf8(fixture.run(&["U"]).stdout).unwrap();
    let formal_evidence = &unresolved[..unresolved.find("A plausible proposal.").unwrap()];
    assert!(formal_evidence.contains("No Lean result is registered"));
    assert!(formal_evidence.contains("Separate commitment — Statement Q."));
    let missing = String::from_utf8(fixture.run(&["C"]).stdout).unwrap();
    assert!(missing.contains("frozen declaration text is unavailable"));
    assert!(!missing.contains(declaration));
    assert!(human.contains("It does not establish the universal claim."));
    assert!(human.contains("Proposed, unreviewed"));
    assert!(human.contains("The same case favors the competing interpretation."));
    assert_eq!(
        human
            .matches("One investigation covers the actual witnesses.")
            .count(),
        1
    );
    assert!(!human.contains("Separate research."));
    assert!(
        value["target_attempt_paths"]
            .as_array()
            .unwrap()
            .iter()
            .any(|p| p == "corpus/attempts/elsewhere.json")
    );
    let limited = String::from_utf8(fixture.run(&["T", "--limit", "1"]).stdout).unwrap();
    assert!(limited.contains("1 further target-scoped"));
    assert!(!limited.contains("The same case favors the competing interpretation."));
    assert_eq!(
        machine.stdout,
        fixture.run(&["T", "--limit", "1", "--json"]).stdout
    );
    let bare: Value = serde_json::from_slice(&fixture.run(&["Q", "--json"]).stdout).unwrap();
    assert_eq!(bare["routes"], json!([]));
    assert_eq!(bare["target_assessment_ids"], json!([]));
    assert!(
        bare["consumers"]
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r["argument_id"] == "a")
    );
    for args in [
        &["T", "--question", "witness"][..],
        &["--question", "   "],
        &["T", "--limit", "0"],
        &["T", "--write"],
    ] {
        assert_eq!(fixture.run(args).status.code(), Some(2), "{args:?}");
    }
    let representative = value["routes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| {
            human.contains(&format!(
                "truth context {}",
                r["argument_id"].as_str().unwrap()
            ))
        })
        .expect("runnable illustrative argument");
    for premise in representative["premise_statement_ids"].as_array().unwrap() {
        assert!(human.contains(&format!("truth synthesis {}", premise.as_str().unwrap())));
    }
    for id in ["T", "Q"] {
        fixture.write("statements", json!({"id":id,"paraphrase":format!("Statement {id}."),"lean_declaration":format!("{id}.Exists")}));
    }
    assert!(fixture.run(&["T.Exists"]).status.success());
    let ambiguous = fixture.run(&["Exists", "--json"]);
    assert_eq!(ambiguous.status.code(), Some(3));
    let err: Value = serde_json::from_slice(&ambiguous.stderr).unwrap();
    assert_eq!(err["error"]["candidates"].as_array().unwrap().len(), 2);
    assert!(
        err["error"]["message"]
            .as_str()
            .unwrap()
            .contains("truth synthesis T")
    );
    assert_eq!(fixture.run(&["missing"]).status.code(), Some(3));
}
