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
    let counterexample = json!({
        "id":"counterexample", "label":"Finite comparison", "date":"2026-11-18",
        "statement_ids":["Q","T","P"], "kind":"countermodel", "outcome":"succeeded",
        "summary":"A finite model separates the inputs in this interpretation. Its scope is limited to that model.",
        "blocker":"Check whether the model represents the actual witnesses.",
        "evidence":["result-b","PR-23"]
    });
    fixture.write("attempts", counterexample.clone());
    fixture.write(
        "attempts",
        json!({
            "id":"blocked-search", "label":"Direct argument search", "date":"2026-11-17",
            "statement_ids":["Q"], "kind":"derivation", "outcome":"failed",
            "summary":"The search found no derivation from the retained inputs.",
            "blocker":"The bridge to the actual witness is still open.", "evidence":["result-c"]
        }),
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
    let previous = value["previous_investigations"].as_array().unwrap();
    assert_eq!(
        previous
            .iter()
            .map(|r| r["attempt_id"].as_str().unwrap())
            .collect::<Vec<_>>(),
        [
            "across",
            "blocked-search",
            "competing",
            "counterexample",
            "direct",
            "elsewhere"
        ]
    );
    assert_eq!(previous[0]["statement_ids"], json!(["P", "S", "T"]));
    assert_eq!(
        value["assessments"]["across"]["statement_ids"],
        json!(["P", "S"])
    );
    assert_eq!(previous[1]["outcome"], "failed");
    assert_eq!(
        previous[1]["blocker"],
        "The bridge to the actual witness is still open."
    );
    for field in [
        "label",
        "date",
        "statement_ids",
        "kind",
        "outcome",
        "summary",
        "blocker",
        "evidence",
    ] {
        assert_eq!(previous[3][field], counterexample[field], "{field}");
    }
    assert_eq!(previous[3]["path"], "corpus/attempts/counterexample.json");
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
    assert!(formal_evidence.contains("Alternative (transcription)"));
    assert!(formal_evidence.contains("truth context b"));
    assert!(formal_evidence.contains("Alternative (derivation)"));
    assert!(formal_evidence.contains("truth context c"));
    let limited = String::from_utf8(fixture.run(&["T", "--limit", "1"]).stdout).unwrap();
    assert_eq!(limited.matches("Alternative (").count(), 1);
    assert!(limited.contains("All 3 argument bundles are available in --json."));
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
    assert!(human.contains("Earlier investigation (countermodel, recorded outcome succeeded)"));
    assert!(human.contains("Its scope is limited to that model."));
    assert!(human.contains("Source — corpus/attempts/counterexample.json"));
    assert!(human.contains("Use --json for full attempt findings"));
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
    let bare_text = String::from_utf8(fixture.run(&["Q"]).stdout).unwrap();
    assert!(bare_text.contains("No current assessment explicitly names this proposition."));
    assert!(bare_text.contains("Its scope is limited to that model."));
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
        fixture.write("statements", json!({"id":id,"label":id,"paraphrase":format!("Statement {id}."),"lean_declaration":format!("{id}.Exists")}));
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

    let withheld = ["a", "--without", "P", "--without", "Q"];
    let output = fixture.run(&withheld);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let withheld_text = String::from_utf8(output.stdout).unwrap();
    assert_eq!(
        withheld_text
            .matches("corpus/attempts/counterexample.json")
            .count(),
        1
    );
    assert!(withheld_text.contains("One investigation covers the actual witnesses."));
    assert!(withheld_text.contains("Its scope is limited to that model."));
    let replay: Value =
        serde_json::from_slice(&fixture.run(&[&withheld[..], &["--json"]].concat()).stdout)
            .unwrap();
    assert_eq!(replay["reachable"], false);
    assert_eq!(
        replay["withheld_assessments"][0]["statement_ids"],
        json!(["P", "S"])
    );
    assert_eq!(
        replay["previous_investigations"],
        json!([previous[0], previous[1], previous[3]])
    );
    let without_q: Value =
        serde_json::from_slice(&fixture.run(&["a", "--without", "Q", "--json"]).stdout).unwrap();
    assert_eq!(without_q["withheld_assessments"], json!([]));
    assert_eq!(
        without_q["previous_investigations"],
        json!([previous[1], previous[3]])
    );
}

#[test]
fn compare_a_selected_argument_without_bootstrapping_its_conclusion() {
    let f = Fixture(
        std::env::temp_dir().join(format!("truth-synthesis-replay-{}", std::process::id())),
    );
    for id in ["P", "Q", "K", "T", "X", "Y", "Z"] {
        f.statement(id);
    }
    f.argument("chosen", &["P", "Q"], "T", false);
    f.write("arguments",json!({"id":"chosen","label":"Chosen route","meaning":"Test","premise_statement_ids":["P","Q"],"commitment_statement_ids":["K"],"conclusion_statement_id":"T","inference_ids":["inference"]}));
    f.argument("alternate", &["P", "K"], "T", true);
    f.argument("recover_q", &["P"], "Q", false);
    f.argument("cycle_entry", &["T"], "P", false);
    f.argument("self", &["T"], "T", false);
    f.argument("starts_x", &["Y"], "X", false);
    f.argument("starts_y", &["X"], "Y", false);
    f.argument("unfounded", &["X"], "T", false);
    f.argument("proposed", &["Q"], "T", false);
    f.write("results",json!({"id":"result-proposed","argument_id":"proposed","challenge_module":"Challenge","solution_module":"Solution","theorem":"proposed","comparator_config":"test","status":"proposed"}));
    let output = f.run(&["chosen", "--compare-premises", "--json"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["mode"], "argument");
    assert_eq!(
        report["supporting_arguments"],
        json!(["alternate", "chosen"])
    );
    assert_eq!(report["derivation"], json!(["chosen"]));
    assert_eq!(report["inputs"][2]["role"], "commitment");
    let cases = report["comparisons"].as_array().unwrap();
    let case = |id: &str| cases.iter().find(|c| c["withheld"] == json!([id])).unwrap();
    assert_eq!(case("P")["reachable"], false);
    assert_eq!(case("K")["reachable"], false);
    assert_eq!(case("Q")["recovered_inputs"], json!(["Q"]));
    assert_eq!(case("Q")["derivation"], json!(["recover_q", "chosen"]));
    let single = f.run(&["chosen", "--without", "Q", "--json"]);
    let single: Value = serde_json::from_slice(&single.stdout).unwrap();
    assert_eq!(single["derivation"], case("Q")["derivation"]);
    assert!(f.run(&["chosen", "--without", "Z"]).status.code().unwrap() != 0);
    assert!(!f.run(&["T", "--without", "K"]).status.success());
    assert!(
        !f.run(&["--question", "Q", "--without", "K"])
            .status
            .success()
    );
    f.argument("weaker", &["Q"], "T", false);
    let alternate: Value =
        serde_json::from_slice(&f.run(&["chosen", "--without", "K", "--json"]).stdout).unwrap();
    assert_eq!(alternate["selected_applicable"], false);
    assert_eq!(alternate["supporting_arguments"], json!(["weaker"]));
    f.argument("zero", &[], "K", false);
    let recovered: Value =
        serde_json::from_slice(&f.run(&["chosen", "--without", "K", "--json"]).stdout).unwrap();
    assert_eq!(recovered["recovered_inputs"], json!(["K"]));
    assert_eq!(recovered["derivation"], json!(["zero", "chosen"]));
}
