//! Solver units (ported from the retired `scripts/test_countermodel.py`) and
//! golden replays: recorded `scripts/Countermodel.lean` skeletons of real
//! theorems against the reports the retired Python finder gave for them
//! (`testdata/countermodel/`; only the certificate's provenance line was
//! changed to name `truth countermodel`). The Lean-checked rediscovery of the
//! hand-written certificates runs in CI after `lake build` (ci.yml).

use super::*;
use serde_json::{Value, json};

fn atom(p: &str, vs: &[&str]) -> Value {
    json!({"t": "atom", "p": p, "args": vs.iter().map(|v| json!({"v": v})).collect::<Vec<_>>()})
}

fn forall(v: &str, sort: &str, body: Value) -> Value {
    json!({"t": "forall", "v": v, "sort": sort, "body": body})
}

fn imp(a: Value, b: Value) -> Value {
    json!({"t": "imp", "a": a, "b": b})
}

fn not(a: Value) -> Value {
    json!({"t": "not", "a": a})
}

fn pure_act(x: &str) -> Value {
    forall("r", "R", not(atom("InPotency", &[x, "r"])))
}

fn lives(x: &str) -> Value {
    json!({"t": "exists", "v": "t", "sort": "T", "body": atom("LivesAt", &[x, "t"])})
}

/// PureActOperates, SelfOperatingUnmovedLives, MovedOnlyAsInPotency ⊢
/// PureActLives (`SelfOperationLife.pureActLives`), written by hand.
fn skeleton() -> Skeleton {
    let value = json!({
        "theorem": "Example.pureActLives",
        "carriers": ["B", "R", "T"],
        "constants": [],
        "predicates": [{"name": "InPotency", "args": ["B", "R"]}, {"name": "MovedIn", "args": ["B", "R"]},
                       {"name": "Operates", "args": ["B"]}, {"name": "LivesAt", "args": ["B", "T"]}],
        "premises": [
            {"name": "hOperates", "lean": "A",
             "formula": forall("x", "B", imp(pure_act("x"), atom("Operates", &["x"])))},
            {"name": "hLife", "lean": "B", "formula": forall("x", "B", imp(atom("Operates", &["x"]), imp(
                forall("r", "R", not(atom("MovedIn", &["x", "r"]))), lives("x"))))},
            {"name": "hMoved", "lean": "C", "formula": forall("x", "B", forall("r", "R", imp(
                atom("MovedIn", &["x", "r"]), atom("InPotency", &["x", "r"]))))},
        ],
        "conclusion": {"lean": "D", "formula": forall("x", "B", imp(pure_act("x"), lives("x")))},
        "unfolded": [],
    });
    Skeleton::parse(&value, "Example").unwrap()
}

fn small(premises: Value, conclusion: Value, predicates: Value, carriers: Value) -> Skeleton {
    let value = json!({"theorem": "Example.t", "carriers": carriers, "constants": [],
                       "predicates": predicates, "premises": premises,
                       "conclusion": {"lean": "C", "formula": conclusion}, "unfolded": []});
    Skeleton::parse(&value, "Example").unwrap()
}

#[test]
fn dpll() {
    assert!(solve(&[vec![1], vec![-1]], 1, &[]).is_none());
    let model = solve(&[vec![1, 2], vec![-1, 2], vec![-2, 3]], 3, &[]).unwrap();
    assert!(model[2] && model[3]);
    // false first: nothing forces 1, so it stays false
    assert!(!model[1]);
}

#[test]
fn sizes_smallest_total_first() {
    let carriers = vec!["A".to_owned(), "B".to_owned()];
    let order: Vec<Vec<usize>> = size_assignments(&carriers, 2)
        .into_iter()
        .map(|sizes| sizes.into_iter().map(|(_, size)| size).collect())
        .collect();
    assert_eq!(order, [vec![1, 1], vec![1, 2], vec![2, 1], vec![2, 2]]);
}

#[test]
fn every_omission_found_and_satisfies_its_target() {
    let skeleton = skeleton();
    for target in omission_targets(&skeleton, None) {
        let name = target.omitted.unwrap();
        let model = find_model(&skeleton, &target.holds, &target.fails, 2)
            .unwrap()
            .unwrap_or_else(|| panic!("{name}"));
        for f in &target.holds {
            assert!(evaluate(&skeleton, &model, f).unwrap());
        }
        for f in &target.fails {
            assert!(!evaluate(&skeleton, &model, f).unwrap());
        }
        let omitted = skeleton.premises.iter().find(|p| p.name == name).unwrap();
        assert!(!evaluate(&skeleton, &model, &omitted.formula).unwrap());
    }
}

#[test]
fn redundant_premise_is_unresolved_not_refuted() {
    let every = forall("x", "B", atom("P", &["x"]));
    let skeleton = small(
        json!([{"name": "h1", "lean": "A", "formula": every},
               {"name": "h2", "lean": "A", "formula": every}]),
        every.clone(),
        json!([{"name": "P", "args": ["B"]}]),
        json!(["B"]),
    );
    let reports = run(&skeleton, None, 2, false, None).unwrap();
    let statuses: Vec<&str> = reports.iter().map(|r| r.status).collect();
    assert_eq!(statuses, ["unresolved", "unresolved"]);
    assert!(
        reports[0]
            .note
            .as_ref()
            .unwrap()
            .contains("does not show the premise is needed")
    );
}

#[test]
fn excluded_middle_premise_holds_in_every_model() {
    let em = forall(
        "P",
        "Prop",
        json!({"t": "or", "a": atom("P", &[]), "b": not(atom("P", &[]))}),
    );
    let skeleton = small(
        json!([{"name": "hEM", "lean": "EM", "formula": em}]),
        forall(
            "x",
            "B",
            json!({"t": "or", "a": atom("Q", &["x"]), "b": not(atom("Q", &["x"]))}),
        ),
        json!([{"name": "Q", "args": ["B"]}]),
        json!(["B"]),
    );
    let [report] = &run(&skeleton, None, 2, false, None).unwrap()[..] else {
        panic!("one report")
    };
    assert_eq!(report.status, "unresolved");
    assert!(
        report
            .note
            .as_ref()
            .unwrap()
            .contains("holds in every model")
    );
}

#[test]
fn predicate_of_predicates() {
    // Possible (fun t => ¬ IsAt x t), with Possible : (T → Prop) → Prop.
    let lam = json!({"lam": [{"v": "t", "sort": "T"}], "body": not(atom("IsAt", &["x", "t"]))});
    let possible_absent = json!({"t": "atom", "p": "Possible", "args": [lam]});
    let skeleton = small(
        json!([{"name": "h", "lean": "H", "formula": forall("x", "B", possible_absent.clone())}]),
        forall("x", "B", not(possible_absent)),
        json!([{"name": "Possible", "args": [{"set": ["T"]}]}, {"name": "IsAt", "args": ["B", "T"]}]),
        json!(["B", "T"]),
    );
    let premise = &skeleton.premises[0].formula;
    let model = find_model(&skeleton, &[premise], &[], 2).unwrap().unwrap();
    assert!(evaluate(&skeleton, &model, premise).unwrap());
    let text = render_model(&skeleton, &model);
    assert!(
        text.iter()
            .any(|line| line.starts_with("abbrev Possible : (T → Prop) → Prop")),
        "{text:?}"
    );
}

#[test]
fn rendering_states_omission_and_negated_conclusion() {
    let skeleton = skeleton();
    let omit = vec!["hLife".to_owned()];
    let [target] = &omission_targets(&skeleton, Some(&omit))[..] else {
        panic!("one target")
    };
    let model = find_model(&skeleton, &target.holds, &target.fails, 2)
        .unwrap()
        .unwrap();
    let text = render_certificate(&skeleton, "CM", &model, target.omitted);
    assert!(
        text.contains("(A) ∧\n    ¬ (B) ∧\n    (C) ∧\n    ¬ (D)"),
        "{text}"
    );
    assert!(text.contains("<;> decide"));
}

#[test]
fn prop_quantified_premise_uses_classical_em() {
    let em = forall(
        "P",
        "Prop",
        json!({"t": "or", "a": atom("P", &[]), "b": not(atom("P", &[]))}),
    );
    let skeleton = small(
        json!([{"name": "hEM", "lean": "EM", "formula": em},
               {"name": "h", "lean": "H", "formula": forall("x", "B", atom("Q", &["x"]))}]),
        forall("x", "B", atom("Q", &["x"])),
        json!([{"name": "Q", "args": ["B"]}]),
        json!(["B"]),
    );
    let reports = run(&skeleton, None, 2, true, None).unwrap();
    let witness = reports.last().unwrap();
    assert_eq!(witness.status, "candidate");
    assert!(
        witness
            .lean
            .as_ref()
            .unwrap()
            .contains("first | decide | exact Classical.em")
    );
}

#[test]
fn checker_statuses() {
    let skeleton = skeleton();
    let accept: Checker = &|_, _| (true, String::new());
    let reports = run(&skeleton, None, 2, true, Some(accept)).unwrap();
    assert!(reports.iter().all(|r| r.status == "lean-checked"));
    // The joint run fails; each snippet is then checked alone.
    let reject_life: Checker =
        &|_, snippet| (!snippet.contains("omit_hLife"), "error: no".to_owned());
    let reports = run(&skeleton, None, 2, true, Some(reject_life)).unwrap();
    let statuses: Vec<(Option<&str>, &str)> = reports
        .iter()
        .map(|r| (r.omitted.as_deref(), r.status))
        .collect();
    assert_eq!(
        statuses,
        [
            (Some("hOperates"), "lean-checked"),
            (Some("hLife"), "lean-rejected"),
            (Some("hMoved"), "lean-checked"),
            (None, "lean-checked"),
        ]
    );
    assert_eq!(reports[1].lean_output.as_deref(), Some("error: no"));
}

#[test]
fn omit_by_name_or_position() {
    let skeleton = skeleton();
    let omit = |given: &[&str]| {
        resolve_omit(
            &skeleton,
            &given.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        )
    };
    assert_eq!(omit(&["2", "hMoved"]).unwrap(), ["hLife", "hMoved"]);
    assert!(omit(&["4"]).unwrap_err().contains("unknown premise"));
    assert!(omit(&["hNope"]).is_err());
}

/// The recorded skeleton and Python report for `name` at `size`.
fn golden(name: &str, size: usize) -> (Value, Value) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/testdata/countermodel");
    let read = |file: String| -> Value {
        serde_json::from_str(&fs::read_to_string(dir.join(file)).unwrap()).unwrap()
    };
    (
        read(format!("{name}.skeleton.json")),
        read(format!("{name}.size{size}.json")),
    )
}

fn replay(name: &str, size: usize) {
    let (skeleton, expected) = golden(name, size);
    let module = expected["module"].as_str().unwrap();
    let skeleton = Skeleton::parse(&skeleton, module).unwrap();
    let reports: Vec<Value> = run(&skeleton, None, size, true, None)
        .unwrap()
        .iter()
        .map(Report::to_json)
        .collect();
    assert_eq!(
        Value::Array(reports),
        expected["reports"],
        "{name} at size {size}"
    );
}

#[test]
fn golden_self_operation_life() {
    replay("pureActLives", 2);
    replay("pureActLives", 3);
}

#[test]
fn golden_perfection_of_being() {
    replay("actualityOnlyInsofarAsBeing", 2);
}

#[test]
fn golden_predicate_of_predicates() {
    replay("necessaryBeingInAct", 2);
}

#[test]
fn golden_component_firstness() {
    replay("noComponentFirst", 2);
}

#[test]
fn golden_excluded_middle() {
    replay("nothingMovesExceptInAct", 2);
}

#[test]
fn golden_causal_maps() {
    replay("causeOfQualityMoreSuch", 2);
}
