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
fn nested_structure_certificate_reuses_field_tables_and_binder_order() {
    let predicate = "«countermodel field 0»";
    let flag = "«countermodel field 1»";
    let keep = "p.inner.relation x";
    let omit = "p.inner.flag x = true";
    let value = json!({
        "theorem": "Example.consumer",
        "carriers": ["A"],
        "constants": [{"name": "x", "sort": "A"}],
        "predicates": [{"name": predicate, "args": ["A"]}, {"name": flag, "args": ["A"]}],
        "structures": [{
            "name": "p",
            "lean_type": "Example.Outer A",
            "lean_value": format!("(@Example.Outer.mk A (@Example.Inner.mk A {predicate} (fun x => decide ({flag} x))))"),
        }],
        "application": ["A", "p", "x", "«countermodel premise 0»", "«countermodel premise 1»"],
        "premises": [
            {"name": "hKeep", "lean": keep, "formula": atom(predicate, &["x"])},
            {"name": "hFlag", "lean": omit, "formula": atom(flag, &["x"])},
        ],
        "conclusion": {"lean": omit, "formula": atom(flag, &["x"])},
        "unfolded": [],
    });
    let skeleton = Skeleton::parse(&value, "Example").unwrap();
    let omissions = ["hFlag".to_owned()];
    let reports = run(&skeleton, Some(&omissions), 1, false, None).unwrap();
    let [report] = reports.as_slice() else {
        panic!("expected one omission report");
    };
    assert_eq!(report.status, "candidate");
    let certificate = report.lean.as_ref().unwrap();
    assert!(certificate.contains(&format!("abbrev {predicate} : A → Prop := fun _ => True")));
    assert!(certificate.contains(&format!("abbrev {flag} : A → Prop := fun _ => False")));
    assert!(certificate.contains(&format!("@Example.Inner.mk A {predicate}")));
    assert!(
        certificate
            .contains("@Example.consumer A p x «countermodel premise 0» «countermodel premise 1»")
    );
    assert!(certificate.contains(&format!("({keep}) ∧\n    ¬ ({omit})")));
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

fn application(function: &str, argument: Value) -> Value {
    json!({"app": function, "arg": argument})
}

fn equation(a: Value, b: Value) -> Value {
    json!({"t": "eq", "a": a, "b": b})
}

fn function_skeleton(
    functions: Value,
    carriers: Value,
    predicates: Value,
    premises: Value,
    conclusion: Value,
) -> Result<Skeleton, String> {
    Skeleton::parse(
        &json!({
            "theorem": "Example.functions", "carriers": carriers, "constants": [],
            "functions": functions, "predicates": predicates, "premises": premises,
            "conclusion": {"lean": "C", "formula": conclusion}, "unfolded": [],
        }),
        "Example",
    )
}

#[test]
fn unary_functions_rediscover_the_occurrence_omissions() {
    let occurs =
        json!({"t": "exists", "v": "e", "sort": "Episode", "body": atom("Occurs", &["e"])});
    let represents = forall(
        "e",
        "Episode",
        imp(
            atom("Occurs", &["e"]),
            json!({"t": "atom", "p": "ExistsIn", "args": [application("represent", json!({"v": "e"}))]}),
        ),
    );
    let exists =
        json!({"t": "exists", "v": "b", "sort": "Being", "body": atom("ExistsIn", &["b"])});
    let skeleton = function_skeleton(
        json!([{"name": "represent", "domain": "Episode", "codomain": "Being"}]),
        json!(["Episode", "Being"]),
        json!([{"name": "Occurs", "args": ["Episode"]}, {"name": "ExistsIn", "args": ["Being"]}]),
        json!([
            {"name": "hOccurs", "lean": "ThoughtOccurs Occurs", "formula": occurs},
            {"name": "hRepresents", "lean": "Represents Occurs ExistsIn represent", "formula": represents},
        ]),
        exists,
    )
    .unwrap();
    for target in omission_targets(&skeleton, None) {
        let model = find_model(&skeleton, &target.holds, &target.fails, 2)
            .unwrap()
            .unwrap();
        assert_eq!(
            model.sizes,
            [("Episode".to_owned(), 1), ("Being".to_owned(), 1)]
        );
        for formula in target.holds {
            assert!(evaluate(&skeleton, &model, formula).unwrap());
        }
        for formula in target.fails {
            assert!(!evaluate(&skeleton, &model, formula).unwrap());
        }
        let omitted = skeleton
            .premises
            .iter()
            .find(|p| Some(p.name.as_str()) == target.omitted)
            .unwrap();
        assert!(!evaluate(&skeleton, &model, &omitted.formula).unwrap());
    }
    let reports = run(&skeleton, None, 2, true, None).unwrap();
    assert_eq!(reports.len(), 3);
    assert!(reports.iter().all(|r| r.status == "candidate"));
    assert!(reports.iter().all(|r| {
        r.lean
            .as_ref()
            .unwrap()
            .contains("abbrev represent : Episode → Being")
    }));
}

#[test]
fn unary_functions_find_a_nonconstant_swap_and_nested_apps() {
    let x = json!({"v": "x"});
    let fx = application("f", x.clone());
    let no_fixed_point = forall("x", "A", not(equation(fx.clone(), x.clone())));
    let involution = forall("x", "A", equation(application("f", fx), x));
    let skeleton = function_skeleton(
        json!([{"name": "f", "domain": "A", "codomain": "A"}]),
        json!(["A"]),
        json!([]),
        json!([
            {"name": "hNoFixed", "lean": "NoFixed f", "formula": no_fixed_point},
            {"name": "hTwice", "lean": "Twice f", "formula": involution},
        ]),
        json!({"t": "true"}),
    )
    .unwrap();
    let holds: Vec<_> = skeleton.premises.iter().map(|p| &p.formula).collect();
    assert!(find_model(&skeleton, &holds, &[], 1).unwrap().is_none());
    let model = find_model(&skeleton, &holds, &[], 2).unwrap().unwrap();
    assert_eq!(model.sizes, [("A".to_owned(), 2)]);
    assert_eq!(model.functions["f"], [1, 0]);
    assert!(
        holds
            .iter()
            .all(|f| evaluate(&skeleton, &model, f).unwrap())
    );
    assert!(
        render_model(&skeleton, &model)
            .iter()
            .any(|line| line == "abbrev f : A → A := fun x => if x = 0 then 1 else 0")
    );
}

#[test]
fn unary_functions_repeated_applications_share_one_output() {
    let fx = application("f", json!({"v": "x"}));
    let inconsistent =
        json!({"t": "exists", "v": "x", "sort": "A", "body": not(equation(fx.clone(), fx))});
    let skeleton = function_skeleton(
        json!([{"name": "f", "domain": "A", "codomain": "A"}]),
        json!(["A"]),
        json!([]),
        json!([{ "name": "h", "lean": "H", "formula": inconsistent }]),
        json!({"t": "true"}),
    )
    .unwrap();
    assert!(
        find_model(&skeleton, &[&skeleton.premises[0].formula], &[], 2)
            .unwrap()
            .is_none()
    );
}

#[test]
fn unary_functions_keep_distinct_names_and_unequal_carriers() {
    let x = json!({"v": "x"});
    let different = forall(
        "x",
        "A",
        not(equation(application("f", x.clone()), application("g", x))),
    );
    let skeleton = function_skeleton(
        json!([
            {"name": "f", "domain": "A", "codomain": "B"},
            {"name": "g", "domain": "A", "codomain": "B"},
        ]),
        json!(["A", "B"]),
        json!([]),
        json!([{ "name": "h", "lean": "H", "formula": different }]),
        json!({"t": "true"}),
    )
    .unwrap();
    let model = find_model(&skeleton, &[&skeleton.premises[0].formula], &[], 2)
        .unwrap()
        .unwrap();
    assert_eq!(model.sizes, [("A".to_owned(), 1), ("B".to_owned(), 2)]);
    assert_eq!(model.functions["f"], [0]);
    assert_eq!(model.functions["g"], [1]);
    assert!(evaluate(&skeleton, &model, &skeleton.premises[0].formula).unwrap());
}

#[test]
fn unary_functions_reject_unknown_carriers_and_duplicate_names() {
    for functions in [
        json!([{"name": "f", "domain": "missing", "codomain": "A"}]),
        json!([{"name": "f", "domain": "A", "codomain": "missing"}]),
        json!([
            {"name": "f", "domain": "A", "codomain": "A"},
            {"name": "f", "domain": "A", "codomain": "A"},
        ]),
    ] {
        assert!(
            function_skeleton(
                functions.clone(),
                json!(["A"]),
                json!([]),
                json!([]),
                json!({"t": "true"}),
            )
            .is_err(),
            "accepted invalid function signatures: {functions}"
        );
    }
}

#[test]
fn unary_functions_reject_malformed_model_tables_even_when_unused() {
    let skeleton = function_skeleton(
        json!([{"name": "f", "domain": "A", "codomain": "B"}]),
        json!(["A", "B"]),
        json!([]),
        json!([]),
        json!({"t": "true"}),
    )
    .unwrap();
    let model = find_model(&skeleton, &[], &[], 1).unwrap().unwrap();
    assert!(evaluate(&skeleton, &model, &Formula::True).unwrap());
    for table in [Vec::new(), vec![0, 0], vec![1]] {
        let mut malformed = model.clone();
        malformed.functions.insert("f".into(), table);
        assert!(evaluate(&skeleton, &malformed, &Formula::True).is_err());
    }
    let mut missing = model.clone();
    missing.functions.remove("f");
    assert!(evaluate(&skeleton, &missing, &Formula::True).is_err());
    let mut extra = model;
    extra.functions.insert("g".into(), vec![0]);
    assert!(evaluate(&skeleton, &extra, &Formula::True).is_err());
}

#[test]
fn unary_functions_report_overflow_before_allocating_tables() {
    let one = function_skeleton(
        json!([{"name": "f", "domain": "A", "codomain": "B"}]),
        json!(["A", "B"]),
        json!([]),
        json!([]),
        json!({"t": "true"}),
    )
    .unwrap();
    let cardinality = function_layout(&one, &[("A".into(), usize::BITS as usize), ("B".into(), 2)])
        .err()
        .unwrap();
    assert!(cardinality.contains("cardinality"), "{cardinality}");
    let dimensions = function_layout(&one, &[("A".into(), usize::MAX), ("B".into(), 1)])
        .err()
        .unwrap();
    assert!(dimensions.contains("dimensions"), "{dimensions}");
    let two = function_skeleton(
        json!([
            {"name": "f", "domain": "A", "codomain": "B"},
            {"name": "g", "domain": "A", "codomain": "B"},
        ]),
        json!(["A", "B"]),
        json!([]),
        json!([]),
        json!({"t": "true"}),
    )
    .unwrap();
    let combined = function_layout(
        &two,
        &[("A".into(), (usize::BITS / 2) as usize), ("B".into(), 2)],
    )
    .err()
    .unwrap();
    assert!(combined.contains("combined"), "{combined}");
}

#[test]
fn unary_functions_enumerate_lazily_in_the_historical_product_order() {
    assert_eq!(
        Assignments::new(&[usize::MAX, 2])
            .take(3)
            .collect::<Vec<_>>(),
        [vec![0, 0], vec![0, 1], vec![1, 0]]
    );
    assert_eq!(
        product(&[2, 3]),
        [
            vec![0, 0],
            vec![0, 1],
            vec![0, 2],
            vec![1, 0],
            vec![1, 1],
            vec![1, 2]
        ]
    );
    assert_eq!(product(&[]), [Vec::<usize>::new()]);
    assert!(product(&[2, 0]).is_empty());
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
