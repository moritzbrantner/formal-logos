use super::*;
use serde_json::json;

fn statement(id: &str, declaration: &str, definitions: &[&str]) -> Statement {
    Statement {
        id: id.into(),
        label: format!("label of {id}"),
        declaration: declaration.into(),
        definitions: definitions.iter().map(|d| (*d).to_owned()).collect(),
    }
}

fn vocab(module: &str, binders: &[&str], constants: &[&str]) -> Vocabulary {
    Vocabulary {
        module: module.into(),
        binders: binders.iter().map(|b| (*b).to_owned()).collect(),
        constants: constants.iter().map(|c| (*c).to_owned()).collect(),
    }
}

fn trial(premises: &[&str]) -> Trial {
    Trial {
        label: "t1".into(),
        target: "T".into(),
        premises: premises.iter().map(|p| (*p).to_owned()).collect(),
        weakening: None,
        sense_bridges: Vec::new(),
    }
}

fn graph(arguments: &[(&str, &[&str], &str)]) -> Graph {
    Graph {
        arguments: arguments
            .iter()
            .map(|(id, premises, conclusion)| Known {
                argument_id: (*id).into(),
                premises: premises.iter().map(|p| (*p).to_owned()).collect(),
                conclusion: (*conclusion).into(),
            })
            .collect(),
        rivals: BTreeMap::new(),
    }
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|i| (*i).to_owned()).collect()
}

// --- goal generation -------------------------------------------------------------

#[test]
fn vocabulary_export_drops_the_declaration_itself() {
    let parsed = parse_vocabulary(&json!([
        {"declaration": "M.P", "module": "M", "binders": ["B", "R"], "constants": ["M.P", "M.Q"]},
        {"declaration": "M.Bad", "error": "unknown declaration"}
    ]))
    .unwrap();
    assert_eq!(parsed.len(), 1);
    assert_eq!(parsed["M.P"], vocab("M", &["B", "R"], &["M.Q"]));
}

#[test]
fn transitive_constants_follow_mentioned_definitions() {
    let mut vocabulary = BTreeMap::new();
    vocabulary.insert("A".to_owned(), vocab("M", &[], &["B"]));
    vocabulary.insert("B".to_owned(), vocab("M", &[], &["C", "A"]));
    vocabulary.insert("C".to_owned(), vocab("M", &[], &[]));
    let closed = transitive_constants(&vocabulary);
    assert_eq!(closed["A"], set(&["B", "C"]));
    assert_eq!(closed["C"], set(&[]));
}

#[test]
fn command_line_names_declarations_and_quotes_the_configuration() {
    let mut statements = BTreeMap::new();
    statements.insert("T".to_owned(), statement("T", "M.Target", &[]));
    statements.insert("P".to_owned(), statement("P", "TruthCore.M.Premise", &[]));
    let tags = tags_of(
        &[json!({"term_label": "CAUSE", "senses": [
            {"id": "s1", "label": "CAUSE_1", "lean_parameters": [{"declaration": "TruthCore.M.Premise", "parameter": "CausesIn"}]}
        ]})],
        &[],
    );
    let line = command_line(
        &trial(&["P"]),
        &statements,
        5000,
        Some("/bin/zip"),
        &tags,
        true,
    );
    assert_eq!(
        line,
        r#"#discover "t1" 5000 "/bin/zip" "{\"bridges\":true,\"tags\":[[\"TruthCore.M.Premise\",\"CausesIn\",\"s1\"]]}" M.Target from TruthCore.M.Premise"#
    );
}

#[test]
fn scratch_hoists_imports_and_lifts_the_command_heartbeat_cap() {
    let text = scratch_text(
        "import Lean\nimport Duper\n/-! doc -/\nnamespace Discover\nend Discover\n",
        &set(&["TruthCore.A"]),
        &["#discover \"t1\" 1 \"\" \"{}\" A from B".into()],
    );
    let imports: Vec<&str> = text
        .lines()
        .take_while(|l| l.starts_with("import "))
        .collect();
    assert_eq!(
        imports,
        ["import Duper", "import Lean", "import TruthCore.A"]
    );
    assert!(text.contains("prove_sweep_probe"));
    assert!(text.contains("namespace Discover"));
    let cap = text.find("set_option maxHeartbeats 0").unwrap();
    assert!(cap < text.find("#discover \"t1\"").unwrap());
    assert_eq!(text.matches("import ").count(), 3);
}

#[test]
fn theorem_text_delta_expands_then_calls_duper() {
    let outcome = json!({"signature": "(h : P) : Q", "unfold": ["M.P", "M.Q"]});
    assert_eq!(
        theorem_text("discovered1", &outcome, 7000),
        "set_option maxHeartbeats 7000 in\ntheorem discovered1 (h : P) : Q :=\n  by\n    delta M.P M.Q at *\n    duper [*]\n"
    );
    let bare = json!({"signature": ": Q", "unfold": []});
    assert_eq!(proof_text(&bare), "by\n  duper [*]");
}

// --- retrieval ---------------------------------------------------------------------

#[test]
fn ranking_requires_shared_parameters_and_prefers_a_fitting_candidate() {
    let target = statement("T", "M.Target", &["D1"]);
    let fitting = statement("A", "M.A", &[]);
    let loose = statement("B", "N.B", &[]);
    let foreign = statement("C", "N.C", &[]);
    let same = statement("S", "M.Target", &[]);
    let mut vocabulary = BTreeMap::new();
    vocabulary.insert(
        "M.Target".into(),
        vocab("M", &["B", "h", "R"], &["M.H", "M.F"]),
    );
    vocabulary.insert("M.A".into(), vocab("M", &["B", "h"], &["M.H"]));
    vocabulary.insert(
        "N.B".into(),
        vocab("N", &["B", "x", "y", "z"], &["M.H", "N.X", "N.Y"]),
    );
    vocabulary.insert("N.C".into(), vocab("N", &["Q"], &["M.H"]));
    let pool = [&fitting, &loose, &foreign, &same];
    let ranked = rank(&target, &pool, &vocabulary, &BTreeMap::new(), 10);
    let ids: Vec<&str> = ranked.iter().map(|c| c.id.as_str()).collect();
    assert_eq!(
        ids,
        ["A", "B"],
        "no shared parameter (C) and the target's own declaration (S) are excluded"
    );
    assert_eq!(
        rank(&target, &pool, &vocabulary, &BTreeMap::new(), 1).len(),
        1
    );
}

#[test]
fn strength_siblings_rank_first() {
    let target = statement("T", "M.Target", &[]);
    let a = statement("A", "M.A", &[]);
    let b = statement("B", "M.B", &[]);
    let mut vocabulary = BTreeMap::new();
    vocabulary.insert("M.Target".into(), vocab("M", &["B"], &["M.H"]));
    vocabulary.insert("M.A".into(), vocab("M", &["B"], &["M.H"]));
    vocabulary.insert("M.B".into(), vocab("M", &["B"], &["M.H"]));
    let mut weaker = BTreeMap::new();
    weaker.insert("B".to_owned(), set(&["T"]));
    let ranked = rank(&target, &[&a, &b], &vocabulary, &weaker, 2);
    assert_eq!(ranked[0].id, "B");
}

#[test]
fn target_selectors_read_the_frontier_report() {
    let report = json!({
        "reaching_root_statements": ["A", "B"],
        "items": [{"statement_id": "A"}, {"statement_id": "C"}, {"statement_id": "A"}],
        "next_steps": {"leaves": [{"statement_id": "L"}]},
    });
    assert_eq!(selected_targets(&report, "open-root").unwrap(), ["A"]);
    assert_eq!(selected_targets(&report, "next-tests").unwrap(), ["L"]);
    assert!(selected_targets(&report, "everything").is_err());
}

// --- filters -------------------------------------------------------------------------

#[test]
fn graph_closure_finds_compositions_of_verified_arguments() {
    let g = graph(&[
        ("a1", &["A"], "B"),
        ("a2", &["B", "C"], "D"),
        ("a3", &["X"], "D"),
    ]);
    assert_eq!(
        g.derivation(&set(&["A", "C"]), "D"),
        Some(vec!["a1".into(), "a2".into()])
    );
    assert_eq!(g.derivation(&set(&["A"]), "D"), None);
    assert_eq!(g.derivation(&set(&["D"]), "D"), Some(Vec::new()));
}

fn closed_outcome() -> Value {
    json!({
        "label": "t1", "alone": null,
        "closed": {"prover": "duper", "used": [0, 2], "axioms": ["propext"]},
        "minimal": [0, 2],
        "proof": {"prover": "duper", "used": [0, 2], "axioms": ["propext", "Classical.choice", "Quot.sound"]},
        "vacuous": null, "probe": false, "witness": "all False",
        "signature": "(h0 : P) (h2 : R) : T", "unfold": [],
    })
}

#[test]
fn a_minimized_new_implication_is_a_discovery() {
    let senses = SenseCheck::empty();
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &closed_outcome(),
        &Graph::default(),
        &senses,
    );
    assert_eq!(f.kind, Kind::Discovery);
    assert_eq!(f.premises, ["P", "R"]);
    assert!(f.filters.is_empty());
}

#[test]
fn known_transcription_and_axiom_filters_reject() {
    let senses = SenseCheck::empty();
    let known = graph(&[("k", &["P", "R"], "T")]);
    let f = classify(&trial(&["P", "Q", "R"]), &closed_outcome(), &known, &senses);
    assert_eq!(f.kind, Kind::Filtered);
    assert_eq!(f.filters[0].0, "known");

    let mut probe = closed_outcome();
    probe["probe"] = json!(true);
    let f = classify(&trial(&["P", "Q", "R"]), &probe, &Graph::default(), &senses);
    assert_eq!(
        (f.kind, f.filters[0].0.as_str()),
        (Kind::Filtered, "transcription")
    );

    let mut native = closed_outcome();
    native["proof"]["axioms"] = json!(["propext", "Lean.ofReduceBool"]);
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &native,
        &Graph::default(),
        &senses,
    );
    assert_eq!(f.kind, Kind::Filtered);
    assert_eq!(
        f.filters[0],
        ("axioms".into(), "uses Lean.ofReduceBool".into())
    );
}

#[test]
fn a_missing_witness_flags_without_rejecting() {
    let mut outcome = closed_outcome();
    outcome["witness"] = Value::Null;
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &outcome,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.kind, Kind::Discovery);
    assert_eq!(f.filters[0].0, "witness");
}

#[test]
fn an_inconsistent_core_is_an_incompatibility_never_support() {
    let mut outcome = closed_outcome();
    outcome["vacuous"] = json!({"prover": "duper", "used": [0, 2], "axioms": []});
    outcome["vacuous_core"] = json!([2]);
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &outcome,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.kind, Kind::Incompatibility);
    assert_eq!(f.premises, ["R"]);
}

#[test]
fn an_incompatibility_with_a_forbidden_axiom_is_filtered() {
    let mut outcome = closed_outcome();
    outcome["vacuous"] = json!({"prover": "duper", "used": [0], "axioms": ["propext"]});
    outcome["vacuous_core"] = json!([0]);
    outcome["vacuous_core_proof"] =
        json!({"prover": "duper", "used": [0], "axioms": ["propext", "sorryAx"]});
    let f = classify(
        &trial(&["P"]),
        &outcome,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.kind, Kind::Filtered);
    assert!(
        f.filters
            .iter()
            .any(|(k, d)| k == "axioms" && d.contains("sorryAx"))
    );
}

#[test]
fn unresolved_errors_and_vocabulary_theorems() {
    let senses = SenseCheck::empty();
    let t = trial(&["P"]);
    let open = json!({"label": "t1", "alone": null, "closed": null});
    assert_eq!(
        classify(&t, &open, &Graph::default(), &senses).kind,
        Kind::Unresolved
    );
    let error = json!({"label": "t1", "error": "boom"});
    assert_eq!(
        classify(&t, &error, &Graph::default(), &senses).kind,
        Kind::Error
    );
    let alone = json!({"label": "t1", "alone": {"prover": "duper", "used": [], "axioms": []}});
    assert_eq!(
        classify(&t, &alone, &Graph::default(), &senses).kind,
        Kind::VocabularyTheorem
    );
    let atp = json!({"label": "t1", "alone": null, "closed": {"prover": "auto+zipperposition", "used": [0], "axioms": []},
                     "reconstruction": "Duper did not reprove"});
    let f = classify(&t, &atp, &Graph::default(), &senses);
    assert_eq!(
        (f.kind, f.filters[0].0.as_str()),
        (Kind::Filtered, "reconstruction")
    );
}

// --- report parsing ------------------------------------------------------------------

#[test]
fn outcomes_parse_from_lean_info_lines_and_the_log() {
    let output = "/tmp/x.lean:9:0: info: DISCOVER-JSON {\"label\":\"t2\",\"closed\":null}\n\
                  DISCOVER-JSON {\"label\":\"t1\",\"alone\":null}\nnoise\nDISCOVER-JSON {broken\n";
    let parsed = parse_outcomes(output);
    assert_eq!(parsed.keys().collect::<Vec<_>>(), ["t1", "t2"]);
    assert!(parsed["t2"]["closed"].is_null());
}

#[test]
fn certification_reads_errors_and_axioms_per_theorem() {
    let (text, ranges) = certification_text(
        &set(&["TruthCore.A"]),
        &[
            (
                "discovered1".into(),
                "theorem discovered1 : True := by\n  duper [*]\n".into(),
            ),
            (
                "discovered2".into(),
                "theorem discovered2 : True := by\n  duper [*]\n".into(),
            ),
        ],
    );
    assert!(text.starts_with("import TruthCore.A\nimport Duper\n"));
    let (_, s1, e1) = ranges[0].clone();
    let (_, s2, _) = ranges[1].clone();
    let message = |severity: &str, line, data: &str| prove_sweep::Message {
        severity: severity.into(),
        line,
        data: data.into(),
    };
    let verdicts = parse_certification(
        &[
            message(
                "information",
                e1 - 1,
                "'discovered1' depends on axioms: [propext, Classical.choice, Quot.sound]",
            ),
            message("error", s2, "duper failed\nmore"),
        ],
        &ranges,
    );
    assert_eq!(
        verdicts["discovered1"],
        Ok(vec![
            "propext".into(),
            "Classical.choice".into(),
            "Quot.sound".into()
        ])
    );
    assert_eq!(verdicts["discovered2"], Err("duper failed".into()));
    assert!(s1 < e1);
}

#[test]
fn missing_bridges_rank_by_targets_unlocked() {
    let bridge = |from: &str| json!({"from": from, "to": "M.T.q", "fixed": ["esse"], "text": format!("∀ x, {from} x → q x"), "used": [0], "domain_identified_by_name": if from == "M.P.a" { json!(["X.B = M.T.B"]) } else { json!([]) }});
    let finding = |label: &str, target: &str, bridges: Vec<Value>| Finding {
        trial: Trial {
            label: label.into(),
            target: target.into(),
            ..trial(&["P"])
        },
        kind: Kind::Unresolved,
        premises: Vec::new(),
        filters: Vec::new(),
        outcome: json!({"bridges": bridges}),
        certified: None,
    };
    let rows = rank_bridges(&[
        finding("t1", "T1", vec![bridge("M.P.a"), bridge("M.P.b")]),
        finding("t2", "T2", vec![bridge("M.P.b")]),
        finding("t3", "T2", vec![bridge("M.P.b")]),
    ]);
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].from, "M.P.b");
    assert_eq!(rows[0].targets, set(&["T1", "T2"]));
    assert_eq!(rows[0].goals, ["t1", "t2", "t3"]);
    assert_eq!(rows[0].premises, set(&["P"]));
    assert_eq!(bridge_json(&rows[1])["unlocks_targets"], json!(["T1"]));
    assert_eq!(
        bridge_json(&rows[1])["domain_identified_by_name"],
        json!(true)
    );
    assert_eq!(
        bridge_json(&rows[0])["domain_identified_by_name"],
        json!(false)
    );
}

#[test]
fn parameter_tags_are_read_tolerantly_and_give_bridge_statements() {
    let disambiguations = [
        json!({"term_label": "CAUSE", "senses": [
            {"id": "s1", "label": "CAUSE_1", "lean_parameters": [{"declaration": "TruthCore.M.A", "parameter": "CausesIn"}]},
            {"id": "s2", "label": "CAUSE_2", "lean_parameters": [
                {"declaration": "TruthCore.N.B", "parameter": "Causes", "arguments": ["_", "_", "esse"]},
                {"declaration": "TruthCore.N.B", "parameter": "Grounds"}]},
            {"id": "s3", "label": "CAUSE_3"}
        ]}),
        json!({"term_label": "OTHER"}),
    ];
    let arguments = [
        json!({"sense_bridges": [{"term": "CAUSE", "from": "s2", "to": "s1", "statement_id": "BRIDGE"}]}),
    ];
    let tags = tags_of(&disambiguations, &arguments);
    assert_eq!(tags.tags.len(), 3);
    // A partial application keeps its fixed arguments in the key; Discover.lean
    // never identifies binders by such a key (see the binding fixture test).
    assert_eq!(
        tags.for_declarations(&["TruthCore.M.A", "TruthCore.N.B"]),
        vec![
            [
                "TruthCore.M.A".to_owned(),
                "CausesIn".to_owned(),
                "s1".to_owned()
            ],
            [
                "TruthCore.N.B".to_owned(),
                "Causes".to_owned(),
                "s2|_ _ esse".to_owned()
            ],
            [
                "TruthCore.N.B".to_owned(),
                "Grounds".to_owned(),
                "s2".to_owned()
            ],
        ]
    );
    assert_eq!(
        tags.bridge_statements("TruthCore.M.A", "TruthCore.N.B"),
        ["BRIDGE"]
    );
    assert!(
        tags.bridge_statements("TruthCore.M.A", "TruthCore.M.A")
            .is_empty()
    );
}

#[test]
fn spec_draft_lists_each_discovery_with_unique_labels() {
    let mut statements = BTreeMap::new();
    statements.insert("T".to_owned(), statement("T", "M.Target", &[]));
    statements.insert("P".to_owned(), statement("P", "M.P", &[]));
    let mut f = classify(
        &trial(&["P", "Q", "R"]),
        &closed_outcome(),
        &Graph::default(),
        &SenseCheck::empty(),
    );
    f.premises = vec!["P".into()];
    let spec = render_spec(
        "TruthCore.Results.Discover.Run",
        &[&f, &f],
        &statements,
        &SenseCheck::empty(),
        "2026-11-19",
    );
    assert_eq!(spec.matches("\n[[argument]]\n").count(), 2);
    assert!(spec.contains("premises = [\"P\"]\nconclusion = \"T\"\n"));
    assert!(spec.contains("theorem = \"discovered1\""));
    assert!(spec.contains("theorem = \"discovered2\""));
    assert!(spec.contains("label = \"label of T (discovered derivation)\""));
    assert!(spec.contains("label = \"label of T (discovered derivation 2)\""));
    assert!(spec.contains("results = \"TruthCore.Results.Discover.Run\""));
    assert!(spec.contains("axioms = [\"propext\", \"Classical.choice\", \"Quot.sound\"]"));
}

#[test]
fn a_refuted_antecedent_flags_vacuous_truth_without_rejecting() {
    let mut outcome = closed_outcome();
    outcome["antecedent_refuted"] = json!(true);
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &outcome,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.kind, Kind::Discovery);
    assert_eq!(f.filters[0].0, "vacuous_target");
}

#[test]
fn an_incompatibility_of_recorded_rivals_is_known() {
    let mut outcome = closed_outcome();
    outcome["vacuous"] = json!({"prover": "duper", "used": [0, 2], "axioms": []});
    outcome["vacuous_core"] = json!([0, 2]);
    let mut g = Graph::default();
    g.rivals.insert("R".into(), set(&["P"]));
    let f = classify(&trial(&["P", "Q", "R"]), &outcome, &g, &SenseCheck::empty());
    assert_eq!((f.kind, f.filters[0].0.as_str()), (Kind::Filtered, "known"));
}

#[test]
fn no_axiom_is_exempt_by_name() {
    // An axiom named like a search auxiliary is still outside the allowance
    // (Codex P2 on #1796): only propext, Classical.choice and Quot.sound pass.
    let axioms = vec![
        "propext".to_owned(),
        "Classical.choice".to_owned(),
        "Quot.sound".to_owned(),
        "_discoverAssumption".to_owned(),
        "_discover._@._stdin._hyg.3".to_owned(),
        "sorryAx".to_owned(),
    ];
    assert_eq!(
        forbidden_axioms(&axioms),
        [
            "_discoverAssumption",
            "_discover._@._stdin._hyg.3",
            "sorryAx"
        ]
    );
}

fn tags_of(disambiguations: &[Value], arguments: &[Value]) -> SenseTags {
    let tags = parameter_tags::ParameterTags::read(
        disambiguations
            .iter()
            .map(|v| ("fixture.json", v.as_object().unwrap())),
    )
    .unwrap();
    SenseTags::from_parts(&tags, arguments.iter().map(|v| v.as_object().unwrap()))
}

#[test]
fn same_module_bindings_pass_and_cross_module_name_identifications_are_rejected() {
    let senses = SenseCheck::empty();
    let mut same = closed_outcome();
    same["domain_identified_by_name"] = json!([]);
    let f = classify(&trial(&["P", "Q", "R"]), &same, &Graph::default(), &senses);
    assert_eq!(f.kind, Kind::Discovery);
    assert!(f.filters.is_empty());

    let mut cross = closed_outcome();
    cross["domain_identified_by_name"] = json!(["N.B.B = M.T.B"]);
    let f = classify(&trial(&["P", "Q", "R"]), &cross, &Graph::default(), &senses);
    assert_eq!(f.kind, Kind::Filtered);
    assert_eq!(f.filters[0].0, "domain_by_name");
    assert!(f.filters[0].1.contains("N.B.B = M.T.B"));

    let mut inconsistent = cross.clone();
    inconsistent["vacuous"] = json!({"prover": "duper", "used": [0], "axioms": []});
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &inconsistent,
        &Graph::default(),
        &senses,
    );
    assert_eq!(
        (f.kind, f.filters[0].0.as_str()),
        (Kind::Filtered, "domain_by_name")
    );
}

#[test]
fn solution_draft_puts_the_option_before_the_doc_comment() {
    let mut statements = BTreeMap::new();
    statements.insert("T".to_owned(), statement("T", "TruthCore.M.Target", &[]));
    statements.insert("P".to_owned(), statement("P", "TruthCore.M.P", &[]));
    let mut f = classify(
        &trial(&["P", "Q", "R"]),
        &closed_outcome(),
        &Graph::default(),
        &SenseCheck::empty(),
    );
    f.premises = vec!["P".into()];
    let text = render_solution(
        "TruthCore.Results.Discover.Run",
        &[&f],
        &statements,
        &BTreeMap::new(),
        5000,
    );
    assert!(
        text.contains("set_option maxHeartbeats 5000 in\n/-- label of T -/\ntheorem discovered1 ")
    );
}

#[test]
fn an_original_is_suppressed_only_by_a_certified_weakening() {
    let finding = |label: &str, of: Option<&str>, kind: Kind| Finding {
        trial: Trial {
            label: label.into(),
            weakening: of.map(|o| ("P".to_owned(), "W".to_owned(), o.to_owned())),
            ..trial(&["P"])
        },
        kind,
        premises: vec!["P".into()],
        filters: Vec::new(),
        outcome: closed_outcome(),
        certified: Some(Ok(vec!["propext".into()])),
    };
    // A weakening whose certification was forced to fail.
    let mut rejected = finding("t2w1", Some("t2"), Kind::Filtered);
    rejected.certified = Some(Err("unknown identifier".into()));
    rejected.filters.push((
        "certification".into(),
        "theorem text rejected: unknown identifier".into(),
    ));
    let mut findings = vec![
        finding("t1", None, Kind::Discovery),
        finding("t1w1", Some("t1"), Kind::Discovery),
        finding("t2", None, Kind::Discovery),
        rejected,
    ];
    suppress_weakened(&mut findings);
    assert_eq!(findings[0].kind, Kind::Filtered);
    assert_eq!(findings[0].filters[0].0, "weakened");
    assert_eq!(findings[1].kind, Kind::Discovery);
    // The weakening failed certification: its certified original stays a
    // discovery, records why, and reaches the spec draft.
    assert_eq!(findings[2].kind, Kind::Discovery);
    assert_eq!(findings[2].filters[0].0, "weakening_rejected");
    assert!(findings[2].filters[0].1.contains("unknown identifier"));
    let mut statements = BTreeMap::new();
    statements.insert("T".to_owned(), statement("T", "M.Target", &[]));
    statements.insert("P".to_owned(), statement("P", "M.P", &[]));
    let chosen: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.kind == Kind::Discovery)
        .collect();
    assert_eq!(
        chosen
            .iter()
            .map(|f| f.trial.label.as_str())
            .collect::<Vec<_>>(),
        ["t1w1", "t2"]
    );
    let spec = render_spec(
        "TruthCore.Results.Discover.Run",
        &chosen,
        &statements,
        &SenseCheck::empty(),
        "2026-11-20",
    );
    assert_eq!(spec.matches("\n[[argument]]\n").count(), 2);
}
