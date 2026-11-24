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
        ..Vocabulary::default()
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
    let ranked = rank(
        &target,
        &pool,
        &vocabulary,
        &BTreeMap::new(),
        &SenseTags::default(),
        10,
    );
    let ids: Vec<&str> = ranked.iter().map(|c| c.id.as_str()).collect();
    assert_eq!(
        ids,
        ["A", "B"],
        "no shared parameter (C) and the target's own declaration (S) are excluded"
    );
    assert_eq!(
        rank(
            &target,
            &pool,
            &vocabulary,
            &BTreeMap::new(),
            &SenseTags::default(),
            1
        )
        .len(),
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
    let ranked = rank(
        &target,
        &[&a, &b],
        &vocabulary,
        &weaker,
        &SenseTags::default(),
        2,
    );
    assert_eq!(ranked[0].id, "B");
}

/// Two direct anchors, a companion shared by both, another companion of B,
/// and a third-hop-only neighbour. Aliases must not consume backfill slots.
fn backfill_fixture() -> (Statement, Vec<Statement>, BTreeMap<String, Vocabulary>) {
    let target = statement("T", "M.Target", &["goal"]);
    let pool = vec![
        target.clone(),
        statement("TargetAlias", "M.Target", &["goal"]),
        statement("A", "M.A", &["goal", "left"]),
        statement("B", "M.B", &["goal", "right"]),
        statement("C", "M.C", &["left", "right", "third"]),
        statement("CAlias", "M.C", &["left", "right", "third"]),
        statement("E", "M.E", &["right"]),
        statement("X", "M.X", &["third"]),
    ];
    let vocabulary = pool
        .iter()
        .map(|s| (s.declaration.clone(), vocab("M", &["x"], &[])))
        .collect();
    (target, pool, vocabulary)
}

#[test]
fn ranking_backfills_companions_without_a_third_hop_or_target_alias() {
    let (target, pool, vocabulary) = backfill_fixture();
    let ranked = rank(
        &target,
        &pool.iter().collect::<Vec<_>>(),
        &vocabulary,
        &BTreeMap::new(),
        &SenseTags::default(),
        8,
    );
    let ids: Vec<_> = ranked.iter().map(|c| c.id.as_str()).collect();
    assert_eq!(ids, ["A", "B", "C", "E"]);
    let reversed = rank(
        &target,
        &pool.iter().rev().collect::<Vec<_>>(),
        &vocabulary,
        &BTreeMap::new(),
        &SenseTags::default(),
        8,
    );
    assert_eq!(
        ranked, reversed,
        "pool iteration order is not a tie-breaker"
    );
}

#[test]
fn ranking_backfill_preserves_direct_scores_order_and_the_cap() {
    let (target, pool, vocabulary) = backfill_fixture();
    let retrieve = |limit| {
        rank(
            &target,
            &pool.iter().collect::<Vec<_>>(),
            &vocabulary,
            &BTreeMap::new(),
            &SenseTags::default(),
            limit,
        )
    };
    assert!(retrieve(0).is_empty());
    assert_eq!(retrieve(1)[0].id, "A");
    let direct = retrieve(2);
    assert_eq!(
        direct.iter().map(|c| c.id.as_str()).collect::<Vec<_>>(),
        ["A", "B"]
    );
    let expanded = retrieve(3);
    assert_eq!(expanded.len(), 3);
    assert_eq!(&expanded[..2], direct.as_slice());
    assert_eq!(expanded[2].id, "C");
}

#[test]
fn ranking_backfill_visits_original_anchors_in_direct_rank_order() {
    let (target, pool, vocabulary) = backfill_fixture();
    // E scores higher against B than C does against A, but B is the second
    // anchor. Backfill introduces no new cross-anchor scoring rule.
    let weaker = BTreeMap::from([("B".to_owned(), set(&["E"]))]);
    let ranked = rank(
        &target,
        &pool.iter().collect::<Vec<_>>(),
        &vocabulary,
        &weaker,
        &SenseTags::default(),
        3,
    );
    assert_eq!(
        ranked.iter().map(|c| c.id.as_str()).collect::<Vec<_>>(),
        ["A", "B", "C"]
    );
}

#[test]
fn ranking_backfill_stays_inside_the_supplied_pool() {
    let (target, pool, vocabulary) = backfill_fixture();
    // The vocabulary still describes the omitted companions. A pool or
    // module restriction must not be undone by following their definitions.
    let scoped: Vec<_> = pool
        .iter()
        .filter(|s| !["C", "CAlias", "E"].contains(&s.id.as_str()))
        .collect();
    let ranked = rank(
        &target,
        &scoped,
        &vocabulary,
        &BTreeMap::new(),
        &SenseTags::default(),
        8,
    );
    assert_eq!(
        ranked.iter().map(|c| c.id.as_str()).collect::<Vec<_>>(),
        ["A", "B"]
    );
}

#[test]
fn ranking_backfill_requires_an_original_direct_anchor() {
    let (mut target, pool, vocabulary) = backfill_fixture();
    target.definitions = set(&["unrelated"]);
    assert!(
        rank(
            &target,
            &pool.iter().collect::<Vec<_>>(),
            &vocabulary,
            &BTreeMap::new(),
            &SenseTags::default(),
            8,
        )
        .is_empty()
    );
}

#[test]
fn ranking_backfill_does_not_admit_names_partial_tags_or_unfitting_binders() {
    let (target, mut pool, mut vocabulary) = backfill_fixture();
    for (id, declaration, definitions, binders) in [
        ("Homonym", "M.Homonym", vec![], vec!["x"]),
        ("Partial", "M.Partial", vec![], vec!["y"]),
        ("OtherSense", "M.OtherSense", vec![], vec!["y"]),
        ("Foreign", "M.Foreign", vec!["left"], vec!["z"]),
    ] {
        pool.push(statement(id, declaration, &definitions));
        vocabulary.insert(declaration.into(), vocab("M", &binders, &[]));
    }
    let tags = tagged(vec![
        tag("M.A", "x", &[], "left-sense"),
        tag("M.Partial", "y", &["fixed"], "left-sense"),
        tag("M.OtherSense", "y", &[], "different-sense"),
    ]);
    let ranked = rank(
        &target,
        &pool.iter().collect::<Vec<_>>(),
        &vocabulary,
        &BTreeMap::new(),
        &tags,
        8,
    );
    assert_eq!(
        ranked.iter().map(|c| c.id.as_str()).collect::<Vec<_>>(),
        ["A", "B", "C", "E"]
    );
}

#[test]
fn ranking_backfill_deduplicates_declarations_before_filling_the_cap() {
    let target = statement("T", "M.Target", &["goal"]);
    let pool = [
        statement("A", "M.A", &["goal", "left"]),
        statement("C", "M.C", &["left"]),
        statement("CAlias", "M.C", &["left"]),
        statement("D", "M.D", &["left"]),
        statement("E", "M.E", &["left"]),
    ];
    let vocabulary = pool
        .iter()
        .chain([&target])
        .map(|s| (s.declaration.clone(), vocab("M", &["x"], &[])))
        .collect();
    let ranked = rank(
        &target,
        &pool.iter().collect::<Vec<_>>(),
        &vocabulary,
        &BTreeMap::new(),
        &SenseTags::default(),
        4,
    );
    assert_eq!(
        ranked.iter().map(|c| c.id.as_str()).collect::<Vec<_>>(),
        ["A", "C", "D", "E"]
    );
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
    let bridge = |from: &str| json!({"from": from, "to": "M.T.q", "fixed": ["esse"], "text": format!("∀ x, {from} x → q x"), "used": [0], "assumed_binders": if from == "M.P.a" { json!(["esse"]) } else { json!([]) }, "domain_identified_by_name": if from == "M.P.a" { json!(["X.B = M.T.B"]) } else { json!([]) }});
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
    // The text report shows both qualifications of a qualified bridge, and
    // none for an unqualified one.
    assert_eq!(
        bridge_qualifications(&rows[1]),
        [
            "assumes an element no used statement introduces: esse",
            "identified across modules by name only (needs a sense tag or a bridge): X.B = M.T.B",
        ]
    );
    assert!(bridge_qualifications(&rows[0]).is_empty());
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

// --- noise filters (#1819) ---------------------------------------------------------

#[test]
fn vocabulary_export_reads_binder_types_and_structure_fields() {
    let parsed = parse_vocabulary(&json!([
        {"declaration": "M.P", "module": "M", "binders": ["W", "m"], "constants": [],
         "binder_types": ["", "M.Profile"], "binder_fields": [[], ["M.Ontic"]]},
        {"declaration": "M.Old", "module": "M", "binders": ["B"], "constants": []}
    ]))
    .unwrap();
    assert_eq!(parsed["M.P"].binder_types, ["", "M.Profile"]);
    assert_eq!(parsed["M.P"].binder_fields[1], set(&["M.Ontic"]));
    // An export without the fields (older exporter) still parses.
    assert!(parsed["M.Old"].binder_fields.is_empty());
}

#[test]
fn a_structure_parameter_projecting_to_a_target_parameter_fits() {
    // OnticTSchemaValid (o : Ontic W B) and OnticFrameKT (m : Profile W B),
    // whose `m.ontic : Ontic W B`: the frame premise fits through `m.ontic`.
    let target = statement("T", "M.TSchema", &[]);
    let frame = statement("F", "N.FrameKT", &[]);
    let unrelated = statement("U", "N.Other", &[]);
    let mut vocabulary = BTreeMap::new();
    let mut goal = vocab("M", &["W", "B", "o"], &["M.Ontic", "M.Valid"]);
    goal.binder_types = vec!["".into(), "".into(), "M.Ontic".into()];
    goal.binder_fields = vec![set(&[]), set(&[]), set(&[])];
    vocabulary.insert("M.TSchema".into(), goal);
    let mut kt = vocab("N", &["W", "B", "m"], &["M.Ontic", "N.Profile"]);
    kt.binder_types = vec!["".into(), "".into(), "N.Profile".into()];
    kt.binder_fields = vec![set(&[]), set(&[]), set(&["M.Ontic"])];
    vocabulary.insert("N.FrameKT".into(), kt);
    let mut other = vocab("N", &["W", "B", "m"], &["M.Ontic", "N.Profile"]);
    other.binder_types = vec!["".into(), "".into(), "N.Other".into()];
    other.binder_fields = vec![set(&[]), set(&[]), set(&["N.Unrelated"])];
    vocabulary.insert("N.Other".into(), other);
    let ranked = rank(
        &target,
        &[&unrelated, &frame],
        &vocabulary,
        &BTreeMap::new(),
        &SenseTags::default(),
        10,
    );
    assert_eq!(ranked[0].id, "F");
    assert!(ranked[0].score > ranked[1].score);
    // A projection alone (no shared parameter name) still admits a candidate.
    let mut lone = vocab("N", &["m"], &["M.Ontic"]);
    lone.binder_types = vec!["N.Profile".into()];
    lone.binder_fields = vec![set(&["M.Ontic"])];
    vocabulary.insert("N.Lone".into(), lone);
    let lonely = statement("L", "N.Lone", &[]);
    assert_eq!(
        rank(
            &target,
            &[&lonely],
            &vocabulary,
            &BTreeMap::new(),
            &SenseTags::default(),
            10
        )
        .len(),
        1
    );
}

fn inconsistent(core: Value) -> Value {
    let mut outcome = closed_outcome();
    outcome["vacuous"] = json!({"prover": "duper", "used": [0, 2], "axioms": []});
    outcome["vacuous_core"] = core;
    outcome
}

#[test]
fn a_literal_negation_core_is_filtered_never_an_incompatibility() {
    // ActNotPriorInTime F := ¬ ActPriorInTime F: the core {P, ¬P}.
    let mut outcome = inconsistent(json!([0, 2]));
    outcome["literal_negation"] = json!([0, 2]);
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &outcome,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.kind, Kind::Filtered);
    assert_eq!(f.filters.len(), 1);
    assert_eq!(f.filters[0].0, "literal_negation");
    assert!(f.filters[0].1.starts_with("R unfolds to the negation of P"));
    assert_eq!(f.premises, ["P", "R"]);
}

#[test]
fn literal_negation_takes_precedence_over_recorded_rivals() {
    // 5fc7a6f9 and 4640876a: recorded rivals, and one is the other's negation.
    let mut outcome = inconsistent(json!([0, 2]));
    outcome["literal_negation"] = json!([0, 2]);
    let mut g = Graph::default();
    g.rivals.insert("R".into(), set(&["P"]));
    g.rivals.insert("P".into(), set(&["R"]));
    let f = classify(&trial(&["P", "Q", "R"]), &outcome, &g, &SenseCheck::empty());
    let names: Vec<&str> = f.filters.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!((f.kind, names), (Kind::Filtered, vec!["literal_negation"]));
}

#[test]
fn a_genuine_incompatibility_is_still_reported() {
    // Negative control: an inconsistent core with no literal negation (the
    // Lean side found none) stays an incompatibility.
    let mut outcome = inconsistent(json!([0, 2]));
    outcome["literal_negation"] = Value::Null;
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &outcome,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.kind, Kind::Incompatibility);
    assert!(f.filters.is_empty());
}

#[test]
fn a_projection_binding_is_flagged_and_named_in_the_spec() {
    let mut outcome = closed_outcome();
    outcome["projection"] = json!({
        "binder": "M.TSchema.o", "bound_to": "N.FrameKT.m.ontic",
        "structure_binder": "N.FrameKT.m", "field": "ontic"
    });
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &outcome,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(
        f.kind,
        Kind::Discovery,
        "the flag informs, it does not reject"
    );
    assert_eq!(f.filters[0].0, "projection_binding");
    assert!(
        f.filters[0]
            .1
            .contains("M.TSchema.o is bound to the projection N.FrameKT.m.ontic")
    );
    let mut statements = BTreeMap::new();
    for id in ["T", "P", "R"] {
        statements.insert(id.to_owned(), statement(id, &format!("M.{id}"), &[]));
    }
    let spec = render_spec(
        "TruthCore.Results.Discover.Run",
        &[&f],
        &statements,
        &SenseCheck::empty(),
        "2026-11-22",
    );
    assert!(spec.contains("Explicit binding choice: the target binder M.TSchema.o"));
    // Without a projection there is no flag.
    let plain = classify(
        &trial(&["P", "Q", "R"]),
        &closed_outcome(),
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert!(plain.filters.iter().all(|(n, _)| n != "projection_binding"));
}

#[test]
fn a_conjunctive_bridge_replaces_single_conjunct_bridges() {
    let conjunctive = json!({
        "from": "M.T.Simple ∧ M.T.Eternal", "to": "M.T.σ.IsGod", "fixed": [],
        "conjunctive": true, "replaces_single_conjuncts": ["M.T.Simple", "M.T.Eternal"],
        "text": "∀ g, Simple g → Eternal g → IsGod σ g", "used": [0],
        "assumed_binders": [], "domain_identified_by_name": []
    });
    let finding = Finding {
        trial: trial(&["P"]),
        kind: Kind::Unresolved,
        premises: Vec::new(),
        filters: Vec::new(),
        outcome: json!({"bridges": [conjunctive]}),
        certified: None,
    };
    let rows = rank_bridges(&[finding]);
    assert_eq!(rows.len(), 1);
    assert!(rows[0].conjunctive);
    assert_eq!(bridge_json(&rows[0])["conjunctive"], json!(true));
    assert_eq!(
        bridge_notes(&rows[0]),
        [
            "conjunctive antecedent; single-conjunct bridges from M.T.Eternal, M.T.Simple were not tried (each is stronger and uninformative)"
        ]
    );
}

#[test]
fn ambiguous_or_unused_projections_are_rejected() {
    let choice = json!({
        "binder": "M.T.x", "bound_to": "M.P.t.fst", "structure_binder": "M.P.t",
        "field": "fst", "ambiguous": true, "alternatives": ["M.P.t.fst", "M.P.t.snd"]
    });
    let mut outcome = closed_outcome();
    outcome["projection"] = choice.clone();
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &outcome,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.kind, Kind::Filtered);
    let names: Vec<&str> = f.filters.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["projection_ambiguous"]);
    assert!(f.filters[0].1.contains("M.P.t.fst, M.P.t.snd"));

    let mut unused = closed_outcome();
    unused["projection"] = json!({"binder": "M.T.x", "bound_to": "M.P.b.val",
        "structure_binder": "M.P.b", "field": "val", "ambiguous": false, "alternatives": ["M.P.b.val"]});
    unused["projection_unused"] = json!(true);
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &unused,
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.kind, Kind::Filtered);
    assert_eq!(f.filters[0].0, "projection_unused");
    assert!(f.filters.iter().all(|(n, _)| n != "projection_binding"));
}

#[test]
fn proved_excludes_goals_closed_by_a_literal_negation() {
    let mut literal = inconsistent(json!([0, 2]));
    literal["literal_negation"] = json!([0, 2]);
    let findings = [
        classify(
            &trial(&["P", "Q", "R"]),
            &literal,
            &Graph::default(),
            &SenseCheck::empty(),
        ),
        classify(
            &trial(&["P", "Q", "R"]),
            &closed_outcome(),
            &Graph::default(),
            &SenseCheck::empty(),
        ),
        classify(
            &trial(&["P"]),
            &json!({"closed": null, "alone": null}),
            &Graph::default(),
            &SenseCheck::empty(),
        ),
    ];
    assert_eq!(proved_count(&findings), 1);
}

#[test]
fn single_conjunct_bridges_rank_last_and_are_noted() {
    let row = |from: &str, single: bool| {
        json!({"from": from, "to": "M.P.R", "fixed": [], "text": format!("∀ g, {from} g → R g"),
               "used": [0], "assumed_binders": [], "domain_identified_by_name": [],
               "single_conjunct": single})
    };
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
    // The single-conjunct bridge unlocks more targets but still ranks last.
    let rows = rank_bridges(&[
        finding("t1", "T1", vec![row("M.T.A2", true)]),
        finding("t2", "T2", vec![row("M.T.A2", true), row("M.T.X", false)]),
    ]);
    assert_eq!(rows[0].from, "M.T.X");
    assert!(rows[1].single_conjunct);
    assert_eq!(bridge_json(&rows[1])["single_conjunct"], json!(true));
    assert!(bridge_notes(&rows[1])[0].contains("no conjunctive bridge passed"));
}

// --- excluded middle as implicit classical logic (#1845) ---------------------------

const EM: &str = "ee4ab504-c8fe-59bc-bc96-7cbeefed6410";

#[test]
fn a_classical_proof_matches_a_known_argument_that_lists_excluded_middle() {
    let senses = SenseCheck::empty();
    // The verified argument lists excluded middle explicitly; Duper's classical
    // proof (`Classical.choice`) used the same premises without it.
    let known = graph(&[("k", &["P", "R", EM], "T")]);
    let f = classify(&trial(&["P", "Q", "R"]), &closed_outcome(), &known, &senses);
    assert_eq!(f.kind, Kind::Filtered);
    assert_eq!(f.filters[0].0, "known");
    assert!(
        f.filters[0]
            .1
            .contains("composes from verified arguments k")
    );
    assert!(f.filters[0].1.contains(EM), "{}", f.filters[0].1);
    let flag = f
        .filters
        .iter()
        .find(|(n, _)| n == "implicit_excluded_middle")
        .expect("the report says the classical proof used excluded middle");
    assert!(flag.1.contains("Classical.choice"));
    // Through a composition too: excluded middle at an inner step.
    let chained = graph(&[("k1", &["P", EM], "M"), ("k2", &["M", "R"], "T")]);
    let f = classify(
        &trial(&["P", "Q", "R"]),
        &closed_outcome(),
        &chained,
        &senses,
    );
    assert_eq!(f.filters[0].0, "known");
    assert!(f.filters[0].1.contains("k1, k2"), "{}", f.filters[0].1);
}

#[test]
fn excluded_middle_matching_does_not_hide_a_new_discovery() {
    let senses = SenseCheck::empty();
    // The known argument needs `S` besides excluded middle; the proof has only
    // `P` and `R`: a genuinely new bundle stays a discovery.
    let known = graph(&[("k", &["P", "S", EM], "T")]);
    let f = classify(&trial(&["P", "Q", "R"]), &closed_outcome(), &known, &senses);
    assert_eq!(f.kind, Kind::Discovery);
    assert!(f.filters.is_empty(), "{:?}", f.filters);
    // A constructive proof (no `Classical.choice`) does not have excluded
    // middle: the argument that lists it does not match, the proof is new.
    let mut constructive = closed_outcome();
    constructive["proof"]["axioms"] = json!(["propext"]);
    let known = graph(&[("k", &["P", "R", EM], "T")]);
    let f = classify(&trial(&["P", "Q", "R"]), &constructive, &known, &senses);
    assert_eq!(f.kind, Kind::Discovery);
    assert!(f.filters.is_empty(), "{:?}", f.filters);
    // An argument without excluded middle matches as before, unflagged.
    let plain = graph(&[("k", &["P", "R"], "T")]);
    let f = classify(&trial(&["P", "Q", "R"]), &closed_outcome(), &plain, &senses);
    assert_eq!(f.filters.len(), 1);
    assert_eq!(f.filters[0].0, "known");
}

#[test]
fn a_classical_proof_of_excluded_middle_itself_is_known_without_an_empty_path() {
    let mut t = trial(&["P", "Q", "R"]);
    t.target = EM.into();
    let f = classify(
        &t,
        &closed_outcome(),
        &Graph::default(),
        &SenseCheck::empty(),
    );
    assert_eq!(f.filters[0].0, "known");
    assert!(
        f.filters[0].1.starts_with("the target is ee4ab504"),
        "{}",
        f.filters[0].1
    );
    assert!(!f.filters[0].1.contains("arguments ,"));
}

#[test]
fn background_derivation_reports_the_granted_statements() {
    let g = graph(&[("a1", &["A", EM], "B"), ("a2", &["B"], "C")]);
    let em = set(&[EM]);
    assert_eq!(g.derivation(&set(&["A"]), "C"), None);
    assert_eq!(
        g.derivation_with(&set(&["A"]), &em, "C"),
        Some((vec!["a1".into(), "a2".into()], set(&[EM])))
    );
    // Listed among the found premises, excluded middle is not "granted".
    assert_eq!(
        g.derivation_with(&set(&["A", EM]), &em, "C"),
        Some((vec!["a1".into(), "a2".into()], BTreeSet::new()))
    );
}

// --- retrieval by authored sense tags and projection-only binders (#1845) ----------

fn tag(
    declaration: &str,
    parameter: &str,
    arguments: &[&str],
    sense: &str,
) -> parameter_tags::ParameterTag {
    parameter_tags::ParameterTag {
        sense_id: sense.into(),
        sense_label: sense.to_uppercase(),
        term: "TERM".into(),
        definition_id: format!("def-{sense}"),
        disambiguation_id: "disamb".into(),
        parameter: parameter_tags::TaggedParameter {
            declaration: declaration.into(),
            parameter: parameter.into(),
            arguments: arguments.iter().map(|a| (*a).to_owned()).collect(),
        },
    }
}

fn tagged(tags: Vec<parameter_tags::ParameterTag>) -> SenseTags {
    SenseTags {
        tags,
        bridges: Vec::new(),
    }
}

#[test]
fn a_shared_authored_sense_admits_a_candidate_without_shared_constants() {
    // `MostTrueIsMostBeing (Being Respect : Type) (MoreIn …)` against Aristotle's
    // `AsToBeingSoToTruth (Entity Respect : Type) (MoreIn …)`: relation binders
    // mention no constant, so only their tags relate them.
    let target = statement("T", "M.Target", &[]);
    let aristotle = statement("A", "N.Aristotle", &[]);
    let mut vocabulary = BTreeMap::new();
    vocabulary.insert("M.Target".into(), vocab("M", &["Being", "MoreIn"], &[]));
    vocabulary.insert("N.Aristotle".into(), vocab("N", &["Entity", "Rel"], &[]));
    let tags = tagged(vec![
        tag("M.Target", "Being", &[], "being1"),
        tag("M.Target", "MoreIn", &[], "more1"),
        tag("N.Aristotle", "Entity", &[], "being1"),
        tag("N.Aristotle", "Rel", &[], "more1"),
    ]);
    let ranked = rank(
        &target,
        &[&aristotle],
        &vocabulary,
        &BTreeMap::new(),
        &tags,
        10,
    );
    assert_eq!(ranked.len(), 1, "the shared senses admit it");
    // Untagged, the same candidate shares nothing: not admitted.
    assert!(
        rank(
            &target,
            &[&aristotle],
            &vocabulary,
            &BTreeMap::new(),
            &SenseTags::default(),
            10
        )
        .is_empty()
    );
    // A partial-application tag (`Rel _ esse`) identifies nothing: it neither
    // fits a binder nor admits the candidate.
    let partial = tagged(vec![
        tag("M.Target", "MoreIn", &[], "more1"),
        tag("N.Aristotle", "Rel", &["_", "esse"], "more1"),
    ]);
    assert!(
        rank(
            &target,
            &[&aristotle],
            &vocabulary,
            &BTreeMap::new(),
            &partial,
            10
        )
        .is_empty()
    );
    // The same on the target side: a partial tag on the target's binder.
    let target_partial = tagged(vec![
        tag("M.Target", "MoreIn", &["_", "esse"], "more1"),
        tag("N.Aristotle", "Rel", &[], "more1"),
    ]);
    assert!(
        rank(
            &target,
            &[&aristotle],
            &vocabulary,
            &BTreeMap::new(),
            &target_partial,
            10
        )
        .is_empty()
    );
}

#[test]
fn parameter_names_alone_never_admit_a_candidate() {
    // The same binder names, no shared constant, definition or sense: a name
    // is not a meaning (AGENTS.md invariant 7).
    let target = statement("T", "M.Target", &[]);
    let homonym = statement("H", "N.Homonym", &[]);
    let mut vocabulary = BTreeMap::new();
    vocabulary.insert(
        "M.Target".into(),
        vocab("M", &["Being", "MoreIn"], &["M.X"]),
    );
    vocabulary.insert(
        "N.Homonym".into(),
        vocab("N", &["Being", "MoreIn"], &["N.Y"]),
    );
    let tags = tagged(vec![tag("M.Target", "MoreIn", &[], "more1")]);
    assert!(
        rank(
            &target,
            &[&homonym],
            &vocabulary,
            &BTreeMap::new(),
            &tags,
            10
        )
        .is_empty()
    );
    // Different senses on same-named binders admit nothing either.
    let other = tagged(vec![
        tag("M.Target", "MoreIn", &[], "more1"),
        tag("N.Homonym", "MoreIn", &[], "more2"),
    ]);
    assert!(
        rank(
            &target,
            &[&homonym],
            &vocabulary,
            &BTreeMap::new(),
            &other,
            10
        )
        .is_empty()
    );
}

#[test]
fn an_untagged_binder_gets_no_tag_bonus() {
    let target = statement("T", "M.Target", &[]);
    let tagged_candidate = statement("A", "N.Tagged", &[]);
    let untagged_candidate = statement("U", "N.Untagged", &[]);
    let mut vocabulary = BTreeMap::new();
    vocabulary.insert("M.Target".into(), vocab("M", &["B", "MoreIn"], &["M.X"]));
    vocabulary.insert("N.Tagged".into(), vocab("N", &["B", "Rel"], &["M.X"]));
    vocabulary.insert("N.Untagged".into(), vocab("N", &["B", "Rel"], &["M.X"]));
    let tags = tagged(vec![
        tag("M.Target", "MoreIn", &[], "more1"),
        tag("N.Tagged", "Rel", &[], "more1"),
    ]);
    let pool = [&tagged_candidate, &untagged_candidate];
    let ranked = rank(&target, &pool, &vocabulary, &BTreeMap::new(), &tags, 10);
    assert_eq!(ranked[0].id, "A");
    let score = |id: &str| ranked.iter().find(|c| c.id == id).unwrap().score;
    assert!(score("A") > score("U"));
    // The untagged candidate scores as if no binder anywhere were tagged,
    // except that the target's tagged sense counts toward its vocabulary.
    let target_untagged = tagged(vec![]);
    let plain = rank(
        &target,
        &pool,
        &vocabulary,
        &BTreeMap::new(),
        &target_untagged,
        10,
    );
    let plain_u = plain.iter().find(|c| c.id == "U").unwrap().score;
    assert!(score("U") <= plain_u);
}

#[test]
fn a_premise_about_the_projected_field_only_ranks_above_one_using_the_whole_structure() {
    // OnticTSchemaValid (o : Ontic W B) against OnticFrameKT (m : Profile W B)
    // := FrameSatisfies .KT m.ontic.frame (`m` only through `ontic`) and
    // NecessaryConcreteAt (m : Profile W B) := ∃ x, m.concrete x ∧ … m.ontic …
    // (`m` also through `concrete`). Both project; only the first is a
    // statement about the projected value.
    let target = statement("T", "M.TSchema", &[]);
    let frame = statement("F", "N.FrameKT", &[]);
    let concrete = statement("C", "N.Concrete", &[]);
    let mut vocabulary = BTreeMap::new();
    let mut goal = vocab("M", &["W", "B", "o"], &["M.Ontic", "M.Valid"]);
    goal.binder_types = vec!["".into(), "".into(), "M.Ontic".into()];
    vocabulary.insert("M.TSchema".into(), goal);
    let mut kt = vocab(
        "N",
        &["W", "B", "m"],
        &["M.Ontic", "N.Profile", "N.Frame", "N.Refl"],
    );
    kt.binder_types = vec!["".into(), "".into(), "N.Profile".into()];
    kt.binder_fields = vec![set(&[]), set(&[]), set(&["M.Ontic"])];
    kt.binder_uses = vec![set(&[]), set(&[]), set(&["M.Ontic"])];
    vocabulary.insert("N.FrameKT".into(), kt);
    let mut nc = vocab("N", &["W", "B", "m"], &["M.Ontic", "N.Profile"]);
    nc.binder_types = vec!["".into(), "".into(), "N.Profile".into()];
    nc.binder_fields = vec![set(&[]), set(&[]), set(&["M.Ontic"])];
    nc.binder_uses = vec![set(&[]), set(&[]), set(&[])];
    vocabulary.insert("N.Concrete".into(), nc);
    let ranked = rank(
        &target,
        &[&concrete, &frame],
        &vocabulary,
        &BTreeMap::new(),
        &SenseTags::default(),
        10,
    );
    assert_eq!(ranked[0].id, "F", "{ranked:?}");
    // Without the projection-only use, the larger frame vocabulary ranks it last.
    vocabulary.get_mut("N.FrameKT").unwrap().binder_uses = vec![set(&[]), set(&[]), set(&[])];
    let ranked = rank(
        &target,
        &[&concrete, &frame],
        &vocabulary,
        &BTreeMap::new(),
        &SenseTags::default(),
        10,
    );
    assert_eq!(ranked[0].id, "C");
}

#[test]
fn vocabulary_export_reads_projection_only_uses() {
    let parsed = parse_vocabulary(&json!([
        {"declaration": "M.P", "module": "M", "binders": ["B", "m"], "constants": [],
         "binder_types": ["", "M.Profile"], "binder_fields": [[], ["M.Ontic"]],
         "binder_uses": [[], ["M.Ontic"]]},
    ]))
    .unwrap();
    assert_eq!(parsed["M.P"].binder_uses[1], set(&["M.Ontic"]));
    assert!(parsed["M.P"].binder_uses[0].is_empty());
}

#[test]
fn a_computed_formula_is_evaluated_by_its_equations_in_the_certified_text() {
    let mut outcome = closed_outcome();
    outcome["unfold"] = json!(["M.Valid", "M.S5"]);
    outcome["equations"] = json!(["M.convergenceFormula", "M.iterBox"]);
    let text = theorem_text("discovered1", &outcome, 100_000);
    assert!(
        text.contains("(h0 : P) (h2 : R) : T"),
        "statement unchanged: {text}"
    );
    let delta = text.find("delta M.Valid M.S5 at *").unwrap();
    let simp = text
        .find("try simp only [M.convergenceFormula, M.iterBox] at *")
        .unwrap();
    let duper = text.find("all_goals duper [*]").unwrap();
    assert!(delta < simp && simp < duper, "{text}");
    // Without equations the proof is the plain delta-and-Duper script.
    let plain = theorem_text("discovered1", &closed_outcome(), 100_000);
    assert!(plain.ends_with("  duper [*]\n"), "{plain}");
    assert!(!plain.contains("simp"));
}

#[test]
fn a_conclusion_that_is_a_registered_bridge_bridges_its_senses() {
    // The schema statement `T` is registered (role conclusion) as the bridge
    // from NECESSARY_11 to NECESSARY_2: an argument concluding it derives the
    // bridge, as `truth check` accepts (#1845).
    let disambiguation = crate::Record {
        path: "corpus/disambiguations/n.json".into(),
        fields: json!({"term_label": "NECESSARY", "senses": [
            {"id": "s2", "label": "NECESSARY_2", "definition_id": "d2"},
            {"id": "s11", "label": "NECESSARY_11", "definition_id": "d11"}]})
        .as_object()
        .unwrap()
        .clone(),
    };
    let records: Vec<(&str, serde_json::Map<String, Value>)> = vec![
        ("T", json!({"definition_ids": ["d2", "d11"]})),
        ("X", json!({"definition_ids": ["d2"]})),
        ("P", json!({"definition_ids": ["d11"]})),
    ]
    .into_iter()
    .map(|(id, v)| (id, v.as_object().unwrap().clone()))
    .collect();
    let bridge = |role: Option<&str>| {
        let mut b = json!({"term": "NECESSARY", "from": "s11", "to": "s2", "statement_id": "T"});
        if let Some(role) = role {
            b["role"] = json!(role);
        }
        b
    };
    let check = |bridges: Vec<Value>| SenseCheck {
        index: senses::sense_index([&disambiguation]).unwrap(),
        statements: records.iter().map(|(id, r)| (*id, r)).collect(),
        bridges,
    };
    let conclusion = check(vec![bridge(Some("conclusion"))]);
    let mixed = conclusion.mixing(&["P".to_owned()], "T");
    assert_eq!(mixed.len(), 1);
    assert_eq!(mixed[0].2.len(), 1, "bridged by the conclusion: {mixed:?}");
    assert_eq!(mixed[0].2[0]["role"], "conclusion");
    // Another conclusion that mixes the same senses is not bridged by it.
    let other = conclusion.mixing(&["P".to_owned()], "X");
    assert!(other[0].2.is_empty());
    // The registered role does not restrict the use, as in `truth check`: a
    // premise-role registration of `T` bridges an argument that concludes `T`
    // (listed with role conclusion) ...
    let premise = check(vec![bridge(None)]);
    let derived = premise.mixing(&["P".to_owned()], "T");
    assert_eq!(derived[0].2.len(), 1, "{derived:?}");
    assert_eq!(derived[0].2[0]["role"], "conclusion");
    // ... and a conclusion-role registration of `T` bridges an argument that
    // has `T` as a premise (listed without a role, i.e. as a premise bridge).
    let used = conclusion.mixing(&["P".to_owned(), "T".to_owned()], "X");
    assert_eq!(used[0].2.len(), 1, "{used:?}");
    assert!(used[0].2[0].get("role").is_none());
    // The spec draft keeps the role, so `argument_batch.py` records it.
    let mut statements = BTreeMap::new();
    statements.insert(
        "T".to_owned(),
        statement("T", "TruthCore.M.T", &["d2", "d11"]),
    );
    statements.insert("P".to_owned(), statement("P", "TruthCore.M.P", &["d11"]));
    let mut f = classify(
        &trial(&["P"]),
        &closed_outcome(),
        &Graph::default(),
        &conclusion,
    );
    f.premises = vec!["P".to_owned()];
    let flag = f.filters.iter().find(|(n, _)| n == "sense_bridge").unwrap();
    assert!(flag.1.contains("is the conclusion"), "{}", flag.1);
    let spec = render_spec("B", &[&f], &statements, &conclusion, "2026-11-22");
    assert!(
        spec.contains("statement_id = \"T\"\nrole = \"conclusion\"\n"),
        "{spec}"
    );
}
