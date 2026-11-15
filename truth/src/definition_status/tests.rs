//! Fixture tests from a recorded `scripts/DefinitionStatus.lean` output (no Lean).

use super::*;

const RECORDED: &str = include_str!("../testdata/definition-status-exporter.json");

struct Fixture(PathBuf);

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn write(root: &Path, path: &str, text: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn recorded() -> Vec<Value> {
    serde_json::from_str(RECORDED).unwrap()
}

fn find<'a>(items: &'a [Value], declaration: &str) -> &'a Value {
    items
        .iter()
        .find(|item| item["declaration"] == declaration)
        .unwrap()
}

#[test]
fn classifies_every_recorded_kind() {
    let items = recorded();
    let status = |name: &str| classify(find(&items, name)).0;
    assert_eq!(
        status("TruthCore.Alternatives.ActPotencyRegress.ChangeOfStateOnlyByImpressedForceReading"),
        Status::Defined
    );
    assert_eq!(
        status("TruthCore.Alternatives.ConciliarGrammarDefinitions.RoleProfile"),
        Status::Defined
    );
    assert_eq!(
        status("TruthCore.Alternatives.PhysicalSpecification.PathFormula"),
        Status::Defined
    );
    assert_eq!(
        status("TruthCore.Alternatives.PhysicalGround.compositeRoot"),
        Status::Defined
    );
    assert_eq!(
        status("TruthCore.Alternatives.Fideism.Practice.AnswersToSharedReason"),
        Status::Primitive
    );
    assert_eq!(
        status("TruthCore.Causality.NecessaryBeingSurvey.FiveCausable"),
        Status::Primitive
    );
    // A body that is a bare parameter is a complete function.
    assert_eq!(
        status("TruthCore.Logic.FormSelection.sensor"),
        Status::Defined
    );
    assert_eq!(status("WellFounded"), Status::Defined);
    assert_eq!(status("TruthCore.Fixture.Opaque"), Status::Primitive);
    assert_eq!(status("TruthCore.Fixture.law"), Status::Constraint);
    assert_eq!(
        status("TruthCore.Fixture.SectionVariable"),
        Status::Unresolved
    );
    let (_, reason) = classify(find(
        &items,
        "TruthCore.Alternatives.Fideism.Practice.AnswersToSharedReason",
    ));
    assert!(reason.contains("TruthCore.Alternatives.Fideism.Practice"));
}

fn fixture(name: &str) -> Fixture {
    let root = std::env::temp_dir().join(format!(
        "truth-definition-status-{name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&root);
    write(&root, TOOL, "-- exporter\n");
    write(
        &root,
        "TruthCore/Fixture.lean",
        "structure Frame where\n  Prior : Nat → Nat → Prop\ndef Defined := 1\n",
    );
    write(&root, "TruthCore/Other.lean", "def Unrelated := 2\n");
    let definition = |id: &str, declaration: Option<&str>, extra: &str| {
        let lean = declaration
            .map(|d| format!(", \"lean_declaration\": \"{d}\""))
            .unwrap_or_default();
        write(
            &root,
            &format!("corpus/definitions/{id}.json"),
            &format!(
                "{{\"id\": \"{id}\", \"label\": \"{id}\", \"term\": \"{id}\", \"definition\": \"Text.\", \"basis\": \"stipulative\", \"note\": \"Fixture.\"{lean}{extra}}}"
            ),
        );
    };
    definition("d-defined", Some("TruthCore.Fixture.Defined"), "");
    definition("d-field", Some("TruthCore.Fixture.Frame.Prior"), "");
    definition(
        "d-gap",
        Some("TruthCore.Fixture.Ghost"),
        ", \"formal_gap\": {\"kind\": \"unresolved\", \"meaning\": \"A ghost.\", \"examples_unavailable\": \"None yet.\", \"exclusions\": [\"Not a body.\"], \"open_obligations\": []}",
    );
    definition("d-prose", None, "");
    Fixture(root)
}

fn described() -> Vec<Value> {
    vec![
        json!({"declaration": "TruthCore.Fixture.Defined", "found": true, "module": "TruthCore.Fixture", "kind": "definition", "proof": false, "parameter_wrapper": false, "head": null, "constants": []}),
        json!({"declaration": "TruthCore.Fixture.Frame.Prior", "found": true, "module": "TruthCore.Fixture", "kind": "projection", "proof": false, "structure": "TruthCore.Fixture.Frame", "parameter_wrapper": false, "head": null, "constants": ["TruthCore.Fixture.Frame"]}),
        json!({"declaration": "TruthCore.Fixture.Ghost", "found": false}),
    ]
}

fn state_name(definition: &Definition) -> &'static str {
    match &definition.state {
        State::NoLean => "no_lean",
        State::Uncomputed => "uncomputed",
        State::Computed { status, .. } => status.name(),
    }
}

fn states(root: &Path) -> BTreeMap<String, &'static str> {
    let corpus = Corpus::load(root).unwrap();
    let cache = read_cache(root).unwrap();
    definitions(root, &corpus, cache.as_ref())
        .unwrap()
        .iter()
        .map(|d| (d.id.clone(), state_name(d)))
        .collect()
}

#[test]
fn cache_round_trips_and_goes_stale_with_its_inputs() {
    let fixture = fixture("stale");
    let root = &fixture.0;
    let cache = build_cache(root, &described()).unwrap();
    assert_eq!(parse_cache(&render_cache(&cache)).unwrap(), cache);
    write(root, CACHE, &render_cache(&cache));
    let fresh = states(root);
    assert_eq!(fresh["d-defined"], "defined");
    assert_eq!(fresh["d-field"], "primitive");
    assert_eq!(fresh["d-gap"], "unresolved");
    assert_eq!(fresh["d-prose"], "no_lean");

    // Editing a file that does not mention a declaration changes nothing.
    write(root, "TruthCore/Other.lean", "def Unrelated := 3\n");
    assert_eq!(states(root), fresh);
    // A file that newly mentions the unresolved name makes it stale.
    write(root, "TruthCore/Other.lean", "def Ghost := 3\n");
    assert_eq!(states(root)["d-gap"], "uncomputed");
    assert_eq!(states(root)["d-defined"], "defined");
    // Editing the defining module makes its entries stale.
    write(
        root,
        "TruthCore/Fixture.lean",
        "structure Frame where\n  Prior : Nat → Nat → Prop\ndef Defined := 2\n",
    );
    assert_eq!(states(root)["d-defined"], "uncomputed");
    // A new exporter makes everything stale.
    write(
        root,
        CACHE,
        &render_cache(&build_cache(root, &described()).unwrap()),
    );
    assert_eq!(states(root)["d-field"], "primitive");
    write(root, TOOL, "-- exporter v2\n");
    assert_eq!(states(root)["d-field"], "uncomputed");
}

#[test]
fn compare_separates_wrong_from_stale() {
    let fixture = fixture("compare");
    let root = &fixture.0;
    let computed = build_cache(root, &described()).unwrap();
    let mut committed = computed.clone();
    committed
        .entries
        .get_mut("TruthCore.Fixture.Defined")
        .unwrap()
        .lean["kind"] = json!("opaque");
    committed
        .entries
        .get_mut("TruthCore.Fixture.Frame.Prior")
        .unwrap()
        .identity = "source:old".into();
    committed.entries.insert(
        "TruthCore.Gone".into(),
        Entry {
            identity: "x".into(),
            lean: json!({}),
        },
    );
    let comparison = compare(Some(&committed), &computed);
    assert_eq!(comparison.wrong, ["TruthCore.Fixture.Defined"]);
    assert_eq!(comparison.stale, ["TruthCore.Fixture.Frame.Prior"]);
    assert_eq!(comparison.extra, ["TruthCore.Gone"]);
    assert_eq!(compare(None, &computed).stale.len(), 3);
}

#[test]
fn prose_requirement_allowlist_and_ratchet() {
    let fixture = fixture("prose");
    let root = &fixture.0;
    write(
        root,
        CACHE,
        &render_cache(&build_cache(root, &described()).unwrap()),
    );
    let corpus = Corpus::load(root).unwrap();
    let loaded = load(root, &corpus).unwrap();
    // Without an allowlist, the field lacks prose; the gap matches Lean.
    let found = findings(&loaded.definitions, &Allowlist::new());
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].contains("d-field") && found[0].contains("primitive"));

    let seeded = needed_allowlist(&loaded.definitions, None);
    assert_eq!(seeded.keys().collect::<Vec<_>>(), ["d-field"]);
    assert!(findings(&loaded.definitions, &seeded).is_empty());
    let report = report(&loaded.definitions, &seeded, false, true);
    assert_eq!(report.by_status["defined"], 1);
    assert_eq!(report.by_status["primitive"], 1);
    assert_eq!(report.by_status["unresolved"], 1);
    assert_eq!(report.by_status["no_lean_declaration"], 1);
    assert_eq!(
        (report.with_prose, report.backlog, report.removable),
        (1, 1, 0)
    );
    assert!(report.summary().contains("1 are allowlisted backlog"));
    assert_eq!(parse_allowlist(&render_allowlist(&seeded)).unwrap(), seeded);

    // The ratchet refuses a new or re-hashed entry.
    let mut grown = seeded.clone();
    grown.insert("d-new".into(), "fnv1a64:0".into());
    assert_eq!(ratchet(&seeded, &grown).len(), 1);
    let mut rehashed = seeded.clone();
    rehashed.insert("d-field".into(), "fnv1a64:1".into());
    assert_eq!(ratchet(&seeded, &rehashed).len(), 1);
    assert!(ratchet(&seeded, &Allowlist::new()).is_empty());

    // A changed record loses its grant; regeneration only shrinks.
    let changed = Allowlist::from([("d-field".to_owned(), "fnv1a64:stale".to_owned())]);
    assert_eq!(findings(&loaded.definitions, &changed).len(), 1);
    assert!(needed_allowlist(&loaded.definitions, Some(&changed)).is_empty());

    // Strict mode turns findings into a check error.
    write(root, CONFIG, "{\"schema_version\": 1, \"strict\": true}");
    assert!(check(root).unwrap_err().contains("d-field"));
    write(root, ALLOWLIST, &render_allowlist(&seeded));
    assert!(check(root).unwrap().is_some());
}

#[test]
fn gap_must_agree_with_lean_and_be_well_formed() {
    let fixture = fixture("gap");
    let root = &fixture.0;
    write(
        root,
        CACHE,
        &render_cache(&build_cache(root, &described()).unwrap()),
    );
    write(
        root,
        "corpus/definitions/d-defined.json",
        "{\"id\": \"d-defined\", \"label\": \"d\", \"term\": \"d\", \"definition\": \"T.\", \"basis\": \"stipulative\", \"note\": \"F.\", \"lean_declaration\": \"TruthCore.Fixture.Defined\", \"formal_gap\": {\"kind\": \"constraint\", \"meaning\": \"M.\", \"examples\": [\"e\"], \"exclusions\": [\"x\"], \"open_obligations\": []}}",
    );
    let corpus = Corpus::load(root).unwrap();
    let loaded = load(root, &corpus).unwrap();
    let found = findings(&loaded.definitions, &Allowlist::new());
    assert!(
        found.iter().any(|f| f.contains("Lean settles")),
        "{found:?}"
    );

    for (gap, message) in [
        ("[]", "must be an object"),
        ("{\"kind\": \"defined\"}", "kind must be"),
        ("{\"kind\": \"primitive\", \"meaning\": \" \"}", "meaning"),
        (
            "{\"kind\": \"primitive\", \"meaning\": \"M\", \"exclusions\": [\"x\"], \"open_obligations\": []}",
            "examples_unavailable",
        ),
        (
            "{\"kind\": \"primitive\", \"meaning\": \"M\", \"examples\": [\"e\"], \"exclusions\": [], \"open_obligations\": []}",
            "exclusions",
        ),
        (
            "{\"kind\": \"primitive\", \"meaning\": \"M\", \"examples\": [\"e\"], \"exclusions\": [\"x\"]}",
            "open_obligations",
        ),
        ("{\"kind\": \"primitive\", \"extra\": 1}", "unknown field"),
    ] {
        let error = validate_gap("p", &serde_json::from_str(gap).unwrap()).unwrap_err();
        assert!(error.contains(message), "{gap}: {error}");
    }
}

#[test]
fn describe_gives_the_lean_kind_or_the_prose_fallback() {
    let fixture = fixture("describe");
    let root = &fixture.0;
    write(
        root,
        CACHE,
        &render_cache(&build_cache(root, &described()).unwrap()),
    );
    let corpus = Corpus::load(root).unwrap();
    let loaded = load(root, &corpus).unwrap();
    let by_id = |id: &str| {
        let definition = loaded.definitions.iter().find(|d| d.id == id).unwrap();
        describe(definition, corpus.get("definitions", id).map(|r| &r.fields))
    };
    let defined = by_id("d-defined");
    assert_eq!(defined["status"], "defined");
    assert!(defined.get("prose").is_none());
    let field = by_id("d-field");
    assert_eq!(field["kind"], "projection");
    assert_eq!(field["prose"]["source"], "definition");
    assert_eq!(by_id("d-gap")["prose"]["source"], "formal_gap");
    assert_eq!(by_id("d-prose")["status"], "no_lean_declaration");
}
