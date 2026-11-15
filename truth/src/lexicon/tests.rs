//! Fixture-corpus tests of the lexicon check, allowlist and multi-sense rule.

use super::*;
use std::path::PathBuf;

const D1: &str = "11111111-1111-4111-8111-111111111111";
const D2: &str = "22222222-2222-4222-8222-222222222222";
const X: &str = "33333333-3333-4333-8333-333333333333";

struct Fixture(PathBuf);

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn write(root: &Path, path: &str, value: Value) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, serde_json::to_string_pretty(&value).unwrap()).unwrap();
}

fn entry(root: &Path, n: u32, fields: Value) {
    let id = format!("{n:08x}-0000-4000-8000-000000000000");
    let mut fields = fields.as_object().unwrap().clone();
    fields.insert("id".into(), json!(id));
    let label = format!(
        "{} ({})",
        fields["lemma"].as_str().unwrap(),
        fields["class"].as_str().unwrap()
    );
    fields.entry("label").or_insert(json!(label));
    write(
        root,
        &format!("{DIRECTORY}/{id}.json"),
        Value::Object(fields),
    );
}

fn statement(root: &Path, id: &str, text: &str, definitions: &[&str]) {
    let mut fields = json!({"id": id, "label": format!("statement {id}"), "paraphrase": text});
    if !definitions.is_empty() {
        fields["definition_ids"] = json!(definitions);
    }
    write(root, &format!("corpus/statements/{id}.json"), fields);
}

fn fixture(name: &str) -> Fixture {
    let root = std::env::temp_dir().join(format!("truth-lexicon-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    for (id, term) in [(D1, "cause (efficient)"), (D2, "cause (final)")] {
        write(
            &root,
            &format!("corpus/definitions/{id}.json"),
            json!({"id": id, "label": term, "term": term, "definition": "That by which.", "basis": "stipulative", "note": "Fixture."}),
        );
    }
    write(
        &root,
        &format!("corpus/disambiguations/{X}.json"),
        json!({"id": X, "label": "Cause", "term": "cause", "term_label": "CAUSE", "resolution": "Two senses.",
               "sense_definition_ids": [D1, D2],
               "senses": [{"id": "44444444-4444-4444-8444-444444444444", "label": "CAUSE_1", "definition_id": D1},
                          {"id": "55555555-5555-4555-8555-555555555555", "label": "CAUSE_2", "definition_id": D2}]}),
    );
    // Strict, so violations are errors; `warn_mode_reports_without_failing`
    // covers the default.
    write(
        &root,
        CONFIG,
        json!({"schema_version": 1, "strict": true, "strict_token_coverage": 0.95}),
    );
    entry(
        &root,
        1,
        json!({"lemma": "the", "class": "function", "category": "article"}),
    );
    entry(
        &root,
        2,
        json!({"lemma": "be", "class": "function", "category": "auxiliary", "forms": ["is"]}),
    );
    entry(
        &root,
        3,
        json!({"lemma": "cause", "class": "technical", "definition_ids": [D1, D2], "disambiguation_ids": [X]}),
    );
    entry(
        &root,
        4,
        json!({"lemma": "prior", "class": "ordinary", "gloss": "Earlier in some order."}),
    );
    entry(
        &root,
        5,
        json!({"lemma": "two", "class": "function", "category": "numeral"}),
    );
    entry(
        &root,
        6,
        json!({"lemma": "sense", "class": "ordinary", "gloss": "A meaning of a word."}),
    );
    entry(
        &root,
        7,
        json!({"lemma": "that", "class": "function", "category": "determiner"}),
    );
    entry(
        &root,
        8,
        json!({"lemma": "by", "class": "function", "category": "preposition"}),
    );
    entry(
        &root,
        9,
        json!({"lemma": "which", "class": "function", "category": "determiner"}),
    );
    entry(
        &root,
        10,
        json!({"lemma": "fixture", "class": "ordinary", "gloss": "A test record."}),
    );
    Fixture(root)
}

#[test]
fn traced_and_linked_prose_passes() {
    let fx = fixture("pass");
    statement(&fx.0, "s1", "The causes are prior.", &[D1]);
    // `are` is not a form of `be` here: add it to show the forms override.
    let check = check(&fx.0);
    assert!(check.is_err(), "'are' is untraced");
    entry(
        &fx.0,
        2,
        json!({"lemma": "be", "class": "function", "category": "auxiliary", "forms": ["is", "are"]}),
    );
    let report = check_ok(&fx.0);
    assert_eq!(report.backlog_fields, 0);
}

fn check_ok(root: &Path) -> Report {
    super::check(root).unwrap().expect("lexicon present")
}

#[test]
fn untraced_word_and_unlinked_sense_fail() {
    let fx = fixture("fail");
    statement(&fx.0, "s1", "The cause is mysterious.", &[]);
    let error = super::check(&fx.0).unwrap_err();
    assert!(error.contains("untraced word: 'mysterious'"), "{error}");
    assert!(error.contains("senses linked: 'cause'"), "{error}");
}

#[test]
fn a_sense_tag_links_and_resolves() {
    let fx = fixture("tag");
    statement(&fx.0, "s1", "The cause is CAUSE_2 prior.", &[]);
    check_ok(&fx.0);
    statement(&fx.0, "s1", "The cause is CAUSE_9 prior.", &[]);
    let error = super::check(&fx.0).unwrap_err();
    assert!(error.contains("'CAUSE_9'"), "{error}");
}

#[test]
fn allowlist_grandfathers_unchanged_fields_only() {
    let fx = fixture("allow");
    statement(&fx.0, "s1", "The cause is mysterious.", &[]);
    let loaded = load(&fx.0).unwrap().unwrap();
    let seeded = needed_allowlist(&loaded.scans, None);
    fs::write(fx.0.join(ALLOWLIST), render_allowlist(&seeded)).unwrap();
    assert_eq!(read_allowlist(&fx.0).unwrap().unwrap(), seeded);
    let report = check_ok(&fx.0);
    assert_eq!(
        (
            report.backlog_fields,
            report.backlog_untraced,
            report.backlog_unlinked
        ),
        (1, 1, 1)
    );
    // A changed field must be fully traced.
    statement(&fx.0, "s1", "The cause is mysterious indeed.", &[]);
    let error = super::check(&fx.0).unwrap_err();
    assert!(
        error.contains("'mysterious'") && error.contains("'indeed'"),
        "{error}"
    );
    // Regeneration only shrinks: the changed field is not re-allowlisted.
    let loaded = load(&fx.0).unwrap().unwrap();
    assert!(needed_allowlist(&loaded.scans, Some(&seeded)).is_empty());
    // Tracing the word and linking a sense makes the entry removable; the
    // link is outside the hashed prose.
    statement(&fx.0, "s1", "The cause is mysterious.", &[D1]);
    entry(
        &fx.0,
        11,
        json!({"lemma": "mysterious", "class": "ordinary", "gloss": "Not understood."}),
    );
    let report = check_ok(&fx.0);
    assert_eq!(report.removable, 1);
}

#[test]
fn ratchet_rejects_growth() {
    let key = "statements/s1/paraphrase".to_owned();
    let base: Allowlist = [(key.clone(), "fnv1a64:01".to_owned())].into();
    assert!(ratchet(&base, &base).is_empty());
    assert!(ratchet(&base, &Allowlist::new()).is_empty());
    let rehashed: Allowlist = [(key, "fnv1a64:02".to_owned())].into();
    assert_eq!(ratchet(&base, &rehashed).len(), 1);
    let mut added = base.clone();
    added.insert("statements/s2/paraphrase".into(), "fnv1a64:03".into());
    assert_eq!(ratchet(&base, &added).len(), 1);
}

#[test]
fn schema_one_allowlists_are_read_for_their_hashes() {
    let old = r#"{"schema_version": 1, "fields": {"statements/s1/paraphrase": {"hash": "fnv1a64:01", "untraced": ["a"], "unlinked": []}}}"#;
    let parsed = parse_allowlist(old).unwrap();
    assert_eq!(parsed["statements/s1/paraphrase"], "fnv1a64:01");
    assert_eq!(parse_allowlist(&render_allowlist(&parsed)).unwrap(), parsed);
    assert!(parse_allowlist(r#"{"fields": {"k": 1}}"#).is_err());
}

fn seed(root: &Path) {
    let loaded = load(root).unwrap().unwrap();
    fs::write(
        root.join(ALLOWLIST),
        render_allowlist(&needed_allowlist(&loaded.scans, None)),
    )
    .unwrap();
}

#[test]
fn tracing_a_compound_part_keeps_an_unchanged_field_grandfathered() {
    // Regression (#1652 L1b): `negation-closure` was untraced as a whole;
    // tracing `negation` splits it and exposes the multi-sense `cause` part.
    let fx = fixture("compoundsplit");
    statement(&fx.0, "s1", "The negation-cause is prior.", &[]);
    seed(&fx.0);
    check_ok(&fx.0);
    entry(
        &fx.0,
        17,
        json!({"lemma": "negation", "class": "ordinary", "gloss": "Denial."}),
    );
    let report = check_ok(&fx.0);
    assert!(report.new_violations.is_empty());
    assert_eq!(
        (
            report.backlog_fields,
            report.backlog_untraced,
            report.backlog_unlinked
        ),
        (1, 0, 1)
    );
}

#[test]
fn a_new_multi_sense_entry_creates_no_new_violation_in_unchanged_fields() {
    let fx = fixture("newsense");
    statement(&fx.0, "s1", "The fixture is concrete.", &[]);
    seed(&fx.0);
    check_ok(&fx.0);
    entry(
        &fx.0,
        18,
        json!({"lemma": "concrete", "class": "technical", "definition_ids": [D1, D2], "disambiguation_ids": [X]}),
    );
    let report = check_ok(&fx.0);
    assert!(report.new_violations.is_empty());
    assert_eq!(report.backlog_unlinked, 1);
    // A changed field must link a sense of the new entry.
    statement(&fx.0, "s1", "The fixture is concrete indeed.", &[]);
    entry(
        &fx.0,
        19,
        json!({"lemma": "indeed", "class": "ordinary", "gloss": "In fact."}),
    );
    assert!(super::check(&fx.0).unwrap_err().contains("'concrete'"));
}

#[test]
fn ordinary_sibling_needs_separation_and_exempts() {
    let fx = fixture("sibling");
    statement(&fx.0, "s1", "The cause is prior.", &[]);
    entry(
        &fx.0,
        12,
        json!({"lemma": "cause", "class": "ordinary", "gloss": "What brings something about."}),
    );
    let error = super::check(&fx.0).unwrap_err();
    assert!(error.contains("technical_separation"), "{error}");
    entry(
        &fx.0,
        12,
        json!({"lemma": "cause", "class": "ordinary", "gloss": "What brings something about.",
                            "technical_separation": "Everyday use, not one of the CAUSE senses."}),
    );
    check_ok(&fx.0);
}

#[test]
fn schema_errors() {
    let fx = fixture("schema");
    entry(&fx.0, 13, json!({"lemma": "odd", "class": "nonsense"}));
    assert!(
        super::check(&fx.0)
            .unwrap_err()
            .contains("class must be one of")
    );
    entry(
        &fx.0,
        13,
        json!({"lemma": "odd", "class": "technical", "definition_ids": ["nope"]}),
    );
    assert!(
        super::check(&fx.0)
            .unwrap_err()
            .contains("unknown definition id")
    );
    entry(
        &fx.0,
        13,
        json!({"lemma": "Odd", "class": "ordinary", "gloss": "x"}),
    );
    assert!(
        super::check(&fx.0)
            .unwrap_err()
            .contains("lemma must be lowercase")
    );
    entry(
        &fx.0,
        13,
        json!({"lemma": "odd", "class": "ordinary", "gloss": "x", "definition_ids": [D1]}),
    );
    assert!(
        super::check(&fx.0)
            .unwrap_err()
            .contains("has no definition_ids")
    );
    entry(
        &fx.0,
        13,
        json!({"lemma": "the", "class": "function", "category": "article", "label": "the again"}),
    );
    assert!(
        super::check(&fx.0)
            .unwrap_err()
            .contains("is also an entry")
    );
}

#[test]
fn phrases_trace_their_words() {
    let fx = fixture("phrase");
    entry(
        &fx.0,
        14,
        json!({"lemma": "per se", "class": "technical", "definition_ids": [D1]}),
    );
    statement(&fx.0, "s1", "The cause is per se prior.", &[D1]);
    check_ok(&fx.0);
    // Punctuation breaks the phrase, leaving `se` untraced.
    statement(&fx.0, "s1", "The cause is per, se prior.", &[D1]);
    assert!(super::check(&fx.0).unwrap_err().contains("'se'"));
}

#[test]
fn no_lexicon_directory_means_no_check() {
    let fx = fixture("absent");
    fs::remove_dir_all(fx.0.join(DIRECTORY)).unwrap();
    assert!(super::check(&fx.0).unwrap().is_none());
}

#[test]
fn compound_parts_are_checked_separately() {
    let fx = fixture("compound");
    // `by` is a function word; it must not exempt the technical `cause`.
    statement(&fx.0, "s1", "The by-cause is prior.", &[]);
    let error = super::check(&fx.0).unwrap_err();
    assert!(error.contains("senses linked: 'cause'"), "{error}");
}

#[test]
fn forms_of_a_phrase_are_indexed() {
    let fx = fixture("phraseform");
    entry(
        &fx.0,
        15,
        json!({"lemma": "per se", "class": "technical", "definition_ids": [D1], "forms": ["per-se"]}),
    );
    statement(&fx.0, "s1", "The cause is per-se prior.", &[D1]);
    check_ok(&fx.0);
}

#[test]
fn an_ordinary_phrase_sibling_exempts_regardless_of_file_order() {
    let fx = fixture("phrasesibling");
    entry(
        &fx.0,
        16,
        json!({"lemma": "per se", "class": "technical", "definition_ids": [D1, D2], "disambiguation_ids": [X]}),
    );
    statement(&fx.0, "s1", "The fixture is per se prior.", &[]);
    assert!(super::check(&fx.0).unwrap_err().contains("'per se'"));
    for n in [1u32 << 31, 0x0f] {
        entry(
            &fx.0,
            n,
            json!({"lemma": "per se", "class": "ordinary", "gloss": "Of itself.", "technical_separation": "Everyday use."}),
        );
        check_ok(&fx.0);
        fs::remove_file(fx.0.join(format!(
            "{DIRECTORY}/{n:08x}-0000-4000-8000-000000000000.json"
        )))
        .unwrap();
    }
}

#[test]
fn warn_mode_reports_without_failing() {
    let fx = fixture("warn");
    write(
        &fx.0,
        CONFIG,
        json!({"schema_version": 1, "strict": false, "strict_token_coverage": 0.5}),
    );
    statement(&fx.0, "s1", "The cause is mysterious.", &[]);
    let report = check_ok(&fx.0);
    assert!(!report.strict);
    assert_eq!(
        report.new_violations.len(),
        2,
        "{:?}",
        report.new_violations
    );
    assert!(report.new_violations[0].contains("1 untraced word: 'mysterious'"));
    assert!(report.new_violations[1].contains("'cause'"));
    assert!(
        report.summary().contains("threshold reached"),
        "{}",
        report.summary()
    );
    // Without the file: warn mode at the default threshold.
    fs::remove_file(fx.0.join(CONFIG)).unwrap();
    assert_eq!(read_config(&fx.0).unwrap(), Config::default());
    assert!(check_ok(&fx.0).summary().contains("warn mode"));
    // Schema errors stay errors in warn mode.
    entry(&fx.0, 13, json!({"lemma": "odd", "class": "nonsense"}));
    assert!(super::check(&fx.0).is_err());
}

#[test]
fn config_errors() {
    let fx = fixture("config");
    for bad in [
        json!({"strict": "no", "strict_token_coverage": 0.9}),
        json!({"strict": true, "strict_token_coverage": 1.5}),
        json!({"strict": true, "strict_token_coverage": 0.9, "extra": 1}),
    ] {
        write(&fx.0, CONFIG, bad);
        assert!(super::check(&fx.0).unwrap_err().contains(CONFIG));
    }
}
