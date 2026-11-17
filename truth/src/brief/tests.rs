//! Regression fixtures for `brief` and `novelty` (#1643).
//!
//! The fixture checkout reproduces, in miniature and with excerpts of the
//! real notes, the two historical failures #1643 names: the
//! ultimate-explanation rivals reported as unexplored although an
//! integration note records extensive rival analysis and an unsettled
//! universal-coverage judgment, and `DependsForBeing ↔ ¬CanBeWithout`
//! called new although a note already derives it (in its own notation)
//! and issue #1589 discusses it. It also fixes the evidence boundaries: a
//! verified result with an open premise stays conditional, a note is not a
//! certified entailment, a closed issue does not establish its thesis, and a
//! missing snapshot is reported, never read as "no prior work".

use super::{
    Inputs, novelty,
    retrieval::{self, Issues, Revision},
};
use crate::{Corpus, dossier::FrontierView};
use serde_json::{Value, json};
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

const GOAL: &str = "a0000000-0000-4000-8000-000000000001";
const OPEN_PREMISE: &str = "a0000000-0000-4000-8000-000000000002";
const DEPENDENCE: &str = "a0000000-0000-4000-8000-000000000003";
const INDEPENDENCE: &str = "a0000000-0000-4000-8000-000000000004";
const SERIES: &str = "a0000000-0000-4000-8000-000000000005";
const RIVAL: &str = "a0000000-0000-4000-8000-000000000006";
const ARGUMENT: &str = "b0000000-0000-4000-8000-000000000001";
const RESULT: &str = "c0000000-0000-4000-8000-000000000001";
const INFERENCE: &str = "f0000000-0000-4000-8000-000000000001";

const VOCABULARY: &str = "namespace TruthCore.Fixture.Priority

variable {B : Type}

/-- Dependence excludes being without. -/
def DependenceExcludesBeingWithout (DependsForBeing CanBeWithout : B → B → Prop) : Prop :=
  ∀ x y, DependsForBeing x y → ¬ CanBeWithout x y

/-- Independence allows being without. -/
def IndependenceAllowsBeingWithout (DependsForBeing CanBeWithout : B → B → Prop) : Prop :=
  ∀ y x, ¬ DependsForBeing y x → CanBeWithout y x

end TruthCore.Fixture.Priority
";

/// Excerpts of `docs/notes/priority-independence-logic-support-investigation.md`.
const PRIORITY_NOTE: &str = "# Support for priority, independence and excluded middle

Research date: 2026-11-13.

## Exact targets and meanings

Write `D(x,y)` for the existing `DependsForBeing x y`, `B(x,y)` for
`CanBeWithout x y`, and `P(y,x)` for `PriorSimply y x`.

| `STMT-FIX-INDEPENDENCE` | `∀ y x, ¬D(y,x) → B(y,x)` |

## Exact constraints, not hypothetical objections

There is also a useful joint-premise diagnostic. The two universal premises

```text
D(y,x) → ¬B(y,x)
¬D(y,x) → B(y,x)
```

imply, with excluded middle, `D(y,x) ↔ ¬B(y,x)`. Hence the bundle identifies
counterfactual dependence with modal inseparability.
";

/// Excerpts of `docs/notes/ultimate-adequacy-integration-735.md`.
const ULTIMATE_NOTE: &str =
    "# Necessary existence: cumulative argument and adequacy comparisons (#735/#786)

## Owner question: explanatory parity and the remaining gap

Owner question, paraphrased (2026-11-06): are the alternatives merely correct?

**Complete explanatory parity has not been established. Neither has an automatic
explanatory victory for a singular necessary being.**

## Strongest surviving replies

The brute fact, infinite regress and impersonal necessary-ground rivals each
survive with an explicit remaining burden for ultimate explanation (#750, #736,
#613); the whole-series target is `STMT-FIX-SERIES`.

## Proposed overall provisional judgment (2026-11-11)

The explanatory practice argument supplies a substantial reason to investigate
ultimate explanation of existence. It has not established the universal coverage
demand against brute fact or infinite regress rivals.
";

const OLD_NOTE: &str = "# Earlier ultimate explanation survey

## Provisional assessment (2026-10-20)

The brute fact and infinite regress rivals for ultimate explanation look
unexplored here. Superseded by the integration note (#735).
";

fn write(root: &Path, path: &str, text: &str) {
    let path = root.join(path);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

fn record(root: &Path, kind: &str, value: Value) {
    let id = value["id"].as_str().unwrap().to_owned();
    write(
        root,
        &format!("corpus/{kind}/{id}.json"),
        &serde_json::to_string_pretty(&value).unwrap(),
    );
}

/// A fresh fixture checkout (no git: revision unknown, no note history).
fn fixture(name: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!("truth-brief-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let statement = |id: &str, legacy: &str, label: &str, lean: Option<&str>| {
        let mut value = json!({"id": id, "legacy_id": legacy, "label": label, "paraphrase": label});
        if let Some(lean) = lean {
            value["lean_declaration"] = json!(lean);
        }
        value
    };
    for value in [
        statement(GOAL, "STMT-FIX-GOAL", "The goal follows", None),
        statement(OPEN_PREMISE, "STMT-FIX-OPEN", "An open bridge holds", None),
        statement(
            DEPENDENCE,
            "STMT-FIX-DEPENDENCE",
            "If x depends for its being on y, then x cannot be without y",
            Some("TruthCore.Fixture.Priority.DependenceExcludesBeingWithout"),
        ),
        statement(
            INDEPENDENCE,
            "STMT-FIX-INDEPENDENCE",
            "If y does not depend for its being on x, then y can be without x",
            Some("TruthCore.Fixture.Priority.IndependenceAllowsBeingWithout"),
        ),
        statement(
            SERIES,
            "STMT-FIX-SERIES",
            "The series has a sufficient reason outside it",
            None,
        ),
        statement(RIVAL, "STMT-FIX-RIVAL", "The goal is a brute fact", None),
    ] {
        record(&root, "statements", value);
    }
    record(
        &root,
        "arguments",
        json!({"id": ARGUMENT, "label": "The goal from the open bridge",
               "premise_statement_ids": [OPEN_PREMISE], "conclusion_statement_id": GOAL,
               "inference_ids": [INFERENCE], "meaning": "Modus ponens on the bridge."}),
    );
    record(
        &root,
        "inferences",
        json!({"id": INFERENCE, "label": "Bridge step", "input_statement_ids": [OPEN_PREMISE],
               "assumption_statement_ids": [], "discharged_statement_ids": [],
               "output_statement_id": GOAL, "rule": "modus_ponens", "meaning": "Apply the bridge."}),
    );
    record(
        &root,
        "results",
        json!({"id": RESULT, "label": "Goal result", "argument_id": ARGUMENT,
               "challenge_module": "TruthCore.Results.Fixture.Challenge",
               "solution_module": "TruthCore.Results.Fixture.Solution",
               "theorem": "TruthCore.Results.Fixture.goal",
               "comparator_config": "results/x/comparator.json", "status": "solution-present"}),
    );
    record(
        &root,
        "relations",
        json!({"id": "d0000000-0000-4000-8000-000000000001", "label": "Brute rival",
               "subject_kind": "statement", "subject_id": RIVAL, "predicate": "alternative_to",
               "object_kind": "statement", "object_id": GOAL}),
    );
    // The open-premise argument also "refutes" the rival: a conditional
    // refutation that the frontier does not count.
    record(
        &root,
        "relations",
        json!({"id": "d0000000-0000-4000-8000-000000000002", "label": "Conditional refutation",
               "subject_kind": "argument", "subject_id": ARGUMENT, "predicate": "refutes",
               "object_kind": "statement", "object_id": RIVAL}),
    );
    record(
        &root,
        "attempts",
        json!({"id": "e0000000-0000-4000-8000-000000000001", "label": "Countermodel to the bridge",
               "date": "2026-11-13", "statement_ids": [OPEN_PREMISE, GOAL], "kind": "countermodel",
               "outcome": "succeeded", "summary": "A two-world model keeps the premise open.",
               "evidence": []}),
    );
    write(&root, "TruthCore/Fixture/Priority.lean", VOCABULARY);
    write(&root, "docs/notes/priority-independence.md", PRIORITY_NOTE);
    write(&root, "docs/notes/ultimate-adequacy.md", ULTIMATE_NOTE);
    write(&root, "docs/notes/old-ultimate-survey.md", OLD_NOTE);
    write(
        &root,
        "snapshot.json",
        &json!({"captured_at": "2026-11-15T11:27:00Z", "items": [
            {"number": 1589, "title": "Test the necessity exception to independence-implies-separability",
             "state": "OPEN", "url": "https://github.com/o/r/issues/1589",
             "body": "`IndependenceAllowsBeingWithout` (STMT-FIX-INDEPENDENCE) says `¬ DependsForBeing y x → CanBeWithout y x`.",
             "comments": [{"body": "Taken together, D → ¬C and ¬D → C give `D ↔ ¬C` for DependsForBeing and CanBeWithout."}]},
            {"number": 1445, "title": "Assess warrant for whole-series explanation", "state": "MERGED",
             "url": "https://github.com/o/r/pull/1445",
             "body": "The parent remains STMT-FIX-SERIES; whole-series coverage remains unresolved."},
            {"number": 900, "title": "Prove the goal", "state": "CLOSED",
             "url": "https://github.com/o/r/issues/900", "body": "Done: STMT-FIX-GOAL is proved."},
            {"number": 12, "title": "Unrelated tooling", "state": "OPEN",
             "url": "https://github.com/o/r/issues/12", "body": "Speed up CI."}
        ]})
        .to_string(),
    );
    root
}

struct Loaded {
    root: PathBuf,
    corpus: Corpus,
    view: FrontierView,
}

fn load(root: &Path) -> Loaded {
    let corpus = Corpus::load(root).unwrap();
    let report = crate::frontier::current_frontier(root, &corpus, GOAL, false, false);
    let view = FrontierView::from_report(&report).unwrap();
    Loaded {
        root: root.to_path_buf(),
        corpus,
        view,
    }
}

fn snapshot(root: &Path, head: Option<i64>) -> Issues {
    Issues::Snapshot(
        retrieval::read_snapshot(root.join("snapshot.json").to_str().unwrap(), head).unwrap(),
    )
}

fn missing() -> Issues {
    Issues::Missing {
        meaning: retrieval::MISSING_ISSUES,
    }
}

fn run<T>(loaded: &Loaded, issues: &Issues, body: impl FnOnce(&Inputs) -> T) -> T {
    let aliases = loaded.corpus.aliases();
    let inputs = Inputs {
        full_evidence: false,
        root: &loaded.root,
        corpus: &loaded.corpus,
        aliases: &aliases,
        view: &loaded.view,
        issues,
        revision: Revision::default(),
    };
    body(&inputs)
}

fn question(loaded: &Loaded, issues: &Issues, text: &str, limit: usize) -> Value {
    let (db, state) = retrieval::open_index(&loaded.root).unwrap();
    run(loaded, issues, |inputs| {
        super::question_brief(inputs, &db, state, text, limit).unwrap()
    })
}

fn check_novelty(loaded: &Loaded, issues: &Issues, text: &str) -> Value {
    let (db, state) = retrieval::open_index(&loaded.root).unwrap();
    run(loaded, issues, |inputs| {
        novelty::novelty(inputs, &db, state, text, None, 4).unwrap()
    })
}

fn numbers(issues: &Value) -> Vec<u64> {
    issues["matches"]
        .as_array()
        .unwrap()
        .iter()
        .map(|issue| issue["number"].as_u64().unwrap())
        .collect()
}

#[test]
fn conditional_consequence_closed_issue_and_note_keep_their_boundaries() {
    let root = fixture("statement");
    let loaded = load(&root);
    let issues = snapshot(&root, None);
    let brief = run(&loaded, &issues, |inputs| {
        super::statement_brief(inputs, GOAL, None).unwrap()
    });
    // The frontier closes the goal as proved, but does not establish it: its
    // only argument has an unestablished premise, so the brief reports a
    // conditional consequence.
    assert_eq!(brief["formal_status"]["closure"], "proved");
    assert_eq!(brief["formal_status"]["established"], false);
    let argument = &brief["arguments"]["concluding"][0];
    assert_eq!(argument["unestablished_premises"], json!([OPEN_PREMISE]));
    assert!(
        argument["reading"]
            .as_str()
            .unwrap()
            .starts_with("verified conditional consequence")
    );
    assert_eq!(argument["results"][0]["id"], RESULT);
    // A closed issue saying "proved" is listed as workflow history only.
    let closed = &brief["issues"]["matches"][0];
    assert_eq!(
        (closed["number"].as_u64(), closed["state"].as_str()),
        (Some(900), Some("CLOSED"))
    );
    assert!(super::BOUNDARY.contains("issue state is workflow history, not warrant"));
    // The rival and the attempt are retrieved with their records.
    assert_eq!(brief["rivals"][0]["other"]["id"], RIVAL);
    let refutation = &brief["rivals"][0]["rival_refuted_by"][0];
    assert_eq!(refutation["counted"], false);
    assert_eq!(refutation["unestablished_premises"], json!([OPEN_PREMISE]));
    assert!(
        refutation["reading"]
            .as_str()
            .unwrap()
            .starts_with("conditional refutation")
    );
    let text = run(&loaded, &issues, |inputs| {
        super::format_brief(&brief, inputs.aliases, 6)
    });
    assert!(
        text.contains("NOT counted: conditional on 1 unestablished premise(s)"),
        "{text}"
    );
    assert_eq!(brief["attempts"][0]["outcome"], "succeeded");
    // A note deriving the biconditional does not close the premise it names.
    let brief = run(&loaded, &issues, |inputs| {
        super::statement_brief(inputs, INDEPENDENCE, None).unwrap()
    });
    assert_ne!(brief["formal_status"]["state"], "closed");
    assert_eq!(brief["formal_status"]["established"], false);
    let sections: Vec<&str> = brief["notes"]["sections"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s["section"].as_str().unwrap())
        .collect();
    assert_eq!(
        sections,
        ["docs/notes/priority-independence.md#exact-targets-and-meanings"]
    );
    assert_eq!(brief["notes"]["boundary"], crate::notes::BOUNDARY);
    assert_eq!(numbers(&brief["issues"]), [1589]);
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn historical_false_novelty_dependence_biconditional() {
    let root = fixture("novelty");
    let loaded = load(&root);
    let report = check_novelty(
        &loaded,
        &snapshot(&root, None),
        "DependsForBeing ↔ ¬CanBeWithout",
    );
    assert_eq!(report["classification"], "partially-recorded");
    let first = &report["hits"][0];
    assert_eq!(first["kind"], "note");
    assert_eq!(
        first["section"],
        "docs/notes/priority-independence.md#exact-constraints-not-hypothetical-objections"
    );
    assert_eq!(first["coverage"], json!([4, 4]));
    assert_eq!(
        first["notation"],
        json!(["D = DependsForBeing", "B = CanBeWithout"])
    );
    assert!(
        first["excerpt"]
            .as_str()
            .unwrap()
            .contains("`D(y,x) ↔ ¬B(y,x)`")
    );
    assert!(
        report["reading"]
            .as_str()
            .unwrap()
            .contains("semantic comparison is unknown")
    );
    // Both formalized directions are found structurally, not as the theorem.
    let structural: Vec<&str> = report["hits"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|hit| {
            hit["via"]
                .as_str()
                .is_some_and(|via| via.starts_with("structural"))
        })
        .map(|hit| hit["ref"]["id"].as_str().unwrap())
        .collect();
    assert_eq!(structural, [DEPENDENCE, INDEPENDENCE]);
    let issues: Vec<u64> = report["hits"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|hit| hit["kind"] == "issue")
        .map(|hit| hit["number"].as_u64().unwrap())
        .collect();
    assert_eq!(issues, [1589]);
    // The note's own notation alone, with no snapshot, still finds it.
    let symbols = check_novelty(&loaded, &missing(), "D(y,x) ↔ ¬B(y,x)");
    assert_eq!(symbols["classification"], "partially-recorded");
    assert_eq!(symbols["hits"][0]["line"], first["line"]);
    let text = run(&loaded, &missing(), |inputs| {
        novelty::format_novelty(&report, inputs.aliases, 4)
    });
    assert!(text.contains("Classification: partially-recorded"));
    assert!(text.contains("#1589 [OPEN]"));
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn historical_underreported_ultimate_explanation_research() {
    let root = fixture("question");
    let loaded = load(&root);
    let brief = question(
        &loaded,
        &snapshot(&root, None),
        "ultimate explanation, brute fact or infinite regress",
        4,
    );
    let ranked = brief["notes"]["ranked"].as_array().unwrap();
    assert_eq!(ranked[0]["path"], "docs/notes/ultimate-adequacy.md");
    let assessments = ranked[0]["assessments"].as_array().unwrap();
    let excerpts: Vec<&str> = assessments
        .iter()
        .map(|entry| entry["excerpt"].as_str().unwrap())
        .collect();
    assert!(
        excerpts
            .iter()
            .any(|text| text.contains("has not been established"))
    );
    assert!(
        excerpts
            .iter()
            .any(|text| text.contains("not established the universal coverage"))
    );
    let rivals = assessments
        .iter()
        .filter(|a| a["kind"] == "rival_analysis")
        .count();
    assert_eq!(rivals, 1);
    let referenced: Vec<u64> = brief["referenced_issue_numbers"]
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| entry["number"].as_u64().unwrap())
        .collect();
    for number in [735, 750, 736, 613] {
        assert!(
            referenced.contains(&number),
            "#{number} not referenced: {referenced:?}"
        );
    }
    // #1445 names the series statement the matched note names.
    assert!(numbers(&brief["issues"]).contains(&1445));
    assert!(!numbers(&brief["issues"]).contains(&12));
    // The superseded older survey is retrieved with its marker, and the
    // assessments are listed newest first rather than reconciled.
    let old = ranked
        .iter()
        .find(|note| note["path"] == "docs/notes/old-ultimate-survey.md")
        .unwrap();
    assert_eq!(
        old["superseded_markers"][0]["location"],
        "docs/notes/old-ultimate-survey.md line 6"
    );
    let dates: Vec<&str> = brief["assessments"]["sections"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|entry| entry["date"].as_str())
        .collect();
    let mut sorted = dates.clone();
    sorted.sort_by(|a, b| b.cmp(a));
    assert_eq!(dates, sorted);
    assert!(dates.contains(&"2026-10-20") && dates.contains(&"2026-11-11"));
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn missing_and_stale_snapshots_are_explicit() {
    let root = fixture("missing");
    let loaded = load(&root);
    let brief = run(&loaded, &missing(), |inputs| {
        super::statement_brief(inputs, GOAL, None).unwrap()
    });
    assert!(
        brief["absent"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry.as_str().unwrap().starts_with("issues: unknown"))
    );
    assert_eq!(brief["issues"]["source"]["availability"], "missing");
    let report = check_novelty(&loaded, &missing(), "gluon confinement in chromodynamics");
    assert_eq!(report["classification"], "no-match-found");
    assert!(
        report["reading"]
            .as_str()
            .unwrap()
            .contains("not evidence of novelty")
    );
    assert!(
        report["caveats"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c == retrieval::MISSING_ISSUES)
    );
    for text in [report.to_string(), brief.to_string()] {
        assert!(!text.contains("\"novel\""));
    }
    // A snapshot older than the checkout's HEAD is flagged.
    let head = retrieval::parse_epoch("2026-11-16T00:00:00Z");
    let Issues::Snapshot(stale) = snapshot(&root, head) else {
        unreachable!()
    };
    assert_eq!(
        (
            stale.older_than_checkout,
            stale.includes_closed,
            stale.pull_requests
        ),
        (Some(true), true, 1)
    );
    // Open-only snapshots cannot show finished work.
    write(
        &root,
        "open.json",
        &json!([{"number": 3, "title": "t", "state": "OPEN", "body": ""}]).to_string(),
    );
    let open = retrieval::read_snapshot(root.join("open.json").to_str().unwrap(), None).unwrap();
    assert!(!open.includes_closed);
    assert_eq!(open.captured_from, "file modification time");
    let report = check_novelty(&loaded, &Issues::Snapshot(open), "brute fact");
    assert!(
        report["caveats"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c.as_str().unwrap().contains("no closed"))
    );
    assert!(retrieval::read_snapshot(root.join("absent.json").to_str().unwrap(), None).is_err());
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn index_freshness_ordering_and_bounds() {
    let root = fixture("fresh");
    let loaded = load(&root);
    let issues = snapshot(&root, None);
    let first = question(&loaded, &issues, "ultimate explanation brute fact", 1);
    assert_eq!(first["index"]["rebuilt"], true);
    let second = question(&loaded, &issues, "ultimate explanation brute fact", 1);
    assert_eq!(second["index"]["rebuilt"], false);
    // Deterministic apart from the freshness record.
    let strip = |mut value: Value| {
        value["index"] = Value::Null;
        value
    };
    assert_eq!(strip(first.clone()), strip(second));
    // Text output is bounded by --limit.
    let text = run(&loaded, &issues, |inputs| {
        super::format_brief(&first, inputs.aliases, 1)
    });
    assert!(text.contains("more (--json lists all)"), "{text}");
    // Editing a note invalidates the projection; the new text is found.
    write(
        &root,
        "docs/notes/zeta.md",
        "# Zeta\n\nA quasar-specific ultimate explanation.\n",
    );
    let third = question(&loaded, &issues, "quasar", 2);
    assert_eq!(third["index"]["rebuilt"], true);
    assert_eq!(third["notes"]["ranked"][0]["path"], "docs/notes/zeta.md");
    let report = check_novelty(&loaded, &issues, "DependsForBeing ↔ ¬CanBeWithout");
    let counts = report["hit_counts"].as_object().unwrap();
    assert!(counts.values().all(|count| count.as_u64().unwrap() >= 1));
    assert!(report["hits"].as_array().unwrap().len() <= 3 * 4 * 3);
    std::fs::remove_dir_all(&root).unwrap();
}

/// The #1644 benchmark's retrieval failures, in miniature: a note dedicated
/// to the question (by title) must outrank long notes that only touch it;
/// a closed issue's successor is shown with its state ("Successor to #N"
/// names a predecessor and is not); a note citing a result by its Lean
/// theorem name is a note naming the target; and a note heading is
/// matched as text of its own.
#[test]
fn benchmark_1644_dedicated_notes_successors_and_theorem_names() {
    let root = fixture("benchmark-1644");
    // A long note touching every query word in one paragraph, and a short
    // note titled for the question whose body never repeats it.
    write(
        &root,
        "docs/notes/a-long-survey.md",
        "# A long survey of many topics\n\n## Assorted remarks\n\n\
         Brute foundations, explanatory points and stopping rules all appear here.\n\n\
         Brute foundations and explanatory stopping are mentioned again.\n",
    );
    write(
        &root,
        "docs/notes/stopping.md",
        "# One standard for every explanatory stopping point (#746)\n\n\
         The map applies the same tests to each stop.\n\n\
         ## Results\n\n`Fixture.goal` consumes the open bridge; nothing here establishes it.\n",
    );
    write(
        &root,
        "docs/notes/weak-coverage.md",
        "# What weak explanatory coverage actually adds\n\nIt adds no frame constraint.\n",
    );
    write(
        &root,
        "snapshot-1644.json",
        &json!({"captured_at": "2026-11-15T11:27:00Z", "items": [
            {"number": 746, "title": "Explanatory stopping points", "state": "OPEN",
             "url": "https://github.com/o/r/issues/746", "body": "Compare termini."},
            {"number": 562, "title": "Bearer regress", "state": "CLOSED",
             "url": "https://github.com/o/r/issues/562",
             "body": "Are brute foundations explanatory stopping points?",
             "comments": [{"body": "## Retired\n\nSuperseded by https://github.com/o/r/issues/1555. Completed evidence stays here."}]},
            {"number": 1555, "title": "Bearer follow-up", "state": "OPEN",
             "url": "https://github.com/o/r/issues/1555",
             "body": "Successor to #562 in the clean-up; brute foundations remain open."}
        ]})
        .to_string(),
    );
    let loaded = load(&root);
    let issues = Issues::Snapshot(
        retrieval::read_snapshot(root.join("snapshot-1644.json").to_str().unwrap(), None).unwrap(),
    );
    let brief = question(
        &loaded,
        &issues,
        "brute foundations as explanatory stopping points",
        4,
    );
    let ranked = brief["notes"]["ranked"].as_array().unwrap();
    assert_eq!(ranked[0]["path"], "docs/notes/stopping.md", "{ranked:?}");
    // The note's own issue is listed, and the retired issue shows where its
    // scope went; the successor's "Successor to #562" is not read as a
    // successor of its own.
    let matches = brief["issues"]["matches"].as_array().unwrap();
    let find = |number: u64| matches.iter().find(|issue| issue["number"] == number);
    let own = find(746).expect("the note's own issue");
    assert!(own["reasons"].to_string().contains("titled for"), "{own}");
    let retired = find(562).expect("the retired issue");
    assert_eq!(
        retired["successors"],
        json!([{"number": 1555, "kind": "issue", "state": "OPEN", "title": "Bearer follow-up"}])
    );
    assert!(find(1555).is_none_or(|issue| issue.get("successors").is_none()));
    let text = run(&loaded, &issues, |inputs| {
        super::format_brief(&brief, inputs.aliases, 6)
    });
    assert!(text.contains("scope handed to #1555 [OPEN]"), "{text}");
    // A note citing the result's theorem by name is a note naming the goal.
    let goal = run(&loaded, &issues, |inputs| {
        super::statement_brief(inputs, GOAL, None).unwrap()
    });
    let sections = goal["notes"]["sections"].to_string();
    assert!(
        sections.contains("docs/notes/stopping.md#results"),
        "{sections}"
    );
    assert!(sections.contains("Fixture.goal (results)"), "{sections}");
    // A longer identifier containing the name is not a mention.
    assert!(!super::names_lean("`Fixture.goalExtra`", "Fixture.goal"));
    assert!(super::names_lean(
        "`TruthCore.Results.Fixture.goal`",
        "Fixture.goal"
    ));
    // The title is matched even though no body paragraph repeats it.
    let report = check_novelty(&loaded, &missing(), "weak explanatory coverage adds");
    assert!(
        report["hits"]
            .as_array()
            .unwrap()
            .iter()
            .any(|hit| hit["path"] == "docs/notes/weak-coverage.md"
                && hit["coverage"] == json!([4, 4])),
        "{report}"
    );
    assert_eq!(
        retrieval::successor_numbers(
            &serde_json::from_value(json!({
                "number": 17, "body": "Successor to #16. Remaining scope continues in #18, #19."
            }))
            .unwrap()
        ),
        [18, 19]
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn novelty_preserves_direction_scope_time_and_assumptions() {
    let root = fixture("logical-boundaries");
    let loaded = load(&root);
    let original = "If x depends for its being on y, then x cannot be without y";
    let exact = check_novelty(&loaded, &missing(), original);
    assert_eq!(exact["comparison"], "normalized-text-identity");
    assert_eq!(exact["classification"], "already-recorded");
    for candidate in [
        "If x cannot be without y, then x depends for its being on y",
        "If x depends for its being on y, then x can be without y",
        "Every x depends for its being on some y",
        "Some x depends for its being on every y",
        "If x formerly depends for its being on y, then x cannot be without y",
        "Assuming excluded middle, if x depends for its being on y, then x cannot be without y",
    ] {
        let report = check_novelty(&loaded, &missing(), candidate);
        assert_ne!(report["classification"], "already-recorded", "{candidate}");
        assert_eq!(report["comparison"], "unknown");
    }
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn novelty_json_does_not_omit_decoy_overflow() {
    let root = fixture("overflow");
    for number in 0..100 {
        write(
            &root,
            &format!("corpus/statements/decoy-{number}.json"),
            &json!({
                "id": format!("decoy-{number}"), "label": format!("decoy {number}"),
                "paraphrase": format!("Dependence candidate {number}")
            })
            .to_string(),
        );
    }
    let loaded = load(&root);
    let report = check_novelty(&loaded, &missing(), "Dependence candidate");
    assert_eq!(report["omitted_from_json"], 0);
    assert!(report["hits"].as_array().unwrap().len() >= 100);
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn canonical_lexicon_forms_discover_semantically_linked_records() {
    let root = fixture("lexicon-paraphrase");
    let definition = "d0000000-0000-4000-8000-000000000001";
    let lexeme = "d0000000-0000-4000-8000-000000000002";
    write(
        &root,
        &format!("corpus/definitions/{definition}.json"),
        &json!({
            "id": definition, "label": "explanatory basis", "term": "ground",
            "definition": "That which explains", "basis": "stipulative", "note": "Fixture"
        })
        .to_string(),
    );
    write(
        &root,
        &format!("corpus/lexicon/{lexeme}.json"),
        &json!({
            "id": lexeme, "label": "ground vocabulary", "lemma": "ground", "class": "technical",
            "forms": ["grounding"], "definition_ids": [definition]
        })
        .to_string(),
    );
    write(&root, &format!("corpus/statements/{OPEN_PREMISE}.json"), &json!({
        "id": OPEN_PREMISE, "label": "An explanatory basis exists", "paraphrase": "An explanatory basis exists",
        "definition_ids": [definition]
    }).to_string());
    let loaded = load(&root);
    let report = check_novelty(&loaded, &missing(), "grounding");
    assert_eq!(report["comparison"], "unknown");
    assert!(
        report["evidence_graph"]["expansion"]["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|node| node["id"] == OPEN_PREMISE)
    );
    assert_eq!(
        report["semantic_discovery"]["mappings"][0]["alternatives"][0]["id"],
        lexeme
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn graph_query_references_and_hits_share_one_content_copy() {
    let root = fixture("graph-reference-sharing");
    let loaded = load(&root);
    let report = check_novelty(&loaded, &snapshot(&root, None), "#1589");
    assert!(
        !report["evidence_graph"]["lanes"]["explicit"]["seeds"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert!(
        !report["evidence_graph"]["expansion"]["nodes"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert!(report["evidence_graph"].get("explicit").is_none());
    let mut seen = std::collections::BTreeSet::new();
    for hit in report["hits"].as_array().unwrap() {
        assert!(hit["ref"].get("content").is_none());
        if let Some(id) = hit["ref"]["id"].as_str().or_else(|| hit["id"].as_str()) {
            assert!(seen.insert(format!("{}:{id}", hit["kind"])));
        }
    }
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn logical_words_preserve_scope_without_content_only_candidates() {
    let root = fixture("operator-candidate");
    write(&root, &format!("corpus/statements/{OPEN_PREMISE}.json"), &json!({
        "id": OPEN_PREMISE, "label": "Mover scope", "paraphrase": "Every mover moves only insofar as it is in act."
    }).to_string());
    let loaded = load(&root);
    let report = check_novelty(
        &loaded,
        &missing(),
        "Every contingent being has an explanation.",
    );
    assert!(
        !report["hits"]
            .as_array()
            .unwrap()
            .iter()
            .any(|hit| hit["id"] == OPEN_PREMISE)
    );
    let query = retrieval::Query::parse("Every being is not contingent");
    assert!(
        query
            .items
            .iter()
            .any(|item| item.text == "Every" && item.kind == "logical")
    );
    assert!(
        query
            .items
            .iter()
            .any(|item| item.text == "not" && item.kind == "logical")
    );
    assert!(!query.fts_expression().unwrap().contains("every"));
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn assessment_batch_keeps_conflicts_provenance_and_absent_targets() {
    let root = fixture("assessment-batch");
    std::fs::write(root.join("docs/notes/conflict.md"), format!("# Rival assessment\n\n`{SERIES}`\n\n## Provisional judgment\n\nThe premise remains unsupported under this interpretation.\n")).unwrap();
    let corpus = Corpus::load(&root).unwrap();
    let ids = [SERIES.to_owned(), OPEN_PREMISE.to_owned()]
        .into_iter()
        .collect();
    let result = super::assessment_batch(&root, &corpus, &ids).unwrap();
    let entries = result["statements"][SERIES].as_array().unwrap();
    assert!(
        entries
            .iter()
            .any(|entry| entry["path"] == "docs/notes/conflict.md")
    );
    assert!(
        entries
            .iter()
            .any(|entry| entry["path"] != "docs/notes/conflict.md")
    );
    assert!(
        entries
            .iter()
            .all(|entry| entry["line"].as_u64().unwrap() > 0)
    );
    assert!(entries.iter().all(|entry| {
        entry["matched_record_ids"]
            .as_array()
            .unwrap()
            .contains(&json!(SERIES))
    }));
    assert_eq!(result["statements"][OPEN_PREMISE], json!([]));
    assert!(
        super::assessment_batch(
            &root,
            &corpus,
            &["unknown".to_owned()].into_iter().collect()
        )
        .is_err()
    );
    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn assessment_batch_retains_theorem_only_citations() {
    let root = fixture("assessment-theorem");
    write(
        &root,
        "docs/notes/theorem-only.md",
        "# Application\n\n`TruthCore.Results.Fixture.goal`\n\n## Provisional judgment\n\nThe application remains conditional.\n",
    );
    write(
        &root,
        "docs/notes/theorem-prefix.md",
        "# Application\n\n`Fixture.goalExtended`\n\n## Provisional judgment\n\nThis is a different theorem.\n",
    );
    let corpus = Corpus::load(&root).unwrap();
    let result =
        super::assessment_batch(&root, &corpus, &[GOAL.to_owned()].into_iter().collect()).unwrap();
    let entries = result["statements"][GOAL].as_array().unwrap();
    let cited = entries
        .iter()
        .find(|entry| entry["path"] == "docs/notes/theorem-only.md")
        .unwrap();
    assert_eq!(cited["matched_record_ids"], json!([RESULT]));
    assert!(
        !entries
            .iter()
            .any(|entry| entry["path"] == "docs/notes/theorem-prefix.md")
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn current_scope_precedes_historical_text_without_promoting_it_to_proof() {
    let root = fixture("current-scope");
    let path = root.join("corpus/attempts/current.json");
    let current = json!({"date":"2026-11-17","statement_ids":[GOAL],
        "scope":"connected reconstruction only","assessment":"Qualified synthesis accepted; adequacy remains unresolved.",
        "next_test":"Obtain same-bearer evidence.","note":"docs/notes/current.md#assessment",
        "reviewed_revision":"1234567890123456789012345678901234567890",
        "review":"accepted_qualified","publication":"merged","evidence":"PR-42, no findings",
        "supersedes":"Pending integration descriptions only"});
    std::fs::write(&path, serde_json::to_vec(&json!({"id":"d0000000-0000-4000-8000-000000000099",
        "statement_ids":[GOAL, OPEN_PREMISE],"date":"2026-10-01","kind":"derivation","outcome":"blocked",
        "summary":"Historical source work. ".repeat(50),"blocker":"Adequacy remains unresolved.","evidence":[],"current_assessment":current})).unwrap()).unwrap();
    let canonical: Value = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    let known = std::collections::HashSet::from([GOAL, OPEN_PREMISE, SERIES]);
    crate::lifecycle::validate(canonical.as_object().unwrap(), &known).unwrap();
    let mut invalid = canonical.clone();
    invalid["current_assessment"]["statement_ids"] = json!([SERIES]);
    assert!(
        crate::lifecycle::validate(invalid.as_object().unwrap(), &known)
            .unwrap_err()
            .contains("scope")
    );
    invalid = canonical.clone();
    invalid["current_assessment"]["review"] = json!("proved");
    assert!(
        crate::lifecycle::validate(invalid.as_object().unwrap(), &known)
            .unwrap_err()
            .contains("review")
    );
    invalid = canonical.clone();
    invalid["revisions"] =
        json!([{"kind":"editorial","revision":"copyedit","reason":"spelling only"}]);
    assert!(crate::lifecycle::validate(invalid.as_object().unwrap(), &known).is_err());
    let corpus = Corpus::load(&root).unwrap();
    let entries = crate::lifecycle::current(&corpus, &BTreeSet::from([GOAL.to_owned()]));
    assert_eq!(entries.len(), 1);
    assert!(
        crate::lifecycle::current(&corpus, &BTreeSet::from([OPEN_PREMISE.to_owned()])).is_empty()
    );
    let batch =
        super::assessment_batch(&root, &corpus, &BTreeSet::from([GOAL.to_owned()])).unwrap();
    assert_eq!(batch["current_assessments"][0]["publication"], "merged");
    let loaded = load(&root);
    let brief = run(&loaded, &missing(), |inputs| {
        super::statement_brief(inputs, GOAL, None).unwrap()
    });
    assert_eq!(brief["current_assessments"], json!(entries));
    let formatted = super::format_brief(&brief, &corpus.aliases(), 3);
    assert!(formatted.starts_with("Current recorded assessment [accepted_qualified; merged]"));
    assert!(formatted.contains("Obtain same-bearer evidence."));
    assert!(formatted.contains("1234567890123456789012345678901234567890"));
    assert_eq!(
        corpus
            .get("attempts", "d0000000-0000-4000-8000-000000000099")
            .unwrap()
            .fields["outcome"],
        "blocked"
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_late_note_date_and_position_do_not_make_an_old_judgment_current() {
    let raw = "# Case\n\n## Provisional judgment (2026-11-17)\n\nThe new synthesis remains qualified.\n\n## Historical assessment\n\nThe old proposal remains pending.\n\nUpdated bibliography 2026-11-18.\n";
    let note = crate::notes::parse("docs/notes/case.md", raw);
    let entries = super::assessment_sections(&note, raw);
    assert_eq!(entries[0]["date"], "2026-11-17");
    assert!(entries.iter().any(|e| e["date"].is_null()));
    assert!(entries.iter().all(|e| e["date"] != "2026-11-18"));
}

#[test]
fn declared_revisions_expose_graph_and_import_consumers_with_per_revision_dispositions() {
    let root = fixture("revision-impact");
    let before = load(&root);
    assert!(
        crate::lifecycle::impacts(
            &root,
            &before.corpus,
            &BTreeSet::from([OPEN_PREMISE.to_owned()])
        )
        .unwrap()
        .is_empty()
    );
    let imported_result = "c0000000-0000-4000-8000-000000000002";
    let unrelated_result = "c0000000-0000-4000-8000-000000000003";
    let unrelated_argument = "b0000000-0000-4000-8000-000000000003";
    let unrelated_inference = "f0000000-0000-4000-8000-000000000003";
    record(
        &root,
        "inferences",
        json!({"id":unrelated_inference,"input_statement_ids":[INDEPENDENCE],"assumption_statement_ids":[],"discharged_statement_ids":[],"output_statement_id":GOAL,"rule":"fixture","meaning":"Independent alternative support for the same conclusion"}),
    );
    record(
        &root,
        "arguments",
        json!({"id":unrelated_argument,"meaning":"Independent alternative proof","inference_ids":[unrelated_inference],"premise_statement_ids":[INDEPENDENCE],"conclusion_statement_id":GOAL}),
    );
    let imported_argument = "b0000000-0000-4000-8000-000000000002";
    let independent_inference = "f0000000-0000-4000-8000-000000000002";
    record(
        &root,
        "inferences",
        json!({"id":independent_inference,"input_statement_ids":[],"assumption_statement_ids":[],"discharged_statement_ids":[],"output_statement_id":DEPENDENCE,"rule":"fixture","meaning":"Independent registered interface"}),
    );
    record(
        &root,
        "arguments",
        json!({"id":imported_argument,"meaning":"Existing imported proof", "inference_ids":[independent_inference], "premise_statement_ids":[],"conclusion_statement_id":DEPENDENCE}),
    );
    record(
        &root,
        "results",
        json!({"id":imported_result,"argument_id":imported_argument,"challenge_module":"TruthCore.Results.Imported.Challenge","theorem":"TruthCore.Results.Imported.theorem","comparator_config":"imported.json","solution_module":"TruthCore.Results.Imported.Solution","status":"solution-present"}),
    );
    record(
        &root,
        "results",
        json!({"id":unrelated_result,"argument_id":unrelated_argument,"challenge_module":"TruthCore.Results.Unrelated.Challenge","theorem":"TruthCore.Results.Unrelated.theorem","comparator_config":"unrelated.json","solution_module":"TruthCore.Results.Unrelated.Solution","status":"solution-present"}),
    );
    write(
        &root,
        "TruthCore/Results/Imported/Solution.lean",
        "import TruthCore.Results.Fixture.Solution\n",
    );
    write(
        &root,
        "TruthCore/Results/Fixture/Solution.lean",
        "-- existing theorem\n",
    );
    write(
        &root,
        "TruthCore/Results/Unrelated/Solution.lean",
        "-- independent theorem\n",
    );
    let current = json!({"date":"2026-11-17","statement_ids":[OPEN_PREMISE],"scope":"support interpretation only",
        "assessment":"The application warrant has changed.","next_test":"Reassess downstream application.",
        "note":"docs/notes/revision.md#assessment","reviewed_revision":"1234567890123456789012345678901234567890",
        "review":"unreviewed","publication":"unpublished","supersedes":"named earlier application only","evidence":"local comparison"});
    let mut attempt = json!({"id":"e0000000-0000-4000-8000-000000000099","statement_ids":[OPEN_PREMISE],"date":"2026-11-17",
        "kind":"reading","outcome":"succeeded","summary":"A declared consequential change.","evidence":[],"current_assessment":current,
        "revisions":[{"kind":"meaning","revision":"meaning-v2","previous":"docs/notes/old.md#meaning","reason":"The selected support relation no longer includes optional activity.","statement_ids":[OPEN_PREMISE],
        "reassessments":[{"consumer":format!("results:{RESULT}"),"disposition":"retained","reason":"The frozen conditional theorem keeps its original interpretation; only metaphysical application needs review."}]},
        {"kind":"judgment","revision":"warrant-v3","previous":"docs/notes/old.md#judgment","reason":"New evidence changes the application warrant.","statement_ids":[OPEN_PREMISE]}]});
    let unchanged_formal_inputs = load(&root);
    let formal_before = run(&unchanged_formal_inputs, &missing(), |i| {
        super::statement_brief(i, GOAL, None).unwrap()["formal_status"].clone()
    });
    record(&root, "attempts", attempt.clone());
    let after = load(&root);
    let impacts = crate::lifecycle::impacts(
        &root,
        &after.corpus,
        &BTreeSet::from([OPEN_PREMISE.to_owned()]),
    )
    .unwrap();
    assert_eq!(impacts.len(), 2);
    let find = |index: usize, key: String| {
        impacts[index]["consumers"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["consumer"] == key)
            .unwrap()
    };
    assert_eq!(
        find(0, format!("arguments:{ARGUMENT}"))["disposition"],
        "pending"
    );
    assert_eq!(
        find(0, format!("statements:{GOAL}"))["disposition"],
        "pending"
    );
    assert_eq!(
        find(0, format!("results:{RESULT}"))["disposition"],
        "retained"
    );
    assert_eq!(
        find(1, format!("results:{RESULT}"))["disposition"],
        "pending"
    );
    assert_eq!(
        find(0, format!("results:{imported_result}"))["disposition"],
        "pending"
    );
    assert_eq!(
        find(0, format!("statements:{DEPENDENCE}"))["disposition"],
        "pending"
    );
    assert!(impacts.iter().all(|i| {
        i["consumers"]
            .as_array()
            .unwrap()
            .iter()
            .all(|c| c["consumer"] != format!("results:{unrelated_result}"))
    }));
    // Downstream endpoint retrieval exposes the upstream revision too.
    assert_eq!(
        crate::lifecycle::impacts(
            &root,
            &after.corpus,
            &BTreeSet::from([DEPENDENCE.to_owned()])
        )
        .unwrap()
        .len(),
        2
    );
    let formal_after = run(&after, &missing(), |i| {
        super::statement_brief(i, GOAL, None).unwrap()["formal_status"].clone()
    });
    assert_eq!(formal_before, formal_after);
    assert_eq!(
        after
            .corpus
            .get("results", unrelated_result)
            .unwrap()
            .fields["status"],
        "solution-present"
    );
    // A misspelled or unaffected acknowledgement cannot silently close review work.
    attempt["revisions"][0]["reassessments"][0]["consumer"] =
        json!(format!("results:{unrelated_result}"));
    record(&root, "attempts", attempt);
    let corpus = Corpus::load(&root).unwrap();
    assert!(
        crate::lifecycle::impacts(&root, &corpus, &BTreeSet::from([OPEN_PREMISE.to_owned()]))
            .unwrap_err()
            .contains("unaffected consumer")
    );
    std::fs::remove_dir_all(root).unwrap();
}
