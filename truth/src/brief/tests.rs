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
    let summary_attempt = "e0000000-0000-4000-8000-000000000090";
    let evidence_attempt = "e0000000-0000-4000-8000-000000000091";
    let bookkeeping_attempt = "e0000000-0000-4000-8000-000000000092";
    let judgment_attempt = "e0000000-0000-4000-8000-000000000093";
    for (id, summary, evidence, selected) in [
        (
            summary_attempt,
            format!("The judgment relies on {OPEN_PREMISE}."),
            json!([]),
            None,
        ),
        (
            evidence_attempt,
            "The judgment uses the cited result.".to_owned(),
            json!([RESULT]),
            None,
        ),
        (
            bookkeeping_attempt,
            "Administrative target registration only.".to_owned(),
            json!([]),
            Some("Administrative entry only.".to_owned()),
        ),
        (
            judgment_attempt,
            "See selected assessment.".to_owned(),
            json!([]),
            Some(format!("The selected judgment relies on {OPEN_PREMISE}.")),
        ),
    ] {
        let mut other = json!({"id":id,"statement_ids":[OPEN_PREMISE],"date":"2026-11-17","kind":"reading","outcome":"succeeded","summary":summary,"evidence":evidence});
        if let Some(assessment) = selected {
            other["current_assessment"] = attempt["current_assessment"].clone();
            other["current_assessment"]["assessment"] = json!(assessment);
            other["current_assessment"]["scope"] = json!("Independent bounded judgment");
            other["current_assessment"]["evidence"] = json!(OPEN_PREMISE); // review bookkeeping only
        }
        record(&root, "attempts", other);
    }
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
    for id in [summary_attempt, judgment_attempt] {
        assert_eq!(find(0, format!("attempts:{id}"))["disposition"], "pending");
        assert_eq!(find(0, format!("attempts:{id}"))["tier"], "prose");
    }
    // Evidence citing only the result retained as unchanged is screened by it
    // for that revision and stays pending for the other one.
    let evidence = find(0, format!("attempts:{evidence_attempt}"));
    assert_eq!(evidence["disposition"], "screened");
    assert_eq!(evidence["screened_by"], format!("results:{RESULT}"));
    assert_eq!(
        find(1, format!("attempts:{evidence_attempt}"))["disposition"],
        "pending"
    );
    assert!(
        impacts.iter().all(|i| i["consumers"]
            .as_array()
            .unwrap()
            .iter()
            .all(
                |c| c["consumer"] != format!("attempts:{bookkeeping_attempt}")
                    && c["consumer"] != "attempts:e0000000-0000-4000-8000-000000000099"
            ))
    );
    // Other attempts' judgments can be explicitly reassessed for this revision.
    let mut acknowledged = attempt.clone();
    acknowledged["revisions"][0]["reassessments"].as_array_mut().unwrap().push(json!({"consumer":format!("attempts:{summary_attempt}"),"disposition":"retained","reason":"The independent assessment still uses the original qualified interpretation."}));
    record(&root, "attempts", acknowledged);
    let acknowledged_corpus = Corpus::load(&root).unwrap();
    let reassessed = crate::lifecycle::impacts(
        &root,
        &acknowledged_corpus,
        &BTreeSet::from([OPEN_PREMISE.to_owned()]),
    )
    .unwrap();
    assert_eq!(
        reassessed[0]["consumers"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["consumer"] == format!("attempts:{summary_attempt}"))
            .unwrap()["disposition"],
        "retained"
    );
    assert_eq!(
        reassessed[1]["consumers"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["consumer"] == format!("attempts:{summary_attempt}"))
            .unwrap()["disposition"],
        "pending"
    );
    record(&root, "attempts", attempt.clone());
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
    // Seed the concluded statement itself: R is an import-discovery source,
    // not an affected alternative producer. T has no declared GOAL premise.
    let mut goal_revision = attempt.clone();
    goal_revision["statement_ids"] = json!([GOAL]);
    goal_revision["current_assessment"]["statement_ids"] = json!([GOAL]);
    for change in goal_revision["revisions"].as_array_mut().unwrap() {
        change["statement_ids"] = json!([GOAL]);
        change["reassessments"] = json!([]);
    }
    record(&root, "attempts", goal_revision);
    let goal_loaded = load(&root);
    let goal_corpus = &goal_loaded.corpus;
    let goal_impacts =
        crate::lifecycle::impacts(&root, goal_corpus, &BTreeSet::from([GOAL.to_owned()])).unwrap();
    for impact in &goal_impacts {
        let consumers = impact["consumers"].as_array().unwrap();
        let imported = consumers
            .iter()
            .find(|c| c["consumer"] == format!("results:{imported_result}"))
            .unwrap();
        assert_eq!(imported["disposition"], "pending");
        assert_eq!(imported["via"], format!("statements:{GOAL}"));
        assert_eq!(imported["import_source"], format!("results:{RESULT}"));
        assert!(
            consumers
                .iter()
                .all(|c| c["consumer"] != format!("results:{RESULT}")
                    && c["consumer"] != format!("results:{unrelated_result}")
                    && c["consumer"] != format!("arguments:{ARGUMENT}")
                    && c["consumer"] != format!("arguments:{unrelated_argument}"))
        );
    }
    assert_eq!(
        formal_before,
        run(&goal_loaded, &missing(), |i| super::statement_brief(
            i, GOAL, None
        )
        .unwrap()["formal_status"]
            .clone())
    );
    assert_eq!(
        goal_corpus.get("results", RESULT).unwrap().fields["status"],
        after.corpus.get("results", RESULT).unwrap().fields["status"]
    );
    assert_eq!(
        goal_corpus.get("results", unrelated_result).unwrap().fields["status"],
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

/// Consumer tiers (#1757): registered premise use and conclusion propagation stay
/// individually addressed; import discovery and mentions may share one group
/// disposition; a consumer individually reassessed as unchanged screens what lies
/// downstream only through it, and a consumer still live past that screen only
/// through import discovery is reported in the import tier.
#[test]
fn revision_consumers_are_tiered_grouped_and_screened_soundly() {
    let root = fixture("revision-tiers");
    // GOAL --premise--> A2 => SERIES, verified by R2.
    let (a2, i2, r2) = (
        "b0000000-0000-4000-8000-000000000012",
        "f0000000-0000-4000-8000-000000000012",
        "c0000000-0000-4000-8000-000000000012",
    );
    // A producer of the revised premise, whose module R2 imports.
    let (pa, pi, pr) = (
        "b0000000-0000-4000-8000-000000000013",
        "f0000000-0000-4000-8000-000000000013",
        "c0000000-0000-4000-8000-000000000013",
    );
    // A result whose module imports the fixture result: import discovery only.
    let (ia, ii, ir) = (
        "b0000000-0000-4000-8000-000000000014",
        "f0000000-0000-4000-8000-000000000014",
        "c0000000-0000-4000-8000-000000000014",
    );
    for (argument, inference, result, premises, conclusion, module) in [
        (a2, i2, r2, vec![GOAL], SERIES, "Second"),
        (pa, pi, pr, vec![], OPEN_PREMISE, "Producer"),
        (ia, ii, ir, vec![], DEPENDENCE, "Imported"),
    ] {
        record(
            &root,
            "inferences",
            json!({"id":inference,"input_statement_ids":premises,"assumption_statement_ids":[],"discharged_statement_ids":[],"output_statement_id":conclusion,"rule":"fixture","meaning":"Fixture step"}),
        );
        record(
            &root,
            "arguments",
            json!({"id":argument,"meaning":"Fixture argument","inference_ids":[inference],"premise_statement_ids":premises,"conclusion_statement_id":conclusion}),
        );
        record(
            &root,
            "results",
            json!({"id":result,"argument_id":argument,"challenge_module":format!("TruthCore.Results.{module}.Challenge"),"theorem":format!("TruthCore.Results.{module}.theorem"),"comparator_config":"x.json","solution_module":format!("TruthCore.Results.{module}.Solution"),"status":"solution-present"}),
        );
    }
    // A3 registers DEPENDENCE (reached only through import discovery) as a premise.
    let a3 = "b0000000-0000-4000-8000-000000000015";
    record(
        &root,
        "arguments",
        json!({"id":a3,"meaning":"Downstream of an import","inference_ids":["f0000000-0000-4000-8000-000000000014"],"premise_statement_ids":[DEPENDENCE],"conclusion_statement_id":RIVAL}),
    );
    write(
        &root,
        "TruthCore/Results/Fixture/Solution.lean",
        "-- fixture\n",
    );
    write(
        &root,
        "TruthCore/Results/Producer/Solution.lean",
        "-- producer\n",
    );
    write(
        &root,
        "TruthCore/Results/Second/Solution.lean",
        "import TruthCore.Results.Producer.Solution\n",
    );
    write(
        &root,
        "TruthCore/Results/Imported/Solution.lean",
        "import TruthCore.Results.Fixture.Solution\n",
    );
    write(
        &root,
        "docs/notes/tier-mention.md",
        "# Mentions\n\n## Use\n\nThe goal STMT-FIX-GOAL is discussed here.\n",
    );
    let current = json!({"date":"2026-11-20","statement_ids":[OPEN_PREMISE],"scope":"bridge warrant only",
        "assessment":"The bridge warrant changed.","next_test":"Reassess consumers.",
        "note":"docs/notes/revision.md#assessment","reviewed_revision":"1234567890123456789012345678901234567890",
        "review":"unreviewed","publication":"unpublished","supersedes":"earlier warrant","evidence":"local"});
    let declare = |reassessments: Value| {
        record(
            &root,
            "attempts",
            json!({"id":"e0000000-0000-4000-8000-000000000098","statement_ids":[OPEN_PREMISE],"date":"2026-11-20",
            "kind":"reading","outcome":"succeeded","summary":"A declared change.","evidence":[],"current_assessment":current,
            "revisions":[{"kind":"premise_warrant","revision":"tiers-v1","previous":"docs/notes/old.md#warrant","reason":"New warrant.","statement_ids":[OPEN_PREMISE],"reassessments":reassessments}]}),
        );
        let corpus = Corpus::load(&root).unwrap();
        crate::lifecycle::impacts(&root, &corpus, &BTreeSet::from([OPEN_PREMISE.to_owned()]))
    };
    let consumer = |impact: &Value, key: String| -> Value {
        impact["consumers"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["consumer"] == key)
            .cloned()
            .unwrap_or_else(|| panic!("{key} not listed"))
    };

    // Unscreened: every registered premise-use chain is premise_use, imports and
    // whatever they reach are import, mentions are reference/prose.
    let impact = declare(json!([])).unwrap().remove(0);
    for key in [
        format!("arguments:{ARGUMENT}"),
        format!("inferences:{INFERENCE}"),
        format!("results:{RESULT}"),
        format!("statements:{GOAL}"),
        format!("arguments:{a2}"),
        format!("results:{r2}"),
        format!("statements:{SERIES}"),
    ] {
        assert_eq!(
            consumer(&impact, key.clone())["tier"],
            "premise_use",
            "{key}"
        );
    }
    for key in [
        format!("results:{ir}"),
        format!("statements:{DEPENDENCE}"),
        format!("arguments:{a3}"),
        format!("statements:{RIVAL}"),
    ] {
        assert_eq!(consumer(&impact, key.clone())["tier"], "import", "{key}");
    }
    assert_eq!(
        consumer(&impact, format!("results:{ir}"))["import_source"],
        format!("results:{RESULT}")
    );
    assert_eq!(
        consumer(
            &impact,
            "relations:d0000000-0000-4000-8000-000000000002".into()
        )["tier"],
        "reference"
    );
    assert_eq!(
        consumer(&impact, "notes:docs/notes/tier-mention.md#use".into())["tier"],
        "prose"
    );
    // Alternative producers of the revised premise are not its consumers.
    assert!(
        impact["consumers"]
            .as_array()
            .unwrap()
            .iter()
            .all(|c| c["consumer"] != format!("results:{pr}"))
    );
    assert_eq!(impact["tiers"]["premise_use"]["consumers"], 8);
    assert_eq!(impact["tiers"]["premise_use"]["pending"], 8);

    // Groups cover only mention and import tiers; premise use stays pending.
    let grouped = declare(json!([
        {"group":"tier:import","disposition":"retained","reason":"Imports reach only the unchanged interface."},
        {"group":"path:docs/notes/tier-mention.md","disposition":"not_applicable","reason":"Historical note."}
    ])).unwrap().remove(0);
    assert_eq!(grouped["tiers"]["import"]["pending"], 0);
    assert_eq!(grouped["tiers"]["premise_use"]["pending"], 8);
    assert_eq!(
        consumer(&grouped, "notes:docs/notes/tier-mention.md#use".into())["disposition_by"],
        "path:docs/notes/tier-mention.md"
    );
    assert_eq!(
        consumer(&grouped, "notes:docs/notes/tier-mention.md#use".into())["disposition"],
        "not_applicable"
    );
    assert_eq!(
        consumer(
            &grouped,
            "relations:d0000000-0000-4000-8000-000000000002".into()
        )["disposition"],
        "pending"
    );
    // No group addressing for registered premise use, and no empty groups.
    let mut attempt = json!({"current_assessment":current,"statement_ids":[OPEN_PREMISE],"revisions":[{"kind":"judgment","revision":"x","previous":"p","reason":"r","statement_ids":[OPEN_PREMISE],
        "reassessments":[{"group":"tier:premise_use","disposition":"retained","reason":"blanket"}]}]});
    let known = std::collections::HashSet::from([OPEN_PREMISE]);
    assert!(crate::lifecycle::validate(attempt.as_object().unwrap(), &known).is_err());
    attempt["revisions"][0]["reassessments"] = json!([{"group":"tier:import","consumer":format!("arguments:{ARGUMENT}"),"disposition":"retained","reason":"both"}]);
    assert!(crate::lifecycle::validate(attempt.as_object().unwrap(), &known).is_err());
    assert!(
        declare(
            json!([{"group":"path:docs/notes/absent.md","disposition":"retained","reason":"none"}])
        )
        .unwrap_err()
        .contains("unaffected group")
    );
    assert!(declare(json!([{"group":"tier:import","disposition":"retained","reason":"a"},{"group":"tier:import","disposition":"revised","reason":"b"}])).unwrap_err().contains("duplicate"));

    // Retaining the direct consumer screens the chain only through it. Its
    // inference and result inherit the disposition; R2 and SERIES stay live
    // through import discovery from the premise's producer, now as import tier.
    let screened = declare(json!([{"consumer":format!("arguments:{ARGUMENT}"),"disposition":"retained","reason":"Conditional use unchanged."}])).unwrap().remove(0);
    assert_eq!(
        consumer(&screened, format!("inferences:{INFERENCE}"))["disposition_by"],
        format!("arguments:{ARGUMENT}")
    );
    assert_eq!(
        consumer(&screened, format!("results:{RESULT}"))["disposition"],
        "retained"
    );
    for key in [
        format!("statements:{GOAL}"),
        format!("arguments:{a2}"),
        format!("results:{ir}"),
        format!("arguments:{a3}"),
    ] {
        let c = consumer(&screened, key.clone());
        assert_eq!(c["disposition"], "screened", "{key}");
        assert!(c["screened_by"].is_string(), "{key}");
    }
    for key in [format!("results:{r2}"), format!("statements:{SERIES}")] {
        let c = consumer(&screened, key.clone());
        assert_eq!(
            (c["tier"].as_str(), c["disposition"].as_str()),
            (Some("import"), Some("pending")),
            "{key}"
        );
    }
    assert_eq!(
        consumer(&screened, format!("results:{r2}"))["import_source"],
        format!("results:{pr}")
    );
    assert_eq!(screened["tiers"]["premise_use"]["pending"], 0);
    let text = crate::lifecycle::lines(&[], std::slice::from_ref(&screened)).join("\n");
    assert!(text.contains("tiers (consumers/pending/screened): premise_use "));
    assert!(text.contains(&format!("[premise_use] statements:{GOAL}: screened")));
    assert!(text.contains(&format!(
        "[premise_use] arguments:{ARGUMENT}: retained — Conditional use unchanged."
    )));
    // Groupable tiers are summarized; --json lists them in full.
    assert!(!text.contains(&format!("results:{r2}")));

    // A revised consumer screens nothing: its conclusion needs its own disposition.
    let revised = declare(json!([{"consumer":format!("arguments:{ARGUMENT}"),"disposition":"revised","reason":"Application changes."}])).unwrap().remove(0);
    assert_eq!(
        consumer(&revised, format!("statements:{GOAL}"))["disposition"],
        "pending"
    );
    assert_eq!(
        consumer(&revised, format!("statements:{GOAL}"))["tier"],
        "premise_use"
    );
    assert_eq!(
        consumer(&revised, format!("results:{RESULT}"))["disposition"],
        "revised"
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn issue_brief_keeps_follow_ups_visible_on_busy_issues() {
    let mut comments = vec![
        json!({"body":"Compare independent standards of goodness.","author":{"login":"reviewer"},"authorAssociation":"OWNER"}),
        json!({"body":"Test the practical inference.","author":{"login":"REPORTER"},"authorAssociation":"CONTRIBUTOR"}),
        json!({"body":"## Follow-up: which conception of goodness actually generates the maximization objection?","url":"https://github.com/o/r/issues/1955#issuecomment-2"}),
    ];
    for i in 1..=10 {
        comments.push(json!({"body":format!("Routine reply {i}.")}));
    }
    let report = json!({"number":1955, "issue":{"author":{"login":"reporter"}, "comments":comments},
        "records":[], "note_sections":[], "pull_requests":[]});
    let rendered = super::issue::render(&report, super::DEFAULT_LIMIT);
    for excerpt in [
        "@reviewer  (repository owner)",
        "@REPORTER  (issue author)",
        "Issue comment 3  https://github.com/o/r/issues/1955#issuecomment-2",
        "which conception of goodness actually generates the maximization objection?",
        "Routine reply 10.",
        "More issue comments in --json.",
    ] {
        assert!(rendered.contains(excerpt), "{excerpt}");
    }
    assert_eq!(
        rendered.matches("Issue comment ").count(),
        super::DEFAULT_LIMIT
    );
    assert!(!rendered.contains("Routine reply 7."));
}

#[test]
fn issue_brief_finds_review_and_delivery_while_issue_is_open() {
    let root = fixture("issue-handoff");
    let id = "73000000-0000-4000-8000-000000000012";
    let record = json!({
        "id":id,"label":"Memory comparison","summary":"The first handoff addressed #12",
        "current_assessment":{"scope":"The memory test for #12","publication":"published",
        "review":"accepted_qualified","reviewed_revision":"reviewed123","assessment":"Both accounts recover the result.",
        "supersedes":"Earlier transfer reading repaired","next_test":"Track the same bearer","note":"docs/notes/memory.md"}
    });
    write(
        &root,
        &format!("corpus/attempts/{id}.json"),
        &record.to_string(),
    );
    write(
        &root,
        "docs/notes/memory.md",
        "# Memory\n\n## Repair (#12)\n\nScoped reference: `STMT-FIX-SERIES`.\n\n## Other (#120)\n\nA different case.\n",
    );
    let section_id = "73000000-0000-4000-8000-000000000200";
    let other_id = "73000000-0000-4000-8000-000000000300";
    let file_id = "73000000-0000-4000-8000-000000000400";
    for (id, note) in [
        (section_id, "docs/notes/memory.md#repair-12"),
        (other_id, "docs/notes/memory.md#other-120"),
        (file_id, "docs/notes/memory.md"),
    ] {
        let linked = json!({"id":id,"label":"Section assessment",
            "current_assessment":{"scope":"Same-bearer comparison","note":note,
            "reviewed_revision":"linked456","next_test":"Check the section-specific prediction"}});
        write(
            &root,
            &format!("corpus/attempts/{id}.json"),
            &linked.to_string(),
        );
    }
    let pr_only_id = "73000000-0000-4000-8000-000000000500";
    let pr_only = json!({"id":pr_only_id,"label":"Delivery history","evidence":["PR-41","PR-410"]});
    write(
        &root,
        &format!("corpus/attempts/{pr_only_id}.json"),
        &pr_only.to_string(),
    );
    let snapshot = json!({"items":[
        {"number":12,"url":"https://github.com/o/r/issues/12","state":"OPEN","body":format!("Compare `{GOAL}`. See #40."),"crossReferences":["https://github.com/o/r/pull/41"],
         "comments":[{"body":"Prior discussion without metadata."},
                     {"body":format!("## Follow-up: which conception of goodness actually generates the maximization objection?\n\nOwner direction: compare competing senses and accounts of goodness. {} END_OF_LONG_COMMENT", "detail ".repeat(50)),
                      "url":"https://github.com/o/r/issues/12#issuecomment-2","createdAt":"2026-11-24T20:35:39Z"},
                     {"body":"  "}]},
        {"number":13,"url":"https://github.com/o/r/issues/13","comments":[{"body":"Owner direction: unrelated work."}]},
        {"number":40,"url":"https://github.com/o/r/pull/40","state":"MERGED"},
        {"number":41,"url":"https://github.com/o/r/pull/41","state":"MERGED","headRefOid":"delivered456"},
        {"number":42,"url":"https://github.com/o/r/pull/42","comments":[{"body":"The subsequent reading of #10/#12."}]},
        {"number":43,"url":"https://github.com/o/r/pull/43","body":"See #120, other/r#12 and https://github.com/other/r/issues/12."},
        {"number":44,"url":"https://github.com/other/r/pull/44","body":"For #12."}
    ]});
    let path = root.join("timeline.json");
    std::fs::write(&path, snapshot.to_string()).unwrap();
    let history = retrieval::Issues::Snapshot(
        retrieval::read_snapshot(path.to_str().unwrap(), None).unwrap(),
    );
    let corpus = Corpus::load(&root).unwrap();
    let brief = super::issue::report(&root, &corpus, 12, &history, Default::default()).unwrap();
    assert_eq!(brief["issue"]["state"], "OPEN");
    let prs = brief["pull_requests"].as_array().unwrap();
    assert_eq!(
        prs.iter()
            .map(|row| row["number"].as_u64().unwrap())
            .collect::<Vec<_>>(),
        vec![40, 41, 42]
    );
    assert_eq!(prs[1]["head"], "delivered456");
    assert!(
        prs[2]["mention_excerpt"]
            .as_str()
            .unwrap()
            .contains("#10/#12")
    );
    assert_eq!(
        brief["records"][0]["current_assessment"]["reviewed_revision"],
        "reviewed123"
    );
    assert!(
        brief["records"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["id"] == GOAL && row["named_by_issue"] == true)
    );
    let records = brief["records"].as_array().unwrap();
    let indirect = records.iter().find(|r| r["id"] == pr_only_id).unwrap();
    assert_eq!(indirect["cited_related_prs"], json!([41]));
    assert_eq!(indirect["direct"], false);
    let by_section = records.iter().find(|r| r["id"] == SERIES).unwrap();
    assert_eq!(
        by_section["named_by_sections"],
        json!(["docs/notes/memory.md#repair-12"])
    );
    let headings = brief["note_sections"].as_array().unwrap();
    assert!(headings.iter().any(|s| s["heading"] == "Repair (#12)"));
    assert!(!headings.iter().any(|s| s["heading"] == "Other (#120)"));
    let text = super::issue::render(&brief, 1);
    for term in [
        "reviewed123",
        "Track the same bearer",
        "Earlier transfer reading repaired",
        "PR #41",
        "Issue comment 2  2026-11-24T20:35:39Z  https://github.com/o/r/issues/12#issuecomment-2",
        "which conception of goodness actually generates the maximization objection? Owner direction: compare competing senses",
        "More issue comments in --json.",
    ] {
        assert!(text.contains(term), "{term}");
    }
    for absent in ["END_OF_LONG_COMMENT", "Prior discussion", "unrelated work"] {
        assert!(!text.contains(absent), "{absent}");
    }
    let expanded = super::issue::render(&brief, 2);
    assert!(expanded.contains("Issue comment 1\n    Prior discussion without metadata."));
    assert!(!expanded.contains("More issue comments"));
    assert_eq!(brief["issue"]["comments"], snapshot["items"][0]["comments"]);
    let split =
        json!({"issues":[snapshot["items"][0]],"pull_requests":[{"number":40,"state":"OPEN"}]});
    std::fs::write(&path, split.to_string()).unwrap();
    let split_history = retrieval::Issues::Snapshot(
        retrieval::read_snapshot(path.to_str().unwrap(), None).unwrap(),
    );
    let split =
        super::issue::report(&root, &corpus, 12, &split_history, Default::default()).unwrap();
    assert_eq!(split["pull_requests"][0]["number"], 40);
    let missing = retrieval::Issues::Missing {
        meaning: retrieval::MISSING_ISSUES,
    };
    let local = super::issue::report(&root, &corpus, 12, &missing, Default::default()).unwrap();
    assert_eq!(local["issue_history"]["availability"], "missing");
    assert!(local["pull_requests"].as_array().unwrap().is_empty());
    assert_eq!(local["records"][0]["id"], id);
    let records = local["records"].as_array().unwrap();
    assert!(records.iter().any(|r| r["id"] == section_id
        && r["assessment_section"] == "docs/notes/memory.md#repair-12"
        && r["mentions_issue"] == false));
    assert!(
        records
            .iter()
            .all(|r| r["id"] != other_id && r["id"] != file_id)
    );
    assert!(super::issue::render(&local, 2).contains("Check the section-specific prediction"));
    assert!(records.iter().all(|r| r["id"] != pr_only_id));
    assert!(!root.join(".cache/truth-index.sqlite").exists());
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn question_synthesis_follows_the_assessment_scope_and_keeps_disagreement() {
    let root = fixture("synthesis-question");
    let write_judgment = |id: &str, review: &str, judgment: &str| {
        write(&root, &format!("corpus/attempts/{id}.json"), &json!({
            "id": id, "statement_ids":[GOAL, OPEN_PREMISE],
            "summary": "Antiquarian search phrase unique to the retired handoff.",
            "current_assessment": {
                "statement_ids":[OPEN_PREMISE], "scope":"Common giver at the actual recipient",
                "assessment":judgment, "next_test":"Identify both recipients on this relation.",
                "note":"docs/notes/priority.md#common-giver","review":review,
                "publication":"published","reviewed_revision":"1234567890123456789012345678901234567890"
            }
        }).to_string());
    };
    write_judgment(
        "d0000000-0000-4000-8000-000000000091",
        "accepted_qualified",
        "One common giver fits the observations. Distinct sources also fit.",
    );
    write_judgment(
        "d0000000-0000-4000-8000-000000000092",
        "unreviewed",
        "A common giver would explain the result if the causal bridge held.",
    );
    let corpus = Corpus::load(&root).unwrap();
    let (report, text) = super::assessment_search::report(&corpus, "common giver", 1).unwrap();
    let matches = report["matches"].as_array().unwrap();
    assert_eq!(matches.len(), 2);
    assert!(
        matches
            .iter()
            .all(|m| m["targets"].as_array().unwrap().len() == 1
                && m["targets"][0]["id"] == OPEN_PREMISE)
    );
    assert!(matches.iter().any(|m| m["review"] == "unreviewed"));
    assert!(text.contains(&format!("truth synthesis {OPEN_PREMISE}")));
    assert!(text.contains("1 further match"));
    assert!(
        super::assessment_search::matches(&corpus, "antiquarian")
            .unwrap()
            .is_empty()
    );
    assert!(
        super::assessment_search::matches(&corpus, "what?")
            .unwrap()
            .is_empty()
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_dedicated_prior_investigation_outweighs_an_incidental_current_match() {
    let root = fixture("question-before-structured-assessments");
    write(&root, "corpus/attempts/prior.json", &json!({
        "id":"d0000000-0000-4000-8000-000000000093","label":"Evil and emotivism",
        "statement_ids":[GOAL],"summary":"An emotivist can still press an internal objection from evil.",
        "blocker":"What does the target concede?", "outcome":"succeeded"
    }).to_string());
    write(&root,"corpus/attempts/incidental.json",&json!({
        "id":"d0000000-0000-4000-8000-000000000094","statement_ids":[OPEN_PREMISE],
        "current_assessment":{"scope":"The problem of calendar dating","assessment":"A dated record survives.",
        "statement_ids":[OPEN_PREMISE],"review":"accepted_qualified"}
    }).to_string());
    let corpus = Corpus::load(&root).unwrap();
    let (result, text) = super::assessment_search::report(
        &corpus,
        "Does emotivism dissolve the problem of evil?",
        1,
    )
    .unwrap();
    let matches = result["matches"].as_array().unwrap();
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0]["kind"], "prior_investigation");
    assert!(text.contains("internal objection from evil"));
    assert!(!text.contains("accepted_qualified"));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn question_search_features_substantive_passages_and_keeps_locators_out_of_ranking() {
    let root = fixture("question-evidence-passages");
    let locator = "Read docs/notes/amber-shale-layers.md.";
    let finding = "The amber inclusions precede both shale layers.";
    let competing = "The shale layers contain amber inclusions of different ages.";
    record(
        &root,
        "statements",
        json!({"id":GOAL,"label":"Amber shale layers",
        "paraphrase":"The amber is above both shale layers."}),
    );
    record(
        &root,
        "attempts",
        json!({"id":"d0000000-0000-4000-8000-000000000095",
        "label":"Field observations", "statement_ids":[GOAL],
        "summary":format!("Sample Q.12 represents a second outcrop. {finding} {locator}")}),
    );
    record(
        &root,
        "attempts",
        json!({"id":"d0000000-0000-4000-8000-000000000096",
        "label":"An alternative timeline","statement_ids":[GOAL], "summary":competing}),
    );
    write(&root, "corpus/attempts/amber-shale-layers.json", &json!({
        "id":"d0000000-0000-4000-8000-000000000097", "label":"Comparison index",
        "statement_ids":[GOAL], "summary":format!("Measurements were taken at the shoreline. {locator}")}).to_string());
    let corpus = Corpus::load(&root).unwrap();
    let (report, prose) =
        super::assessment_search::report(&corpus, "amber shale layers", 2).unwrap();
    let matches = report["matches"].as_array().unwrap();
    assert_eq!(matches.len(), 2);
    assert!(prose.contains(finding));
    assert!(prose.contains(competing));
    assert!(!prose.contains(locator));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn search_retrieves_a_scoped_note_when_attempts_miss_the_question_phrase() {
    let root = fixture("question-note-fallback");
    record(
        &root,
        "attempts",
        json!({"id":"d0000000-0000-4000-8000-000000000098",
        "label":"Temporary equipment","summary":"The temporary sensors belong to the same apparatus.",
        "statement_ids":[GOAL]}),
    );
    let note = "The sensors can be temporally coincident in this apparatus.";
    write(
        &root,
        "docs/notes/experimental.md",
        &format!("# Readings\n\n## Sensor timing\n\n{note}\n"),
    );
    let corpus = Corpus::load(&root).unwrap();
    let (report, prose) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "Are the sensors temporally coincident?",
        2,
    )
    .unwrap();
    assert_eq!(
        report["note_match"]["section"],
        "docs/notes/experimental.md#sensor-timing"
    );
    assert_eq!(report["note_match"]["passage"], note);
    assert!(prose.contains(note));
    assert!(!root.join(".cache/truth-index.sqlite").exists());
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_generic_phrase_in_a_note_cannot_displace_a_more_specific_investigation() {
    let root = fixture("question-note-competing-topic");
    record(
        &root,
        "attempts",
        json!({"id":"d0000000-0000-4000-8000-000000000099",
        "label":"Museum acquisition", "statement_ids":[GOAL],
        "summary":"Pottery fragments identify the missing archive."}),
    );
    write(
        &root,
        "docs/notes/funding.md",
        "# Accounting\n\nThe grant covered public access.\n",
    );
    let corpus = Corpus::load(&root).unwrap();
    let (report, prose) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "Does pottery in the archive support public access?",
        2,
    )
    .unwrap();
    assert_eq!(report["matches"][0]["scope"], "Museum acquisition");
    assert!(report.get("note_match").is_none());
    assert!(!prose.contains("The grant covered"));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_conversational_introduction_preserves_the_displayed_question_and_the_topic_ranking() {
    let root = fixture("question-conversational-introduction");
    record(
        &root,
        "attempts",
        json!({"id":"d0000000-0000-4000-8000-000000000100",
        "label":"Cross section", "statement_ids":[GOAL], "summary":"The amber inclusions precede both shale layers."}),
    );
    record(
        &root,
        "attempts",
        json!({"id":"d0000000-0000-4000-8000-000000000101",
        "label":"Our reasons to believe", "statement_ids":[GOAL], "summary":"We currently have reason to believe the testimony."}),
    );
    let corpus = Corpus::load(&root).unwrap();
    let q = "What do we currently have reason to believe about the amber inclusions?";
    let (report, prose) = super::assessment_search::report(&corpus, q, 2).unwrap();
    let direct = super::assessment_search::matches(&corpus, "the amber inclusions?").unwrap();
    assert_eq!(report["matches"], json!(direct));
    assert_eq!(report["matches"][0]["scope"], "Cross section");
    assert_eq!(report["question"], q);
    assert!(prose.contains(q));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn question_returns_frozen_lean_evidence_without_any_notes_or_assessments() {
    let root = fixture("proof-question");
    std::fs::remove_dir_all(root.join("docs")).unwrap();
    std::fs::remove_dir_all(root.join("corpus/attempts")).unwrap();
    let source = "namespace TruthCore.Results.Fixture\ntheorem goal (h : True) : True := by\n  sorry\nend TruthCore.Results.Fixture\n";
    write(&root, "TruthCore/Results/Fixture/Challenge.lean", source);
    write(
        &root,
        "TruthCore/Results/Fixture/Solution.lean",
        &source.replace("sorry", "exact h"),
    );
    record(
        &root,
        "statements",
        json!({"id":GOAL, "label":"Cardinality surcharge",
        "paraphrase":"The goal follows."}),
    );
    let corpus = Corpus::load(&root).unwrap();
    for question in [
        "TruthCore.Results.Fixture.goal",
        "goal from the open bridge",
        "Cardinality surcharge",
    ] {
        let (result, text) =
            super::assessment_search::report_for_root(&root, &corpus, question, 2).unwrap();
        let proofs = result["lean_results"].as_array().unwrap();
        assert_eq!(proofs.len(), 1);
        assert_eq!(proofs[0]["id"], RESULT);
        assert_eq!(proofs[0]["premise_statement_ids"], json!([OPEN_PREMISE]));
        assert_eq!(proofs[0]["conclusion_statement_id"], GOAL);
        assert!(text.contains("goal (h : True) : True"), "{text}");
        assert!(text.contains("Matching Lean results"));
        assert!(result["matches"].as_array().unwrap().is_empty());
    }
    let (primary, text) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "TruthCore.Results.Fixture.goal",
        1,
    )
    .unwrap();
    assert_eq!(primary["lean_results"][0]["result_label"], "Goal result");
    assert_eq!(primary["comparator_companions"], json!([]));
    assert!(text.contains(&format!(
        "Registered primary theorem — Goal result [{RESULT}]"
    )));

    let companion = "namespace TruthCore.Results.Fixture\ntheorem paired : True := by\n  sorry\ntheorem pending : True := by\n  sorry\nend TruthCore.Results.Fixture\n";
    write(&root, "TruthCore/Results/Fixture/Challenge.lean", companion);
    write(
        &root,
        "TruthCore/Results/Fixture/Solution.lean",
        "namespace TruthCore.Results.Fixture\ntheorem paired : True := by\n  trivial\nend TruthCore.Results.Fixture\n",
    );
    for (name, module, detail) in [
        ("paired", "Solution", "trivial"),
        ("pending", "Challenge", "Frozen Lean specification"),
    ] {
        let (lookup, text) = super::assessment_search::report_for_root(
            &root,
            &corpus,
            &format!("TruthCore.Results.Fixture.{name}"),
            1,
        )
        .unwrap();
        assert_eq!(
            lookup["lean_declaration"]["path"],
            format!("TruthCore/Results/Fixture/{module}.lean")
        );
        assert_eq!(lookup["comparator_companions"], json!([]));
        assert!(text.contains(detail), "{text}");
    }
    let (library, text) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "TruthCore.Fixture.Priority.DependenceExcludesBeingWithout",
        2,
    )
    .unwrap();
    assert_eq!(
        library["lean_declaration"]["path"],
        "TruthCore/Fixture/Priority.lean"
    );
    assert!(text.contains("∀ x y, DependsForBeing x y"));
    assert_ne!(
        library["lean_declaration"]["name"],
        library["lean_results"][0]["theorem"]
    );
    let (wrong, _) =
        super::assessment_search::report_for_root(&root, &corpus, "Wrong.Namespace.goal", 2)
            .unwrap();
    assert_eq!(wrong["lean_results"], json!([]));
    assert!(wrong.get("lean_declaration").is_none());
    let (miss, _) =
        super::assessment_search::report_for_root(&root, &corpus, "xylophones", 2).unwrap();
    assert_eq!(miss["lean_results"], json!([]));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn question_discovers_existing_lean_helpers_without_theorem_names_or_notes() {
    let root = fixture("question-library-reuse");
    std::fs::remove_dir_all(root.join("docs")).unwrap();
    std::fs::remove_dir_all(root.join("corpus/attempts")).unwrap();
    let path = "TruthCore/Results/Causality/ContingentAncestry/Solution.lean";
    write(
        &root,
        path,
        r#"namespace TruthCore.Results.Causality.ContingentAncestry
/-- Founded descent among contingent ancestors yields a necessary ancestor. -/
theorem necessaryAncestor (h : True) :
    True := by
  exact h

private theorem contingentNecessaryAncestorDescent : True := by
  trivial

theorem unrelated : True := by
  -- contingent necessary ancestor descent
  trivial
end TruthCore.Results.Causality.ContingentAncestry
"#,
    );
    write(
        &root,
        "TruthCore/Results/Causality/ContingentAncestry/Challenge.lean",
        "namespace TruthCore.Results.Causality.ContingentAncestry\ntheorem contingentNecessaryAncestorDescentPending : True := by\n  sorry\nend TruthCore.Results.Causality.ContingentAncestry\n",
    );
    let corpus = Corpus::load(&root).unwrap();
    let (report, text) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "contingent necessary ancestor descent",
        5,
    )
    .unwrap();
    let candidates = report["lean_library_candidates"].as_array().unwrap();
    assert_eq!(candidates.len(), 1, "{candidates:?}");
    assert_eq!(
        candidates[0]["name"],
        "TruthCore.Results.Causality.ContingentAncestry.necessaryAncestor"
    );
    assert_eq!(candidates[0]["path"], path);
    assert_eq!(candidates[0]["line"], 3);
    assert_eq!(candidates[0]["registered_result_ids"], json!([]));
    assert_eq!(
        candidates[0]["signature"],
        "theorem necessaryAncestor (h : True) :\n    True"
    );
    assert!(report["lean_results"].as_array().unwrap().is_empty());
    assert!(text.contains("source matches, not equivalence or verification claims"));
    assert!(text.contains(path));
    assert!(!text.contains("exact h"));
    assert!(!text.contains("sorry"));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn library_candidates_skip_comment_prose_and_keep_assignments_inside_types() {
    let root = fixture("question-library-comments");
    std::fs::remove_dir_all(root.join("docs")).unwrap();
    std::fs::remove_dir_all(root.join("corpus/attempts")).unwrap();
    let path = "TruthCore/Results/Fixture/Comments/Solution.lean";
    write(
        &root,
        path,
        r#"namespace TruthCore.Results.Fixture.Comments
/-- The bridge gives common nature, and the imported
theorem gives identity bridge. Conditional on the OPEN bridge. -/
theorem uniqueIdentityBridge (h : Preserved (G := G) s) (x : C)
    (q : Q { x with a := 1 }) : let y := x; IdentityBridge s y := by
  exact h -- := not a signature
/- outer /- inner -/
theorem phantomIdentityBridge : True := by
  trivial
-/
end TruthCore.Results.Fixture.Comments
"#,
    );
    let corpus = Corpus::load(&root).unwrap();
    let (report, _) =
        super::assessment_search::report_for_root(&root, &corpus, "identity bridge", 5).unwrap();
    let candidates = report["lean_library_candidates"].as_array().unwrap();
    assert_eq!(candidates.len(), 1, "{candidates:?}");
    assert_eq!(
        candidates[0]["name"],
        "TruthCore.Results.Fixture.Comments.uniqueIdentityBridge"
    );
    assert_eq!(
        candidates[0]["signature"],
        "theorem uniqueIdentityBridge (h : Preserved (G := G) s) (x : C)\n    \
         (q : Q { x with a := 1 }) : let y := x; IdentityBridge s y"
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn contingent_descent_retrieves_the_existing_necessary_ancestor_implementation() {
    let root = fixture("question-real-contingent-ancestry");
    std::fs::remove_dir_all(root.join("docs")).unwrap();
    std::fs::remove_dir_all(root.join("corpus/attempts")).unwrap();
    let path = "TruthCore/Results/Causality/ContingentAncestry/Solution.lean";
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let source = std::fs::read_to_string(repository.join(path)).unwrap();
    write(&root, path, &source);
    let corpus = Corpus::load(&root).unwrap();
    let (report, _) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "contingent necessary ancestor descent",
        5,
    )
    .unwrap();
    let candidates = report["lean_library_candidates"].as_array().unwrap();
    assert!(
        candidates.iter().any(|hit| {
            hit["name"] == "TruthCore.Results.Causality.ContingentAncestry.necessaryAncestor"
                && hit["path"] == path
                && hit["signature"]
                    .as_str()
                    .is_some_and(|s| s.contains("ContingentConeFounded"))
        }),
        "{candidates:?}"
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn registered_proof_search_uses_theorem_words_and_result_descriptions() {
    let root = fixture("question-result-description");
    std::fs::remove_dir_all(root.join("docs")).unwrap();
    std::fs::remove_dir_all(root.join("corpus/attempts")).unwrap();
    record(
        &root,
        "results",
        json!({
            "id": RESULT,
            "label": "Goal result",
            "argument_id": ARGUMENT,
            "challenge_module": "TruthCore.Results.Fixture.Challenge",
            "solution_module": "TruthCore.Results.Fixture.Solution",
            "theorem": "TruthCore.Results.Fixture.necessaryAncestor",
            "comparator_config": "results/x/comparator.json",
            "status": "solution-present",
            "description": "Contingent founded descent along actual inputs."
        }),
    );
    let corpus = Corpus::load(&root).unwrap();
    let (report, _) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "contingent necessary ancestor descent",
        5,
    )
    .unwrap();
    assert_eq!(report["lean_results"][0]["id"], RESULT);
    assert_eq!(
        report["lean_results"][0]["theorem"],
        "TruthCore.Results.Fixture.necessaryAncestor"
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn exact_lean_lookup_uses_comparator_names_and_frozen_locations() {
    let root = fixture("question-comparator-companions");
    let second = "c0000000-0000-4000-8000-000000000002";
    let unrelated = "c0000000-0000-4000-8000-000000000003";
    let scope = "TruthCore.Results.Fixture";
    let companion = format!("{scope}.paired");
    let challenge = format!("{scope}.Challenge");
    let challenge_path = "TruthCore/Results/Fixture/Challenge.lean";
    let frozen = "namespace TruthCore.Other\ntheorem paired : True := by\n  sorry\nend TruthCore.Other\n\nnamespace TruthCore.Results.Fixture\ntheorem goal : True := by\n  sorry\ntheorem otherGoal : True := by\n  sorry\ntheorem paired : True := by\n  sorry\nend TruthCore.Results.Fixture\n";
    write(&root, challenge_path, frozen);
    write(
        &root,
        "TruthCore/Results/Fixture/Solution.lean",
        &format!(
            "{}\nnamespace {scope}\ntheorem helper : True := by\n  trivial\nend {scope}\n",
            frozen.replace("sorry", "trivial"),
        ),
    );
    for (id, path, primary, label) in [
        (RESULT, "results/x/comparator.json", "goal", "Goal result"),
        (
            second,
            "results/y/comparator.json",
            "otherGoal",
            "Other goal result",
        ),
    ] {
        let primary = format!("{scope}.{primary}");
        record(
            &root,
            "results",
            json!({"id":id, "label":label, "argument_id":ARGUMENT,
                "theorem":primary, "challenge_module":challenge, "comparator_config":path,
                "solution_module":format!("{scope}.Solution"), "status":"solution-present"}),
        );
        write(
            &root,
            path,
            &json!({"challenge_module":challenge,"theorem_names":[primary,companion,companion]})
                .to_string(),
        );
    }
    record(
        &root,
        "results",
        json!({"id":unrelated, "label":"Unrelated result", "argument_id":ARGUMENT,
            "theorem":"TruthCore.Unrelated.paired", "comparator_config":"results/z/comparator.json",
            "challenge_module":"TruthCore.Unrelated.Challenge", "solution_module":"TruthCore.Unrelated.Solution",
            "status":"solution-present"}),
    );
    write(
        &root,
        "results/z/comparator.json",
        r#"{"theorem_names":["TruthCore.Unrelated.paired","TruthCore.Unrelated.helper"]}"#,
    );
    let corpus = Corpus::load(&root).unwrap();
    let (lookup, text) =
        super::assessment_search::report_for_root(&root, &corpus, &format!("`{companion}`"), 1)
            .unwrap();
    assert_eq!(lookup["lean_results"], json!([]));
    assert_eq!(lookup["lean_declaration"]["name"], companion);
    assert_eq!(
        lookup["comparator_companions"],
        json!([
            {"result_id":RESULT, "result_label":"Goal result", "comparator_config":"results/x/comparator.json",
                "challenge_path":challenge_path, "challenge_line":11},
            {"result_id":second, "result_label":"Other goal result", "comparator_config":"results/y/comparator.json",
                "challenge_path":challenge_path, "challenge_line":11}
        ])
    );
    assert!(text.contains("Companion theorem listed in Comparator configuration"));
    assert!(text.contains(&format!("Goal result [{RESULT}]")));
    assert!(text.contains(&format!("Other goal result [{second}]")));
    assert!(text.contains(&format!("Frozen Challenge — {challenge_path}:11")));
    assert!(!text.contains("Unrelated result"));

    for name in [
        format!("{scope}.helper"),
        "TruthCore.Other.paired".to_owned(),
    ] {
        let (helper, text) =
            super::assessment_search::report_for_root(&root, &corpus, &name, 2).unwrap();
        assert_eq!(helper["lean_declaration"]["name"], name);
        assert_eq!(helper["lean_results"], json!([]));
        assert_eq!(helper["comparator_companions"], json!([]));
        assert!(text.contains("Lean library declaration"));
        assert!(!text.contains("Comparator configuration"));
    }
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn question_returns_explicit_attempt_evidence_when_result_text_does_not_match() {
    let root = fixture("question-cited-lean-results");
    let current = "d0000000-0000-4000-8000-000000000102";
    let prior = "d0000000-0000-4000-8000-000000000103";
    let second_result = "c0000000-0000-4000-8000-000000000002";
    let uncited_result = "c0000000-0000-4000-8000-000000000003";
    let theorem = "TruthCore.Results.Fixture.goal";
    for (id, name) in [
        (second_result, "corollary"),
        (uncited_result, "independent"),
    ] {
        record(
            &root,
            "results",
            json!({"id":id, "argument_id":ARGUMENT, "theorem":format!("TruthCore.Results.Fixture.{name}"),
                "challenge_module":"TruthCore.Results.Fixture.Challenge",
                "solution_module":"TruthCore.Results.Fixture.Solution",
                "comparator_config":"results/x/comparator.json","status":"solution-present"}),
        );
    }
    record(
        &root,
        "attempts",
        json!({"id":current,"label":"Earlier readings","statement_ids":[GOAL, OPEN_PREMISE],
            "evidence":[RESULT,second_result,"PR-41"],
            "current_assessment":{
                "scope":"Finite store after a cut",
                "assessment":"A finite store allows sustained output after a cut. The open bridge still needs support.",
                "statement_ids":[OPEN_PREMISE],"review":"accepted_qualified"
            }
        }),
    );
    record(
        &root,
        "attempts",
        json!({"id":prior,"label":"Earlier readings","statement_ids":[GOAL],
            "summary":"A finite store allows sustained output after a cut.",
            "evidence":[RESULT,GOAL,"PR-42"]}),
    );
    let corpus = Corpus::load(&root).unwrap();
    let run = |question, limit| {
        super::assessment_search::report_for_root(&root, &corpus, question, limit).unwrap()
    };
    let source = |attempt_id| {
        json!({
            "attempt_id":attempt_id, "path":format!("corpus/attempts/{attempt_id}.json")
        })
    };
    let question =
        "Does sustained output after a cut require ongoing input or can a finite store explain it?";
    let (report, text) = run(question, 3);
    assert_eq!(report["lean_results"], json!([]));
    let cited = report["cited_lean_results"].as_array().unwrap();
    assert_eq!(cited.len(), 2);
    assert_eq!(cited[0]["id"], RESULT);
    assert_eq!(cited[0]["theorem"], theorem);
    assert_eq!(
        cited[0]["cited_by"],
        json!([source(current), source(prior)])
    );
    assert_eq!(cited[1]["id"], second_result);
    assert_eq!(cited[1]["cited_by"], json!([source(current)]));
    assert_eq!(report["matches"][0]["statement_ids"], json!([OPEN_PREMISE]));
    for term in [
        "No direct text match for a registered Lean result.",
        "Lean results cited in the investigations' evidence history",
        &format!("Cited in attempt evidence — {prior} (corpus/attempts/{prior}.json)"),
        &format!("Result {RESULT}"),
        theorem,
    ] {
        assert!(text.contains(term), "{text}");
    }
    assert_eq!(text.matches(theorem).count(), 1);
    assert!(!text.contains("PR-41"));

    let (limited, _) = run(question, 1);
    let cited = limited["cited_lean_results"].as_array().unwrap();
    assert_eq!(cited.len(), 1);
    assert_eq!(cited[0]["cited_by"], json!([source(current)]));

    let (direct, text) = run("open bridge", 3);
    assert_eq!(direct["lean_results"][0]["id"], RESULT);
    assert_eq!(
        direct["lean_results"][0]["cited_by"],
        json!([source(current)])
    );
    assert_eq!(direct["cited_lean_results"], json!([]));
    assert_eq!(text.matches(theorem).count(), 1);
    assert!(text.contains(&format!("Cited in attempt evidence — {current}")));

    let (exact, _) = run(theorem, 3);
    assert_eq!(exact["lean_results"][0]["id"], RESULT);
    assert!(exact["lean_results"][0].get("cited_by").is_none());
    assert_eq!(exact["cited_lean_results"], json!([]));

    let (miss, text) = run("two-world model", 3);
    assert_eq!(miss["cited_lean_results"], json!([]));
    assert!(text.contains("The displayed investigations cite no registered Lean results."));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_limited_question_preserves_proofs_about_the_current_assessment() {
    let root = fixture("current-assessment-cited-proofs");
    let recent = "c0000000-0000-4000-8000-000000000006";
    let argument = "a0000000-0000-4000-8000-000000000006";
    let attempt = "d0000000-0000-4000-8000-000000000106";
    record(
        &root,
        "arguments",
        json!({"id":argument, "label":"Finite tracer consequence", "meaning":"The recent consequence follows from the supplied bridge.", "inference_ids":[INFERENCE],
        "conclusion_statement_id":SERIES, "premise_statement_ids":[]}),
    );
    record(
        &root,
        "results",
        json!({"id":recent, "argument_id":argument,
        "theorem":"TruthCore.Results.Fixture.recent", "status":"solution-present", "challenge_module":"TruthCore.Results.Fixture.Challenge", "solution_module":"TruthCore.Results.Fixture.Solution", "comparator_config":"results/x/comparator.json"}),
    );
    record(
        &root,
        "attempts",
        json!({"id":attempt, "label":"Earlier and later studies",
        "statement_ids":[GOAL, SERIES], "evidence":[RESULT, recent],
        "current_assessment":{"scope":"Finite supplier audits", "assessment":"Finite supplier audits identify the initial bearer.", "statement_ids":[SERIES]}}),
    );
    let corpus = Corpus::load(&root).unwrap();
    for limit in [1, 2] {
        let (report, _) = super::assessment_search::report_for_root(
            &root,
            &corpus,
            "finite supplier audits",
            limit,
        )
        .unwrap();
        let citations = report["cited_lean_results"].as_array().unwrap();
        assert_eq!(citations[0]["id"], recent);
        assert_eq!(citations[0]["cited_by"][0]["attempt_id"], attempt);
        assert_eq!(citations.len(), limit);
        if limit == 2 {
            assert_eq!(citations[1]["id"], RESULT);
        }
    }
    // Both conclusions are now in scope. The question selects the last citation.
    // The second slot still exposes the first recorded result.
    record(
        &root,
        "statements",
        json!({"id":GOAL, "label":"The goal follows", "paraphrase":"The comparison permits a finite supply."}),
    );
    let other = "c0000000-0000-4000-8000-000000000007";
    record(
        &root,
        "results",
        json!({"id":other, "argument_id":ARGUMENT, "label":"A tracer", "theorem":"TruthCore.Results.Fixture.other",
            "challenge_module":"TruthCore.Results.Fixture.Challenge","solution_module":"TruthCore.Results.Fixture.Solution",
            "comparator_config":"results/x/comparator.json","status":"solution-present"}),
    );
    record(
        &root,
        "attempts",
        json!({"id":attempt, "label":"Earlier and later studies",
            "statement_ids":[GOAL, SERIES], "evidence":[RESULT, other, recent],
            "current_assessment":{"scope":"Finite supplier audits", "assessment":"A tracer marks the initial bearer in a finite supplier audit.", "statement_ids":[GOAL, SERIES]}}),
    );
    let corpus = Corpus::load(&root).unwrap();
    let (report, _) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "Does a finite supplier audit leave a tracer?",
        1,
    )
    .unwrap();
    assert_eq!(report["lean_results"], json!([]));
    assert_eq!(report["cited_lean_results"][0]["id"], recent);
    let (report, _) = super::assessment_search::report_for_root(
        &root,
        &corpus,
        "Does a finite supplier audit leave a tracer?",
        2,
    )
    .unwrap();
    assert_eq!(report["cited_lean_results"][1]["id"], RESULT);
    std::fs::remove_dir_all(root).unwrap();
}
