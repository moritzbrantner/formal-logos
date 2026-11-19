//! Challenge parsing, scratch generation and outcome classification, without
//! Lean (the messages are written by hand in `lean --json` form).

use super::*;

const CHALLENGE: &str = "import TruthCore.A
import TruthCore.B

namespace TruthCore.Results.X
open TruthCore.A

/-- A doc comment with `sorry` and := inside. -/
theorem first {B : Type} (P Q : B → Prop)
    (h : ∀ x, P x → Q x) (x : B) (hx : P x) : Q x := by
  sorry

-- theorem commented : True := by sorry

theorem proved : True := by
  trivial

/-- Two-line. -/
theorem second (p : Prop) (hp : p) : p := sorry

theorem _root_.Elsewhere.third : True := by sorry

end TruthCore.Results.X
";

fn challenge() -> Challenge {
    Challenge::parse("TruthCore.Results.X.Challenge", CHALLENGE)
}

#[test]
fn parses_imports_and_sorry_targets() {
    let c = challenge();
    assert_eq!(c.imports, ["TruthCore.A", "TruthCore.B"]);
    let names: Vec<&str> = c.targets.iter().map(|t| t.theorem.as_str()).collect();
    assert_eq!(
        names,
        [
            "TruthCore.Results.X.first",
            "TruthCore.Results.X.second",
            "Elsewhere.third"
        ]
    );
    let first = &c.targets[0];
    assert_eq!(
        first.statement,
        " {B : Type} (P Q : B → Prop)\n    (h : ∀ x, P x → Q x) (x : B) (hx : P x) : Q x"
    );
    // the span starts at the doc comment and ends after `sorry`
    let span = &c.body[first.span.0..first.span.1];
    assert!(span.starts_with("/-- A doc comment"), "{span}");
    assert!(span.ends_with("sorry"), "{span}");
    assert_eq!(c.targets[1].statement, " (p : Prop) (hp : p) : p");
}

#[test]
fn module_challenges_become_ordinary() {
    let text = "module\n\npublic import TruthCore.A\n\n@[expose] public section\n\nnamespace N\npublic theorem t : True := by sorry\nend N\n";
    let c = Challenge::parse("M.Challenge", text);
    assert_eq!(c.imports, ["TruthCore.A"]);
    assert!(!c.body.contains("public") && !c.body.contains("module"));
    assert_eq!(c.targets.len(), 1);
    assert_eq!(c.targets[0].theorem, "N.t");
}

#[test]
fn filters() {
    let names = vec!["first".to_owned()];
    assert!(selected("TruthCore.Results.X.first", &names, false));
    assert!(!selected("TruthCore.Results.X.firstly", &names, false));
    let modules = vec!["TruthCore.Results".to_owned()];
    assert!(selected("TruthCore.Results.X.Challenge", &modules, true));
    assert!(!selected("TruthCore.ResultsY.Challenge", &modules, true));
    assert!(selected("anything", &[], true));
}

#[test]
fn portfolio_order_and_copies() {
    let labels: Vec<&str> = PORTFOLIO.iter().map(|(label, _)| *label).collect();
    assert_eq!(
        labels,
        [
            "decide",
            "omega",
            "tauto",
            "simp_all",
            "aesop",
            "grind",
            "unfold+grind",
            "unfold+aesop"
        ]
    );
    let c = challenge();
    let scratch = generate(&[(&c, 0)], 1000);
    // per target: the portfolio, the probe, then the control
    assert_eq!(scratch.copies.len(), 3 * (PORTFOLIO.len() + 2));
    assert!(
        scratch
            .text
            .starts_with("import Aesop\nimport Mathlib.Tactic.Tauto\nimport TruthCore.A\n")
    );
    assert!(!scratch.text.contains("A doc comment"));
    assert!(
        scratch
            .text
            .contains("theorem proved : True := by\n  trivial")
    );
    let lines: Vec<&str> = scratch.text.split('\n').collect();
    for copy in &scratch.copies {
        let head = lines[copy.lines.0 - 1];
        assert_eq!(head, "set_option maxHeartbeats 1000 in", "{copy:?}");
        let tail = lines[copy.lines.1 - 1].trim();
        let expected = match copy.attempt {
            Attempt::Tactic(k) => PORTFOLIO[k].1,
            Attempt::Probe => "prove_sweep_probe",
            Attempt::Control => "sorry",
        };
        assert_eq!(tail, expected, "{copy:?}");
    }
    assert!(
        scratch
            .text
            .contains("theorem «prove_sweep_2_control» : True := by")
    );
    // one Challenge is not wrapped; several are, each in a section
    assert!(!scratch.text.contains("\nsection\n"));
    let two = generate(&[(&c, 0), (&c, 3)], 1000);
    assert_eq!(two.text.matches("\nsection\n").count(), 2);
    assert!(two.text.contains("«prove_sweep_5_control»"));
}

fn message(severity: &str, line: usize, data: &str) -> Message {
    Message {
        severity: severity.into(),
        line,
        data: data.into(),
    }
}

fn names(c: &Challenge) -> (BTreeMap<usize, (String, String)>, BTreeMap<usize, usize>) {
    let names = c
        .targets
        .iter()
        .enumerate()
        .map(|(i, t)| (i, (t.theorem.clone(), c.module.clone())))
        .collect();
    let chunks = (0..c.targets.len()).map(|i| (i, 0)).collect();
    (names, chunks)
}

fn line_of(scratch: &Scratch, target: usize, attempt: Attempt) -> usize {
    scratch
        .copies
        .iter()
        .find(|c| c.target == target && c.attempt == attempt)
        .unwrap()
        .lines
        .1
}

#[test]
fn classifies_closed_unresolved_error_and_transcriptions() {
    let c = challenge();
    let scratch = generate(&[(&c, 0)], 1000);
    let (names, chunks) = names(&c);
    let mut messages = Vec::new();
    // target 0: decide..simp_all fail, aesop closes; the probe applies h
    for k in 0..4 {
        messages.push(message(
            "error",
            line_of(&scratch, 0, Attempt::Tactic(k)),
            "failed",
        ));
    }
    messages.push(message(
        "information",
        line_of(&scratch, 0, Attempt::Probe),
        "prove-sweep-probe: apply h",
    ));
    messages.push(message(
        "warning",
        line_of(&scratch, 0, Attempt::Control),
        "declaration uses `sorry`",
    ));
    // target 1: everything fails, the probe closes it by assumption
    for k in 0..PORTFOLIO.len() {
        messages.push(message(
            "error",
            line_of(&scratch, 1, Attempt::Tactic(k)),
            "failed",
        ));
    }
    messages.push(message(
        "information",
        line_of(&scratch, 1, Attempt::Probe),
        "prove-sweep-probe: assumption",
    ));
    messages.push(message(
        "warning",
        line_of(&scratch, 1, Attempt::Control),
        "declaration uses `sorry`",
    ));
    // target 2: the statement does not elaborate
    messages.push(message(
        "error",
        line_of(&scratch, 2, Attempt::Control),
        "unknown identifier 'Foo'\nmore",
    ));
    let (outcomes, retry) = classify(&scratch, &messages, &names, &chunks);
    let by: Vec<(&str, Option<&str>, Option<&str>)> = outcomes
        .iter()
        .map(|(_, o)| (o.status, o.closed_by.as_deref(), o.transcription.as_deref()))
        .collect();
    assert_eq!(
        by,
        [
            ("closed", Some("aesop"), Some("apply h")),
            ("closed", Some(PROBE_LABEL), Some("assumption")),
            ("error", None, None),
        ]
    );
    assert_eq!(
        outcomes[2].1.message.as_deref(),
        Some("unknown identifier 'Foo'")
    );
    assert_eq!(retry, BTreeSet::from([0]));
    let json = outcomes[0].1.to_json();
    assert_eq!(json["likely_transcription"], true);
    let summary = summary(&outcomes.into_iter().map(|(_, o)| o).collect::<Vec<_>>());
    assert_eq!(summary["closed"], 2);
    assert_eq!(summary["closed_by"]["aesop"], 1);
    assert_eq!(summary["likely_transcriptions"], 2);
}

#[test]
fn a_sorry_warning_or_an_unreached_control_is_not_a_closure() {
    let c = challenge();
    let scratch = generate(&[(&c, 0)], 1000);
    let (names, chunks) = names(&c);
    // no messages at all: Lean never got there
    let (outcomes, retry) = classify(&scratch, &[], &names, &chunks);
    assert!(outcomes.iter().all(|(_, o)| o.status == "error"));
    assert_eq!(retry, BTreeSet::from([0]));
    // an import failure is reported as the reason
    let (outcomes, _) = classify(
        &scratch,
        &[message("error", 1, "unknown module prefix")],
        &names,
        &chunks,
    );
    assert_eq!(
        outcomes[0].1.message.as_deref(),
        Some("unknown module prefix")
    );
    // every tactic copy leaves a sorry: unresolved
    let mut messages = Vec::new();
    for copy in &scratch.copies {
        messages.push(message("warning", copy.lines.1, "declaration uses `sorry`"));
    }
    let (outcomes, retry) = classify(&scratch, &messages, &names, &chunks);
    assert!(
        outcomes.iter().all(|(_, o)| o.status == "unresolved"),
        "{outcomes:?}"
    );
    assert!(retry.is_empty());
}

#[test]
fn lean_json_messages() {
    let stdout = concat!(
        r#"{"severity":"error","pos":{"line":12,"column":3},"data":"boom"}"#,
        "\nnot json\n",
        r#"{"severity":"information","pos":{"line":4,"column":0},"data":"hi"}"#
    );
    assert_eq!(
        parse_messages(stdout),
        [
            message("error", 12, "boom"),
            message("information", 4, "hi")
        ]
    );
}
