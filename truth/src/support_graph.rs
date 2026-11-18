//! Complete result-backed premise/conclusion graph for symbolic support analysis.
//!
//! This projection deliberately does not use frontier closure: direct inputs and
//! registered implications remain distinct, including conditional transcriptions.
//! Consumers must take the least fixed point and disable the current target's
//! direct input. A result record supplies provenance, not fresh verification.

use crate::{Corpus, Record, sha256::sha256_hex, thickness::text};
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

pub const DEFAULT_TARGETS: [&str; 2] = [
    "8626f8a5-9531-5da7-9ebd-f901e74b1129", // God exists.
    "da3facd6-008e-5e76-92fa-677350c2dfdb", // Same necessary classical root.
];

pub const SCOPE: &str = "Exact backward slice of registered statement-ID rules; not premise truth, joint satisfiability, a complete inventory of possible arguments, or fresh Lean verification.";

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    NoTargets,
    UnknownTarget(String),
    MissingArgument { result: String, argument: String },
    MissingStatement { argument: String, statement: String },
    Serialization(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoTargets => write!(f, "at least one target statement is required"),
            Self::UnknownTarget(id) => write!(f, "unknown target statement: {id}"),
            Self::MissingArgument { result, argument } => {
                write!(f, "result {result} references missing argument {argument}")
            }
            Self::MissingStatement {
                argument,
                statement,
            } => {
                write!(
                    f,
                    "argument {argument} references missing statement {statement}"
                )
            }
            Self::Serialization(message) => {
                write!(f, "could not serialize support graph: {message}")
            }
        }
    }
}

impl std::error::Error for Error {}

#[derive(Debug, Serialize)]
pub struct Statement {
    pub id: String,
    pub path: String,
    pub legacy_id: Option<String>,
    pub label: String,
    pub paraphrase: String,
    pub lean_declaration: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ResultProvenance {
    pub result_id: String,
    pub path: String,
    pub theorem: String,
    pub solution_module: String,
    pub status: String,
    pub transcription: Option<Value>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Rule {
    pub argument_id: String,
    pub argument_path: String,
    pub premise_statement_ids: Vec<String>,
    pub conclusion_statement_id: String,
    pub result_ids: Vec<String>,
    pub results: Vec<ResultProvenance>,
}

#[derive(Debug, Serialize)]
pub struct Conjunction {
    pub premise_statement_ids: Vec<String>,
    /// All immediate arguments with exactly this premise set.
    pub argument_ids: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct DirectSummary {
    pub rule_count: usize,
    pub result_count: usize,
    pub distinct_input_count: usize,
    pub distinct_conjunction_count: usize,
    pub minimal_conjunction_count: usize,
    pub minimal_conjunctions: Vec<Conjunction>,
}

#[derive(Debug, Serialize)]
pub struct SupportGraph {
    pub schema_version: u32,
    pub kind: &'static str,
    pub complete: bool,
    pub input_identity: String,
    /// Digest of targets, statement dictionary and rule provenance, independent
    /// of Git metadata and unrelated corpus records.
    pub graph_sha256: String,
    pub scope: &'static str,
    pub semantics: Value,
    pub target_statement_ids: Vec<String>,
    pub statement_count: usize,
    pub rule_count: usize,
    pub result_count: usize,
    pub terminal_statement_count: usize,
    pub terminal_statement_ids: Vec<String>,
    pub statements: Vec<Statement>,
    pub rules: Vec<Rule>,
    pub direct: BTreeMap<String, DirectSummary>,
}

fn optional_text(record: &Record, key: &str) -> Option<String> {
    record
        .fields
        .get(key)
        .and_then(Value::as_str)
        .map(str::to_owned)
}

fn direct_summary(rules: &[Rule], target: &str) -> DirectSummary {
    let immediate: Vec<_> = rules
        .iter()
        .filter(|r| r.conclusion_statement_id == target)
        .collect();
    let inputs: BTreeSet<_> = immediate
        .iter()
        .flat_map(|r| &r.premise_statement_ids)
        .collect();
    let mut conjunctions: BTreeMap<Vec<String>, Vec<String>> = BTreeMap::new();
    for rule in &immediate {
        conjunctions
            .entry(rule.premise_statement_ids.clone())
            .or_default()
            .push(rule.argument_id.clone());
    }
    let minimal_conjunctions: Vec<_> = conjunctions
        .iter()
        .filter(|(premises, _)| {
            !conjunctions.keys().any(|other| {
                other.len() < premises.len()
                    && other.iter().all(|p| premises.binary_search(p).is_ok())
            })
        })
        .map(|(premises, arguments)| Conjunction {
            premise_statement_ids: premises.clone(),
            argument_ids: arguments.clone(),
        })
        .collect();
    DirectSummary {
        rule_count: immediate.len(),
        result_count: immediate.iter().map(|r| r.results.len()).sum(),
        distinct_input_count: inputs.len(),
        distinct_conjunction_count: conjunctions.len(),
        minimal_conjunction_count: minimal_conjunctions.len(),
        minimal_conjunctions,
    }
}

/// Export the union of complete backward slices, without a traversal cap.
///
/// All result-backed arguments are conditional edges, irrespective of status,
/// transcription or route-designation metadata. Multiple results of the same
/// argument preserve their provenance but contribute only one graph edge.
pub fn build(corpus: &Corpus, targets: &[String]) -> Result<SupportGraph, Error> {
    let targets: BTreeSet<_> = targets.iter().cloned().collect();
    if targets.is_empty() {
        return Err(Error::NoTargets);
    }
    for target in &targets {
        if corpus.get("statements", target).is_none() {
            return Err(Error::UnknownTarget(target.clone()));
        }
    }
    let mut results_by_argument: BTreeMap<String, Vec<ResultProvenance>> = BTreeMap::new();
    for (id, result) in corpus.records_by_id("results") {
        // Corpus::load has already validated these required string fields.
        let argument_id = text(&result.fields, "argument_id");
        if corpus.get("arguments", argument_id).is_none() {
            return Err(Error::MissingArgument {
                result: id.into(),
                argument: argument_id.into(),
            });
        }
        results_by_argument
            .entry(argument_id.into())
            .or_default()
            .push(ResultProvenance {
                result_id: id.into(),
                path: result.path.clone(),
                theorem: text(&result.fields, "theorem").into(),
                solution_module: text(&result.fields, "solution_module").into(),
                status: text(&result.fields, "status").into(),
                transcription: result.fields.get("transcription").cloned(),
            });
    }
    let mut by_conclusion: BTreeMap<String, Vec<Rule>> = BTreeMap::new();
    for (argument_id, results) in results_by_argument {
        let argument =
            corpus
                .get("arguments", &argument_id)
                .ok_or_else(|| Error::MissingArgument {
                    result: results
                        .first()
                        .map(|r| r.result_id.clone())
                        .unwrap_or_default(),
                    argument: argument_id.clone(),
                })?;
        let conclusion = text(&argument.fields, "conclusion_statement_id");
        let premises: BTreeSet<String> =
            crate::thickness::list(&argument.fields, "premise_statement_ids")
                .into_iter()
                .map(str::to_owned)
                .collect();
        for statement in premises.iter().map(String::as_str).chain([conclusion]) {
            if corpus.get("statements", statement).is_none() {
                return Err(Error::MissingStatement {
                    argument: argument_id.clone(),
                    statement: statement.into(),
                });
            }
        }
        by_conclusion
            .entry(conclusion.into())
            .or_default()
            .push(Rule {
                argument_id,
                argument_path: argument.path.clone(),
                premise_statement_ids: premises.into_iter().collect(),
                conclusion_statement_id: conclusion.into(),
                result_ids: results.iter().map(|r| r.result_id.clone()).collect(),
                results,
            });
    }
    let mut reached = targets.clone();
    let mut pending: VecDeque<_> = targets.iter().cloned().collect();
    let mut selected = BTreeMap::new();
    while let Some(conclusion) = pending.pop_front() {
        for rule in by_conclusion.get(&conclusion).into_iter().flatten() {
            selected.insert(rule.argument_id.clone(), rule.clone());
            for premise in &rule.premise_statement_ids {
                if reached.insert(premise.clone()) {
                    pending.push_back(premise.clone());
                }
            }
        }
    }
    let rules: Vec<_> = selected.into_values().collect();
    let statements: Vec<_> = reached
        .iter()
        .map(|id| {
            // Targets and every result-backed premise were checked above.
            let record = corpus
                .get("statements", id)
                .ok_or_else(|| Error::UnknownTarget(id.clone()))?;
            Ok(Statement {
                id: id.clone(),
                path: record.path.clone(),
                legacy_id: optional_text(record, "legacy_id"),
                label: optional_text(record, "label").unwrap_or_else(|| id.clone()),
                paraphrase: text(&record.fields, "paraphrase").into(),
                lean_declaration: optional_text(record, "lean_declaration"),
            })
        })
        .collect::<Result<_, Error>>()?;
    let terminal_statement_ids: Vec<_> = reached
        .into_iter()
        .filter(|id| !by_conclusion.contains_key(id))
        .collect();
    let direct = targets
        .iter()
        .map(|id| (id.clone(), direct_summary(&rules, id)))
        .collect();
    let target_statement_ids: Vec<_> = targets.into_iter().collect();
    let bytes = serde_json::to_vec(&(&target_statement_ids, &statements, &rules))
        .map_err(|error| Error::Serialization(error.to_string()))?;
    Ok(SupportGraph {
        schema_version: 1,
        kind: "registered-support-graph",
        complete: true,
        input_identity: corpus.input_identity(),
        graph_sha256: sha256_hex(&bytes),
        scope: SCOPE,
        semantics: json!({
            "rules": "one edge per argument with at least one registered result; all result witnesses retained",
            "transcriptions": "included as conditional implications",
            "direct_or_derived": "direct premise input OR conjunctions of recursively supported rule premises",
            "terminal_inputs": "statements with no incoming result-backed rule",
            "target_input": "disable the current target's direct input in either basis, even if terminal; other target inputs remain available",
            "cycles": "least fixed point; a cycle supplies no initial evidence",
            "zero_premise_rules": "contribute true",
            "closed_floor_substitutions": false,
            "source_support_as_implication": false,
            "false_input": "premise not supplied, not its logical negation",
            "direct_absorption": "literal premise-set subset absorption only"
        }),
        statement_count: statements.len(),
        rule_count: rules.len(),
        result_count: rules.iter().map(|r| r.results.len()).sum(),
        terminal_statement_count: terminal_statement_ids.len(),
        target_statement_ids,
        terminal_statement_ids,
        statements,
        rules,
        direct,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Map;

    fn corpus(
        statements: &[&str],
        rules: &[(&str, &str, &[&str])],
        results: &[(&str, &str, bool)],
    ) -> Corpus {
        let mut kinds: BTreeMap<&'static str, BTreeMap<String, Record>> = BTreeMap::new();
        let mut add = |kind: &'static str, value: Value| {
            let fields: Map<_, _> = value.as_object().expect("fixture object").clone();
            let id = fields["id"].as_str().expect("fixture id").to_owned();
            kinds.entry(kind).or_default().insert(
                id.clone(),
                Record {
                    path: format!("corpus/{kind}/{id}.json"),
                    fields,
                },
            );
        };
        for id in statements {
            add(
                "statements",
                json!({"id": id, "label": id, "paraphrase": format!("{id} holds"), "status": "closed"}),
            );
        }
        for (id, conclusion, premises) in rules {
            add(
                "arguments",
                json!({"id": id, "conclusion_statement_id": conclusion, "premise_statement_ids": premises}),
            );
        }
        for (id, argument, transcription) in results {
            add(
                "results",
                json!({"id": id, "argument_id": argument, "theorem": format!("Fixture.{id}"), "solution_module": "Fixture", "status": "solution-present", "transcription": transcription}),
            );
        }
        Corpus {
            records: kinds,
            fingerprint: 0,
        }
    }

    fn targets(ids: &[&str]) -> Vec<String> {
        ids.iter().map(|id| (*id).into()).collect()
    }

    #[test]
    fn result_backing_absorption_and_provenance() {
        let corpus = corpus(
            &["P", "Q", "G", "U"],
            &[
                ("a", "G", &["P"]),
                ("b", "G", &["Q", "P", "P"]),
                ("c", "G", &["P"]),
                ("unproved", "G", &["U"]),
            ],
            &[
                ("r1", "a", true),
                ("r2", "a", false),
                ("r3", "b", false),
                ("r4", "c", false),
            ],
        );
        let graph = build(&corpus, &targets(&["G"])).expect("graph");
        assert_eq!(
            (graph.statement_count, graph.rule_count, graph.result_count),
            (3, 3, 4)
        );
        assert_eq!(graph.terminal_statement_ids, ["P", "Q"]);
        assert_eq!(graph.rules[0].result_ids, ["r1", "r2"]);
        assert_eq!(graph.rules[0].results[0].transcription, Some(json!(true)));
        assert_eq!(graph.rules[1].premise_statement_ids, ["P", "Q"]);
        let direct = &graph.direct["G"];
        assert_eq!(
            (
                direct.rule_count,
                direct.result_count,
                direct.distinct_input_count
            ),
            (3, 4, 2)
        );
        assert_eq!(
            (
                direct.distinct_conjunction_count,
                direct.minimal_conjunction_count
            ),
            (2, 1)
        );
        assert_eq!(direct.minimal_conjunctions[0].argument_ids, ["a", "c"]);
        assert_eq!(direct.minimal_conjunctions[0].premise_statement_ids, ["P"]);
        // "closed" statements remain inputs: no status-derived zero-premise edge.
        assert!(
            graph
                .rules
                .iter()
                .all(|r| !r.premise_statement_ids.is_empty())
        );
    }

    #[test]
    fn cycles_zero_premise_rules_and_target_union_are_preserved() {
        let corpus = corpus(
            &["P", "Q", "G", "T", "U"],
            &[
                ("pq", "Q", &["P"]),
                ("qp", "P", &["Q"]),
                ("qg", "G", &["Q"]),
                ("tg", "G", &["T"]),
                ("truth", "T", &[]),
            ],
            &[
                ("r1", "pq", false),
                ("r2", "qp", false),
                ("r3", "qg", false),
                ("r4", "tg", false),
                ("r5", "truth", false),
            ],
        );
        let graph = build(&corpus, &targets(&["U", "G", "G"])).expect("graph");
        assert_eq!(graph.target_statement_ids, ["G", "U"]);
        assert_eq!(graph.terminal_statement_ids, ["U"]);
        assert_eq!(graph.rule_count, 5);
        assert_eq!(
            graph
                .rules
                .iter()
                .filter(|r| r.premise_statement_ids.is_empty())
                .count(),
            1
        );
        assert_eq!(graph.direct["U"].rule_count, 0);
        assert_eq!(graph.semantics["closed_floor_substitutions"], false);
        let reordered = build(&corpus, &targets(&["G", "U"])).expect("reordered graph");
        assert_eq!(graph.graph_sha256, reordered.graph_sha256);
    }

    #[test]
    fn a_real_empty_conjunction_absorbs_other_immediate_options() {
        let corpus = corpus(
            &["P", "G"],
            &[("a", "G", &["P"]), ("b", "G", &[])],
            &[("r1", "a", false), ("r2", "b", false)],
        );
        let graph = build(&corpus, &targets(&["G"])).expect("graph");
        assert_eq!(graph.direct["G"].minimal_conjunction_count, 1);
        assert!(
            graph.direct["G"].minimal_conjunctions[0]
                .premise_statement_ids
                .is_empty()
        );
        assert_eq!(
            graph.direct["G"].minimal_conjunctions[0].argument_ids,
            ["b"]
        );
    }

    #[test]
    fn unknown_targets_and_dangling_rule_references_fail() {
        let empty = corpus(&["G"], &[], &[]);
        assert_eq!(
            build(&empty, &[]).expect_err("empty targets"),
            Error::NoTargets
        );
        assert_eq!(
            build(&empty, &targets(&["X"])).expect_err("unknown target"),
            Error::UnknownTarget("X".into())
        );
        let missing_argument = corpus(&["G"], &[], &[("r", "a", false)]);
        assert_eq!(
            build(&missing_argument, &targets(&["G"])).expect_err("missing argument"),
            Error::MissingArgument {
                result: "r".into(),
                argument: "a".into()
            }
        );
        let missing_premise = corpus(&["G"], &[("a", "G", &["P"])], &[("r", "a", false)]);
        assert_eq!(
            build(&missing_premise, &targets(&["G"])).expect_err("missing premise"),
            Error::MissingStatement {
                argument: "a".into(),
                statement: "P".into()
            }
        );
        let missing_conclusion = corpus(&["G"], &[("a", "X", &[])], &[("r", "a", false)]);
        assert_eq!(
            build(&missing_conclusion, &targets(&["G"])).expect_err("missing conclusion"),
            Error::MissingStatement {
                argument: "a".into(),
                statement: "X".into()
            }
        );
    }
}
