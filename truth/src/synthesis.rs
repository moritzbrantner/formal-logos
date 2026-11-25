//! Read the scoped judgments on a proposition alongside the actual registered
//! arguments that produce and consume it. A shared citation is one record.
use crate::{
    Corpus, Record,
    context::{Lean, module_path},
    frontier::{Frontier, transcription_flags},
    lifecycle,
    thickness::{Records, list, text},
};
use serde::Serialize;
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

#[derive(Serialize)]
pub struct Statement<'a> {
    id: &'a str,
    path: &'a str,
    label: &'a str,
    paraphrase: &'a str,
    lean_declaration: Option<&'a Value>,
    definition_ids: Vec<&'a str>,
    disambiguation_ids: Vec<&'a str>,
}

impl<'a> From<&'a Record> for Statement<'a> {
    fn from(record: &'a Record) -> Self {
        let fields = &record.fields;
        Self {
            id: text(fields, "id"),
            path: &record.path,
            label: text(fields, "label"),
            paraphrase: text(fields, "paraphrase"),
            lean_declaration: fields.get("lean_declaration"),
            definition_ids: list(fields, "definition_ids"),
            disambiguation_ids: list(fields, "disambiguation_ids"),
        }
    }
}

#[derive(Serialize)]
struct Argument<'a> {
    argument_id: &'a str,
    argument_path: &'a str,
    label: &'a str,
    meaning: &'a str,
    conclusion_statement_id: &'a str,
    premise_statement_ids: Vec<&'a str>,
    commitment_statement_ids: Vec<&'a str>,
    result_ids: Vec<&'a str>,
    status: &'static str,
}

#[derive(Serialize)]
struct Premise<'a> {
    #[serde(flatten)]
    statement: Statement<'a>,
    assessment_ids: Vec<String>,
    formal_status: Value,
}

#[derive(Serialize)]
struct SharedPremise<'a> {
    statement_id: &'a str,
    argument_ids: BTreeSet<&'a str>,
}

#[derive(Serialize)]
struct SharedAssessment<'a> {
    attempt_id: String,
    /// Only the immediate premises that are explicitly indexed by this assessment.
    statement_ids: BTreeSet<&'a str>,
    argument_ids: BTreeSet<&'a str>,
}

#[derive(Serialize)]
pub struct Synthesis<'a> {
    schema_version: u32,
    input_identity: String,
    target: Statement<'a>,
    formal_status: Value,
    pub summary: Vec<String>,
    target_assessment_ids: Vec<String>,
    assessments: BTreeMap<String, Value>,
    routes: Vec<Argument<'a>>,
    premises: BTreeMap<&'a str, Premise<'a>>,
    shared_premises: Vec<SharedPremise<'a>>,
    shared_assessments: Vec<SharedAssessment<'a>>,
    consumers: Vec<Argument<'a>>,
    related_statements: BTreeMap<&'a str, Statement<'a>>,
    objections: Vec<Value>,
    results: BTreeMap<&'a str, Value>,
    direct_assumption_available: bool,
    /// All target-indexed attempts, including those without a scoped current judgment.
    target_attempt_paths: Vec<&'a str>,
}

fn statement<'a>(corpus: &'a Corpus, id: &str) -> Result<Statement<'a>, String> {
    corpus
        .get("statements", id)
        .map(Statement::from)
        .ok_or_else(|| format!("argument references missing statement {id}"))
}

/// Read the theorem specified by this result from its frozen Challenge.
pub fn result_witness(root: &Path, result: &Record) -> Value {
    let fields = &result.fields;
    let theorem = text(fields, "theorem");
    let challenge = text(fields, "challenge_module");
    let solution = text(fields, "solution_module");
    let (_, advertised) = Lean::new(root).challenge_statements(challenge, theorem);
    json!({
        "id": fields.get("id"),
        "path": result.path,
        "argument_id": fields.get("argument_id"),
        "theorem": fields.get("theorem"),
        "status": fields.get("status"),
        "challenge_path": (!challenge.is_empty()).then(|| module_path(challenge)),
        "solution_path": (!solution.is_empty()).then(|| module_path(solution)),
        "comparator_config": fields.get("comparator_config"),
        "advertised_statement": advertised,
    })
}

/// Render the exact frozen text and its source alongside the recorded status.
pub fn format_result_witness(witness: &Value) -> String {
    let status = witness["status"].as_str().unwrap_or("unspecified");
    let theorem = witness["theorem"].as_str().unwrap_or("unnamed theorem");
    let status_label = match status {
        "solution-present" => "solution-present, solution registered",
        "verified" => "verified in the result record",
        other => other,
    };
    let mut lines = vec![format!("Lean theorem — {theorem} ({status_label})")];
    let advertised = &witness["advertised_statement"];
    if let Some(declaration) = advertised["statement"].as_str() {
        lines.push(declaration.to_owned());
    } else {
        lines.push("The frozen declaration text is unavailable in this checkout.".into());
    }
    if let Some(path) = witness["challenge_path"].as_str() {
        let location = advertised["line"]
            .as_u64()
            .map(|line| format!(":{line}"))
            .unwrap_or_default();
        lines.push(format!("Challenge — {path}{location}"));
    }
    if let Some(path) = witness["solution_path"].as_str() {
        lines.push(format!("Solution — {path}"));
    }
    lines.join("\n")
}

/// Build the one-step argument neighborhood. All producer bundles are retained,
/// even transcriptions, unverified proposals, and bundles absorbed by another.
/// Separate commitments never become ordinary premises in the overlap analysis.
pub fn build<'a>(
    root: &Path,
    corpus: &'a Corpus,
    target: &'a Record,
) -> Result<Synthesis<'a>, String> {
    let target = Statement::from(target);
    let records = Records::from_corpus(corpus);
    let flags = transcription_flags(root, &records);
    let frontier = Frontier::new(target.id, &records, &flags);
    let mut results_by_argument: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for (id, result) in corpus.records_by_id("results") {
        results_by_argument
            .entry(text(&result.fields, "argument_id"))
            .or_default()
            .push((id, result));
    }
    let mut results = BTreeMap::new();
    let mut routes = Vec::new();
    let mut consumers = Vec::new();
    let mut uses = BTreeMap::<_, BTreeSet<_>>::new();
    let mut related_statements = BTreeMap::new();
    let mut route_results = BTreeSet::new();
    for (id, argument) in corpus.records_by_id("arguments") {
        let fields = &argument.fields;
        let conclusion = text(fields, "conclusion_statement_id");
        let premises = list(fields, "premise_statement_ids");
        let commitments = list(fields, "commitment_statement_ids");
        let produces = conclusion == target.id;
        let consumes = premises.contains(&target.id) || commitments.contains(&target.id);
        if !produces && !consumes {
            continue;
        }
        let witnesses = results_by_argument
            .get(id)
            .map(Vec::as_slice)
            .unwrap_or_default();
        for &(rid, result) in witnesses {
            results.entry(rid).or_insert_with(|| {
                let mut witness = result_witness(root, result);
                witness["transcription"] = json!(frontier.result_transcription(rid));
                witness
            });
        }
        let status = if witnesses.is_empty() {
            "unverified"
        } else if witnesses
            .iter()
            .all(|(rid, _)| frontier.result_transcription(rid).is_some())
        {
            "transcription"
        } else {
            "derivation"
        };
        let entry = || Argument {
            argument_id: id,
            argument_path: &argument.path,
            label: text(fields, "label"),
            meaning: text(fields, "meaning"),
            conclusion_statement_id: conclusion,
            premise_statement_ids: premises.clone(),
            commitment_statement_ids: commitments.clone(),
            result_ids: witnesses.iter().map(|(rid, _)| *rid).collect(),
            status,
        };
        if produces {
            route_results.extend(witnesses.iter().map(|(rid, _)| *rid));
            // Commitments stay visible independently of ordinary input status.
            for &sid in &commitments {
                related_statements.insert(sid, statement(corpus, sid)?);
            }
            for &premise in &premises {
                uses.entry(premise).or_default().insert(id);
            }
            routes.push(entry());
        }
        if consumes {
            for &sid in premises.iter().chain(&commitments).chain([&conclusion]) {
                if sid != target.id
                    && !uses.contains_key(sid)
                    && !related_statements.contains_key(sid)
                {
                    related_statements.insert(sid, statement(corpus, sid)?);
                }
            }
            consumers.push(entry());
        }
    }
    related_statements.retain(|id, _| !uses.contains_key(id));
    let scoped: BTreeSet<_> = uses.keys().copied().chain([target.id]).collect();
    let mut states = frontier.formal_statuses(&scoped);
    let formal_status = states[target.id].clone();
    let current = lifecycle::current(corpus, &scoped.iter().map(|id| id.to_string()).collect());
    let mut by_statement: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    let mut assessments = BTreeMap::new();
    let mut shared_assessments = Vec::new();
    for mut record in current {
        let aid = field(&record, "attempt_id").to_owned();
        let cited = corpus
            .get("attempts", &aid)
            .map(|attempt| list(&attempt.fields, "evidence"))
            .unwrap_or_default();
        record["route_results_cited_by_attempt"] = json!(
            cited
                .into_iter()
                .filter(|id| route_results.contains(id))
                .collect::<BTreeSet<_>>()
        );
        let mut linked = BTreeSet::new();
        let mut arguments = BTreeSet::new();
        for sid in record["statement_ids"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
        {
            if let Some(&known) = scoped.get(sid) {
                let ids = by_statement.entry(known).or_default();
                if !ids.contains(&aid) {
                    ids.push(aid.clone());
                }
                if let Some(routes) = uses.get(known) {
                    arguments.extend(routes);
                    linked.insert(known);
                }
            }
        }
        if arguments.len() > 1 {
            shared_assessments.push(SharedAssessment {
                attempt_id: aid.clone(),
                statement_ids: linked,
                argument_ids: arguments,
            });
        }
        assessments.insert(aid, record);
    }
    let target_assessment_ids = by_statement.get(target.id).cloned().unwrap_or_default();
    let mut shared_premises = Vec::new();
    let mut premises = BTreeMap::new();
    for (sid, arguments) in uses {
        premises.insert(
            sid,
            Premise {
                statement: statement(corpus, sid)?,
                assessment_ids: by_statement.remove(sid).unwrap_or_default(),
                formal_status: states.remove(sid).unwrap_or_default(),
            },
        );
        if arguments.len() > 1 {
            shared_premises.push(SharedPremise {
                statement_id: sid,
                argument_ids: arguments,
            });
        }
    }
    let mut objections = Vec::new();
    for (_, relation) in corpus.records_by_id("relations") {
        let fields = &relation.fields;
        let predicate = text(fields, "predicate");
        if text(fields, "object_kind") == "statement"
            && scoped.contains(text(fields, "object_id"))
            && matches!(predicate, "attacks" | "alternative_to" | "refutes")
        {
            let mut value = Value::Object(fields.clone());
            value["path"] = json!(relation.path);
            objections.push(value);
        }
    }
    let target_attempt_paths = corpus
        .records_by_id("attempts")
        .filter(|(_, record)| list(&record.fields, "statement_ids").contains(&target.id))
        .map(|(_, record)| record.path.as_str())
        .collect();
    let mut report = Synthesis {
        schema_version: 1,
        input_identity: corpus.input_identity(),
        target,
        formal_status,
        summary: Vec::new(),
        target_assessment_ids,
        assessments,
        routes,
        premises,
        shared_premises,
        shared_assessments,
        consumers,
        related_statements,
        objections,
        results,
        direct_assumption_available: true,
        target_attempt_paths,
    };
    report.summary = report.reading(DEFAULT_LIMIT);
    Ok(report)
}

pub const DEFAULT_LIMIT: usize = 2;

fn field<'a>(record: &'a Value, name: &str) -> &'a str {
    record[name].as_str().unwrap_or_default()
}

impl Synthesis<'_> {
    fn argument_label(&self, id: &str) -> &str {
        self.routes
            .iter()
            .find(|route| route.argument_id == id)
            .map_or("unnamed argument", |route| route.label)
    }

    fn position(&self, id: &str, include_test: bool) -> String {
        let record = &self.assessments[id];
        let review = match field(record, "review") {
            "accepted_qualified" => "Reviewed with qualifications",
            "unreviewed" => "Proposed, unreviewed",
            "changes_requested" => "Review requested changes",
            _ => "Review status unavailable",
        };
        let mut lines = vec![
            format!(
                "{review} · {} · {}",
                field(record, "date"),
                field(record, "scope")
            ),
            field(record, "assessment").to_string(),
        ];
        if include_test {
            lines.push(format!("Next test — {}", field(record, "next_test")));
        }
        lines.push(format!("Source — {}", field(record, "note")));
        lines.join("\n")
    }

    /// Presentation order is for navigation. Give a directly indexed position
    /// backed by a cited route result an early place, then surface another
    /// review status if present. None of these criteria grades warrant.
    fn positions(&self) -> Vec<&str> {
        let mut ids: Vec<_> = self
            .target_assessment_ids
            .iter()
            .map(String::as_str)
            .collect();
        ids.sort_by_key(|id| {
            let current = &self.assessments[*id];
            let cites_route = current["route_results_cited_by_attempt"]
                .as_array()
                .is_some_and(|r| !r.is_empty());
            let scope = current["statement_ids"].as_array().map_or(0, Vec::len);
            (
                current["review"] != "accepted_qualified",
                scope != 1,
                !cites_route,
                scope,
            )
        });
        if let Some(&first) = ids.first()
            && let Some(i) = ids
                .iter()
                .position(|id| self.assessments[*id]["review"] != self.assessments[first]["review"])
        {
            ids[1..=i].rotate_right(1);
        }
        ids
    }

    /// Give a readable producer with its frozen declaration first. The number
    /// of inputs only breaks ties between otherwise comparable examples.
    fn illustrative_argument(&self) -> String {
        let exemplar = self
            .routes
            .iter()
            .map(|route| {
                let witness = route
                    .result_ids
                    .iter()
                    .map(|rid| &self.results[rid])
                    .min_by_key(|result| {
                        (
                            result["advertised_statement"].is_null(),
                            !result["transcription"].is_null(),
                        )
                    });
                (route, witness)
            })
            .min_by_key(|(route, witness)| {
                (
                    witness.is_none_or(|w| w["advertised_statement"].is_null()),
                    match route.status {
                        "derivation" => 0,
                        "transcription" => 1,
                        _ => 2,
                    },
                    route.premise_statement_ids.len() + route.commitment_statement_ids.len(),
                )
            });
        let Some((route, witness)) = exemplar else {
            return "No registered argument concludes this statement. Its direct-assumption option remains available.".into();
        };

        let mut lines = vec![format!(
            "Illustrative argument ({}) — {}\n  truth context {}",
            route.status, route.label, route.argument_id
        )];
        if let Some(witness) = witness {
            lines.push(format_result_witness(witness));
        } else {
            lines.push(
                "No Lean result is registered for any argument concluding this statement.".into(),
            );
        }
        if route.premise_statement_ids.is_empty() {
            lines.push("  This argument registers no ordinary premises.".into());
        }
        for &id in &route.premise_statement_ids {
            lines.push(format!(
                "  {}  →  truth synthesis {id}",
                self.premises[id].statement.paraphrase
            ));
        }
        for &id in &route.commitment_statement_ids {
            let label = self
                .premises
                .get(id)
                .map(|p| p.statement.paraphrase)
                .or_else(|| self.related_statements.get(id).map(|s| s.paraphrase))
                .unwrap_or(id);
            lines.push(format!(
                "  Separate commitment — {label}  →  truth synthesis {id}"
            ));
        }
        lines.join("\n")
    }

    pub fn reading(&self, limit: usize) -> Vec<String> {
        let formal = if self.formal_status["established"] == true {
            "The frontier records this proposition as established."
        } else if self.formal_status["closure"] == "proved" {
            "The frontier records a conditional proof. The proposition remains unestablished."
        } else if self.formal_status["closure"].is_string() {
            "The frontier records closure. The proposition remains unestablished."
        } else {
            "The proposition remains open under the frontier rules."
        };
        let refutation = if self.formal_status["refuted"] == true {
            " The frontier also counts a refutation of this statement."
        } else {
            ""
        };
        let mut paragraphs = vec![format!("{}\n{formal}{refutation}", self.target.paraphrase)];
        if let Some(name) = self.target.lean_declaration.and_then(Value::as_str) {
            paragraphs.push(format!("Lean proposition — {name}"));
        }
        paragraphs.push(self.illustrative_argument());
        let positions = self.positions();
        let shown: BTreeSet<_> = positions.iter().copied().take(limit).collect();
        if positions.is_empty() {
            paragraphs.push(format!("No current assessment explicitly names this proposition. Earlier attempts and their findings can be inspected with truth dossier {}.", self.target.id));
        } else {
            for (idx, id) in positions.iter().take(limit).enumerate() {
                paragraphs.push(self.position(id, idx == 0));
            }
            if positions.len() > shown.len() {
                paragraphs.push(format!("{} further target-scoped judgments and their revision tests are available in --json.", positions.len() - shown.len()));
            }
        }
        if let Some(shared) = self.shared_premises.iter().max_by_key(|s| {
            (
                s.argument_ids.len(),
                !self.premises[s.statement_id].assessment_ids.is_empty(),
            )
        }) {
            let premise = &self.premises[shared.statement_id];
            let examples = shared
                .argument_ids
                .iter()
                .take(2)
                .map(|id| format!("“{}”", self.argument_label(id)))
                .collect::<Vec<_>>()
                .join(" and ");
            paragraphs.push(format!("The arguments {examples} both require “{}”. This premise occurs in {} of {} registered arguments for the target. Reusing it carries the same obligation into each argument.", premise.statement.paraphrase, shared.argument_ids.len(), self.routes.len()));
        } else if self.routes.len() > 1 {
            paragraphs.push("The registered arguments share no immediate premise ID. Deeper dependencies and common evidence can still connect them.".into());
        }
        // Give the actual verdict on a premise. Skip an assessment already quoted
        // for the target and prefer a premise recurring across several arguments.
        let mut samples: Vec<_> = self
            .premises
            .values()
            .filter_map(|p| {
                let id = p
                    .assessment_ids
                    .iter()
                    .filter(|id| !shown.contains(id.as_str()))
                    .min_by_key(|id| {
                        self.assessments[*id]["statement_ids"]
                            .as_array()
                            .map_or(usize::MAX, Vec::len)
                    })?;
                let multiplicity = self
                    .shared_premises
                    .iter()
                    .find(|shared| shared.statement_id == p.statement.id)
                    .map_or(1, |shared| shared.argument_ids.len());
                Some((std::cmp::Reverse(multiplicity), p, id))
            })
            .collect();
        samples.sort_by_key(|(overlap, p, _)| (*overlap, p.statement.id));
        if let Some((_, p, id)) = samples.first() {
            let mut example = format!(
                "A judgment indexed to the premise “{}”\n{}",
                p.statement.paraphrase,
                self.position(id, false)
            );
            if let Some(shared) = self
                .shared_assessments
                .iter()
                .find(|s| &s.attempt_id == *id)
            {
                example.push_str(&format!(
                    "\nThis one assessment is indexed to premises used by {} of these arguments.",
                    shared.argument_ids.len()
                ));
            }
            paragraphs.push(example);
        }
        if let Some(missing) = self.premises.values().find(|p| p.assessment_ids.is_empty()) {
            paragraphs.push(format!("No scoped current assessment is recorded for the premise “{}”. Earlier work can be inspected with truth dossier {}.", missing.statement.paraphrase, missing.statement.id));
        }
        if let Some(relation) = self
            .objections
            .iter()
            .find(|r| field(r, "object_id") == self.target.id)
            .or_else(|| self.objections.first())
        {
            let sid = field(relation, "object_id");
            let statement = self
                .premises
                .get(sid)
                .map_or(self.target.paraphrase, |p| p.statement.paraphrase);
            paragraphs.push(format!("Recorded challenge to “{statement}” — {} ({}). A registered challenge carries its own assumptions. See {}.", field(relation,"label"),field(relation,"predicate"),field(relation,"path")));
        }
        if let Some(consumer) = self.consumers.iter().min_by_key(|a| {
            (
                a.conclusion_statement_id != crate::support_graph::DEFAULT_TARGETS[0],
                a.status == "unverified",
            )
        }) {
            let inputs = consumer
                .premise_statement_ids
                .iter()
                .filter(|id| **id != self.target.id)
                .map(|&id| {
                    self.premises
                        .get(id)
                        .map(|p| p.statement.label)
                        .or_else(|| self.related_statements.get(id).map(|s| s.label))
                        .unwrap_or(id)
                })
                .collect::<Vec<_>>();
            let co_premises = match inputs.as_slice() {
                [] => "It has no other registered premise.".to_string(),
                [one] => format!("It also needs “{one}”."),
                [a, b] => format!("It also needs “{a}” and “{b}”."),
                [first, rest @ ..] => format!(
                    "It also needs “{first}” and {} other premises listed in --json.",
                    rest.len()
                ),
            };
            paragraphs.push(format!(
                "Downstream, “{}” uses this statement ({}). {co_premises} See {}.",
                consumer.label, consumer.status, consumer.argument_path
            ));
        }
        paragraphs.push("Use --json for every scope, review, test, premise, challenge and argument. Follow a premise with truth synthesis PREMISE_ID.".into());
        paragraphs
    }
}
