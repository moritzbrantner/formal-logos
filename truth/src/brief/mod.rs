//! `truth brief` and `truth novelty` (#1643, #954 slice B9): an
//! evidence-linked, read-only research brief and an advisory novelty check.
//!
//! Both views **retrieve**; neither decides. Formal status comes only from
//! the frontier report (`dossier::FrontierView`); arguments, rivals, strength
//! orders, attempts and senses from the corpus records the dossier reads;
//! note passages from `docs/notes` (through the `truth index` projection and
//! explicit mentions, `truth::notes`); issue history only from an offline
//! snapshot, whose absence or age is reported. Every entry cites its record,
//! note section or issue. Notes and issues are research text and workflow
//! history: a note never becomes a certified entailment, an issue's state is
//! not philosophical warrant, a verified result with an open premise stays a
//! conditional consequence, and no hit (or no snapshot) is evidence that no
//! prior work exists.

pub mod novelty;
pub mod retrieval;
#[cfg(test)]
mod tests;

use crate::{
    Corpus, Record,
    dossier::{DossierIndex, FrontierView},
    identity::Aliases,
    notes,
};
use retrieval::{Issues, Query, Revision};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

/// A record by kind and id.
pub type RecordKey = (String, String);

/// Default number of entries per section in the text view.
pub const DEFAULT_LIMIT: usize = 6;
/// Candidate note sections and records taken from the index per query.
const CANDIDATES: i64 = 80;
/// Notes evaluated paragraph by paragraph per query.
const NOTES_EVALUATED: usize = 16;

/// What every brief says about itself.
pub const BOUNDARY: &str = "retrieval only: formal status is the frontier's; notes are uncertified research text; \
     issue state is workflow history, not warrant; a verified result with an open premise is a conditional \
     consequence; an absent hit or snapshot is not evidence that no prior work exists";

/// The shared inputs of one brief or novelty run.
pub struct Inputs<'a> {
    pub root: &'a Path,
    pub corpus: &'a Corpus,
    pub aliases: &'a Aliases,
    pub view: &'a FrontierView,
    pub issues: &'a Issues,
    pub revision: Revision,
}

fn text<'a>(record: &'a Map<String, Value>, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn list<'a>(record: &'a Map<String, Value>, field: &str) -> Vec<&'a str> {
    record
        .get(field)
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect()
}

impl Inputs<'_> {
    /// `{kind, id, label}` of a record reference.
    pub fn reference(&self, kind: &str, id: &str) -> Value {
        json!({"kind": kind, "id": id, "label": self.aliases.label(id)})
    }

    /// The frontier's verdict on a statement, and nothing more.
    pub fn formal_state(&self, sid: &str) -> Value {
        let item = self.view.item(sid);
        let state = match (self.view.closed_statements.get(sid), item) {
            (Some(_), _) => "closed",
            (None, Some(_)) => "open",
            (None, None) => "not on the frontier",
        };
        json!({
            "state": state,
            "closure": self.view.closed_statements.get(sid),
            "established": self.view.established_statements.contains(sid),
            "reaches_root": self.view.reaching_root_statements.contains(sid),
            "frontier_status": item.and_then(|item| item.get("status")).cloned(),
        })
    }

    /// The revision identity every view reports.
    pub fn identity(&self) -> Value {
        json!({
            "revision": self.revision,
            "input_identity": self.corpus.input_identity(),
            "frontier_root": self.view.root,
        })
    }

    fn statement(&self, sid: &str) -> Option<&Map<String, Value>> {
        self.corpus
            .get("statements", sid)
            .map(|record| &record.fields)
    }
}

/// A brief's target: a statement, or an argument or result read through its
/// conclusion.
pub fn target_statement(corpus: &Corpus, kind: &str, id: &str) -> Option<String> {
    match kind {
        "statements" => Some(id.to_owned()),
        "arguments" => corpus
            .get("arguments", id)
            .map(|record| text(&record.fields, "conclusion_statement_id").to_owned()),
        "results" => corpus
            .get("results", id)
            .and_then(|result| corpus.get("arguments", text(&result.fields, "argument_id")))
            .map(|record| text(&record.fields, "conclusion_statement_id").to_owned()),
        _ => None,
    }
}

fn argument_entry(inputs: &Inputs, argument: &Record, results: &[&Record]) -> Value {
    let fields = &argument.fields;
    let premises = list(fields, "premise_statement_ids");
    let open: Vec<&str> = premises
        .iter()
        .copied()
        .filter(|premise| !inputs.view.established_statements.contains(*premise))
        .collect();
    let result_entries: Vec<Value> = results
        .iter()
        .map(|result| {
            let id = text(&result.fields, "id");
            json!({
                "id": id,
                "label": inputs.aliases.label(id),
                "theorem": result.fields.get("theorem"),
                "status": result.fields.get("status"),
                "transcription": inputs.view.transcription_results.get(id).map(|kind| kind.kind.clone()),
                "path": result.path,
            })
        })
        .collect();
    let reading = if results.is_empty() {
        "argument record without a verification result: no checked consequence"
    } else if open.is_empty() {
        "verified result whose premises are all established in the frontier"
    } else {
        "verified conditional consequence: it supports the conclusion only together with its unestablished premises"
    };
    json!({
        "id": text(fields, "id"),
        "label": text(fields, "label"),
        "path": argument.path,
        "premises": premises.iter().map(|premise| json!({
            "id": premise,
            "label": inputs.aliases.label(premise),
            "state": inputs.formal_state(premise)["state"],
            "established": inputs.view.established_statements.contains(*premise),
        })).collect::<Vec<_>>(),
        "unestablished_premises": open,
        "results": result_entries,
        "reading": reading,
    })
}

/// The note sections explicitly mentioning `ids`, grouped by section, with
/// the note's latest written date, superseded markers and the recorded
/// assessments and rival analysis of each mentioning note.
fn note_evidence(
    inputs: &Inputs,
    ids: &BTreeSet<&str>,
) -> Result<(Vec<Value>, Vec<Value>), String> {
    let lookup = notes::Lookup::of_corpus(inputs.corpus);
    let found = notes::mentioning(inputs.root, &lookup, ids)?;
    let mut sections: BTreeMap<String, (String, String, usize, BTreeSet<String>)> = BTreeMap::new();
    let mut order: Vec<String> = Vec::new();
    for entry in &found {
        let key = entry["section"].as_str().unwrap_or_default().to_owned();
        if !sections.contains_key(&key) {
            order.push(key.clone());
        }
        let section = sections.entry(key).or_insert_with(|| {
            (
                entry["path"].as_str().unwrap_or_default().to_owned(),
                entry["heading"].as_str().unwrap_or_default().to_owned(),
                entry["line"].as_u64().unwrap_or_default() as usize,
                BTreeSet::new(),
            )
        });
        section.3.insert(format!(
            "{} ({})",
            entry["mention"].as_str().unwrap_or_default(),
            entry["kind"].as_str().unwrap_or_default()
        ));
    }
    let paths: BTreeSet<String> = sections.values().map(|(path, ..)| path.clone()).collect();
    let mut notes_read: BTreeMap<String, notes::Note> = BTreeMap::new();
    let mut texts: BTreeMap<String, String> = BTreeMap::new();
    for path in &paths {
        let raw = std::fs::read_to_string(inputs.root.join(path))
            .map_err(|error| format!("{path}: {error}"))?;
        notes_read.insert(path.clone(), notes::parse(path, &raw));
        texts.insert(path.clone(), raw);
    }
    let mut out: Vec<Value> = order
        .iter()
        .map(|key| {
            let (path, heading, line, mentions) = &sections[key];
            json!({
                "section": key,
                "path": path,
                "heading": heading,
                "line": line,
                "mentions": mentions,
                "note_date": retrieval::latest_date(&texts[path]),
                "superseded_markers": superseded(&texts[path], path),
            })
        })
        .collect();
    // Newest written note first; within a note, file order.
    out.sort_by(|a, b| {
        b["note_date"]
            .as_str()
            .cmp(&a["note_date"].as_str())
            .then_with(|| a["path"].as_str().cmp(&b["path"].as_str()))
            .then_with(|| a["line"].as_u64().cmp(&b["line"].as_u64()))
    });
    let mut assessments = Vec::new();
    for (path, note) in &notes_read {
        assessments.extend(assessment_sections(note, &texts[path], 4));
    }
    sort_assessments(&mut assessments);
    Ok((out, assessments))
}

fn superseded(raw: &str, path: &str) -> Vec<Value> {
    retrieval::superseded_lines(raw)
        .into_iter()
        .map(|(offset, line)| json!({"location": format!("{path} line {}", offset + 1), "text": line}))
        .collect()
}

/// The judgment-headed and rival-headed sections of a note (at most `limit`
/// of each), each with the paragraph that states what is or is not settled.
pub fn assessment_sections(note: &notes::Note, raw: &str, limit: usize) -> Vec<Value> {
    let note_date = retrieval::latest_date(raw);
    let mut out = Vec::new();
    for (kind, heading) in [
        ("assessment", &*retrieval::ASSESSMENT_HEADING),
        ("rival_analysis", &*retrieval::RIVAL_HEADING),
    ] {
        let mut taken = 0;
        for section in &note.sections {
            if taken == limit
                || section.level == 0
                || !heading.is_match(&section.heading).unwrap_or(false)
            {
                continue;
            }
            // A judgment heading takes precedence over a rival heading.
            if kind == "rival_analysis"
                && retrieval::ASSESSMENT_HEADING
                    .is_match(&section.heading)
                    .unwrap_or(false)
            {
                continue;
            }
            let paragraphs = retrieval::paragraphs(&section.body, retrieval::body_line(section));
            let Some((line, paragraph)) = retrieval::status_paragraph(&paragraphs) else {
                continue;
            };
            taken += 1;
            out.push(json!({
                "kind": kind,
                "section": note.key(section),
                "heading": section.heading,
                "line": line,
                "date": retrieval::latest_date(&section.heading).or_else(|| note_date.clone()),
                "dated_by": if retrieval::latest_date(&section.heading).is_some() { "heading" } else { "latest date written in the note" },
                "excerpt": retrieval::excerpt(paragraph, 360),
            }));
        }
    }
    out
}

/// Newest first by recorded date, then location: several notes' judgments
/// are listed side by side, never reconciled.
pub fn sort_assessments(assessments: &mut [Value]) {
    assessments.sort_by(|a, b| {
        b["date"]
            .as_str()
            .cmp(&a["date"].as_str())
            .then_with(|| a["section"].as_str().cmp(&b["section"].as_str()))
    });
}

/// The snapshot issues that explicitly mention one of `ids` (exact uuid,
/// legacy id, label code span or record path), are acceptance-targeted at
/// `sid`, or are referenced by number from `referenced`.
fn issue_evidence(
    inputs: &Inputs,
    sid: Option<&str>,
    ids: &BTreeSet<&str>,
    referenced: &BTreeMap<u64, Vec<String>>,
) -> Result<Vec<Value>, String> {
    let Some(snapshot) = inputs.issues.snapshot() else {
        return Ok(Vec::new());
    };
    let lookup = notes::Lookup::of_corpus(inputs.corpus);
    let targeted: BTreeSet<u64> = match sid {
        Some(sid) => crate::issues::analyze(
            &snapshot.issues,
            inputs.corpus,
            &inputs.view.closed_statements,
            Some(inputs.root),
        )
        .map(|report| report.issues_for_id(sid).into_iter().collect())
        .unwrap_or_default(),
        None => BTreeSet::new(),
    };
    let mut out = Vec::new();
    for issue in &snapshot.issues {
        let number = issue
            .get("number")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        let mut reasons: Vec<Value> = Vec::new();
        if targeted.contains(&number) {
            reasons.push(json!({"why": "acceptance block names the target", "where": "truth-core-acceptance"}));
        }
        let mut mentioned = BTreeSet::new();
        for (place, unit) in retrieval::issue_units(issue) {
            let section = notes::Section {
                anchor: String::new(),
                heading: String::new(),
                level: 0,
                line: 1,
                body: unit,
            };
            for link in lookup.links(&section).0 {
                if ids.contains(link.id.as_str()) && mentioned.insert(link.id.clone()) {
                    reasons.push(json!({
                        "why": "explicit mention",
                        "where": place,
                        "mention": link.mention,
                        "record": inputs.reference(&link.kind, &link.id),
                    }));
                }
            }
        }
        if let Some(places) = referenced.get(&number) {
            reasons.push(json!({"why": "referenced by number from a note", "where": places}));
        }
        if !reasons.is_empty() {
            let mut header = retrieval::issue_header(issue);
            header["reasons"] = json!(reasons);
            out.push(header);
        }
    }
    out.sort_by(|a, b| {
        let count = |value: &Value| value["reasons"].as_array().map_or(0, Vec::len);
        count(b)
            .cmp(&count(a))
            .then_with(|| b["number"].as_u64().cmp(&a["number"].as_u64()))
    });
    Ok(out)
}

/// Issue numbers referenced from note sections, with their locations.
fn note_references(root: &Path, sections: &[Value]) -> BTreeMap<u64, Vec<String>> {
    let mut out: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    let mut cache: BTreeMap<String, notes::Note> = BTreeMap::new();
    for entry in sections {
        let path = entry["path"].as_str().unwrap_or_default();
        let key = entry["section"].as_str().unwrap_or_default();
        if !cache.contains_key(path)
            && let Ok(raw) = std::fs::read_to_string(root.join(path))
        {
            cache.insert(path.to_owned(), notes::parse(path, &raw));
        }
        let Some(note) = cache.get(path) else {
            continue;
        };
        for section in note
            .sections
            .iter()
            .filter(|section| note.key(section) == key)
        {
            for number in
                retrieval::issue_references(&format!("{}\n{}", section.heading, section.body))
            {
                let places = out.entry(number).or_default();
                if !places.iter().any(|place| place == key) {
                    places.push(key.to_owned());
                }
            }
        }
    }
    out
}

/// The research brief of statement `sid`. `requested` records an argument
/// or result target read through its conclusion.
pub fn statement_brief(
    inputs: &Inputs,
    sid: &str,
    requested: Option<Value>,
) -> Result<Value, String> {
    let corpus = inputs.corpus;
    let index = DossierIndex::new(corpus);
    let dossier = index
        .dossier(sid, inputs.view)
        .ok_or_else(|| format!("unknown statement: {sid}"))?;
    let statement = inputs.statement(sid).cloned().unwrap_or_default();
    let results_of = |argument: &str| -> Vec<&Record> {
        let mut found: Vec<&Record> = corpus
            .entries("results")
            .into_iter()
            .filter(|result| text(&result.fields, "argument_id") == argument)
            .collect();
        found.sort_by_key(|result| text(&result.fields, "id").to_owned());
        found
    };
    let mut concluding = Vec::new();
    let mut premise_of = Vec::new();
    for argument in corpus.entries("arguments") {
        let fields = &argument.fields;
        if text(fields, "conclusion_statement_id") == sid {
            concluding.push(argument_entry(
                inputs,
                argument,
                &results_of(text(fields, "id")),
            ));
        } else if list(fields, "premise_statement_ids").contains(&sid) {
            premise_of.push(json!({
                "id": text(fields, "id"),
                "label": text(fields, "label"),
                "conclusion": inputs.reference("statements", text(fields, "conclusion_statement_id")),
                "verified": !results_of(text(fields, "id")).is_empty(),
            }));
        }
    }
    // Rivals, objections, refutations, strength orders and equivalences.
    let relations: Vec<&Record> = corpus
        .entries("relations")
        .into_iter()
        .filter(|relation| {
            text(&relation.fields, "subject_id") == sid
                || text(&relation.fields, "object_id") == sid
        })
        .collect();
    let refuters = |target: &str| -> Vec<Value> {
        corpus
            .entries("relations")
            .into_iter()
            .filter(|relation| {
                text(&relation.fields, "predicate") == "refutes" && text(&relation.fields, "object_id") == target
            })
            .map(|relation| {
                json!({
                    "relation": text(&relation.fields, "id"),
                    "by": inputs.reference(text(&relation.fields, "subject_kind"), text(&relation.fields, "subject_id")),
                })
            })
            .collect()
    };
    let mut rivals = Vec::new();
    let mut strength = Vec::new();
    for relation in &relations {
        let fields = &relation.fields;
        let predicate = text(fields, "predicate");
        let outgoing = text(fields, "subject_id") == sid;
        let (other_kind, other) = if outgoing {
            (text(fields, "object_kind"), text(fields, "object_id"))
        } else {
            (text(fields, "subject_kind"), text(fields, "subject_id"))
        };
        let entry = json!({
            "relation": text(fields, "id"),
            "predicate": predicate,
            "direction": if outgoing { "target is subject" } else { "target is object" },
            "other": inputs.reference(other_kind, other),
            "other_state": (other_kind == "statement").then(|| inputs.formal_state(other)["state"].clone()),
            "note": fields.get("note").and_then(Value::as_str).map(|note| retrieval::excerpt(note, 300)),
        });
        match predicate {
            "alternative_to" | "attacks" => {
                let mut entry = entry;
                if other_kind == "statement" {
                    entry["rival_refuted_by"] = json!(refuters(other));
                }
                rivals.push(entry);
            }
            "refutes" if !outgoing => rivals.push(entry),
            "strengthens"
            | "strength_comparison"
            | "logically_equivalent_to"
            | "instance_of_schema" => strength.push(entry),
            _ => {}
        }
    }
    let mut attempts: Vec<Value> = dossier
        .attempts
        .iter()
        .map(|attempt| {
            let id = text(attempt, "id");
            json!({
                "id": id,
                "label": text(attempt, "label"),
                "date": attempt.get("date"),
                "kind": attempt.get("kind"),
                "outcome": attempt.get("outcome"),
                "summary": attempt.get("summary"),
                "blocker": attempt.get("blocker"),
                "path": corpus.get("attempts", id).map(|record| record.path.clone()),
            })
        })
        .collect();
    attempts.reverse(); // newest first (the dossier sorts by date, then id)
    let mut mention_ids: BTreeSet<&str> = BTreeSet::from([sid]);
    for argument in &concluding {
        if let Some(id) = argument["id"].as_str() {
            mention_ids.insert(id);
        }
        for result in argument["results"].as_array().into_iter().flatten() {
            if let Some(id) = result["id"].as_str() {
                mention_ids.insert(id);
            }
        }
    }
    let (note_sections, assessments) = note_evidence(inputs, &mention_ids)?;
    let referenced = note_references(inputs.root, &note_sections);
    let issues = issue_evidence(inputs, Some(sid), &mention_ids, &referenced)?;
    let related = crate::related::related(corpus, sid, 6)
        .map(|report| {
            report
                .matches
                .iter()
                .map(|found| {
                    json!({
                        "id": found.statement_id,
                        "label": inputs.aliases.label(&found.statement_id),
                        "tier": found.tier,
                        "reasons": found.reasons.iter().map(|reason| reason.kind()).collect::<Vec<_>>(),
                    })
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let senses: Vec<Value> = corpus
        .get("statements", sid)
        .map(|record| index.sense_labels(&record.fields))
        .unwrap_or_default()
        .into_iter()
        .map(|(term, labels)| json!({"term": term, "senses": labels}))
        .collect();
    let definitions: Vec<Value> = dossier
        .definition_ids
        .iter()
        .map(|id| inputs.reference("definitions", id))
        .collect();
    let disambiguations: Vec<Value> = dossier
        .disambiguation_ids
        .iter()
        .map(|id| inputs.reference("disambiguations", id))
        .collect();
    let routes = dossier.route_contributions.len();
    let open_leaf = dossier
        .route_contributions
        .iter()
        .filter(|route| route.open_leaf)
        .count();
    let mut formal = inputs.formal_state(sid);
    formal["authority"] = json!(
        "frontier report (truth frontier); a closure such as `proved` is not establishment unless \
         `established` is true; nothing in this brief changes either"
    );
    formal["floor"] = json!(dossier.floor);
    formal["routes"] = json!({"root_routes": routes, "open_leaf_on": open_leaf});
    let claims = json!({
        "stating": dossier.claim_ids,
        "supporting": dossier.supporting_claim_ids,
        "bibliographic": dossier.bibliographic_claim_ids,
    });
    let mut absent = Vec::new();
    for (name, empty) in [
        ("arguments concluding the target", concluding.is_empty()),
        (
            "recorded rivals, objections or refutations",
            rivals.is_empty(),
        ),
        ("strength orders or equivalences", strength.is_empty()),
        ("attempts", attempts.is_empty()),
        ("note sections naming the target", note_sections.is_empty()),
        (
            "assessments in notes naming the target",
            assessments.is_empty(),
        ),
        (
            "source claims",
            dossier.claim_ids.is_empty() && dossier.supporting_claim_ids.is_empty(),
        ),
    ] {
        if empty {
            absent.push(format!("{name}: not recorded"));
        }
    }
    match inputs.issues {
        Issues::Missing { .. } => {
            absent.push(format!("issues: unknown ({})", retrieval::MISSING_ISSUES))
        }
        Issues::Snapshot(_) if issues.is_empty() => {
            absent.push("issues: none in the snapshot mention or target the target".into())
        }
        Issues::Snapshot(_) => {}
    }
    Ok(json!({
        "mode": "statement",
        "boundary": BOUNDARY,
        "requested": requested,
        "identity": inputs.identity(),
        "statement": {
            "id": sid,
            "legacy_id": statement.get("legacy_id"),
            "label": statement.get("label"),
            "paraphrase": statement.get("paraphrase"),
            "lean_declaration": statement.get("lean_declaration"),
            "path": corpus.get("statements", sid).map(|record| record.path.clone()),
        },
        "senses": senses,
        "definitions": definitions,
        "disambiguations": disambiguations,
        "formal_status": formal,
        "claims": claims,
        "arguments": {"concluding": concluding, "premise_of": premise_of},
        "rivals": rivals,
        "strength_and_equivalence": strength,
        "attempts": attempts,
        "notes": {"boundary": notes::BOUNDARY, "sections": note_sections},
        "assessments": {
            "boundary": "judgment- and rival-headed sections of the notes naming the target, newest first; \
                         quoted, not reconciled, and not formal status",
            "sections": assessments,
        },
        "issues": {"source": inputs.issues, "matches": issues},
        "related": related,
        "absent": absent,
    }))
}

/// One note paragraph scored against a query.
#[derive(Clone, Debug)]
pub struct ParagraphHit {
    pub path: String,
    pub section: String,
    pub heading: String,
    pub line: usize,
    pub matched: Vec<bool>,
    pub excerpt: String,
    pub aliases: Vec<(String, String)>,
}

impl ParagraphHit {
    pub fn covered(&self) -> usize {
        retrieval::coverage(&self.matched).0
    }
}

/// A note evaluated against a query: every paragraph's coverage.
pub struct NoteScore {
    pub note: notes::Note,
    pub raw: String,
    pub paragraphs: Vec<ParagraphHit>,
}

/// Scores every paragraph of the notes at `paths` against `query`, with
/// each note's own notation (`D(x,y)` for `DependsForBeing x y`).
pub fn score_notes(root: &Path, query: &Query, paths: &[String]) -> Vec<NoteScore> {
    let mut out = Vec::new();
    for path in paths {
        let Ok(raw) = std::fs::read_to_string(root.join(path)) else {
            continue;
        };
        let note = notes::parse(path, &raw);
        let aliases = retrieval::note_aliases(&raw);
        let mut paragraphs = Vec::new();
        for section in &note.sections {
            for (line, paragraph) in
                retrieval::paragraphs(&section.body, retrieval::body_line(section))
            {
                let matched = query.matched(&paragraph, &aliases);
                if retrieval::coverage(&matched).0 == 0 {
                    continue;
                }
                let used: Vec<(String, String)> = query
                    .items
                    .iter()
                    .zip(&matched)
                    .filter(|(item, hit)| **hit && item.kind == "identifier")
                    .filter_map(|(item, _)| {
                        let key = item.text.to_lowercase();
                        aliases
                            .get(&key)
                            .filter(|alias| {
                                !paragraph
                                    .to_lowercase()
                                    .split(|c: char| !c.is_alphanumeric())
                                    .any(|w| w == key)
                                    && paragraph.contains(&format!("{alias}("))
                            })
                            .map(|alias| (alias.clone(), item.text.clone()))
                    })
                    .collect();
                paragraphs.push(ParagraphHit {
                    path: path.clone(),
                    section: note.key(section),
                    heading: section.heading.clone(),
                    line,
                    excerpt: best_line_excerpt(query, &paragraph, &aliases),
                    matched,
                    aliases: used,
                });
            }
        }
        out.push(NoteScore {
            note,
            raw,
            paragraphs,
        });
    }
    out
}

/// The paragraph, or for a long one its best-matching line, clipped.
fn best_line_excerpt(query: &Query, paragraph: &str, aliases: &BTreeMap<String, String>) -> String {
    if paragraph.chars().count() <= 360 {
        return retrieval::excerpt(paragraph, 360);
    }
    let best = paragraph
        .lines()
        .enumerate()
        .max_by_key(|(index, line)| {
            (
                retrieval::coverage(&query.matched(line, aliases)).0,
                std::cmp::Reverse(*index),
            )
        })
        .map(|(_, line)| line)
        .unwrap_or(paragraph);
    retrieval::excerpt(best, 360)
}

fn paragraph_json(query: &Query, hit: &ParagraphHit) -> Value {
    let (covered, total) = retrieval::coverage(&hit.matched);
    json!({
        "section": hit.section,
        "heading": hit.heading,
        "line": hit.line,
        "coverage": [covered, total],
        "matched": retrieval::matched_items(query, &hit.matched),
        "notation": hit.aliases.iter().map(|(alias, identifier)| format!("{alias} = {identifier}")).collect::<Vec<_>>(),
        "excerpt": hit.excerpt,
    })
}

/// The candidate notes for `query`: the distinct notes of the index's
/// best-ranked sections, then `extra` notes, at most [`NOTES_EVALUATED`].
pub fn candidate_notes(
    db: &rusqlite::Connection,
    query: &Query,
    extra: &[String],
) -> Result<(Vec<String>, Vec<RecordKey>), String> {
    let (sections, records) = match query.fts_expression() {
        Some(expression) => retrieval::index_candidates(db, &expression, CANDIDATES)?,
        None => (Vec::new(), Vec::new()),
    };
    let mut paths: Vec<String> = Vec::new();
    for path in sections
        .into_iter()
        .map(|hit| hit.path)
        .chain(extra.iter().cloned())
    {
        if !paths.contains(&path) && paths.len() < NOTES_EVALUATED {
            paths.push(path);
        }
    }
    Ok((paths, records))
}

/// A research brief for a question: the notes, records and issues the
/// question's words and identifiers retrieve, with each note's recorded
/// assessments and rival analysis and the issues it references.
pub fn question_brief(
    inputs: &Inputs,
    db: &rusqlite::Connection,
    index_state: Value,
    question: &str,
    limit: usize,
) -> Result<Value, String> {
    let query = Query::parse(question);
    let (paths, record_candidates) = candidate_notes(db, &query, &[])?;
    let scores = score_notes(inputs.root, &query, &paths);
    let total = query.items.len();
    let half = total.div_ceil(2).max(1);
    let mut ranked: Vec<(usize, usize, &NoteScore)> = scores
        .iter()
        .map(|score| {
            let best = score
                .paragraphs
                .iter()
                .map(ParagraphHit::covered)
                .max()
                .unwrap_or(0);
            let strong = score
                .paragraphs
                .iter()
                .filter(|hit| hit.covered() >= half)
                .count();
            (best, strong, score)
        })
        .filter(|(best, ..)| *best > 0)
        .collect();
    ranked.sort_by(|a, b| {
        b.0.cmp(&a.0)
            .then(b.1.cmp(&a.1))
            .then_with(|| a.2.note.path.cmp(&b.2.note.path))
    });
    let mut note_out = Vec::new();
    let mut referenced: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    let mut anchors: BTreeMap<String, (String, usize)> = BTreeMap::new();
    let mut changed_by: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    let lookup = notes::Lookup::of_corpus(inputs.corpus);
    for (best, strong, score) in ranked.iter().take(limit.max(1) * 2) {
        let mut hits: Vec<&ParagraphHit> = score.paragraphs.iter().collect();
        hits.sort_by(|a, b| b.covered().cmp(&a.covered()).then(a.line.cmp(&b.line)));
        let strong_sections: BTreeSet<&str> = hits
            .iter()
            .filter(|hit| hit.covered() >= half)
            .map(|hit| hit.section.as_str())
            .collect();
        for section in &score.note.sections {
            let key = score.note.key(section);
            if !strong_sections.contains(key.as_str()) {
                continue;
            }
            for number in
                retrieval::issue_references(&format!("{}\n{}", section.heading, section.body))
            {
                let places = referenced.entry(number).or_default();
                if !places.contains(&key) {
                    places.push(key.clone());
                }
            }
            for link in lookup.links(section).0 {
                if link.kind == "statements" {
                    let entry = anchors.entry(link.id.clone()).or_insert((key.clone(), 0));
                    entry.1 += 1;
                }
            }
        }
        let mut history = retrieval::history(inputs.root, &score.note.path, 5);
        for change in &mut history {
            if let Some(number) = change["pull_request"].as_u64() {
                if let Some(issue) = inputs.issues.snapshot().and_then(|snapshot| {
                    snapshot
                        .issues
                        .iter()
                        .find(|issue| issue.get("number").and_then(Value::as_u64) == Some(number))
                }) {
                    change["title"] = issue.get("title").cloned().unwrap_or(Value::Null);
                    change["state"] = issue.get("state").cloned().unwrap_or(Value::Null);
                }
                let paths = changed_by.entry(number).or_default();
                if !paths.contains(&score.note.path) {
                    paths.push(score.note.path.clone());
                }
            }
        }
        note_out.push(json!({
            "path": score.note.path,
            "title": score.note.title,
            "note_date": retrieval::latest_date(&score.raw),
            "history": history,
            "best_coverage": [best, total],
            "paragraphs_with_half_or_more": strong,
            "best_paragraphs": hits.iter().take(3).map(|hit| paragraph_json(&query, hit)).collect::<Vec<_>>(),
            "assessments": assessment_sections(&score.note, &score.raw, 3),
            "superseded_markers": superseded(&score.raw, &score.note.path),
        }));
    }
    let mut assessments: Vec<Value> = note_out
        .iter()
        .flat_map(|note| note["assessments"].as_array().cloned().unwrap_or_default())
        .collect();
    sort_assessments(&mut assessments);
    let records = record_hits(inputs, &query, &record_candidates, limit * 2);
    // Statements the best note sections name most often.
    let mut anchor_list: Vec<(String, String, usize)> = anchors
        .into_iter()
        .map(|(id, (section, count))| (id, section, count))
        .collect();
    anchor_list.sort_by(|a, b| b.2.cmp(&a.2).then_with(|| a.0.cmp(&b.0)));
    anchor_list.truncate(limit.max(1) * 2);
    let anchor_json: Vec<Value> = anchor_list
        .iter()
        .map(|(id, section, count)| {
            let mut reference = inputs.reference("statements", id);
            reference["named_by"] = json!(section);
            reference["mentions"] = json!(count);
            reference["formal_state"] = inputs.formal_state(id)["state"].clone();
            reference
        })
        .collect();
    let anchor_ids: BTreeSet<&str> = anchor_list.iter().map(|(id, ..)| id.as_str()).collect();
    let note_paths: Vec<String> = note_out
        .iter()
        .take(limit.max(1))
        .filter_map(|note| note["path"].as_str().map(str::to_owned))
        .collect();
    let (issues, issue_total) = question_issues(
        inputs,
        &query,
        &anchor_ids,
        &referenced,
        &changed_by,
        &note_paths,
        limit,
    );
    let mut absent = Vec::new();
    if note_out.is_empty() {
        absent.push("notes: no note paragraph contains a query word".to_owned());
    }
    if assessments.is_empty() {
        absent.push("assessments: no judgment-headed section in the matched notes".to_owned());
    }
    match inputs.issues {
        Issues::Missing { .. } => {
            absent.push(format!("issues: unknown ({})", retrieval::MISSING_ISSUES))
        }
        Issues::Snapshot(_) if issues.is_empty() => {
            absent.push("issues: no snapshot item matched".into())
        }
        Issues::Snapshot(_) => {}
    }
    Ok(json!({
        "mode": "question",
        "boundary": BOUNDARY,
        "question": query,
        "identity": inputs.identity(),
        "index": index_state,
        "notes": {"boundary": notes::BOUNDARY, "ranked": note_out},
        "assessments": {
            "boundary": "judgment- and rival-headed sections of the matched notes, newest first; quoted, \
                         not reconciled, and not formal status",
            "sections": assessments,
        },
        "named_statements": anchor_json,
        "records": records,
        "referenced_issue_numbers": referenced_ranked(&referenced),
        "note_changed_by_pull_requests": changed_by,
        "issues": {"source": inputs.issues, "matches": issues, "matched_total": issue_total},
        "absent": absent,
    }))
}

/// Records among the index candidates whose prose covers query items, with
/// a statement's frontier state; best coverage first, then kind and id.
pub fn record_hits(
    inputs: &Inputs,
    query: &Query,
    candidates: &[(String, String)],
    limit: usize,
) -> Vec<Value> {
    let none = BTreeMap::new();
    let mut scored: Vec<(usize, &str, &str, Vec<bool>)> = candidates
        .iter()
        .filter_map(|(kind, id)| {
            let record = inputs.corpus.get(kind, id)?;
            let matched = query.matched(&retrieval::record_prose(&record.fields), &none);
            let covered = retrieval::coverage(&matched).0;
            (covered > 0).then_some((covered, kind.as_str(), id.as_str(), matched))
        })
        .collect();
    scored.sort_by(|a, b| {
        b.0.cmp(&a.0)
            .then_with(|| a.1.cmp(b.1))
            .then_with(|| a.2.cmp(b.2))
    });
    scored
        .into_iter()
        .take(limit)
        .map(|(covered, kind, id, matched)| {
            let record = &inputs.corpus.get(kind, id).expect("scored record").fields;
            json!({
                "kind": kind,
                "id": id,
                "label": record.get("label"),
                "path": inputs.corpus.get(kind, id).map(|record| record.path.clone()),
                "coverage": [covered, query.items.len()],
                "matched": retrieval::matched_items(query, &matched),
                "substantial": query.substantial(&matched),
                "formal_state": (kind == "statements").then(|| inputs.formal_state(id)["state"].clone()),
                "outcome": record.get("outcome"),
                "date": record.get("date"),
            })
        })
        .collect()
}

/// Issue numbers referenced from matched note sections, most-referenced
/// first: `{number, sections}`.
fn referenced_ranked(referenced: &BTreeMap<u64, Vec<String>>) -> Vec<Value> {
    let mut ranked: Vec<(&u64, &Vec<String>)> = referenced.iter().collect();
    ranked.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(b.0)));
    ranked
        .into_iter()
        .map(|(number, sections)| json!({"number": number, "sections": sections}))
        .collect()
}

/// Snapshot items for a question, by evidence weight: referenced by number
/// from a matched note section or a PR that changed a matched note (3
/// each), naming a matched note (2), naming a statement those notes name
/// (1), and lexical coverage of at least half the query (1). At most
/// `limit * 5` are returned, with the total.
fn question_issues(
    inputs: &Inputs,
    query: &Query,
    anchors: &BTreeSet<&str>,
    referenced: &BTreeMap<u64, Vec<String>>,
    changed_by: &BTreeMap<u64, Vec<String>>,
    note_paths: &[String],
    limit: usize,
) -> (Vec<Value>, usize) {
    let Some(snapshot) = inputs.issues.snapshot() else {
        return (Vec::new(), 0);
    };
    let lookup = notes::Lookup::of_corpus(inputs.corpus);
    let none = BTreeMap::new();
    let total = query.items.len();
    let mut out: Vec<(usize, usize, u64, Value)> = Vec::new();
    for issue in &snapshot.issues {
        let number = issue
            .get("number")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        let mut reasons = Vec::new();
        let mut weight = 0;
        if let Some(places) = referenced.get(&number) {
            weight += 3;
            reasons.push(
                json!({"why": "referenced by number from a matched note section", "where": places}),
            );
        }
        if let Some(paths) = changed_by.get(&number) {
            weight += 3;
            reasons.push(
                json!({"why": "merged change to a matched note (git history)", "notes": paths}),
            );
        }
        let mut best: (usize, String, String, bool) = (0, String::new(), String::new(), false);
        let mut named = BTreeSet::new();
        let mut paths = BTreeSet::new();
        for (place, unit) in retrieval::issue_units(issue) {
            let matched = query.matched(&unit, &none);
            let covered = retrieval::coverage(&matched).0;
            if covered > best.0 {
                best = (
                    covered,
                    place.clone(),
                    retrieval::excerpt(&unit, 240),
                    query.substantial(&matched),
                );
            }
            for path in note_paths {
                if unit.contains(path.as_str())
                    || unit.contains(path.rsplit('/').next().unwrap_or(path))
                {
                    paths.insert(path.clone());
                }
            }
            let section = notes::Section {
                anchor: String::new(),
                heading: String::new(),
                level: 0,
                line: 1,
                body: unit,
            };
            for link in lookup.links(&section).0 {
                if anchors.contains(link.id.as_str()) {
                    named.insert((link.id.clone(), place.clone()));
                }
            }
        }
        if !paths.is_empty() {
            weight += 2;
            reasons.push(json!({"why": "names a matched note", "notes": paths}));
        }
        let mut seen = BTreeSet::new();
        let named: Vec<Value> = named
            .into_iter()
            .filter(|(id, _)| seen.insert(id.clone()))
            .map(|(id, place)| {
                let mut reference = inputs.reference("statements", &id);
                reference["where"] = json!(place);
                reference
            })
            .collect();
        if !named.is_empty() {
            weight += 1;
            reasons
                .push(json!({"why": "names a statement the matched notes name", "records": named}));
        }
        if best.3 {
            weight += 1;
            reasons.push(json!({"why": "lexical", "where": best.1, "coverage": [best.0, total], "excerpt": best.2}));
        }
        if !reasons.is_empty() {
            let mut header = retrieval::issue_header(issue);
            header["reasons"] = json!(reasons);
            header["weight"] = json!(weight);
            header["best_coverage"] = json!([best.0, total]);
            out.push((weight, best.0, number, header));
        }
    }
    out.sort_by(|a, b| b.0.cmp(&a.0).then(b.1.cmp(&a.1)).then(b.2.cmp(&a.2)));
    let matched = out.len();
    (
        out.into_iter()
            .take(limit * 5)
            .map(|(.., value)| value)
            .collect(),
        matched,
    )
}

fn clip(value: &Value, max: usize) -> String {
    retrieval::excerpt(&crate::pyfmt::text(value), max)
}

fn show(aliases: &Aliases, value: &Value) -> String {
    let id = value["id"].as_str().unwrap_or_default();
    match value["label"].as_str() {
        Some(label) if id.len() >= 8 => format!("{} [{}]", retrieval::excerpt(label, 90), &id[..8]),
        _ => aliases.show(id),
    }
}

fn more(lines: &mut Vec<String>, len: usize, limit: usize) {
    if len > limit {
        lines.push(format!("  … {} more (--json lists all)", len - limit));
    }
}

fn issue_source_line(source: &Value) -> String {
    match source["availability"].as_str() {
        Some("snapshot") => format!(
            "Issue snapshot: {} ({} items, {} PRs; captured {} by {}; closed items: {}; comments: {}{})",
            source["path"].as_str().unwrap_or_default(),
            source["items"],
            source["pull_requests"],
            source["captured_at"].as_str().unwrap_or("unknown"),
            source["captured_from"].as_str().unwrap_or_default(),
            if source["includes_closed"] == true {
                "included"
            } else {
                "NOT included"
            },
            if source["includes_comments"] == true {
                "included"
            } else {
                "not included"
            },
            if source["older_than_checkout"] == true {
                "; OLDER than the checkout's HEAD commit: later issue activity unknown"
            } else {
                ""
            }
        ),
        _ => format!("Issue snapshot: missing — {}", retrieval::MISSING_ISSUES),
    }
}

fn issue_lines(lines: &mut Vec<String>, issues: &Value, limit: usize) {
    lines.push(issue_source_line(&issues["source"]));
    let matches = issues["matches"].as_array().cloned().unwrap_or_default();
    for issue in matches.iter().take(limit) {
        let reasons: Vec<String> = issue["reasons"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|reason| {
                let mut why = reason["why"].as_str().unwrap_or_default().to_owned();
                if let Some(record) = reason.get("record") {
                    why.push_str(&format!(
                        " {}",
                        record["label"]
                            .as_str()
                            .map_or_else(|| clip(&record["id"], 40), |l| retrieval::excerpt(l, 50))
                    ));
                }
                if let Some(records) = reason["records"].as_array() {
                    let shown: Vec<String> =
                        records.iter().take(2).map(|r| clip(&r["id"], 8)).collect();
                    why.push_str(&format!(" ({})", shown.join(", ")));
                }
                if let Some(notes) = reason["notes"].as_array() {
                    why.push_str(&format!(" ({} notes)", notes.len()));
                }
                if let Some(coverage) = reason.get("coverage") {
                    why.push_str(&format!(" {}/{}", coverage[0], coverage[1]));
                }
                why
            })
            .collect();
        lines.push(format!(
            "  #{} [{} {}] {} — {}",
            issue["number"],
            issue["kind"].as_str().unwrap_or_default(),
            issue["state"].as_str().unwrap_or("unknown"),
            clip(&issue["title"], 80),
            reasons.join("; ")
        ));
    }
    let total = issues["matched_total"]
        .as_u64()
        .map_or(matches.len(), |total| total as usize);
    more(lines, total, limit);
}

fn assessment_lines(lines: &mut Vec<String>, assessments: &Value, limit: usize) {
    let sections = assessments["sections"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    lines.push(format!(
        "Recorded assessments and rival analysis in notes ({}; quoted, not formal status):",
        sections.len()
    ));
    for entry in sections.iter().take(limit) {
        lines.push(format!(
            "  [{}] {} {} line {}: \"{}\"",
            entry["kind"].as_str().unwrap_or_default(),
            entry["date"].as_str().unwrap_or("undated"),
            entry["section"].as_str().unwrap_or_default(),
            entry["line"],
            clip(&entry["excerpt"], 220)
        ));
    }
    more(lines, sections.len(), limit);
}

fn identity_line(identity: &Value) -> String {
    format!(
        "Revision: {} ({}); corpus {}",
        identity["revision"]["commit"].as_str().unwrap_or("unknown"),
        identity["revision"]["committed_at"]
            .as_str()
            .unwrap_or("time unknown"),
        identity["input_identity"].as_str().unwrap_or_default()
    )
}

/// The text view of a brief: every entry with its record, note or issue
/// reference, at most `limit` per section.
pub fn format_brief(brief: &Value, aliases: &Aliases, limit: usize) -> String {
    let mut lines = Vec::new();
    let absent = brief["absent"].as_array().cloned().unwrap_or_default();
    if brief["mode"] == "question" {
        lines.push(format!(
            "Research brief (question): {}",
            brief["question"]["text"].as_str().unwrap_or_default()
        ));
        lines.push(identity_line(&brief["identity"]));
        lines.push(format!(
            "Index: {} {} ({})",
            brief["index"]["path"].as_str().unwrap_or_default(),
            if brief["index"]["rebuilt"] == true {
                "rebuilt for this query"
            } else {
                "reused (current)"
            },
            brief["index"]["digest"].as_str().unwrap_or_default()
        ));
        lines.push(format!("Boundary: {BOUNDARY}."));
        let ranked = brief["notes"]["ranked"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        lines.push(format!(
            "Notes ({} matched; coverage = query items found in one paragraph):",
            ranked.len()
        ));
        for note in ranked.iter().take(limit) {
            lines.push(format!(
                "  {} — {} (latest date {}; best {}/{}, {} paragraphs ≥ half)",
                note["path"].as_str().unwrap_or_default(),
                clip(&note["title"], 80),
                note["note_date"].as_str().unwrap_or("none"),
                note["best_coverage"][0],
                note["best_coverage"][1],
                note["paragraphs_with_half_or_more"]
            ));
            for hit in note["best_paragraphs"]
                .as_array()
                .into_iter()
                .flatten()
                .take(2)
            {
                lines.push(format!(
                    "    {} line {} [{}/{}]: \"{}\"",
                    hit["section"].as_str().unwrap_or_default(),
                    hit["line"],
                    hit["coverage"][0],
                    hit["coverage"][1],
                    clip(&hit["excerpt"], 200)
                ));
            }
            for entry in note["assessments"]
                .as_array()
                .into_iter()
                .flatten()
                .filter(|a| a["kind"] == "assessment")
                .take(2)
            {
                lines.push(format!(
                    "    assessment {} line {}: \"{}\"",
                    entry["section"].as_str().unwrap_or_default(),
                    entry["line"],
                    clip(&entry["excerpt"], 240)
                ));
            }
            let changes: Vec<String> = note["history"]
                .as_array()
                .into_iter()
                .flatten()
                .take(3)
                .map(|change| match change["pull_request"].as_u64() {
                    Some(number) => format!(
                        "{} #{number}{}",
                        change["date"].as_str().unwrap_or_default(),
                        change["title"]
                            .as_str()
                            .map(|title| format!(" \"{}\"", retrieval::excerpt(title, 70)))
                            .unwrap_or_default()
                    ),
                    None => format!(
                        "{} {}",
                        change["date"].as_str().unwrap_or_default(),
                        change["commit"].as_str().unwrap_or_default()
                    ),
                })
                .collect();
            if !changes.is_empty() {
                lines.push(format!(
                    "    last changed (git first-parent merges, newest first): {}",
                    changes.join(", ")
                ));
            }
            for marker in note["superseded_markers"]
                .as_array()
                .into_iter()
                .flatten()
                .take(2)
            {
                lines.push(format!(
                    "    superseded/retired marker {}: \"{}\"",
                    marker["location"].as_str().unwrap_or_default(),
                    clip(&marker["text"], 160)
                ));
            }
        }
        more(&mut lines, ranked.len(), limit);
        let named = brief["named_statements"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        lines.push(format!(
            "Statements the best note sections name ({}):",
            named.len()
        ));
        for entry in named.iter().take(limit) {
            lines.push(format!(
                "  {} — frontier: {}; named {}× in {}",
                show(aliases, entry),
                entry["formal_state"].as_str().unwrap_or_default(),
                entry["mentions"],
                entry["named_by"].as_str().unwrap_or_default()
            ));
        }
        more(&mut lines, named.len(), limit);
        let records = brief["records"].as_array().cloned().unwrap_or_default();
        lines.push(format!("Records by prose coverage ({}):", records.len()));
        for record in records.iter().take(limit) {
            lines.push(format!(
                "  {} {} [{}/{}]{}",
                record["kind"].as_str().unwrap_or_default(),
                show(aliases, record),
                record["coverage"][0],
                record["coverage"][1],
                record["formal_state"]
                    .as_str()
                    .map(|state| format!(" frontier: {state}"))
                    .unwrap_or_default()
            ));
        }
        more(&mut lines, records.len(), limit);
        let referenced: Vec<String> = brief["referenced_issue_numbers"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|entry| {
                format!(
                    "#{} ({})",
                    entry["number"],
                    entry["sections"].as_array().map_or(0, Vec::len)
                )
            })
            .collect();
        lines.push(format!(
            "Issue numbers referenced by the matched note sections (sections): {}{}",
            if referenced.is_empty() {
                "none".to_owned()
            } else {
                referenced
                    .iter()
                    .take(limit * 3)
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(", ")
            },
            if referenced.len() > limit * 3 {
                format!(" … {} more", referenced.len() - limit * 3)
            } else {
                String::new()
            }
        ));
        issue_lines(&mut lines, &brief["issues"], limit);
    } else {
        let statement = &brief["statement"];
        lines.push(format!(
            "Research brief: {} [{}]{}",
            statement["label"].as_str().unwrap_or_default(),
            statement["id"].as_str().unwrap_or_default(),
            statement["legacy_id"]
                .as_str()
                .map(|legacy| format!(" ({legacy})"))
                .unwrap_or_default()
        ));
        if let Some(requested) = brief["requested"].as_object() {
            lines.push(format!(
                "Requested {} {}; this brief is of its conclusion.",
                requested
                    .get("kind")
                    .and_then(Value::as_str)
                    .unwrap_or_default(),
                aliases.show(
                    requested
                        .get("id")
                        .and_then(Value::as_str)
                        .unwrap_or_default()
                )
            ));
        }
        lines.push(clip(&statement["paraphrase"], 400));
        lines.push(format!(
            "Lean: {}",
            statement["lean_declaration"].as_str().unwrap_or("none")
        ));
        lines.push(identity_line(&brief["identity"]));
        lines.push(format!("Boundary: {BOUNDARY}."));
        let formal = &brief["formal_status"];
        lines.push(format!(
            "Formal status (frontier, root {}): {}{}; established: {} (a closure is not establishment); reaches root: {}; open leaf on {} of {} root routes",
            brief["identity"]["frontier_root"].as_str().map_or_else(|| "none".into(), |root| aliases.show(root)),
            formal["state"].as_str().unwrap_or_default(),
            formal["closure"].as_str().map(|closure| format!(" ({closure})")).or_else(|| formal["frontier_status"].as_str().map(|s| format!(" ({s})"))).unwrap_or_default(),
            formal["established"],
            formal["reaches_root"],
            formal["routes"]["open_leaf_on"],
            formal["routes"]["root_routes"]
        ));
        let senses: Vec<String> = brief["senses"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|sense| {
                format!(
                    "{}: {}",
                    sense["term"].as_str().unwrap_or_default(),
                    crate::pyfmt::text(&sense["senses"])
                )
            })
            .collect();
        if !senses.is_empty() {
            lines.push(format!("Senses: {}", senses.join("; ")));
        }
        let definitions: Vec<String> = brief["definitions"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|d| show(aliases, d))
            .collect();
        lines.push(format!(
            "Definitions ({}): {}{}",
            definitions.len(),
            if definitions.is_empty() {
                "none linked".into()
            } else {
                definitions
                    .iter()
                    .take(limit)
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(", ")
            },
            if definitions.len() > limit {
                " …"
            } else {
                ""
            }
        ));
        let concluding = brief["arguments"]["concluding"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        lines.push(format!("Arguments concluding it ({}):", concluding.len()));
        for argument in concluding.iter().take(limit) {
            let open: Vec<String> = argument["unestablished_premises"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|id| aliases.show(id.as_str().unwrap_or_default()))
                .collect();
            let results: Vec<String> = argument["results"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|result| {
                    format!(
                        "{}{}",
                        result["id"]
                            .as_str()
                            .unwrap_or_default()
                            .get(..8)
                            .unwrap_or_default(),
                        result["transcription"]
                            .as_str()
                            .map(|kind| format!(" ({kind})"))
                            .unwrap_or_default()
                    )
                })
                .collect();
            lines.push(format!(
                "  {} — {}; results: {}; unestablished premises: {}",
                show(aliases, argument),
                argument["reading"].as_str().unwrap_or_default(),
                if results.is_empty() {
                    "none".into()
                } else {
                    results.join(", ")
                },
                if open.is_empty() {
                    "none".into()
                } else {
                    open.join(", ")
                }
            ));
        }
        more(&mut lines, concluding.len(), limit);
        let premise_of = brief["arguments"]["premise_of"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        lines.push(format!(
            "Used as a premise by {} arguments",
            premise_of.len()
        ));
        let rivals = brief["rivals"].as_array().cloned().unwrap_or_default();
        lines.push(format!(
            "Rivals, objections and refutations ({}):",
            rivals.len()
        ));
        for rival in rivals.iter().take(limit) {
            let refuted: Vec<String> = rival["rival_refuted_by"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|r| show(aliases, &r["by"]))
                .collect();
            lines.push(format!(
                "  {} {} ({}){}{} [{}]",
                rival["predicate"].as_str().unwrap_or_default(),
                show(aliases, &rival["other"]),
                rival["direction"].as_str().unwrap_or_default(),
                rival["other_state"]
                    .as_str()
                    .map(|state| format!("; frontier: {state}"))
                    .unwrap_or_default(),
                if refuted.is_empty() {
                    String::new()
                } else {
                    format!("; rival refuted by {}", refuted.join(", "))
                },
                rival["relation"]
                    .as_str()
                    .unwrap_or_default()
                    .get(..8)
                    .unwrap_or_default()
            ));
        }
        more(&mut lines, rivals.len(), limit);
        let strength = brief["strength_and_equivalence"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        lines.push(format!(
            "Strength orders and equivalences ({}):",
            strength.len()
        ));
        for entry in strength.iter().take(limit) {
            lines.push(format!(
                "  {} {} ({})",
                entry["predicate"].as_str().unwrap_or_default(),
                show(aliases, &entry["other"]),
                entry["direction"].as_str().unwrap_or_default()
            ));
        }
        more(&mut lines, strength.len(), limit);
        let attempts = brief["attempts"].as_array().cloned().unwrap_or_default();
        lines.push(format!("Attempts ({}, newest first):", attempts.len()));
        for attempt in attempts.iter().take(limit) {
            lines.push(format!(
                "  {} {} {} {}: {}",
                attempt["date"].as_str().unwrap_or("undated"),
                attempt["kind"].as_str().unwrap_or_default(),
                attempt["outcome"].as_str().unwrap_or_default(),
                attempt["id"]
                    .as_str()
                    .unwrap_or_default()
                    .get(..8)
                    .unwrap_or_default(),
                clip(&attempt["summary"], 200)
            ));
        }
        more(&mut lines, attempts.len(), limit);
        let sections = brief["notes"]["sections"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        lines.push(format!(
            "Note sections naming the target or its arguments ({}; {}):",
            sections.len(),
            notes::BOUNDARY
        ));
        for section in sections.iter().take(limit) {
            lines.push(format!(
                "  {} line {} ({}): {}",
                section["section"].as_str().unwrap_or_default(),
                section["line"],
                section["note_date"].as_str().unwrap_or("undated"),
                crate::pyfmt::text(&section["mentions"])
            ));
        }
        more(&mut lines, sections.len(), limit);
        assessment_lines(&mut lines, &brief["assessments"], limit);
        issue_lines(&mut lines, &brief["issues"], limit);
        let related: Vec<String> = brief["related"]
            .as_array()
            .into_iter()
            .flatten()
            .take(limit)
            .map(|r| show(aliases, r))
            .collect();
        lines.push(format!(
            "Related statements (truth related): {}",
            if related.is_empty() {
                "none".into()
            } else {
                related.join("; ")
            }
        ));
    }
    lines.push(format!(
        "Not recorded / unknown:{}",
        if absent.is_empty() {
            " nothing reported absent"
        } else {
            ""
        }
    ));
    for entry in &absent {
        lines.push(format!("  - {}", entry.as_str().unwrap_or_default()));
    }
    lines.join("\n")
}
