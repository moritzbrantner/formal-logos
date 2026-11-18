//! `truth semantics`: the semantic dependencies of a proposition or a
//! derivation in one view, and an equivocation preflight for a candidate
//! argument.
//!
//! It composes what already exists rather than adding a second sense
//! engine: the sense index and the term-sense computation `truth check`
//! uses ([`crate::senses`]), the legacy sense allowlist and the per-argument
//! sense rules of `truth check` ([`crate::check::validate_argument_senses`]),
//! and the formal status of definitions ([`crate::definition_status`]).
//!
//! - **Statement mode**: the proposition, its definitions (sense, Lean
//!   declaration, formal status, basis), the disambiguations it is read
//!   against, the senses it uses (flagging senses that are not distinct Lean
//!   types), and the arguments concluding or using it with a per-term
//!   compatibility verdict naming the statement that carries each sense.
//! - **Argument mode**: the same verdicts for one argument, the compact
//!   semantics of each of its statements, and a verdict summary over its
//!   support ancestry.
//! - **Preflight**: a candidate argument built in memory from premises,
//!   conclusion and optional bridges, judged by the same rule `truth check`
//!   applies to a new argument (the legacy allowlist does not apply).
//!
//! Everything is read-only and advisory about meaning: a `single sense`
//! verdict says the records link one sense per term, not that the prose or
//! the Lean statement is free of equivocation.

use crate::check::{Allowlist, load_sense_allowlist, validate_argument_senses};
use crate::definition_status::{self, State, Status};
use crate::senses::{
    SenseIndex, argument_term_senses, bridged, sense_index, senses_without_distinct_declaration,
};
use crate::{Corpus, Record};
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::path::Path;

type Obj = Map<String, Value>;

/// The default bound on each list of arguments.
pub const DEFAULT_LIMIT: usize = 10;
/// The path `truth check` messages name for the preflight candidate.
pub const CANDIDATE: &str = "candidate argument";
const EXCERPT: usize = 180;

fn text<'a>(record: &'a Obj, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn list<'a>(record: &'a Obj, field: &str) -> Vec<&'a str> {
    record
        .get(field)
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

fn excerpt(text: &str) -> String {
    let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if text.chars().count() <= EXCERPT {
        return text;
    }
    let cut: String = text.chars().take(EXCERPT).collect();
    format!("{}…", cut.trim_end())
}

/// The compatibility of one term's senses within one argument, in the order
/// `truth check` decides it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Verdict {
    /// One sense of the term.
    Single,
    /// Several senses, connected by the argument's `sense_bridges`.
    Bridged,
    /// Several senses in a premise-free `sense_mixing_control` argument.
    Control,
    /// Several senses without a bridge, accepted only because the argument is
    /// in the legacy allowlist (#1233).
    Allowlisted,
    /// Several senses without a bridge: `truth check` rejects it.
    Unbridged,
}

impl Verdict {
    pub const ALL: [Verdict; 5] = [
        Verdict::Single,
        Verdict::Bridged,
        Verdict::Control,
        Verdict::Allowlisted,
        Verdict::Unbridged,
    ];

    pub fn code(self) -> &'static str {
        match self {
            Verdict::Single => "single_sense",
            Verdict::Bridged => "bridged",
            Verdict::Control => "mixing_control",
            Verdict::Allowlisted => "allowlisted_mixing",
            Verdict::Unbridged => "unbridged_mixing",
        }
    }

    pub fn text(self) -> &'static str {
        match self {
            Verdict::Single => "single sense",
            Verdict::Bridged => "bridged",
            Verdict::Control => "mixing control",
            Verdict::Allowlisted => "allowlisted mixing — equivocation risk (legacy)",
            Verdict::Unbridged => "unbridged mixing",
        }
    }

    fn parse(code: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|verdict| verdict.code() == code)
    }

    /// An equivocation risk: senses mixed without a bridge.
    pub fn risk(self) -> bool {
        matches!(self, Verdict::Allowlisted | Verdict::Unbridged)
    }
}

/// A requested preflight bridge: a statement, and optionally the two senses
/// it relates (uuid or label each); without them the senses are the ones the
/// statement itself links, per term.
#[derive(Clone, Debug)]
pub struct BridgeRequest {
    pub statement_id: String,
    pub senses: Option<(String, String)>,
}

/// The loaded inputs of every mode.
pub struct Semantics<'a> {
    statements: HashMap<&'a str, &'a Obj>,
    arguments: Vec<&'a Record>,
    argument_by_id: HashMap<&'a str, &'a Obj>,
    concluding: HashMap<&'a str, Vec<&'a str>>,
    disambiguations: Vec<&'a Record>,
    definitions: HashMap<&'a str, &'a Obj>,
    index: SenseIndex,
    allowlist: Allowlist,
    sense_declaration: HashMap<String, Option<String>>,
    undeclared: HashSet<String>,
    formal: HashMap<String, definition_status::Definition>,
    reaching_root: Option<BTreeSet<String>>,
}

impl<'a> Semantics<'a> {
    /// Loads the sense index, the legacy allowlist and the definition
    /// formal statuses of `corpus` at `root`.
    pub fn new(root: &Path, corpus: &'a Corpus) -> Result<Self, String> {
        let by_id = |kind| {
            corpus
                .records(kind)
                .into_iter()
                .map(|record| (text(record, "id"), record))
                .collect::<HashMap<_, _>>()
        };
        let disambiguations = corpus.entries("disambiguations");
        let index = sense_index(disambiguations.iter().copied())?;
        let allowlist = load_sense_allowlist(root)?;
        let undeclared = senses_without_distinct_declaration(disambiguations.iter().copied())
            .into_iter()
            .map(|(_, sense)| text(sense, "id").to_owned())
            .collect();
        let mut sense_declaration = HashMap::new();
        for disambiguation in &disambiguations {
            let senses = disambiguation
                .fields
                .get("senses")
                .and_then(Value::as_array);
            for sense in senses.into_iter().flatten().filter_map(Value::as_object) {
                sense_declaration
                    .entry(text(sense, "id").to_owned())
                    .or_insert_with(|| {
                        sense
                            .get("lean_declaration")
                            .and_then(Value::as_str)
                            .map(str::to_owned)
                    });
            }
        }
        // A malformed formal_gap is `truth check`'s error to report; here the
        // statuses are then unknown.
        let formal = definition_status::read_cache(root)
            .and_then(|cache| definition_status::definitions(root, corpus, cache.as_ref()))
            .unwrap_or_default()
            .into_iter()
            .map(|definition| (definition.id.clone(), definition))
            .collect();
        let arguments = corpus.entries("arguments");
        let mut concluding: HashMap<&str, Vec<&str>> = HashMap::new();
        for argument in &arguments {
            concluding
                .entry(text(&argument.fields, "conclusion_statement_id"))
                .or_default()
                .push(text(&argument.fields, "id"));
        }
        Ok(Semantics {
            statements: by_id("statements"),
            argument_by_id: by_id("arguments"),
            arguments,
            concluding,
            disambiguations,
            definitions: by_id("definitions"),
            index,
            allowlist,
            sense_declaration,
            undeclared,
            formal,
            reaching_root: None,
        })
    }

    /// The statements reaching the frontier root (the frontier report's
    /// `reaching_root_statements`); arguments concluding one of them are
    /// listed first and marked as on a root route.
    pub fn with_reaching_root(mut self, reaching: BTreeSet<String>) -> Self {
        self.reaching_root = Some(reaching);
        self
    }

    fn label_of(&self, kind: &str, id: &str) -> String {
        let record = match kind {
            "statements" => self.statements.get(id),
            "arguments" => self.argument_by_id.get(id),
            "definitions" => self.definitions.get(id),
            _ => None,
        };
        record
            .map(|r| text(r, "label"))
            .unwrap_or_default()
            .to_owned()
    }

    fn sense_view(&self, id: &str) -> Value {
        let sense = &self.index.by_id[id];
        let declaration = self.sense_declaration.get(id).cloned().flatten();
        json!({
            "id": id,
            "term": sense.term,
            "label": sense.label,
            "definition_id": sense.definition_id,
            "lean_declaration": declaration,
            "distinct_lean_declaration": !self.undeclared.contains(id),
        })
    }

    /// term -> sense ids the definitions carry (the check engine's index).
    fn senses_of(&self, definitions: &[&str]) -> BTreeMap<String, BTreeSet<String>> {
        let mut used: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for definition in definitions {
            for id in self
                .index
                .by_definition
                .get(*definition)
                .into_iter()
                .flatten()
            {
                used.entry(self.index.by_id[id].term.clone())
                    .or_default()
                    .insert(id.clone());
            }
        }
        used
    }

    fn formal_status(&self, id: &str) -> (&'static str, &'static str, Option<String>) {
        let Some(definition) = self.formal.get(id) else {
            return ("unknown", "unknown (definition status not loaded)", None);
        };
        let gap = definition
            .gap
            .as_ref()
            .map(|gap| text(gap.as_object().unwrap_or(&Obj::new()), "kind").to_owned());
        let (code, words) = match &definition.state {
            State::NoLean => ("no_lean_declaration", "no Lean declaration"),
            State::Uncomputed => (
                "not_computed",
                "not computed (`truth definitions refresh --write` after `lake build`)",
            ),
            State::Computed { status, .. } => match status {
                Status::Defined => ("defined", "settled by Lean"),
                Status::Primitive => ("primitive", "primitive"),
                Status::Constraint => ("constraint", "constraint"),
                Status::Unresolved => ("unresolved", "unresolved"),
            },
        };
        (code, words, gap)
    }

    fn definition_view(&self, id: &str) -> Value {
        let Some(record) = self.definitions.get(id) else {
            return json!({"id": id, "known": false});
        };
        let senses: Vec<Value> = self
            .index
            .by_definition
            .get(id)
            .into_iter()
            .flatten()
            .map(|sense| self.sense_view(sense))
            .collect();
        let (code, words, gap) = self.formal_status(id);
        json!({
            "id": id,
            "known": true,
            "label": text(record, "label"),
            "term": text(record, "term"),
            "basis": record.get("basis").cloned().unwrap_or(Value::Null),
            "lean_declaration": record.get("lean_declaration").cloned().unwrap_or(Value::Null),
            "formal_status": code,
            "formal_status_text": words,
            "formal_gap_kind": gap,
            "senses": senses,
        })
    }

    /// The disambiguations a statement is read against: those it links and
    /// those reached through a linked definition that is one of their senses.
    fn disambiguation_views(&self, record: &Obj) -> Vec<Value> {
        let linked: BTreeSet<&str> = list(record, "disambiguation_ids").into_iter().collect();
        let definitions: BTreeSet<&str> = list(record, "definition_ids").into_iter().collect();
        let mut views = Vec::new();
        for disambiguation in &self.disambiguations {
            let fields = &disambiguation.fields;
            let id = text(fields, "id");
            let senses: Vec<&str> = list(fields, "sense_definition_ids")
                .into_iter()
                .filter(|definition| definitions.contains(definition))
                .collect();
            if !linked.contains(id) && senses.is_empty() {
                continue;
            }
            let takes: BTreeSet<String> = self
                .senses_of(&senses)
                .into_iter()
                .filter(|(term, _)| term == text(fields, "term_label"))
                .flat_map(|(_, ids)| ids)
                .map(|sense| self.index.by_id[&sense].label.clone())
                .collect();
            views.push(json!({
                "id": id,
                "label": text(fields, "label"),
                "term": text(fields, "term"),
                "term_label": text(fields, "term_label"),
                "linked": linked.contains(id),
                "takes": takes,
                "takes_definition_ids": senses,
                "resolution_excerpt": excerpt(text(fields, "resolution")),
            }));
        }
        for id in &linked {
            if !self
                .disambiguations
                .iter()
                .any(|d| text(&d.fields, "id") == *id)
            {
                views.push(json!({"id": id, "known": false, "linked": true}));
            }
        }
        views
    }

    fn senses_used_view(&self, used: &BTreeMap<String, BTreeSet<String>>) -> Vec<Value> {
        used.iter()
            .map(|(term, ids)| {
                let mut senses: Vec<Value> = ids.iter().map(|id| self.sense_view(id)).collect();
                senses.sort_by(|a, b| a["label"].as_str().cmp(&b["label"].as_str()));
                json!({"term": term, "senses": senses})
            })
            .collect()
    }

    /// Steps 1-4 for one statement: proposition, definitions,
    /// disambiguations and senses used.
    pub fn statement_semantics(&self, sid: &str) -> Value {
        let Some(record) = self.statements.get(sid) else {
            return json!({"id": sid, "known": false});
        };
        let definitions: Vec<&str> = list(record, "definition_ids");
        json!({
            "id": sid,
            "known": true,
            "label": text(record, "label"),
            "paraphrase": text(record, "paraphrase"),
            "lean_declaration": record.get("lean_declaration").cloned().unwrap_or(Value::Null),
            "definitions": definitions.iter().map(|id| self.definition_view(id)).collect::<Vec<_>>(),
            "disambiguations": self.disambiguation_views(record),
            "senses_used": self.senses_used_view(&self.senses_of(&definitions)),
        })
    }

    /// term -> sense -> the statements (by role) or the argument itself that
    /// carry it, in role order: argument, conclusion, premises, commitments.
    fn carriers(&self, fields: &Obj) -> BTreeMap<String, BTreeMap<String, Vec<Value>>> {
        let mut out: BTreeMap<String, BTreeMap<String, Vec<Value>>> = BTreeMap::new();
        let mut add = |definitions: Vec<&str>, role: &str, sid: Option<&str>| {
            for (term, senses) in self.senses_of(&definitions) {
                for sense in senses {
                    let carriers = out
                        .entry(term.clone())
                        .or_default()
                        .entry(sense)
                        .or_default();
                    let entry = json!({"role": role, "statement_id": sid,
                                       "label": sid.map(|sid| self.label_of("statements", sid))});
                    if !carriers.contains(&entry) {
                        carriers.push(entry);
                    }
                }
            }
        };
        add(list(fields, "definition_ids"), "argument", None);
        let statement_definitions =
            |sid: &str| self.statements.get(sid).map(|s| list(s, "definition_ids"));
        let conclusion = text(fields, "conclusion_statement_id");
        add(
            statement_definitions(conclusion).unwrap_or_default(),
            "conclusion",
            Some(conclusion),
        );
        for (field, role) in [
            ("premise_statement_ids", "premise"),
            ("commitment_statement_ids", "commitment"),
        ] {
            for sid in list(fields, field) {
                add(
                    statement_definitions(sid).unwrap_or_default(),
                    role,
                    Some(sid),
                );
            }
        }
        out
    }

    /// Step 5 for one argument record: per term, its senses with the
    /// statements carrying each and the verdict `truth check` reaches;
    /// `allowlisted` applies the legacy allowlist (false for a new argument).
    pub fn analyze(&self, fields: &Obj, allowlisted: bool) -> Value {
        let empty = Vec::new();
        let bridges = fields
            .get("sense_bridges")
            .and_then(Value::as_array)
            .unwrap_or(&empty);
        let control = fields.get("sense_mixing_control") == Some(&Value::Bool(true));
        let used = argument_term_senses(fields, &self.statements, &self.index);
        let carriers = self.carriers(fields);
        let id = text(fields, "id");
        let mut terms = Vec::new();
        for (term, senses) in &used {
            let verdict = if senses.len() < 2 {
                Verdict::Single
            } else if control {
                Verdict::Control
            } else if bridged(term, senses, bridges) {
                Verdict::Bridged
            } else if allowlisted && self.allowlist.covers(id, term, senses) {
                Verdict::Allowlisted
            } else {
                Verdict::Unbridged
            };
            let mut views: Vec<Value> = senses
                .iter()
                .map(|sense| {
                    let mut view = self.sense_view(sense);
                    view["carriers"] = json!(
                        carriers
                            .get(term)
                            .and_then(|by_sense| by_sense.get(sense))
                            .cloned()
                            .unwrap_or_default()
                    );
                    view
                })
                .collect();
            views.sort_by(|a, b| a["label"].as_str().cmp(&b["label"].as_str()));
            let term_bridges: Vec<Value> = bridges
                .iter()
                .filter(|bridge| bridge.get("term").and_then(Value::as_str) == Some(term))
                .map(|bridge| {
                    let end = |key| bridge.get(key).and_then(Value::as_str).unwrap_or_default();
                    let label = |key| self.index.by_id.get(end(key)).map(|s| s.label.clone());
                    json!({
                        "statement_id": end("statement_id"),
                        "label": self.label_of("statements", end("statement_id")),
                        "role": bridge.get("role").and_then(Value::as_str).unwrap_or("premise"),
                        "from": end("from"),
                        "to": end("to"),
                        "from_label": label("from"),
                        "to_label": label("to"),
                    })
                })
                .collect();
            terms.push(json!({
                "term": term,
                "verdict": verdict.code(),
                "verdict_text": verdict.text(),
                "senses": views,
                "bridges": term_bridges,
            }));
        }
        let conclusion = text(fields, "conclusion_statement_id");
        json!({
            "id": id,
            "label": text(fields, "label"),
            "conclusion_statement_id": conclusion,
            "premise_statement_ids": list(fields, "premise_statement_ids"),
            "commitment_statement_ids": list(fields, "commitment_statement_ids"),
            "sense_mixing_control": control,
            "root_route": self.reaching_root.as_ref().map(|reaching| reaching.contains(conclusion)),
            "terms": terms,
        })
    }

    /// Arguments in file order, those on a root route first.
    fn ordered(&self, ids: Vec<&'a str>) -> Vec<&'a str> {
        let mut ids = ids;
        if let Some(reaching) = &self.reaching_root {
            ids.sort_by_key(|id| {
                let conclusion = text(self.argument_by_id[id], "conclusion_statement_id");
                !reaching.contains(conclusion)
            });
        }
        ids
    }

    fn argument_list(&self, ids: Vec<&'a str>, limit: usize) -> (Value, Vec<Value>) {
        let ids = self.ordered(ids);
        let all: Vec<Value> = ids
            .iter()
            .map(|id| self.analyze(self.argument_by_id[id], true))
            .collect();
        let list = json!({
            "total": all.len(),
            "shown": all.iter().take(limit).cloned().collect::<Vec<_>>(),
        });
        (list, all)
    }

    /// Statement mode: steps 1-6.
    pub fn statement_view(&self, sid: &str, limit: usize) -> Value {
        let concluding: Vec<&str> = self
            .arguments
            .iter()
            .filter(|a| text(&a.fields, "conclusion_statement_id") == sid)
            .map(|a| text(&a.fields, "id"))
            .collect();
        let using: Vec<&str> = self
            .arguments
            .iter()
            .filter(|a| {
                list(&a.fields, "premise_statement_ids").contains(&sid)
                    || list(&a.fields, "commitment_statement_ids").contains(&sid)
            })
            .map(|a| text(&a.fields, "id"))
            .collect();
        let (concluding, mut all) = self.argument_list(concluding, limit);
        let (using, more) = self.argument_list(using, limit);
        all.extend(more);
        json!({
            "mode": "statement",
            "statement": self.statement_semantics(sid),
            "arguments": {"concluding": concluding, "using": using},
            "summary": summary(&all, limit),
        })
    }

    /// The arguments supporting `fields`' premises and commitments,
    /// transitively (every argument concluding a reached statement), in
    /// breadth-first order; the argument itself is excluded.
    fn ancestry(&self, fields: &'a Obj) -> Vec<&'a str> {
        let own = text(fields, "id");
        let mut seen_statements: HashSet<&str> = HashSet::new();
        let mut seen: HashSet<&str> = HashSet::from([own]);
        let mut order = Vec::new();
        let mut pending: VecDeque<&str> = list(fields, "premise_statement_ids")
            .into_iter()
            .chain(list(fields, "commitment_statement_ids"))
            .collect();
        while let Some(sid) = pending.pop_front() {
            if !seen_statements.insert(sid) {
                continue;
            }
            for argument in self.concluding.get(sid).into_iter().flatten() {
                if seen.insert(argument) {
                    order.push(*argument);
                    let record = self.argument_by_id[argument];
                    pending.extend(list(record, "premise_statement_ids"));
                    pending.extend(list(record, "commitment_statement_ids"));
                }
            }
        }
        order
    }

    /// Argument mode: the argument's verdicts, its statements' semantics
    /// and a summary over its support ancestry.
    pub fn argument_view(&self, aid: &str, limit: usize) -> Value {
        let fields = self.argument_by_id[aid];
        let statements: Vec<Value> =
            std::iter::once(("conclusion", text(fields, "conclusion_statement_id")))
                .chain(
                    list(fields, "premise_statement_ids")
                        .into_iter()
                        .map(|sid| ("premise", sid)),
                )
                .chain(
                    list(fields, "commitment_statement_ids")
                        .into_iter()
                        .map(|sid| ("commitment", sid)),
                )
                .map(|(role, sid)| {
                    let mut view = self.statement_semantics(sid);
                    view["role"] = json!(role);
                    view
                })
                .collect();
        let ancestry: Vec<Value> = self
            .ancestry(fields)
            .into_iter()
            .map(|id| self.analyze(self.argument_by_id[id], true))
            .collect();
        json!({
            "mode": "argument",
            "argument": self.analyze(fields, true),
            "statements": statements,
            "ancestry": summary(&ancestry, limit),
        })
    }

    /// The sense a token names: its uuid or its unique label.
    pub fn resolve_sense(&self, token: &str) -> Result<String, String> {
        if self.index.by_id.contains_key(token) {
            return Ok(token.to_owned());
        }
        let found: Vec<&String> = self
            .index
            .by_id
            .iter()
            .filter(|(_, sense)| sense.label == token)
            .map(|(id, _)| id)
            .collect();
        match found.as_slice() {
            [id] => Ok((*id).clone()),
            [] => Err(format!("unknown sense: {token}")),
            _ => Err(format!(
                "sense label {token} names several senses; pass a uuid"
            )),
        }
    }

    /// Preflight: the candidate argument `premises ⊢ conclusion` with the
    /// argument-level `definitions` (as `argument_batch.py records` writes a
    /// batch's `definitions` into each argument) and the requested bridges,
    /// judged as `truth check` judges a new argument. Commitments and
    /// `term_senses` are not modelled.
    pub fn preflight(
        &self,
        premises: &[String],
        conclusion: &str,
        definitions: &[String],
        requests: &[BridgeRequest],
    ) -> Result<Value, String> {
        for sid in premises.iter().map(String::as_str).chain([conclusion]) {
            if !self.statements.contains_key(sid) {
                return Err(format!("unknown statement: {sid}"));
            }
        }
        for definition in definitions {
            if !self.definitions.contains_key(definition.as_str()) {
                return Err(format!("unknown definition: {definition}"));
            }
        }
        let dedup = |items: &[String]| {
            items.iter().fold(Vec::<String>::new(), |mut kept, item| {
                if !kept.contains(item) {
                    kept.push(item.clone());
                }
                kept
            })
        };
        let mut premises = dedup(premises);
        let definitions = dedup(definitions);
        let mut added = Vec::new();
        let mut bridges = Vec::new();
        let mut notes = Vec::new();
        for request in requests {
            let sid = request.statement_id.as_str();
            let Some(statement) = self.statements.get(sid) else {
                return Err(format!("unknown bridge statement: {sid}"));
            };
            let role = if sid == conclusion {
                "conclusion"
            } else {
                "premise"
            };
            let mut edges: Vec<(String, String, String)> = Vec::new();
            match &request.senses {
                Some((from, to)) => {
                    let (from, to) = (self.resolve_sense(from)?, self.resolve_sense(to)?);
                    let (a, b) = (&self.index.by_id[&from], &self.index.by_id[&to]);
                    if a.term != b.term || from == to {
                        return Err(format!(
                            "bridge {sid}: {} and {} are not two senses of one term",
                            a.label, b.label
                        ));
                    }
                    edges.push((a.term.clone(), from, to));
                }
                None => {
                    for (term, senses) in self.senses_of(&list(statement, "definition_ids")) {
                        let mut senses = senses.into_iter();
                        let Some(first) = senses.next() else {
                            continue;
                        };
                        for other in senses {
                            edges.push((term.clone(), first.clone(), other));
                        }
                    }
                }
            }
            if edges.is_empty() {
                // Not added as a premise: it would bring its own senses in
                // without relating any.
                notes.push(format!(
                    "bridge {sid} links fewer than two senses of any term, so it relates none and is not added; name them as STATEMENT@SENSE,SENSE"
                ));
                continue;
            }
            if role == "premise" && !premises.iter().any(|p| p == sid) {
                premises.push(sid.to_owned());
                added.push(sid.to_owned());
            }
            for (term, from, to) in edges {
                let mut bridge = json!({"term": term, "from": from, "to": to, "statement_id": sid});
                if role == "conclusion" {
                    bridge["role"] = json!("conclusion");
                }
                bridges.push(bridge);
            }
        }
        let mut candidate = json!({
            "id": "",
            "conclusion_statement_id": conclusion,
            "premise_statement_ids": premises,
        });
        if !definitions.is_empty() {
            candidate["definition_ids"] = json!(definitions);
        }
        if !bridges.is_empty() {
            candidate["sense_bridges"] = json!(bridges);
        }
        // The disambiguations `truth check` requires the argument to link.
        let mut used: HashSet<&str> = definitions.iter().map(String::as_str).collect();
        for sid in premises.iter().map(String::as_str).chain([conclusion]) {
            used.extend(list(self.statements[sid], "definition_ids"));
        }
        let required: Vec<&str> = self
            .disambiguations
            .iter()
            .filter(|d| {
                list(&d.fields, "sense_definition_ids")
                    .into_iter()
                    .filter(|definition| used.contains(definition))
                    .collect::<BTreeSet<_>>()
                    .len()
                    > 1
            })
            .map(|d| text(&d.fields, "id"))
            .collect();
        if !required.is_empty() {
            candidate["disambiguation_ids"] = json!(required);
        }
        let fields = candidate.as_object().expect("object");
        let check = validate_argument_senses(
            CANDIDATE,
            fields,
            &self.statements,
            &self.disambiguations,
            &self.index,
            &Allowlist::default(),
        );
        let analysis = self.analyze(fields, false);
        let terms = analysis["terms"].as_array().cloned().unwrap_or_default();
        let unbridged: Vec<Value> = terms
            .iter()
            .filter(|term| term["verdict"] == Verdict::Unbridged.code())
            .map(|term| {
                let labels: Vec<&str> = term["senses"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(|sense| sense["label"].as_str())
                    .collect();
                let name = term["term"].as_str().unwrap_or_default();
                json!({
                    "term": name,
                    "senses": labels,
                    "needed": format!(
                        "list a premise relating {} in sense_bridges (--bridge STATEMENT@{}), or split the argument per sense",
                        labels.join(" and "),
                        labels.join(",")
                    ),
                })
            })
            .collect();
        let undeclared: Vec<Value> = terms
            .iter()
            .flat_map(|term| term["senses"].as_array().cloned().unwrap_or_default())
            .filter(|sense| sense["distinct_lean_declaration"] == false)
            .collect();
        let passes = check.is_ok();
        Ok(json!({
            "mode": "preflight",
            "candidate": candidate,
            "added_premises": added,
            "notes": notes,
            "terms": terms,
            "unbridged": unbridged,
            "senses_without_distinct_lean_declaration": undeclared,
            "check": {"passes": passes, "message": check.err()},
            "agrees_with_check": passes == unbridged.is_empty(),
        }))
    }
}

/// Counts per verdict over `analyses` (term uses and arguments) and the
/// equivocation risks, at most `limit` listed.
pub fn summary(analyses: &[Value], limit: usize) -> Value {
    let mut uses: BTreeMap<&str, usize> = Verdict::ALL.iter().map(|v| (v.code(), 0)).collect();
    let mut arguments: BTreeMap<&str, usize> = uses.clone();
    let mut risks = Vec::new();
    let mut risky_arguments = BTreeSet::new();
    let mut risky_root_route = BTreeSet::new();
    // An argument both concluding and using the target counts once.
    let mut seen = HashSet::new();
    let analyses: Vec<&Value> = analyses
        .iter()
        .filter(|analysis| {
            let id = analysis["id"].as_str().unwrap_or_default();
            id.is_empty() || seen.insert(id)
        })
        .collect();
    for analysis in &analyses {
        let mut verdicts = BTreeSet::new();
        for term in analysis["terms"].as_array().into_iter().flatten() {
            let Some(verdict) = term["verdict"].as_str().and_then(Verdict::parse) else {
                continue;
            };
            *uses.get_mut(verdict.code()).expect("verdict") += 1;
            verdicts.insert(verdict);
            if verdict.risk() {
                let id = analysis["id"].as_str().unwrap_or_default().to_owned();
                if analysis["root_route"] == true {
                    risky_root_route.insert(id.clone());
                }
                risky_arguments.insert(id);
                risks.push(json!({
                    "argument_id": analysis["id"],
                    "label": analysis["label"],
                    "root_route": analysis["root_route"],
                    "term": term["term"],
                    "verdict": verdict.code(),
                    "senses": term["senses"].as_array().into_iter().flatten()
                        .map(|sense| sense["label"].clone()).collect::<Vec<_>>(),
                }));
            }
        }
        for verdict in verdicts {
            *arguments.get_mut(verdict.code()).expect("verdict") += 1;
        }
    }
    json!({
        "arguments": analyses.len(),
        "term_uses": uses,
        "arguments_by_verdict": arguments,
        "risky_arguments": risky_arguments.len(),
        "risky_root_route_arguments": risky_root_route.len(),
        "equivocation_risks_total": risks.len(),
        "equivocation_risks": risks.into_iter().take(limit).collect::<Vec<_>>(),
    })
}

// ---------------------------------------------------------------------------
// Text.

fn short(id: &str) -> &str {
    id.get(..8).unwrap_or(id)
}

fn show(label: &Value, id: &Value) -> String {
    let id = id.as_str().unwrap_or_default();
    match label.as_str().filter(|label| !label.is_empty()) {
        Some(label) if id.is_empty() => label.to_owned(),
        Some(label) => format!("{label} [{}]", short(id)),
        None => id.to_owned(),
    }
}

/// At most this many carriers of one sense are named in text.
const CARRIERS: usize = 3;

fn carriers_text(carriers: &Value) -> String {
    let carriers = carriers.as_array().cloned().unwrap_or_default();
    let mut shown: Vec<String> = carriers
        .iter()
        .take(CARRIERS)
        .map(|carrier| match carrier["statement_id"].as_str() {
            Some(_) => format!(
                "{} {}",
                carrier["role"].as_str().unwrap_or_default(),
                show(&carrier["label"], &carrier["statement_id"])
            ),
            None => "argument definition_ids".to_owned(),
        })
        .collect();
    if carriers.len() > CARRIERS {
        shown.push(format!("and {} more", carriers.len() - CARRIERS));
    }
    shown.join("; ")
}

fn sense_text(sense: &Value) -> String {
    let mut out = sense["label"].as_str().unwrap_or_default().to_owned();
    if sense["distinct_lean_declaration"] == false {
        out.push_str(" (no distinct Lean declaration)");
    }
    out
}

/// One argument's verdicts, indented by `indent`.
fn argument_text(analysis: &Value, indent: &str, lines: &mut Vec<String>) {
    let route = match analysis["root_route"].as_bool() {
        Some(true) => "  [root route]",
        _ => "",
    };
    lines.push(format!(
        "{indent}- {}{route}",
        show(&analysis["label"], &analysis["id"])
    ));
    let terms = analysis["terms"].as_array().cloned().unwrap_or_default();
    if terms.is_empty() {
        lines.push(format!("{indent}    no disambiguated term"));
    }
    // One sense per term: one line of sense labels (carriers in --json).
    let single: Vec<String> = terms
        .iter()
        .filter(|term| term["verdict"] == Verdict::Single.code())
        .flat_map(|term| term["senses"].as_array().cloned().unwrap_or_default())
        .map(|sense| sense_text(&sense))
        .collect();
    if !single.is_empty() {
        lines.push(format!(
            "{indent}    single sense ({}): {}",
            single.len(),
            single.join(", ")
        ));
    }
    for term in terms {
        let name = term["term"].as_str().unwrap_or_default();
        let verdict = term["verdict_text"].as_str().unwrap_or_default();
        let senses = term["senses"].as_array().cloned().unwrap_or_default();
        if term["verdict"] == Verdict::Single.code() {
            continue;
        }
        lines.push(format!("{indent}    {name}: {verdict}"));
        for sense in &senses {
            lines.push(format!(
                "{indent}      {} <- {}",
                sense_text(sense),
                carriers_text(&sense["carriers"])
            ));
        }
        for bridge in term["bridges"].as_array().into_iter().flatten() {
            lines.push(format!(
                "{indent}      bridge {} -> {} by {} {}",
                bridge["from_label"].as_str().unwrap_or("?"),
                bridge["to_label"].as_str().unwrap_or("?"),
                bridge["role"].as_str().unwrap_or_default(),
                show(&bridge["label"], &bridge["statement_id"])
            ));
        }
    }
}

/// Steps 1-4 as text; `compact` omits the paraphrase and resolution excerpts.
fn statement_text(view: &Value, compact: bool, lines: &mut Vec<String>) {
    let role = view["role"]
        .as_str()
        .map(|role| format!("{role}: "))
        .unwrap_or_default();
    if view["known"] == false {
        lines.push(format!(
            "{role}unknown statement {}",
            view["id"].as_str().unwrap_or_default()
        ));
        return;
    }
    lines.push(format!("{role}{}", show(&view["label"], &view["id"])));
    if !compact {
        lines.push(format!(
            "  paraphrase: {}",
            view["paraphrase"].as_str().unwrap_or_default()
        ));
    }
    lines.push(format!(
        "  lean: {}",
        view["lean_declaration"].as_str().unwrap_or("none")
    ));
    let definitions = view["definitions"].as_array().cloned().unwrap_or_default();
    lines.push(format!("  definitions ({}):", definitions.len()));
    for definition in &definitions {
        if definition["known"] == false {
            lines.push(format!(
                "    - unknown definition {}",
                definition["id"].as_str().unwrap_or_default()
            ));
            continue;
        }
        let senses: Vec<String> = definition["senses"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|sense| {
                format!(
                    "{} of {}",
                    sense["label"].as_str().unwrap_or_default(),
                    sense["term"].as_str().unwrap_or_default()
                )
            })
            .collect();
        let sense = if senses.is_empty() {
            "no sense label".to_owned()
        } else {
            senses.join(", ")
        };
        let gap = match definition["formal_gap_kind"].as_str() {
            Some(kind) if !kind.is_empty() => format!(", formal_gap {kind}"),
            Some(_) => ", formal_gap".to_owned(),
            None => String::new(),
        };
        lines.push(format!(
            "    - {} — term \"{}\", {sense}; lean {}; formal status: {}{gap}; {}",
            show(&definition["label"], &definition["id"]),
            definition["term"].as_str().unwrap_or_default(),
            definition["lean_declaration"].as_str().unwrap_or("none"),
            definition["formal_status_text"]
                .as_str()
                .unwrap_or_default(),
            definition["basis"].as_str().unwrap_or("basis unrecorded"),
        ));
    }
    let disambiguations = view["disambiguations"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    lines.push(format!("  disambiguations ({}):", disambiguations.len()));
    for disambiguation in &disambiguations {
        if disambiguation["known"] == false {
            lines.push(format!(
                "    - unknown disambiguation {}",
                disambiguation["id"].as_str().unwrap_or_default()
            ));
            continue;
        }
        let takes: Vec<&str> = disambiguation["takes"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        let takes = if takes.is_empty() {
            "takes no sense of it (linked only)".to_owned()
        } else {
            format!("takes {}", takes.join(", "))
        };
        let how = if disambiguation["linked"] == true {
            "linked"
        } else {
            "via a definition"
        };
        lines.push(format!(
            "    - {} ({}, {how}) — {takes}",
            show(&disambiguation["label"], &disambiguation["id"]),
            disambiguation["term_label"].as_str().unwrap_or_default(),
        ));
        if !compact {
            lines.push(format!(
                "      resolution: {}",
                disambiguation["resolution_excerpt"]
                    .as_str()
                    .unwrap_or_default()
            ));
        }
    }
    let used = view["senses_used"].as_array().cloned().unwrap_or_default();
    if used.is_empty() {
        lines.push("  senses used: none".to_owned());
    } else {
        lines.push("  senses used:".to_owned());
    }
    for term in &used {
        let senses = term["senses"].as_array().cloned().unwrap_or_default();
        let labels: Vec<String> = senses
            .iter()
            .map(|sense| {
                format!(
                    "{} ({})",
                    sense["label"].as_str().unwrap_or_default(),
                    sense["lean_declaration"]
                        .as_str()
                        .unwrap_or("no lean_declaration")
                )
            })
            .collect();
        lines.push(format!(
            "    {}: {}",
            term["term"].as_str().unwrap_or_default(),
            labels.join(", ")
        ));
        for sense in senses
            .iter()
            .filter(|s| s["distinct_lean_declaration"] == false)
        {
            lines.push(format!(
                "      ! {} has no distinct Lean declaration: bind-check cannot catch equivocation on this sense",
                sense["label"].as_str().unwrap_or_default()
            ));
        }
    }
}

fn summary_text(summary: &Value, heading: &str, lines: &mut Vec<String>) {
    let counts = |field: &str| {
        Verdict::ALL
            .iter()
            .map(|verdict| {
                format!(
                    "{} {}",
                    summary[field][verdict.code()].as_u64().unwrap_or(0),
                    verdict.text()
                )
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    lines.push(format!(
        "{heading}: {} argument(s); term uses: {}",
        summary["arguments"],
        counts("term_uses")
    ));
    lines.push(format!(
        "  arguments with: {}",
        counts("arguments_by_verdict")
    ));
    let total = summary["equivocation_risks_total"].as_u64().unwrap_or(0);
    if total == 0 {
        lines.push("  equivocation risks: none".to_owned());
        return;
    }
    let risks = summary["equivocation_risks"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    lines.push(format!(
        "  equivocation risks: {total} term use(s) in {} argument(s), {} of them on a root route{}",
        summary["risky_arguments"],
        summary["risky_root_route_arguments"],
        if risks.len() < total as usize {
            format!(", first {} shown", risks.len())
        } else {
            String::new()
        }
    ));
    for risk in risks {
        let senses: Vec<&str> = risk["senses"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        let route = if risk["root_route"] == true {
            " [root route]"
        } else {
            ""
        };
        lines.push(format!(
            "    - {}{route}: {} {} ({})",
            show(&risk["label"], &risk["argument_id"]),
            risk["term"].as_str().unwrap_or_default(),
            Verdict::parse(risk["verdict"].as_str().unwrap_or_default()).map_or("", Verdict::text),
            senses.join(", ")
        ));
    }
}

fn list_text(heading: &str, list: &Value, lines: &mut Vec<String>) {
    let shown = list["shown"].as_array().cloned().unwrap_or_default();
    lines.push(String::new());
    lines.push(format!("{heading} ({} of {}):", shown.len(), list["total"]));
    if shown.is_empty() {
        lines.push("  none".to_owned());
    }
    for analysis in &shown {
        argument_text(analysis, "  ", lines);
    }
}

/// The text of any mode's view.
pub fn format(view: &Value) -> String {
    let mut lines = Vec::new();
    match view["mode"].as_str() {
        Some("statement") => {
            lines.push("Semantics of statement".to_owned());
            statement_text(&view["statement"], false, &mut lines);
            list_text(
                "Arguments concluding it",
                &view["arguments"]["concluding"],
                &mut lines,
            );
            list_text(
                "Arguments using it as a premise or commitment",
                &view["arguments"]["using"],
                &mut lines,
            );
            lines.push(String::new());
            summary_text(&view["summary"], "Summary", &mut lines);
        }
        Some("argument") => {
            lines.push("Semantics of argument".to_owned());
            argument_text(&view["argument"], "", &mut lines);
            for statement in view["statements"].as_array().into_iter().flatten() {
                lines.push(String::new());
                statement_text(statement, true, &mut lines);
            }
            lines.push(String::new());
            summary_text(
                &view["ancestry"],
                "Ancestry (arguments concluding its premises, transitively)",
                &mut lines,
            );
        }
        Some("preflight") => {
            let candidate = &view["candidate"];
            lines.push("Equivocation preflight of a candidate argument (as truth check judges a new argument; the legacy allowlist does not apply)".to_owned());
            lines.push(format!(
                "  conclusion: {}",
                candidate["conclusion_statement_id"]
                    .as_str()
                    .unwrap_or_default()
            ));
            for premise in candidate["premise_statement_ids"]
                .as_array()
                .into_iter()
                .flatten()
            {
                lines.push(format!(
                    "  premise: {}",
                    premise.as_str().unwrap_or_default()
                ));
            }
            for added in view["added_premises"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "  added bridge statement {} as a premise (a premise bridge must be a premise)",
                    added.as_str().unwrap_or_default()
                ));
            }
            for definition in candidate["definition_ids"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "  argument definition: {}",
                    definition.as_str().unwrap_or_default()
                ));
            }
            for note in view["notes"].as_array().into_iter().flatten() {
                lines.push(format!("  note: {}", note.as_str().unwrap_or_default()));
            }
            let required: Vec<&str> = candidate["disambiguation_ids"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .collect();
            if !required.is_empty() {
                lines.push(format!(
                    "  must link in disambiguation_ids: {}",
                    required.join(", ")
                ));
            }
            lines.push(String::new());
            let mut analysis =
                json!({"id": "", "label": "candidate argument", "terms": view["terms"]});
            analysis["root_route"] = Value::Null;
            argument_text(&analysis, "", &mut lines);
            lines.push(String::new());
            let unbridged = view["unbridged"].as_array().cloned().unwrap_or_default();
            if unbridged.is_empty() {
                lines.push("Unbridged mixing: none".to_owned());
            } else {
                lines.push(format!("Unbridged mixing ({}):", unbridged.len()));
                for entry in &unbridged {
                    lines.push(format!(
                        "  - {}: {}",
                        entry["term"].as_str().unwrap_or_default(),
                        entry["needed"].as_str().unwrap_or_default()
                    ));
                }
            }
            let undeclared = view["senses_without_distinct_lean_declaration"]
                .as_array()
                .cloned()
                .unwrap_or_default();
            if !undeclared.is_empty() {
                let labels: Vec<&str> = undeclared
                    .iter()
                    .filter_map(|sense| sense["label"].as_str())
                    .collect();
                lines.push(format!(
                    "Senses without a distinct Lean declaration (bind-check cannot catch equivocation on them): {}",
                    labels.join(", ")
                ));
            }
            lines.push(match view["check"]["message"].as_str() {
                None => "truth check verdict for a new argument: passes the sense rules".to_owned(),
                Some(message) => {
                    format!("truth check verdict for a new argument: fails: {message}")
                }
            });
        }
        _ => {}
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn excerpt_is_bounded_on_a_char_boundary() {
        let long = "é".repeat(EXCERPT + 5);
        let cut = excerpt(&long);
        assert!(cut.ends_with('…'));
        assert_eq!(cut.chars().count(), EXCERPT + 1);
        assert_eq!(excerpt("a  b\nc"), "a b c");
    }

    #[test]
    fn summary_counts_term_uses_and_arguments() {
        let analysis = |id: &str, verdicts: &[&str]| {
            json!({"id": id, "label": id, "root_route": null, "terms": verdicts.iter()
                .map(|v| json!({"term": "T", "verdict": v, "senses": []})).collect::<Vec<_>>()})
        };
        let all = [
            analysis("a", &["single_sense", "allowlisted_mixing"]),
            analysis("b", &["allowlisted_mixing", "allowlisted_mixing"]),
            analysis("c", &["bridged"]),
            // Concludes and uses the target: listed twice, counted once.
            analysis("b", &["allowlisted_mixing", "allowlisted_mixing"]),
        ];
        let summary = summary(&all, 1);
        assert_eq!(summary["arguments"], 3);
        assert_eq!(summary["term_uses"]["allowlisted_mixing"], 3);
        assert_eq!(summary["arguments_by_verdict"]["allowlisted_mixing"], 2);
        assert_eq!(summary["risky_arguments"], 2);
        assert_eq!(summary["equivocation_risks_total"], 3);
        assert_eq!(summary["equivocation_risks"].as_array().unwrap().len(), 1);
    }
}
