//! `truth tree STATEMENT`: the argument graph re-rooted at any statement
//! (#1674), with the definitions and senses of every statement in view.
//!
//! The view creates no authority. Every status is read from one frontier
//! report computed with the statement as the frontier root
//! ([`crate::frontier::current_frontier`]); this module only selects and
//! arranges records.
//!
//! - **Down (support):** the arguments concluding the root, each with its
//!   premises and inference steps, recursively. Alternative arguments are OR
//!   branches; an argument's premises are an AND bundle.
//! - **Up (dependents):** the arguments that use the root as a premise, their
//!   conclusions and co-premises, recursively toward the case root.
//! - **Strength orders:** `strengthens` relations touching the view.
//! - **Terms:** each statement's `definition_ids` and `disambiguation_ids`,
//!   with the sense label a definition carries.
//!
//! Traversal is breadth-first, so every node sits at its shallowest depth;
//! shared nodes appear once (a DAG), and edges back to a node on the current
//! path are marked `cycle`. Depth limits and the node budget leave explicit
//! truncation markers. Every edge has a `kind` and an `extra_premises` list so
//! derived edges (the reserved [`RESERVED_KINDS`]) can be added later without
//! a format change.

use crate::Corpus;
use serde::Serialize;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

pub const DEFAULT_DOWN: usize = 3;
pub const DEFAULT_UP: usize = 3;
pub const DEFAULT_BUDGET: usize = 400;

/// Edge kinds this version emits.
pub const EDGE_KINDS: &[&str] = &["supports", "uses", "strengthens"];
/// Edge kinds reserved for derived inversions (#1674 phase 2), never emitted
/// yet: `contrapositive` (from a verified argument P1..Pn ⊢ C, the edge
/// ¬C ∧ the other premises ⊢ ¬Pi) and `inverse_conditional` (C ∧ ¬B ⊢ A,
/// only with an explicit exhaustiveness premise C → A ∨ B in
/// `extra_premises`). The unconditioned inverse C ⊢ A is invalid and is never
/// emitted.
pub const RESERVED_KINDS: &[&str] = &["contrapositive", "inverse_conditional"];

#[derive(Debug, Clone, Copy)]
pub struct Options {
    pub down: usize,
    pub up: usize,
    pub budget: usize,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            down: DEFAULT_DOWN,
            up: DEFAULT_UP,
            budget: DEFAULT_BUDGET,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct Truncation {
    pub statement_id: String,
    /// `down` or `up`.
    pub side: &'static str,
    /// `depth` or `budget`.
    pub reason: &'static str,
    /// Arguments (concluding it for `down`, using it for `up`) not shown.
    pub omitted_arguments: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct Edge {
    /// One of [`EDGE_KINDS`] (later also [`RESERVED_KINDS`]).
    pub kind: &'static str,
    /// `supports`: argument → conclusion; `uses`: argument → premise;
    /// `strengthens`: strong statement → weak statement.
    pub from: String,
    pub to: String,
    pub argument_id: Option<String>,
    pub relation_id: Option<String>,
    pub result_id: Option<String>,
    /// Premises the edge needs besides its endpoints (empty for the record
    /// edges; derived edges list theirs here).
    pub extra_premises: Vec<String>,
    /// Backed by a result record (`supports`/`uses`: the argument has one;
    /// `strengthens`: the registration's backing result exists).
    pub verified: bool,
    /// How a derived edge was obtained; `null` for record edges.
    pub derivation: Option<String>,
    /// The edge returns to a node on the current path of the walk from the
    /// root (the walk does not continue through it).
    pub cycle: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct SenseUse {
    pub disambiguation_id: String,
    pub sense_id: Option<String>,
    pub sense_label: Option<String>,
    pub lean_declaration: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Definition {
    pub id: String,
    pub label: Option<String>,
    pub term: Option<String>,
    pub basis: Option<String>,
    pub lean_declaration: Option<String>,
    /// The senses of disambiguations this definition defines.
    pub senses: Vec<SenseUse>,
    /// The lexicon's computed formal status (Lean definition, primitive,
    /// constraint or prose meaning; #1652 L3). `null` until that data exists.
    pub formal_status: Option<Value>,
    /// Statements in view linking it.
    pub used_by: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Disambiguation {
    pub id: String,
    pub label: Option<String>,
    pub term_label: Option<String>,
    pub senses: Vec<Value>,
    pub used_by: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct StatementNode {
    pub id: String,
    pub label: Option<String>,
    pub legacy_id: Option<String>,
    pub lean_declaration: Option<String>,
    /// `root`, `support` (down side), `dependent` (up side), `co_premise`
    /// (another premise of an up-side argument, not expanded) or
    /// `strength_neighbor` (the other end of a strength order, not expanded).
    pub role: &'static str,
    pub down_depth: Option<usize>,
    pub up_depth: Option<usize>,
    /// Frontier `statement_statuses` entry.
    pub status: Value,
    /// Frontier source depth (`bare`, `stated`, `supported`).
    pub depth: Value,
    /// Frontier closure reason, `null` when open.
    pub closed: Value,
    pub established: bool,
    /// Whether it reaches the tree root through the frontier's walk.
    pub reaches_tree_root: bool,
    pub is_case_root: bool,
    pub definition_ids: Vec<String>,
    pub disambiguation_ids: Vec<String>,
    /// The sense labels its linked definitions carry.
    pub senses: Vec<SenseUse>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Step {
    pub id: String,
    pub label: Option<String>,
    pub rule: Option<String>,
    pub input_statement_ids: Vec<String>,
    pub output_statement_id: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ResultRef {
    pub id: String,
    pub theorem: Option<String>,
    pub status: Option<String>,
    /// Declared or detected transcription kind, `null` otherwise.
    pub transcription: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ArgumentNode {
    pub id: String,
    pub label: Option<String>,
    /// The walks that admitted it: `down` (from its conclusion) and/or `up`.
    pub sides: Vec<&'static str>,
    /// The premises from which the upward walk admitted it.
    pub up_from: Vec<String>,
    pub conclusion_statement_id: String,
    pub premise_statement_ids: Vec<String>,
    pub steps: Vec<Step>,
    pub results: Vec<ResultRef>,
    pub verified: bool,
    /// For an argument concluding the tree root: its frontier route entry
    /// (cost and open premises), `null` otherwise.
    pub route: Option<Value>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Tree {
    pub schema_version: u32,
    pub root: String,
    pub case_root: String,
    pub options: Value,
    pub edge_kinds: &'static [&'static str],
    pub reserved_edge_kinds: &'static [&'static str],
    pub statements: Vec<StatementNode>,
    pub arguments: Vec<ArgumentNode>,
    pub edges: Vec<Edge>,
    pub definitions: Vec<Definition>,
    pub disambiguations: Vec<Disambiguation>,
    pub truncated: Vec<Truncation>,
    pub node_count: usize,
}

fn string(record: &Map<String, Value>, field: &str) -> Option<String> {
    record.get(field).and_then(Value::as_str).map(str::to_owned)
}

fn strings(record: &Map<String, Value>, field: &str) -> Vec<String> {
    record
        .get(field)
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect()
}

struct Index<'a> {
    corpus: &'a Corpus,
    report: &'a Value,
    concluding: HashMap<String, Vec<String>>,
    using: HashMap<String, Vec<String>>,
    results: HashMap<String, Vec<ResultRef>>,
    senses_of: HashMap<String, Vec<SenseUse>>,
}

impl<'a> Index<'a> {
    fn new(corpus: &'a Corpus, report: &'a Value) -> Self {
        let mut concluding: HashMap<String, Vec<String>> = HashMap::new();
        let mut using: HashMap<String, Vec<String>> = HashMap::new();
        for (id, record) in corpus.records_by_id("arguments") {
            if let Some(conclusion) = string(&record.fields, "conclusion_statement_id") {
                concluding
                    .entry(conclusion)
                    .or_default()
                    .push(id.to_owned());
            }
            let premises: BTreeSet<String> = strings(&record.fields, "premise_statement_ids")
                .into_iter()
                .collect();
            for premise in premises {
                using.entry(premise).or_default().push(id.to_owned());
            }
        }
        let mut results: HashMap<String, Vec<ResultRef>> = HashMap::new();
        for (id, record) in corpus.records_by_id("results") {
            let Some(argument) = string(&record.fields, "argument_id") else {
                continue;
            };
            let transcription = report["transcription_results"][id]["kind"]
                .as_str()
                .map(str::to_owned)
                .or_else(|| string(&record.fields, "transcription"));
            results.entry(argument).or_default().push(ResultRef {
                id: id.to_owned(),
                theorem: string(&record.fields, "theorem"),
                status: string(&record.fields, "status"),
                transcription,
            });
        }
        let mut senses_of: HashMap<String, Vec<SenseUse>> = HashMap::new();
        for (id, record) in corpus.records_by_id("disambiguations") {
            let senses = record.fields.get("senses").and_then(Value::as_array);
            let mut covered = HashSet::new();
            for sense in senses.into_iter().flatten() {
                let Some(definition) = sense["definition_id"].as_str() else {
                    continue;
                };
                covered.insert(definition.to_owned());
                senses_of
                    .entry(definition.to_owned())
                    .or_default()
                    .push(SenseUse {
                        disambiguation_id: id.to_owned(),
                        sense_id: sense["id"].as_str().map(str::to_owned),
                        sense_label: sense["label"].as_str().map(str::to_owned),
                        lean_declaration: sense["lean_declaration"].as_str().map(str::to_owned),
                    });
            }
            // A legacy disambiguation lists its senses only as definitions.
            for definition in strings(&record.fields, "sense_definition_ids") {
                if covered.insert(definition.clone()) {
                    senses_of.entry(definition).or_default().push(SenseUse {
                        disambiguation_id: id.to_owned(),
                        sense_id: None,
                        sense_label: None,
                        lean_declaration: None,
                    });
                }
            }
        }
        Self {
            corpus,
            report,
            concluding,
            using,
            results,
            senses_of,
        }
    }

    fn statement(&self, id: &str) -> Option<&Map<String, Value>> {
        self.corpus
            .get("statements", id)
            .map(|record| &record.fields)
    }

    fn argument(&self, id: &str) -> Option<&Map<String, Value>> {
        self.corpus
            .get("arguments", id)
            .map(|record| &record.fields)
    }

    fn verified(&self, argument: &str) -> bool {
        self.results.contains_key(argument)
    }

    fn transcription(&self, argument: &str) -> bool {
        self.results
            .get(argument)
            .is_some_and(|results| results.iter().all(|result| result.transcription.is_some()))
    }

    fn label(&self, kind: &str, id: &str) -> String {
        self.corpus
            .get(kind, id)
            .and_then(|record| string(&record.fields, "label"))
            .unwrap_or_default()
    }

    /// Arguments in display order: verified non-transcription first, then
    /// verified transcriptions, then unverified; each by label, then id.
    fn ordered(&self, arguments: Option<&Vec<String>>) -> Vec<String> {
        let mut arguments: Vec<String> = arguments.cloned().unwrap_or_default();
        arguments.sort_by_cached_key(|id| {
            let rank = match (self.verified(id), self.transcription(id)) {
                (true, false) => 0,
                (true, true) => 1,
                _ => 2,
            };
            (rank, self.label("arguments", id), id.clone())
        });
        arguments.dedup();
        arguments
    }
}

struct Builder<'a> {
    index: &'a Index<'a>,
    options: Options,
    root: String,
    statements: BTreeMap<String, StatementNode>,
    order: Vec<String>,
    arguments: BTreeMap<String, ArgumentNode>,
    argument_order: Vec<String>,
    edges: Vec<Edge>,
    edge_keys: HashSet<(&'static str, String, String)>,
    truncated: Vec<Truncation>,
    case_root: String,
}

impl Builder<'_> {
    fn count(&self) -> usize {
        self.statements.len() + self.arguments.len()
    }

    fn add_statement(&mut self, id: &str, role: &'static str) {
        if self.statements.contains_key(id) {
            return;
        }
        let index = self.index;
        let report = index.report;
        let record = index.statement(id);
        let field = |name: &str| record.and_then(|record| string(record, name));
        let list = |name: &str| {
            record
                .map(|record| strings(record, name))
                .unwrap_or_default()
        };
        let definition_ids = list("definition_ids");
        let disambiguation_ids = list("disambiguation_ids");
        // A definition that is a sense of several disambiguations shows the
        // senses of those the statement links, or all when it links none.
        let senses = definition_ids
            .iter()
            .flat_map(|definition| {
                let senses = index
                    .senses_of
                    .get(definition)
                    .map_or(&[][..], Vec::as_slice);
                let linked: Vec<&SenseUse> = senses
                    .iter()
                    .filter(|sense| disambiguation_ids.contains(&sense.disambiguation_id))
                    .collect();
                if linked.is_empty() {
                    senses.iter().collect()
                } else {
                    linked
                }
            })
            .cloned()
            .collect();
        let contains = |field: &str| {
            report[field]
                .as_array()
                .is_some_and(|ids| ids.iter().any(|value| value == id))
        };
        self.statements.insert(
            id.to_owned(),
            StatementNode {
                id: id.to_owned(),
                label: field("label"),
                legacy_id: field("legacy_id"),
                lean_declaration: field("lean_declaration"),
                role,
                down_depth: None,
                up_depth: None,
                status: report["statement_statuses"]
                    .get(id)
                    .cloned()
                    .unwrap_or(Value::Null),
                depth: report["statement_depths"]
                    .get(id)
                    .cloned()
                    .unwrap_or(Value::Null),
                closed: report["closed_statements"]
                    .get(id)
                    .cloned()
                    .unwrap_or(Value::Null),
                established: contains("established_statements"),
                reaches_tree_root: id == self.root || contains("reaching_root_statements"),
                is_case_root: id == self.case_root,
                definition_ids,
                disambiguation_ids,
                senses,
            },
        );
        self.order.push(id.to_owned());
    }

    fn edge(&mut self, kind: &'static str, from: &str, to: &str, argument: Option<&str>) {
        if !self
            .edge_keys
            .insert((kind, from.to_owned(), to.to_owned()))
        {
            return;
        }
        self.edges.push(Edge {
            kind,
            from: from.to_owned(),
            to: to.to_owned(),
            argument_id: argument.map(str::to_owned),
            relation_id: None,
            result_id: argument.and_then(|argument| {
                self.index
                    .results
                    .get(argument)
                    .and_then(|results| results.first())
                    .map(|result| result.id.clone())
            }),
            extra_premises: Vec::new(),
            verified: argument.is_some_and(|argument| self.index.verified(argument)),
            derivation: None,
            cycle: false,
        });
    }

    fn add_argument(&mut self, id: &str, side: &'static str) {
        let index = self.index;
        let record = index.argument(id).cloned().unwrap_or_default();
        let premises = strings(&record, "premise_statement_ids");
        let conclusion = string(&record, "conclusion_statement_id").unwrap_or_default();
        let steps = strings(&record, "inference_ids")
            .into_iter()
            .map(|step| {
                let inference = index.corpus.get("inferences", &step).map(|r| &r.fields);
                let field = |name: &str| inference.and_then(|r| string(r, name));
                Step {
                    label: field("label"),
                    rule: field("rule"),
                    input_statement_ids: inference
                        .map(|r| strings(r, "input_statement_ids"))
                        .unwrap_or_default(),
                    output_statement_id: field("output_statement_id"),
                    id: step,
                }
            })
            .collect();
        let route = (conclusion == self.root)
            .then(|| {
                index.report["routes"]["routes"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .find(|route| route["argument_id"] == id)
                    .map(|route| {
                        json!({
                            "cost": route["cost"],
                            "cheapest": route["cheapest"],
                            "open_premise_statement_ids": route["open_premise_statement_ids"],
                        })
                    })
            })
            .flatten();
        self.arguments.insert(
            id.to_owned(),
            ArgumentNode {
                id: id.to_owned(),
                label: string(&record, "label"),
                sides: vec![side],
                up_from: Vec::new(),
                conclusion_statement_id: conclusion,
                premise_statement_ids: premises,
                steps,
                results: index.results.get(id).cloned().unwrap_or_default(),
                verified: index.verified(id),
                route,
            },
        );
        self.argument_order.push(id.to_owned());
    }

    fn truncate(&mut self, id: &str, side: &'static str, reason: &'static str, omitted: usize) {
        self.truncated.push(Truncation {
            statement_id: id.to_owned(),
            side,
            reason,
            omitted_arguments: omitted,
        });
    }

    fn down(&mut self) {
        let mut queue = VecDeque::from([(self.root.clone(), 0usize)]);
        while let Some((statement, depth)) = queue.pop_front() {
            let arguments = self.index.ordered(self.index.concluding.get(&statement));
            if arguments.is_empty() {
                continue;
            }
            if depth >= self.options.down {
                self.truncate(&statement, "down", "depth", arguments.len());
                continue;
            }
            for (position, argument) in arguments.iter().enumerate() {
                let premises = self
                    .index
                    .argument(argument)
                    .map(|record| strings(record, "premise_statement_ids"))
                    .unwrap_or_default();
                let fresh: BTreeSet<&String> = premises
                    .iter()
                    .filter(|premise| !self.statements.contains_key(*premise))
                    .collect();
                if self.count() + 1 + fresh.len() > self.options.budget {
                    self.truncate(&statement, "down", "budget", arguments.len() - position);
                    break;
                }
                self.add_argument(argument, "down");
                self.edge("supports", argument, &statement, Some(argument));
                for premise in &premises {
                    if !self.statements.contains_key(premise) {
                        self.add_statement(premise, "support");
                        if let Some(node) = self.statements.get_mut(premise) {
                            node.down_depth = Some(depth + 1);
                        }
                        queue.push_back((premise.clone(), depth + 1));
                    }
                    self.edge("uses", argument, premise, Some(argument));
                }
            }
        }
    }

    fn up(&mut self) {
        let mut queue = VecDeque::from([(self.root.clone(), 0usize)]);
        while let Some((statement, depth)) = queue.pop_front() {
            let arguments = self.index.ordered(self.index.using.get(&statement));
            if arguments.is_empty() {
                continue;
            }
            if depth >= self.options.up {
                self.truncate(&statement, "up", "depth", arguments.len());
                continue;
            }
            for (position, argument) in arguments.iter().enumerate() {
                let Some(record) = self.index.argument(argument) else {
                    continue;
                };
                let premises = strings(record, "premise_statement_ids");
                let conclusion = string(record, "conclusion_statement_id").unwrap_or_default();
                let mut fresh: BTreeSet<&String> = premises
                    .iter()
                    .filter(|premise| !self.statements.contains_key(*premise))
                    .collect();
                if !self.statements.contains_key(&conclusion) {
                    fresh.insert(&conclusion);
                }
                // A conclusion already in view (from the support side or as
                // a co-premise) is still walked upward once.
                let expand = self
                    .statements
                    .get(&conclusion)
                    .is_none_or(|node| node.up_depth.is_none());
                let cost = usize::from(!self.arguments.contains_key(argument)) + fresh.len();
                if self.count() + cost > self.options.budget {
                    self.truncate(&statement, "up", "budget", arguments.len() - position);
                    break;
                }
                if !self.arguments.contains_key(argument) {
                    self.add_argument(argument, "up");
                }
                if let Some(node) = self.arguments.get_mut(argument) {
                    if !node.sides.contains(&"up") {
                        node.sides.push("up");
                    }
                    node.up_from.push(statement.clone());
                }
                if expand {
                    self.add_statement(&conclusion, "dependent");
                    if let Some(node) = self.statements.get_mut(&conclusion) {
                        node.up_depth = Some(depth + 1);
                    }
                    queue.push_back((conclusion.clone(), depth + 1));
                }
                self.edge("supports", argument, &conclusion, Some(argument));
                for premise in &premises {
                    self.add_statement(premise, "co_premise");
                    self.edge("uses", argument, premise, Some(argument));
                }
            }
        }
    }

    /// `strengthens` relations with an end in view; a missing end joins as
    /// an unexpanded `strength_neighbor` while the budget allows.
    fn strength(&mut self) {
        let corpus = self.index.corpus;
        for (id, record) in corpus.records_by_id("relations") {
            let fields = &record.fields;
            if fields.get("predicate").and_then(Value::as_str) != Some("strengthens") {
                continue;
            }
            let (Some(strong), Some(weak)) =
                (string(fields, "subject_id"), string(fields, "object_id"))
            else {
                continue;
            };
            let known = |id: &str| self.statements.contains_key(id);
            if !known(&strong) && !known(&weak) {
                continue;
            }
            let missing = usize::from(!known(&strong)) + usize::from(!known(&weak));
            if missing > 0 {
                if self.count() + missing > self.options.budget {
                    continue;
                }
                self.add_statement(&strong, "strength_neighbor");
                self.add_statement(&weak, "strength_neighbor");
            }
            let result = string(fields, "verification_result_id");
            let verified = result
                .as_deref()
                .is_some_and(|result| corpus.get("results", result).is_some());
            self.edges.push(Edge {
                kind: "strengthens",
                from: strong,
                to: weak,
                argument_id: result
                    .as_deref()
                    .and_then(|result| corpus.get("results", result))
                    .and_then(|result| string(&result.fields, "argument_id")),
                relation_id: Some(id.to_owned()),
                result_id: result,
                extra_premises: Vec::new(),
                verified,
                derivation: None,
                cycle: false,
            });
        }
    }

    /// Marks the edges that return to a node on the current path of a
    /// depth-first walk from the root, down through `supports`/`uses` and up
    /// through their reverse, in display order.
    fn mark_cycles(&mut self) {
        let mut cycles = HashSet::new();
        let walk = Walk::new(&self.edges, self.arguments.values());
        for side in ["down", "up"] {
            walk.visit(
                &self.root,
                side,
                &mut Vec::new(),
                &mut HashSet::new(),
                &mut cycles,
            );
        }
        for position in cycles {
            self.edges[position].cycle = true;
        }
    }

    fn finish(mut self) -> Tree {
        self.mark_cycles();
        let index = self.index;
        let mut definitions: BTreeMap<String, Definition> = BTreeMap::new();
        let mut disambiguations: BTreeMap<String, Disambiguation> = BTreeMap::new();
        for id in &self.order {
            let node = &self.statements[id];
            for definition in &node.definition_ids {
                definitions
                    .entry(definition.clone())
                    .or_insert_with(|| {
                        let record = index
                            .corpus
                            .get("definitions", definition)
                            .map(|r| &r.fields);
                        let field = |name: &str| record.and_then(|r| string(r, name));
                        Definition {
                            id: definition.clone(),
                            label: field("label"),
                            term: field("term"),
                            basis: field("basis"),
                            lean_declaration: field("lean_declaration"),
                            senses: index.senses_of.get(definition).cloned().unwrap_or_default(),
                            formal_status: record.and_then(|r| r.get("formal_status")).cloned(),
                            used_by: Vec::new(),
                        }
                    })
                    .used_by
                    .push(id.clone());
            }
            for disambiguation in &node.disambiguation_ids {
                disambiguations
                    .entry(disambiguation.clone())
                    .or_insert_with(|| {
                        let record = index
                            .corpus
                            .get("disambiguations", disambiguation)
                            .map(|r| &r.fields);
                        let field = |name: &str| record.and_then(|r| string(r, name));
                        Disambiguation {
                            id: disambiguation.clone(),
                            label: field("label"),
                            term_label: field("term_label"),
                            senses: record
                                .and_then(|r| r.get("senses"))
                                .and_then(Value::as_array)
                                .cloned()
                                .unwrap_or_default(),
                            used_by: Vec::new(),
                        }
                    })
                    .used_by
                    .push(id.clone());
            }
        }
        let node_count = self.count();
        let mut statements = self.statements;
        let mut arguments = self.arguments;
        Tree {
            schema_version: 1,
            options: json!({
                "down": self.options.down,
                "up": self.options.up,
                "budget": self.options.budget,
            }),
            edge_kinds: EDGE_KINDS,
            reserved_edge_kinds: RESERVED_KINDS,
            statements: self
                .order
                .iter()
                .filter_map(|id| statements.remove(id))
                .collect(),
            arguments: self
                .argument_order
                .iter()
                .filter_map(|id| arguments.remove(id))
                .collect(),
            edges: self.edges,
            definitions: definitions.into_values().collect(),
            disambiguations: disambiguations.into_values().collect(),
            truncated: self.truncated,
            node_count,
            root: self.root,
            case_root: self.case_root,
        }
    }
}

/// The depth-first walk shared by cycle marking and the text form.
struct Walk<'a> {
    edges: &'a [Edge],
    /// (statement, argument, side): the walk on `side` admitted the argument
    /// from the statement, so the display follows exactly the traversal.
    admitted: HashSet<(String, String, &'static str)>,
    into: HashMap<&'a str, Vec<usize>>,
    out: HashMap<&'a str, Vec<usize>>,
}

impl<'a> Walk<'a> {
    fn new<'n>(edges: &'a [Edge], arguments: impl Iterator<Item = &'n ArgumentNode>) -> Self {
        let mut admitted = HashSet::new();
        for argument in arguments {
            if argument.sides.contains(&"down") {
                admitted.insert((
                    argument.conclusion_statement_id.clone(),
                    argument.id.clone(),
                    "down",
                ));
            }
            for premise in &argument.up_from {
                admitted.insert((premise.clone(), argument.id.clone(), "up"));
            }
        }
        let mut into: HashMap<&str, Vec<usize>> = HashMap::new();
        let mut out: HashMap<&str, Vec<usize>> = HashMap::new();
        for (position, edge) in edges.iter().enumerate() {
            if edge.kind == "supports" || edge.kind == "uses" {
                into.entry(edge.to.as_str()).or_default().push(position);
                out.entry(edge.from.as_str()).or_default().push(position);
            }
        }
        Self {
            edges,
            admitted,
            into,
            out,
        }
    }

    /// The (edge, argument, next statements) steps from `statement` on
    /// `side`: down, the arguments supporting it and their premises; up, the
    /// arguments using it and their conclusions.
    fn steps(&self, statement: &str, side: &'static str) -> Vec<(String, Vec<(usize, String)>)> {
        let edges = self.edges;
        let (first, second) = if side == "down" {
            ("supports", "uses")
        } else {
            ("uses", "supports")
        };
        let admitted = |argument: &str| {
            self.admitted
                .contains(&(statement.to_owned(), argument.to_owned(), side))
        };
        let mut arguments: Vec<&str> = self
            .into
            .get(statement)
            .into_iter()
            .flatten()
            .filter(|&&position| edges[position].kind == first)
            .map(|&position| edges[position].from.as_str())
            .filter(|argument| admitted(argument))
            .collect();
        arguments.dedup();
        arguments
            .into_iter()
            .map(|argument| {
                let next = self
                    .out
                    .get(argument)
                    .into_iter()
                    .flatten()
                    .filter(|&&position| edges[position].kind == second)
                    .map(|&position| (position, edges[position].to.clone()))
                    .collect();
                (argument.to_owned(), next)
            })
            .collect()
    }

    fn visit(
        &self,
        statement: &str,
        side: &'static str,
        path: &mut Vec<String>,
        done: &mut HashSet<String>,
        cycles: &mut HashSet<usize>,
    ) {
        if !done.insert(statement.to_owned()) {
            return;
        }
        path.push(statement.to_owned());
        for (_, next) in self.steps(statement, side) {
            for (position, target) in next {
                if path.contains(&target) {
                    cycles.insert(position);
                } else {
                    self.visit(&target, side, path, done, cycles);
                }
            }
        }
        path.pop();
    }
}

/// Unknown statement.
#[derive(Debug)]
pub struct UnknownStatement(pub String);

/// The tree rooted at `root` from a frontier `report` computed with `root`
/// as its frontier root.
pub fn tree(
    corpus: &Corpus,
    report: &Value,
    root: &str,
    case_root: &str,
    options: Options,
) -> Result<Tree, UnknownStatement> {
    if corpus.get("statements", root).is_none() {
        return Err(UnknownStatement(root.to_owned()));
    }
    let index = Index::new(corpus, report);
    let mut builder = Builder {
        index: &index,
        options,
        root: root.to_owned(),
        statements: BTreeMap::new(),
        order: Vec::new(),
        arguments: BTreeMap::new(),
        argument_order: Vec::new(),
        edges: Vec::new(),
        edge_keys: HashSet::new(),
        truncated: Vec::new(),
        case_root: case_root.to_owned(),
    };
    builder.add_statement(root, "root");
    if let Some(node) = builder.statements.get_mut(root) {
        node.down_depth = Some(0);
        node.up_depth = Some(0);
    }
    builder.down();
    builder.up();
    builder.strength();
    Ok(builder.finish())
}

fn clip(text: &str, width: usize) -> String {
    let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
    match text.char_indices().nth(width) {
        Some((cut, _)) => format!("{}…", &text[..cut]),
        None => text,
    }
}

/// A statement's frontier status: `closed: <reason>` or `open: <depth>`,
/// with the frontier status when it adds something.
fn status(node: &StatementNode) -> String {
    let mut parts = Vec::new();
    match node.closed.as_str() {
        Some(reason) => parts.push(format!("closed: {reason}")),
        None => parts.push(format!("open: {}", node.depth.as_str().unwrap_or("?"))),
    }
    if let Some(status) = node.status.as_str()
        && !["open", "proved"].contains(&status)
    {
        parts.push(status.to_owned());
    }
    parts.push(
        if node.established {
            "established"
        } else {
            "unestablished"
        }
        .into(),
    );
    if node.is_case_root {
        parts.push("case root".into());
    }
    format!("[{}]", parts.join("; "))
}

fn argument_tag(node: &ArgumentNode) -> String {
    let mut tag = match node.results.first() {
        None => "no result".to_owned(),
        Some(result) => {
            let theorem = result.theorem.as_deref().unwrap_or("?");
            match &result.transcription {
                Some(kind) => format!("transcription ({kind}): {theorem}"),
                None => format!("verified: {theorem}"),
            }
        }
    };
    if let Some(route) = &node.route {
        tag.push_str(&format!("; route cost {}", route["cost"]));
        if route["cheapest"] == true {
            tag.push_str(", cheapest");
        }
    }
    format!("[{tag}]")
}

struct Printer<'a> {
    tree: &'a Tree,
    walk: Walk<'a>,
    statements: HashMap<&'a str, &'a StatementNode>,
    arguments: HashMap<&'a str, &'a ArgumentNode>,
    truncated: HashMap<(&'a str, &'a str), &'a Truncation>,
    printed: HashSet<String>,
    lines: Vec<String>,
}

impl Printer<'_> {
    fn statement(&self, id: &str) -> String {
        match self.statements.get(id) {
            Some(node) => format!("{id} {}", status(node)),
            None => id.to_owned(),
        }
    }

    fn truncation(&mut self, statement: &str, side: &str, indent: &str) {
        if let Some(marker) = self.truncated.get(&(statement, side)) {
            self.lines.push(format!(
                "{indent}… truncated ({}): {} more argument(s) not shown",
                marker.reason, marker.omitted_arguments
            ));
        }
    }

    fn steps(&mut self, argument: &str, indent: &str) {
        let Some(node) = self.arguments.get(argument) else {
            return;
        };
        let rules: Vec<String> = node
            .steps
            .iter()
            .map(|step| clip(step.rule.as_deref().unwrap_or("?"), 70))
            .collect();
        if !rules.is_empty() {
            self.lines
                .push(format!("{indent}steps: {}", rules.join(" | ")));
        }
    }

    fn down(&mut self, statement: &str, indent: &str, path: &mut Vec<String>) {
        path.push(statement.to_owned());
        let steps = self.walk.steps(statement, "down");
        let alternatives = steps.len();
        for (argument, next) in steps {
            let tag = self
                .arguments
                .get(argument.as_str())
                .map(|node| argument_tag(node))
                .unwrap_or_default();
            let marker = if alternatives > 1 { "OR" } else { "BY" };
            self.lines
                .push(format!("{indent}{marker} {argument} {tag}"));
            let inner = format!("{indent}   ");
            self.steps(&argument, &inner);
            let bundle = next.len();
            for (position, premise) in next {
                let marker = if bundle > 1 { "AND " } else { "" };
                let line = format!("{inner}{marker}{}", self.statement(&premise));
                if self.walk.edges[position].cycle || path.contains(&premise) {
                    self.lines
                        .push(format!("{line} (cycle: on the path above)"));
                } else if !self.printed.insert(premise.clone()) {
                    self.lines.push(format!("{line} (shown above)"));
                } else {
                    self.lines.push(line);
                    let deeper = format!("{inner}    ");
                    self.down(&premise, &deeper, path);
                }
            }
        }
        self.truncation(statement, "down", indent);
        path.pop();
    }

    fn up(&mut self, statement: &str, indent: &str, path: &mut Vec<String>) {
        path.push(statement.to_owned());
        for (argument, next) in self.walk.steps(statement, "up") {
            let Some(node) = self.arguments.get(argument.as_str()).copied() else {
                continue;
            };
            self.lines
                .push(format!("{indent}USED BY {argument} {}", argument_tag(node)));
            let inner = format!("{indent}   ");
            let others: Vec<String> = node
                .premise_statement_ids
                .iter()
                .filter(|premise| premise.as_str() != statement)
                .map(|premise| self.statement(premise))
                .collect();
            for other in others {
                self.lines.push(format!("{inner}WITH {other}"));
            }
            for (position, conclusion) in next {
                let line = format!("{inner}=> {}", self.statement(&conclusion));
                if self.walk.edges[position].cycle || path.contains(&conclusion) {
                    self.lines
                        .push(format!("{line} (cycle: on the path above)"));
                } else if !self.printed.insert(conclusion.clone()) {
                    self.lines.push(format!("{line} (shown above)"));
                } else {
                    self.lines.push(line);
                    let deeper = format!("{inner}   ");
                    self.up(&conclusion, &deeper, path);
                }
            }
        }
        self.truncation(statement, "up", indent);
        path.pop();
    }
}

/// The indented text form: support tree, dependents, strength orders and
/// terms. Ids are raw uuids; the CLI humanizes them.
pub fn format_tree(tree: &Tree) -> String {
    let mut printer = Printer {
        tree,
        walk: Walk::new(&tree.edges, tree.arguments.iter()),
        statements: tree.statements.iter().map(|n| (n.id.as_str(), n)).collect(),
        arguments: tree.arguments.iter().map(|n| (n.id.as_str(), n)).collect(),
        truncated: tree
            .truncated
            .iter()
            .map(|t| ((t.statement_id.as_str(), t.side), t))
            .collect(),
        printed: HashSet::new(),
        lines: Vec::new(),
    };
    let root = tree.root.clone();
    printer
        .lines
        .push(format!("Tree at {}", printer.statement(&root)));
    if let Some(node) = printer.statements.get(root.as_str())
        && let Some(lean) = &node.lean_declaration
    {
        printer.lines.push(format!("  lean: {lean}"));
    }
    printer.lines.push(format!(
        "Support (down {}; OR: alternative arguments, AND: premises of one argument; statuses with this statement as frontier root):",
        tree.options["down"]
    ));
    printer.printed.insert(root.clone());
    let before = printer.lines.len();
    printer.down(&root, "  ", &mut Vec::new());
    if printer.lines.len() == before {
        printer.lines.push("  (no argument concludes it)".into());
    }
    printer.printed = HashSet::from([root.clone()]);
    printer.lines.push(format!(
        "Dependents (up {}; arguments using it as a premise, WITH: their other premises):",
        tree.options["up"]
    ));
    let before = printer.lines.len();
    printer.up(&root, "  ", &mut Vec::new());
    if printer.lines.len() == before {
        printer.lines.push("  (no argument uses it)".into());
    }
    let strength: Vec<&Edge> = tree
        .edges
        .iter()
        .filter(|edge| edge.kind == "strengthens")
        .collect();
    if !strength.is_empty() {
        printer
            .lines
            .push("Strength orders (strong => weak):".into());
        for edge in strength {
            printer.lines.push(format!(
                "  {} => {} (relation {}{})",
                edge.from,
                edge.to,
                edge.relation_id.as_deref().unwrap_or("?"),
                if edge.verified {
                    ""
                } else {
                    "; backing result missing"
                }
            ));
        }
    }
    printer.lines.push(format!(
        "Terms ({} definitions, {} disambiguations across {} statements):",
        tree.definitions.len(),
        tree.disambiguations.len(),
        tree.statements.len()
    ));
    for definition in &tree.definitions {
        let mut line = format!("  {}", definition.id);
        let senses: Vec<&str> = definition
            .senses
            .iter()
            .filter_map(|sense| sense.sense_label.as_deref())
            .collect();
        if !senses.is_empty() {
            line.push_str(&format!(" sense {}", senses.join(", ")));
        }
        if let Some(lean) = &definition.lean_declaration {
            line.push_str(&format!("; lean {lean}"));
        }
        if let Some(status) = &definition.formal_status {
            line.push_str(&format!(
                "; formal status {}",
                status
                    .as_str()
                    .map_or_else(|| status.to_string(), str::to_owned)
            ));
        }
        line.push_str(&format!("; used by {}", definition.used_by.len()));
        printer.lines.push(line);
    }
    let shown = printer.tree.node_count;
    printer.lines.push(format!(
        "{shown} nodes (budget {}); {} truncation marker(s)",
        tree.options["budget"],
        tree.truncated.len()
    ));
    printer.lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{fs, path::PathBuf};

    struct Dir(PathBuf);

    impl Drop for Dir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn write(root: &std::path::Path, relative: &str, value: Value) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, value.to_string()).unwrap();
    }

    /// X <- ARG-1 (A, P) | ARG-2 (B, P): OR alternatives sharing P.
    /// A <- ARG-3 (C), C <- ARG-4 (A): a cycle. B <- ARG-5 (D1),
    /// D1 <- ARG-6 (D2): a chain to truncate. P <- ARG-REG (S) with
    /// S strengthens P. U <- ARG-U (X, Q): a dependent with a co-premise.
    fn fixture() -> Dir {
        use std::sync::atomic::{AtomicU32, Ordering};
        static NEXT: AtomicU32 = AtomicU32::new(0);
        let root = std::env::temp_dir().join(format!(
            "truth-tree-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        for id in ["X", "A", "B", "C", "P", "S", "D1", "D2", "U", "Q"] {
            let mut statement = json!({"id": id, "label": format!("statement {id}"),
                "paraphrase": format!("{id} holds.")});
            if id == "X" {
                statement["definition_ids"] = json!(["DEF-1"]);
                statement["disambiguation_ids"] = json!(["DISAMB-1"]);
            }
            write(&root, &format!("corpus/statements/{id}.json"), statement);
        }
        let arguments: &[(&str, &[&str], &str, bool)] = &[
            ("ARG-1", &["A", "P"], "X", true),
            ("ARG-2", &["B", "P"], "X", false),
            ("ARG-3", &["C"], "A", true),
            ("ARG-4", &["A"], "C", true),
            ("ARG-5", &["D1"], "B", true),
            ("ARG-6", &["D2"], "D1", true),
            ("ARG-REG", &["S"], "P", true),
            ("ARG-U", &["X", "Q"], "U", true),
        ];
        for (id, premises, conclusion, verified) in arguments {
            write(
                &root,
                &format!("corpus/inferences/I-{id}.json"),
                json!({"id": format!("I-{id}"), "input_statement_ids": premises,
                    "output_statement_id": conclusion, "rule": "modus ponens", "meaning": "m",
                    "assumption_statement_ids": [], "discharged_statement_ids": []}),
            );
            write(
                &root,
                &format!("corpus/arguments/{id}.json"),
                json!({"id": id, "label": format!("argument {id}"),
                    "premise_statement_ids": premises, "inference_ids": [format!("I-{id}")],
                    "conclusion_statement_id": conclusion, "meaning": "m"}),
            );
            if *verified {
                write(
                    &root,
                    &format!("corpus/results/RES-{id}.json"),
                    json!({"id": format!("RES-{id}"), "argument_id": id,
                        "challenge_module": "M.Challenge", "solution_module": "M.Solution",
                        "theorem": format!("M.{id}"), "comparator_config": "c",
                        "status": "solution-present"}),
                );
            }
        }
        write(
            &root,
            "corpus/relations/REL-S.json",
            json!({"id": "REL-S", "subject_kind": "statement", "subject_id": "S",
                "predicate": "strengthens", "object_kind": "statement", "object_id": "P",
                "verification_result_id": "RES-ARG-REG", "note": "S entails P"}),
        );
        write(
            &root,
            "corpus/definitions/DEF-1.json",
            json!({"id": "DEF-1", "label": "X-ness", "term": "x", "definition": "d",
                "basis": "stipulative", "note": "n", "lean_declaration": "M.XNess"}),
        );
        write(
            &root,
            "corpus/disambiguations/DISAMB-1.json",
            json!({"id": "DISAMB-1", "label": "X senses", "term": "x", "resolution": "r",
                "term_label": "XNESS", "sense_definition_ids": ["DEF-1"],
                "senses": [{"id": "SENSE-1", "label": "XNESS_1", "definition_id": "DEF-1",
                    "lean_declaration": "M.XNess"}]}),
        );
        Dir(root)
    }

    fn build(dir: &Dir, root: &str, options: Options) -> Result<Tree, UnknownStatement> {
        let corpus = Corpus::load(&dir.0).unwrap();
        let report = crate::frontier::current_frontier(&dir.0, &corpus, root, false, false);
        tree(&corpus, &report, root, "U", options)
    }

    fn edges<'a>(tree: &'a Tree, kind: &str, to: &str) -> Vec<&'a Edge> {
        tree.edges
            .iter()
            .filter(|edge| edge.kind == kind && edge.to == to)
            .collect()
    }

    #[test]
    fn alternatives_shared_premises_cycles_and_strength() {
        let dir = fixture();
        let view = build(&dir, "X", Options::default()).unwrap();
        // OR: two arguments conclude X, verified first.
        let supports: Vec<&str> = edges(&view, "supports", "X")
            .iter()
            .map(|edge| edge.from.as_str())
            .collect();
        assert_eq!(supports, ["ARG-1", "ARG-2"]);
        assert!(edges(&view, "supports", "X")[0].verified);
        assert!(!edges(&view, "supports", "X")[1].verified);
        // Shared P: one node, two uses edges.
        assert_eq!(view.statements.iter().filter(|n| n.id == "P").count(), 1);
        assert_eq!(edges(&view, "uses", "P").len(), 2);
        // The cycle A <-> C is cut at the edge back to A.
        let back = edges(&view, "uses", "A");
        let back: Vec<_> = back.iter().filter(|edge| edge.from == "ARG-4").collect();
        assert_eq!(back.len(), 1);
        assert!(back[0].cycle);
        assert!(view.edges.iter().filter(|edge| edge.cycle).count() == 1);
        // The strength order S => P, backed by its result.
        let strength = edges(&view, "strengthens", "P");
        assert_eq!(strength.len(), 1);
        assert_eq!(strength[0].from, "S");
        assert_eq!(strength[0].relation_id.as_deref(), Some("REL-S"));
        assert!(strength[0].verified);
        // Up: ARG-U uses X; its co-premise Q and conclusion U join the view.
        let up = edges(&view, "uses", "X");
        assert_eq!(up.len(), 1);
        assert_eq!(up[0].from, "ARG-U");
        let node = |id: &str| view.statements.iter().find(|n| n.id == id).unwrap();
        assert_eq!(node("Q").role, "co_premise");
        assert_eq!(node("U").role, "dependent");
        assert!(node("U").is_case_root);
        // Every edge has a kind and an (empty) extra-premise list.
        assert!(view.edges.iter().all(|edge| EDGE_KINDS.contains(&edge.kind)
            && edge.extra_premises.is_empty()
            && edge.derivation.is_none()));
        // Terms: X's definition with its sense label.
        assert_eq!(node("X").senses[0].sense_label.as_deref(), Some("XNESS_1"));
        assert_eq!(view.definitions[0].id, "DEF-1");
        assert_eq!(view.definitions[0].used_by, ["X"]);
        assert!(view.definitions[0].formal_status.is_none());
        assert_eq!(view.disambiguations[0].used_by, ["X"]);
        // Statuses come from the frontier with X as root.
        assert_eq!(node("D2").depth, "bare");
        assert!(node("D1").closed == "proved");
        assert!(node("D1").reaches_tree_root);
        let text = format_tree(&view);
        for needle in [
            "OR ARG-1",
            "OR ARG-2",
            "AND P",
            "(shown above)",
            "(cycle",
            "USED BY ARG-U",
            "WITH Q",
            "=> U",
            "S => P",
            "sense XNESS_1",
        ] {
            assert!(text.contains(needle), "{needle} missing from\n{text}");
        }
        // Deterministic.
        let again = build(&dir, "X", Options::default()).unwrap();
        assert_eq!(
            serde_json::to_value(&view).unwrap(),
            serde_json::to_value(&again).unwrap()
        );
        assert_eq!(format_tree(&again), text);
    }

    #[test]
    fn depth_and_budget_truncation_are_marked() {
        let dir = fixture();
        let view = build(
            &dir,
            "X",
            Options {
                down: 2,
                up: 0,
                budget: 100,
            },
        )
        .unwrap();
        let marker = |id: &str, side: &str| {
            view.truncated
                .iter()
                .find(|t| t.statement_id == id && t.side == side)
                .map(|t| (t.reason, t.omitted_arguments))
        };
        // D1 sits at depth 2: its argument is cut by depth.
        assert_eq!(marker("D1", "down"), Some(("depth", 1)));
        assert!(view.statements.iter().all(|n| n.id != "D2"));
        assert_eq!(marker("X", "up"), Some(("depth", 1)));
        assert!(format_tree(&view).contains("… truncated (depth): 1 more argument(s) not shown"));
        // A budget of 4 nodes: X, ARG-1, A, P; ARG-2 does not fit.
        let view = build(
            &dir,
            "X",
            Options {
                down: 3,
                up: 3,
                budget: 4,
            },
        )
        .unwrap();
        assert_eq!(view.node_count, 4);
        assert!(view.truncated.iter().any(|t| t.statement_id == "X"
            && t.side == "down"
            && t.reason == "budget"
            && t.omitted_arguments == 1));
        assert!(view.node_count <= 4);
    }

    #[test]
    fn the_text_follows_each_side_s_own_walk() {
        let dir = fixture();
        // At A, the support walk admits ARG-3 and ARG-4 (the cycle); with
        // up 0 the dependents section shows none of them.
        let view = build(
            &dir,
            "A",
            Options {
                down: 3,
                up: 0,
                budget: 100,
            },
        )
        .unwrap();
        let text = format_tree(&view);
        let dependents = text.split("Dependents").nth(1).unwrap();
        assert!(!dependents.contains("USED BY"), "{text}");
        assert!(text.contains("BY ARG-3"));
        // With down 0 the support section shows nothing the upward walk added.
        let view = build(
            &dir,
            "A",
            Options {
                down: 0,
                up: 3,
                budget: 100,
            },
        )
        .unwrap();
        let text = format_tree(&view);
        let support = text.split("Dependents").next().unwrap();
        assert!(!support.contains("BY ARG"), "{text}");
        assert!(support.contains("… truncated (depth): 1 more argument(s) not shown"));
        assert!(text.contains("USED BY ARG-4"));
        assert!(text.contains("USED BY ARG-1"));
    }

    #[test]
    fn re_rooting_turns_the_tree_around() {
        let dir = fixture();
        let view = build(&dir, "P", Options::default()).unwrap();
        // Down: P from S; up: P is used by ARG-1 and ARG-2 toward X, then U.
        assert_eq!(edges(&view, "supports", "P")[0].from, "ARG-REG");
        let up: Vec<&str> = edges(&view, "uses", "P")
            .iter()
            .map(|e| e.from.as_str())
            .collect();
        assert_eq!(up, ["ARG-1", "ARG-2"]);
        assert!(
            view.statements
                .iter()
                .any(|n| n.id == "U" && n.up_depth == Some(2))
        );
    }

    #[test]
    fn unknown_statement_is_an_error() {
        let dir = fixture();
        assert!(
            matches!(build(&dir, "NOPE", Options::default()), Err(UnknownStatement(id)) if id == "NOPE")
        );
    }
}
