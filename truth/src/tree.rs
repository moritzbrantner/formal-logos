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

/// Edge kinds this version emits. `supports`, `uses` and `strengthens` are
/// record edges; `contrapositive` and `inverse_conditional` are derived
/// inversions (#1674 phase 2), computed in the view and never corpus records
/// unless materialized (`--materialize-edge`):
///
/// - `contrapositive`, from a verified non-transcription argument
///   P1, …, Pn ⊢ C: ¬C with the other premises gives ¬Pi (always valid;
///   [`CONTRAPOSITIVE_LEMMA`]). The edge runs from C to Pi and negates both.
/// - `inverse_conditional`, at the tree root A used by one of several
///   alternative arguments for C: C, with every other alternative's premise
///   bundle failing, gives A, but only under the exhaustiveness premise
///   "C holds only through these arguments", listed under the edge's
///   `inversion.requires` ([`INVERSE_LEMMA`]).
///
/// The unconditioned inverse C ⊢ A is invalid (A = B = false, C = true;
/// `TruthCore.Logic.Inversion.unconditioned_inverse_invalid`) and is never
/// emitted.
pub const EDGE_KINDS: &[&str] = &[
    "supports",
    "uses",
    "strengthens",
    "contrapositive",
    "inverse_conditional",
];
/// Edge kinds reserved for later phases (none now).
pub const RESERVED_KINDS: &[&str] = &[];
/// The generic lemma a `contrapositive` edge instantiates at its argument's
/// result theorem.
pub const CONTRAPOSITIVE_LEMMA: &str = "TruthCore.Logic.Inversion.contrapositive";
/// The generic lemma an `inverse_conditional` edge instantiates.
pub const INVERSE_LEMMA: &str = "TruthCore.Logic.Inversion.inverse_premise_of_exhaustive_at";
/// Where materialized inversions live (`--materialize-edge`).
pub const MATERIALIZED_RESULTS: &str = "TruthCore.Results.Logic.Inversions";
pub const MATERIALIZED_VOCABULARY: &str = "TruthCore.Logic.Inversions";

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
    /// `strengthens`: the registration's backing result exists). A derived
    /// edge is verified only when its materialized result exists.
    pub verified: bool,
    /// How a derived edge was obtained; `null` for record edges.
    pub derivation: Option<String>,
    /// The edge returns to a node on the current path of the walk from the
    /// root (the walk does not continue through it).
    pub cycle: bool,
    /// The inversion a derived edge states; `null` for record edges.
    pub inversion: Option<Inversion>,
}

/// One premise a derived edge needs besides its source statement.
#[derive(Debug, Clone, Serialize)]
pub struct Requirement {
    /// `negated_conclusion` (¬C of a contrapositive), `co_premise` (another
    /// premise of the argument), `negated_alternative` (the premise bundle of
    /// another argument for C fails) or `exhaustiveness` (C holds only
    /// through the listed arguments).
    pub role: &'static str,
    /// The corpus statement stating it, `null` when none is registered.
    pub statement_id: Option<String>,
    /// For `negated_alternative`: the alternative argument.
    pub argument_id: Option<String>,
    /// For `negated_alternative`: its premise bundle; for `exhaustiveness`:
    /// the alternative arguments' conclusions are all C, so this lists the
    /// arguments it ranges over.
    pub argument_ids: Vec<String>,
    pub premise_statement_ids: Vec<String>,
    pub registered: bool,
    /// Frontier closure reason of the registered statement, `null` when open
    /// or unregistered.
    pub closed: Value,
    pub established: bool,
    pub description: String,
}

/// What a derived edge states and how it would be checked.
#[derive(Debug, Clone, Serialize)]
pub struct Inversion {
    /// Stable edge key, accepted by `--materialize-edge`:
    /// `contrapositive:<argument>:<premise>` or
    /// `inverse_conditional:<argument>:<premise>`.
    pub key: String,
    /// The generic Lean lemma it instantiates.
    pub lemma: &'static str,
    /// The result theorem it is composed with (`contrapositive` only).
    pub source_theorem: Option<String>,
    /// The edge concludes ¬`to` from ¬`from` (contrapositive) rather than
    /// `to` from `from` (inverse).
    pub negated: bool,
    /// Every premise besides `from`, registered or not.
    pub requires: Vec<Requirement>,
    /// The theorem a materialization of this edge defines.
    pub materialized_theorem: Option<String>,
    /// The materialized result, when it exists.
    pub materialized_result_id: Option<String>,
    pub materialized_argument_id: Option<String>,
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
    pub solution_module: Option<String>,
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

/// `foo_bar` -> `FooBar`, keeping ASCII letters and digits only.
fn pascal(text: &str) -> String {
    text.split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|part| !part.is_empty())
        .map(|part| {
            let mut chars = part.chars();
            chars.next().map_or_else(String::new, |first| {
                first.to_ascii_uppercase().to_string() + chars.as_str()
            })
        })
        .collect()
}

/// The module name of a materialized contrapositive of `theorem` (in the
/// Solution module `solution_module`) at its argument's premise `position`
/// (1-based): under [`MATERIALIZED_RESULTS`] and [`MATERIALIZED_VOCABULARY`].
pub fn materialized_name(solution_module: &str, theorem: &str, position: usize) -> String {
    let segment = solution_module
        .strip_suffix(".Solution")
        .unwrap_or(solution_module)
        .rsplit('.')
        .next()
        .unwrap_or_default();
    let mut name = pascal(segment);
    let last = pascal(theorem.rsplit('.').next().unwrap_or(theorem));
    if last != name {
        name.push_str(&last);
    }
    if name.is_empty() || name.starts_with(|c: char| c.is_ascii_digit()) {
        name.insert(0, 'R');
    }
    format!("{name}Contra{position}")
}

struct Index<'a> {
    corpus: &'a Corpus,
    report: &'a Value,
    concluding: HashMap<String, Vec<String>>,
    using: HashMap<String, Vec<String>>,
    results: HashMap<String, Vec<ResultRef>>,
    /// Result theorem -> (result id, argument id).
    by_theorem: HashMap<String, (String, String)>,
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
        let mut by_theorem = HashMap::new();
        for (id, record) in corpus.records_by_id("results") {
            let Some(argument) = string(&record.fields, "argument_id") else {
                continue;
            };
            if let Some(theorem) = string(&record.fields, "theorem") {
                by_theorem
                    .entry(theorem)
                    .or_insert_with(|| (id.to_owned(), argument.clone()));
            }
            let transcription = report["transcription_results"][id]["kind"]
                .as_str()
                .map(str::to_owned)
                .or_else(|| string(&record.fields, "transcription"));
            results.entry(argument).or_default().push(ResultRef {
                id: id.to_owned(),
                theorem: string(&record.fields, "theorem"),
                solution_module: string(&record.fields, "solution_module"),
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
            by_theorem,
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
            inversion: None,
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
        // The statements the walks reached: a neighbor added here does not
        // admit further relations, whatever the relation order.
        let seeds: HashSet<String> = self.statements.keys().cloned().collect();
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
            if !seeds.contains(&strong) && !seeds.contains(&weak) {
                continue;
            }
            let known = |id: &str| self.statements.contains_key(id);
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
                inversion: None,
            });
        }
    }

    /// The derived inversion edges (#1674 phase 2): a `contrapositive` edge
    /// for every premise of every verified non-transcription argument in
    /// view, and an `inverse_conditional` edge for every argument in view
    /// that uses the tree root and has an alternative argument for its
    /// conclusion. They add no nodes.
    fn inversions(&mut self) {
        let index = self.index;
        let report = index.report;
        let registered = |role: &'static str, statement: &str, description: String| Requirement {
            role,
            statement_id: Some(statement.to_owned()),
            argument_id: None,
            argument_ids: Vec::new(),
            premise_statement_ids: Vec::new(),
            registered: true,
            closed: report["closed_statements"]
                .get(statement)
                .cloned()
                .unwrap_or(Value::Null),
            established: report["established_statements"]
                .as_array()
                .is_some_and(|ids| ids.iter().any(|value| value == statement)),
            description,
        };
        let mut derived = Vec::new();
        for argument in &self.argument_order {
            let node = &self.arguments[argument];
            let Some(result) = node
                .results
                .iter()
                .find(|result| result.transcription.is_none())
            else {
                continue;
            };
            let conclusion = &node.conclusion_statement_id;
            let mut premises: Vec<&String> = Vec::new();
            for premise in &node.premise_statement_ids {
                if !premises.contains(&premise) {
                    premises.push(premise);
                }
            }
            for (position, premise) in premises.iter().enumerate() {
                let others: Vec<String> = premises
                    .iter()
                    .filter(|other| *other != premise)
                    .map(|other| (*other).clone())
                    .collect();
                let materialized_theorem = result
                    .solution_module
                    .as_deref()
                    .zip(result.theorem.as_deref())
                    .map(|(module, theorem)| {
                        format!(
                            "{MATERIALIZED_RESULTS}.{}.contrapositive",
                            materialized_name(module, theorem, position + 1)
                        )
                    });
                let materialized = materialized_theorem
                    .as_ref()
                    .and_then(|theorem| index.by_theorem.get(theorem));
                // The materialized argument's premise outside the other
                // premises is its registered ¬C.
                let negated_conclusion = materialized.and_then(|(_, argument)| {
                    index.argument(argument).and_then(|record| {
                        strings(record, "premise_statement_ids")
                            .into_iter()
                            .find(|premise| !others.contains(premise))
                    })
                });
                let description = format!("the negation of {conclusion}");
                let mut requires = vec![match &negated_conclusion {
                    Some(statement) => registered("negated_conclusion", statement, description),
                    None => Requirement {
                        role: "negated_conclusion",
                        statement_id: None,
                        argument_id: None,
                        argument_ids: Vec::new(),
                        premise_statement_ids: Vec::new(),
                        registered: false,
                        closed: Value::Null,
                        established: false,
                        description,
                    },
                }];
                requires.extend(others.iter().map(|other| {
                    registered(
                        "co_premise",
                        other,
                        format!("another premise of {argument}"),
                    )
                }));
                derived.push(Edge {
                    kind: "contrapositive",
                    from: conclusion.clone(),
                    to: (*premise).clone(),
                    argument_id: Some(argument.clone()),
                    relation_id: None,
                    result_id: Some(result.id.clone()),
                    extra_premises: others,
                    verified: materialized.is_some(),
                    derivation: Some(format!(
                        "not {conclusion}, with the other premises, gives not {premise}: {} composed with {CONTRAPOSITIVE_LEMMA}",
                        result.theorem.as_deref().unwrap_or("?")
                    )),
                    cycle: false,
                    inversion: Some(Inversion {
                        key: format!("contrapositive:{argument}:{premise}"),
                        lemma: CONTRAPOSITIVE_LEMMA,
                        source_theorem: result.theorem.clone(),
                        negated: true,
                        requires,
                        materialized_theorem,
                        materialized_result_id: materialized.map(|(result, _)| result.clone()),
                        materialized_argument_id: materialized
                            .map(|(_, argument)| argument.clone()),
                    }),
                });
            }
        }
        let root = self.root.clone();
        for argument in &self.argument_order {
            let node = &self.arguments[argument];
            if !node.up_from.contains(&root) {
                continue;
            }
            let conclusion = &node.conclusion_statement_id;
            let alternatives = index.ordered(index.concluding.get(conclusion));
            if alternatives.len() < 2 {
                continue;
            }
            let mut requires = vec![Requirement {
                role: "exhaustiveness",
                statement_id: None,
                argument_id: None,
                argument_ids: alternatives.clone(),
                premise_statement_ids: Vec::new(),
                registered: false,
                closed: Value::Null,
                established: false,
                description: format!(
                    "{conclusion} holds only through the {} recorded arguments for it: if it holds, all premises of one of them hold (unregistered open premise; no corpus record states this coverage)",
                    alternatives.len()
                ),
            }];
            for alternative in alternatives.iter().filter(|other| *other != argument) {
                let premises = index
                    .argument(alternative)
                    .map(|record| strings(record, "premise_statement_ids"))
                    .unwrap_or_default();
                requires.push(Requirement {
                    role: "negated_alternative",
                    statement_id: None,
                    argument_id: Some(alternative.clone()),
                    argument_ids: Vec::new(),
                    description: format!("not all premises of {alternative} hold"),
                    premise_statement_ids: premises,
                    registered: false,
                    closed: Value::Null,
                    established: false,
                });
            }
            derived.push(Edge {
                kind: "inverse_conditional",
                from: conclusion.clone(),
                to: root.clone(),
                argument_id: Some(argument.clone()),
                relation_id: None,
                result_id: None,
                extra_premises: Vec::new(),
                verified: false,
                derivation: Some(format!(
                    "{conclusion}, with every other alternative failing, gives {root} only under the exhaustiveness premise: {INVERSE_LEMMA}"
                )),
                cycle: false,
                inversion: Some(Inversion {
                    key: format!("inverse_conditional:{argument}:{root}"),
                    lemma: INVERSE_LEMMA,
                    source_theorem: None,
                    negated: false,
                    requires,
                    materialized_theorem: None,
                    materialized_result_id: None,
                    materialized_argument_id: None,
                }),
            });
        }
        self.edges.extend(derived);
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
            schema_version: 2,
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
    builder.inversions();
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

impl Printer<'_> {
    /// Derived inversions: the contrapositives toward the root and every
    /// conditional inverse in full, the other contrapositives as a count.
    fn inversions(&mut self) {
        let tree = self.tree;
        let derived: Vec<&Edge> = tree
            .edges
            .iter()
            .filter(|edge| edge.inversion.is_some())
            .collect();
        let count = |kind: &str| derived.iter().filter(|edge| edge.kind == kind).count();
        self.lines.push(format!(
            "Inversions (derived in this view, not corpus arguments; {} contrapositive, {} inverse_conditional; the unconditioned inverse C => A is invalid and never derived):",
            count("contrapositive"),
            count("inverse_conditional")
        ));
        let mut shown = 0;
        for edge in &derived {
            let Some(inversion) = &edge.inversion else {
                continue;
            };
            let argument = edge.argument_id.as_deref().unwrap_or("?");
            if edge.kind == "contrapositive" {
                if edge.to != tree.root {
                    continue;
                }
                let others: Vec<String> = edge
                    .extra_premises
                    .iter()
                    .map(|other| format!(" WITH {other}"))
                    .collect();
                let checked = match &inversion.materialized_result_id {
                    Some(result) => format!("materialized: result {result}"),
                    None => "not materialized".to_owned(),
                };
                self.lines.push(format!(
                    "  NOT {}{} => NOT {} (contrapositive of {argument}; {} with {}; {checked})",
                    edge.from,
                    others.join(""),
                    edge.to,
                    inversion.source_theorem.as_deref().unwrap_or("?"),
                    inversion.lemma
                ));
            } else {
                let failing: Vec<String> = inversion
                    .requires
                    .iter()
                    .filter_map(|requirement| requirement.argument_id.as_deref())
                    .map(|alternative| format!(" WITH NOT ALL OF {alternative}"))
                    .collect();
                let alternatives = inversion
                    .requires
                    .iter()
                    .find(|requirement| requirement.role == "exhaustiveness")
                    .map_or(0, |requirement| requirement.argument_ids.len());
                self.lines.push(format!(
                    "  {}{} => {} GIVEN the unregistered open premise that {} holds only through its {alternatives} recorded arguments (inverse via {argument}; {})",
                    edge.from,
                    failing.join(""),
                    edge.to,
                    edge.from,
                    inversion.lemma
                ));
            }
            self.lines.push(format!("     key {}", inversion.key));
            shown += 1;
        }
        let hidden = derived.len() - shown;
        if hidden > 0 {
            self.lines.push(format!(
                "  … {hidden} further contrapositive edge(s) toward other premises (listed in --json)"
            ));
        }
        if derived.is_empty() {
            self.lines
                .push("  (no verified non-transcription argument in view)".into());
        }
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
    printer.inversions();
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
        // A chain beyond the view: N1 strengthens Q (a co-premise) and N2
        // strengthens N1; only the first touches a reached statement.
        for (id, strong, weak) in [("REL-N1", "N1", "Q"), ("REL-N2", "N2", "N1")] {
            write(
                &root,
                &format!("corpus/statements/{strong}.json"),
                json!({"id": strong, "paraphrase": "p"}),
            );
            write(
                &root,
                &format!("corpus/relations/{id}.json"),
                json!({"id": id, "subject_kind": "statement", "subject_id": strong,
                    "predicate": "strengthens", "object_kind": "statement", "object_id": weak,
                    "verification_result_id": "RES-NONE", "note": "n"}),
            );
        }
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
        // A neighbor does not admit further strength relations.
        assert_eq!(edges(&view, "strengthens", "Q")[0].from, "N1");
        assert!(!edges(&view, "strengthens", "Q")[0].verified);
        assert!(edges(&view, "strengthens", "N1").is_empty());
        assert!(view.statements.iter().all(|n| n.id != "N2"));
        // Up: ARG-U uses X; its co-premise Q and conclusion U join the view.
        let up = edges(&view, "uses", "X");
        assert_eq!(up.len(), 1);
        assert_eq!(up[0].from, "ARG-U");
        let node = |id: &str| view.statements.iter().find(|n| n.id == id).unwrap();
        assert_eq!(node("Q").role, "co_premise");
        assert_eq!(node("U").role, "dependent");
        assert!(node("U").is_case_root);
        // Every record edge has a kind and an (empty) extra-premise list.
        assert!(
            view.edges
                .iter()
                .all(|edge| EDGE_KINDS.contains(&edge.kind))
        );
        assert!(
            view.edges
                .iter()
                .filter(|edge| edge.inversion.is_none())
                .all(|edge| edge.extra_premises.is_empty() && edge.derivation.is_none())
        );
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

    fn derived<'a>(tree: &'a Tree, kind: &str) -> Vec<&'a Edge> {
        tree.edges.iter().filter(|edge| edge.kind == kind).collect()
    }

    #[test]
    fn contrapositive_edges_come_from_verified_arguments() {
        let dir = fixture();
        let view = build(&dir, "X", Options::default()).unwrap();
        let contrapositive = derived(&view, "contrapositive");
        // ARG-1 (A, P ⊢ X) is verified: ¬X with P gives ¬A, ¬X with A gives ¬P.
        let of = |argument: &str| -> Vec<(&str, &str, Vec<String>)> {
            contrapositive
                .iter()
                .filter(|edge| edge.argument_id.as_deref() == Some(argument))
                .map(|edge| {
                    (
                        edge.from.as_str(),
                        edge.to.as_str(),
                        edge.extra_premises.clone(),
                    )
                })
                .collect()
        };
        assert_eq!(
            of("ARG-1"),
            [
                ("X", "A", vec!["P".to_owned()]),
                ("X", "P", vec!["A".to_owned()])
            ]
        );
        // ARG-2 has no result: no contrapositive.
        assert!(of("ARG-2").is_empty());
        // ARG-U (X, Q ⊢ U), on the up side: ¬U with Q gives ¬X.
        assert!(of("ARG-U").contains(&("U", "X", vec!["Q".to_owned()])));
        let edge = contrapositive
            .iter()
            .find(|edge| edge.argument_id.as_deref() == Some("ARG-1") && edge.to == "A")
            .unwrap();
        let inversion = edge.inversion.as_ref().unwrap();
        assert_eq!(inversion.key, "contrapositive:ARG-1:A");
        assert_eq!(inversion.lemma, CONTRAPOSITIVE_LEMMA);
        assert_eq!(inversion.source_theorem.as_deref(), Some("M.ARG-1"));
        assert!(inversion.negated);
        // Not checked in Lean until materialized.
        assert!(!edge.verified);
        assert_eq!(edge.result_id.as_deref(), Some("RES-ARG-1"));
        assert_eq!(
            inversion.materialized_theorem.as_deref(),
            Some("TruthCore.Results.Logic.Inversions.MARG1Contra1.contrapositive")
        );
        let roles: Vec<(&str, bool)> = inversion
            .requires
            .iter()
            .map(|requirement| (requirement.role, requirement.registered))
            .collect();
        assert_eq!(roles, [("negated_conclusion", false), ("co_premise", true)]);
        assert!(edge.derivation.as_deref().unwrap().contains("M.ARG-1"));
        // At X no argument using X has an alternative for its conclusion
        // (U has one argument): no inverse at all. In particular the
        // unconditioned inverse U ⊢ X is never emitted.
        assert!(derived(&view, "inverse_conditional").is_empty());
        let text = format_tree(&view);
        assert!(text.contains("NOT U WITH Q => NOT X"), "{text}");
        assert!(text.contains("key contrapositive:ARG-U:X"), "{text}");
        assert!(text.contains("never derived"), "{text}");
    }

    #[test]
    fn a_materialized_contrapositive_is_verified() {
        let dir = fixture();
        let theorem = "TruthCore.Results.Logic.Inversions.MARG1Contra1.contrapositive";
        for (id, premises, conclusion) in [("ARG-NOT-A", ["NOT-X", "P"], "NOT-A")] {
            for statement in [premises[0], conclusion] {
                write(
                    &dir.0,
                    &format!("corpus/statements/{statement}.json"),
                    json!({"id": statement, "paraphrase": "p"}),
                );
            }
            write(
                &dir.0,
                &format!("corpus/arguments/{id}.json"),
                json!({"id": id, "premise_statement_ids": premises, "inference_ids": ["I-1"],
                    "conclusion_statement_id": conclusion, "meaning": "m"}),
            );
            write(
                &dir.0,
                &format!("corpus/results/RES-{id}.json"),
                json!({"id": format!("RES-{id}"), "argument_id": id, "theorem": theorem,
                    "challenge_module": "C", "solution_module": "S", "comparator_config": "c",
                    "status": "solution-present", "transcription": "instantiation"}),
            );
        }
        let view = build(&dir, "X", Options::default()).unwrap();
        let edge = derived(&view, "contrapositive")
            .into_iter()
            .find(|edge| edge.argument_id.as_deref() == Some("ARG-1") && edge.to == "A")
            .unwrap();
        assert!(edge.verified);
        let inversion = edge.inversion.as_ref().unwrap();
        assert_eq!(
            inversion.materialized_result_id.as_deref(),
            Some("RES-ARG-NOT-A")
        );
        assert_eq!(
            inversion.materialized_argument_id.as_deref(),
            Some("ARG-NOT-A")
        );
        // Its ¬X is now a registered (open) statement.
        assert_eq!(inversion.requires[0].statement_id.as_deref(), Some("NOT-X"));
        assert!(inversion.requires[0].registered);
        assert!(inversion.requires[0].closed.is_null());
        // The other premise edge stays unverified.
        assert!(
            !derived(&view, "contrapositive")
                .iter()
                .any(|edge| edge.argument_id.as_deref() == Some("ARG-1")
                    && edge.to == "P"
                    && edge.verified)
        );
    }

    #[test]
    fn inverse_edges_need_an_exhaustiveness_premise() {
        let dir = fixture();
        // At A: ARG-1 uses A and concludes X, which ARG-2 also concludes.
        let view = build(&dir, "A", Options::default()).unwrap();
        let inverse = derived(&view, "inverse_conditional");
        assert_eq!(inverse.len(), 1, "{inverse:?}");
        let edge = inverse[0];
        assert_eq!((edge.from.as_str(), edge.to.as_str()), ("X", "A"));
        assert_eq!(edge.argument_id.as_deref(), Some("ARG-1"));
        assert!(!edge.verified);
        let inversion = edge.inversion.as_ref().unwrap();
        assert_eq!(inversion.lemma, INVERSE_LEMMA);
        assert!(!inversion.negated);
        let exhaustiveness = &inversion.requires[0];
        assert_eq!(exhaustiveness.role, "exhaustiveness");
        assert!(!exhaustiveness.registered);
        assert!(exhaustiveness.statement_id.is_none());
        assert_eq!(exhaustiveness.argument_ids, ["ARG-1", "ARG-2"]);
        let alternative = &inversion.requires[1];
        assert_eq!(alternative.role, "negated_alternative");
        assert_eq!(alternative.argument_id.as_deref(), Some("ARG-2"));
        assert_eq!(alternative.premise_statement_ids, ["B", "P"]);
        // ARG-4 uses A for C, the only argument for C: no inverse C ⊢ A.
        assert!(inverse.iter().all(|edge| edge.from != "C"));
        // Regression (#1674): no derived edge is the unconditioned inverse.
        // Every inverse edge lists the exhaustiveness premise.
        for root in ["A", "B", "C", "P", "X", "Q", "D1"] {
            let view = build(&dir, root, Options::default()).unwrap();
            for edge in derived(&view, "inverse_conditional") {
                let inversion = edge.inversion.as_ref().unwrap();
                assert!(
                    inversion
                        .requires
                        .iter()
                        .any(|requirement| requirement.role == "exhaustiveness"),
                    "{edge:?}"
                );
                assert_eq!(edge.to, root);
            }
        }
        let text = format_tree(&view);
        assert!(
            text.contains("X WITH NOT ALL OF ARG-2 => A GIVEN the unregistered open premise"),
            "{text}"
        );
    }

    #[test]
    fn materialized_names_are_lean_identifiers() {
        assert_eq!(
            materialized_name(
                "TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore.Solution",
                "TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore.roweDeductiveCore",
                1
            ),
            "RoweDeductiveCoreContra1"
        );
        assert_eq!(
            materialized_name("A.Projection.Solution", "A.Projection.checks", 2),
            "ProjectionChecksContra2"
        );
        assert_eq!(materialized_name("A.Solution", "A.x_1", 3), "AX1Contra3");
    }

    #[test]
    fn unknown_statement_is_an_error() {
        let dir = fixture();
        assert!(
            matches!(build(&dir, "NOPE", Options::default()), Err(UnknownStatement(id)) if id == "NOPE")
        );
    }
}
