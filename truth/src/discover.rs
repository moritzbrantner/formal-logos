//! `truth discover`: search for new implications between corpus propositions
//! with Duper (issue #1784, docs/discover.md).
//!
//! For each target statement the engine ranks candidate premises from a pool
//! of existing statements (closed ones by default), builds the goal
//! `∀ params, P₁ → … → Pₙ → T` over the statements' own Lean declarations
//! (`scripts/Discover.lean` binds their parameters by name and type), and has
//! Duper search for a proof over the delta-expanded definitions. A proof is
//! minimized by deleting premises, tested for vacuity (`False` from the
//! premises) and a transcription shape, given a one-point witness where one
//! exists, and filtered: not already derivable by composing verified
//! arguments, no unbridged sense mixing, only the permitted axioms. Every
//! surviving implication is re-elaborated from its rendered theorem text in a
//! separate Lean run (the certification run) and its axioms are checked.
//!
//! The search is advisory. The kernel checks every proof it reports, but a
//! discovery is a conditional support option for review, not a corpus record:
//! `--write-spec` writes an `argument_batch.py` spec draft and a Solution draft
//! and nothing else. A target without a proof is unresolved, never refuted.

use crate::{Corpus, parameter_tags, prove_sweep, senses, subprocess};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

/// The Lean search command file.
pub const DISCOVER_LEAN: &str = "scripts/Discover.lean";
/// The vocabulary exporter (`truth bridges` reads the same export).
pub const CONSTANTS_LEAN: &str = "scripts/StatementConstants.lean";
/// The only axioms a discovered proof may use (docs/axiom-policy.md).
pub const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];
const MARKER: &str = "DISCOVER-JSON ";
/// Filters that flag a discovery without rejecting it.
pub const INFORMATIONAL: [&str; 5] = [
    "witness",
    "sense_bridge",
    "vacuous_target",
    "projection_binding",
    "implicit_excluded_middle",
];
/// The recorded logical-background statements a classical proof supplies
/// without listing them: excluded middle (`TruthCore.Logic.ExcludedMiddle`,
/// `∀ p, p ∨ ¬p`, legacy `STMT-EXCLUDED-MIDDLE`), which `Classical.choice`
/// proves (`Classical.em`). Duper proves classically, so a verified argument
/// that lists excluded middle as an explicit premise matches a found proof
/// without it (the `known` filter). No other statement is recorded as logical
/// background: the corpus's only such list is this one floor statement
/// (`LEGACY_FLOOR_STATEMENTS` of `truth check`).
pub const CLASSICAL_BACKGROUND: [&str; 1] = ["ee4ab504-c8fe-59bc-bc96-7cbeefed6410"];

/// Which statements may serve as premises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pool {
    /// Closed in the frontier (established, or derived from established).
    Closed,
    /// Closed, or the conclusion of a verified non-transcription result.
    Proved,
    /// Every statement with a Lean declaration: conditional support options.
    All,
}

impl Pool {
    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "closed" => Some(Self::Closed),
            "proved" => Some(Self::Proved),
            "all" => Some(Self::All),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::Closed => "closed",
            Self::Proved => "proved",
            Self::All => "all",
        }
    }
}

#[derive(Clone)]
pub struct Options {
    /// Search missing bridges for goals that fail.
    pub bridges: bool,
    /// `maxHeartbeats` (thousands) of each prover attempt.
    pub heartbeats: u64,
    /// Candidate premises per target.
    pub candidates: usize,
    pub pool: Pool,
    /// An exact, ordered premise bundle for every target. Empty selects
    /// ranked retrieval; nonempty bypasses the pool and optional bridges.
    pub premises: Vec<String>,
    /// A Zipperposition executable for lean-auto premise selection.
    pub zipperposition: Option<String>,
    /// Parallel Lean processes.
    pub jobs: usize,
    /// Targets per Lean process.
    pub batch: usize,
    /// Declaration prefixes (`TruthCore.Causality`) targets and retrieved
    /// candidates must match. Explicit premises are not filtered.
    pub modules: Vec<String>,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            bridges: true,
            heartbeats: 100_000,
            candidates: 8,
            pool: Pool::Closed,
            premises: Vec::new(),
            zipperposition: None,
            jobs: 2,
            batch: 6,
            modules: Vec::new(),
        }
    }
}

// --- Corpus view ------------------------------------------------------------------

/// The Lean vocabulary of a declaration (`scripts/StatementConstants.lean`).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Vocabulary {
    pub module: String,
    pub binders: Vec<String>,
    /// TruthCore constants in its type and body, itself excluded.
    pub constants: BTreeSet<String>,
    /// The head constant of each binder's type (`""` when none or not a
    /// TruthCore constant), aligned with `binders`.
    pub binder_types: Vec<String>,
    /// For each binder whose type is a TruthCore structure, the head constants
    /// of its fields' types, aligned with `binders` (projection fit, #1819).
    pub binder_fields: Vec<BTreeSet<String>>,
    /// For each binder that occurs only as the structure argument of field
    /// projections (`m` in `FrameSatisfies .KT m.ontic.frame`), the head
    /// constants of those fields' types; empty otherwise. Aligned with
    /// `binders` (#1845).
    pub binder_uses: Vec<BTreeSet<String>>,
}

/// Parses the `StatementConstants.lean` export.
pub fn parse_vocabulary(value: &Value) -> Result<BTreeMap<String, Vocabulary>, String> {
    let rows = value
        .as_array()
        .ok_or("constants export must be a JSON array")?;
    let mut out = BTreeMap::new();
    for row in rows {
        let Some(declaration) = row["declaration"].as_str() else {
            continue;
        };
        if row.get("error").is_some() {
            continue;
        }
        let strings = |key: &str| -> Vec<String> {
            row[key]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        };
        let nested = |key: &str| -> Vec<BTreeSet<String>> {
            row[key]
                .as_array()
                .into_iter()
                .flatten()
                .map(|heads| {
                    heads
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter_map(Value::as_str)
                        .map(str::to_owned)
                        .collect()
                })
                .collect()
        };
        out.insert(
            declaration.to_owned(),
            Vocabulary {
                module: row["module"].as_str().unwrap_or_default().to_owned(),
                binders: strings("binders"),
                constants: strings("constants")
                    .into_iter()
                    .filter(|c| c != declaration)
                    .collect(),
                binder_types: strings("binder_types"),
                binder_fields: nested("binder_fields"),
                binder_uses: nested("binder_uses"),
            },
        );
    }
    Ok(out)
}

/// A statement with a Lean declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct Statement {
    pub id: String,
    pub label: String,
    pub declaration: String,
    pub definitions: BTreeSet<String>,
}

/// A verified argument: its premises, conclusion and ids.
#[derive(Clone, Debug, PartialEq)]
pub struct Known {
    pub argument_id: String,
    pub premises: BTreeSet<String>,
    pub conclusion: String,
}

/// The verified derivation graph: every argument a result verifies.
#[derive(Default)]
pub struct Graph {
    pub arguments: Vec<Known>,
    /// Recorded rival pairs (`alternative_to`, `attacks`), both directions.
    pub rivals: BTreeMap<String, BTreeSet<String>>,
}

impl Graph {
    pub fn from_corpus(corpus: &Corpus) -> Self {
        let verified: BTreeSet<&str> = corpus
            .records("results")
            .into_iter()
            .filter_map(|r| r.get("argument_id").and_then(Value::as_str))
            .collect();
        let mut arguments = Vec::new();
        for (id, record) in corpus.records_by_id("arguments") {
            if !verified.contains(id) {
                continue;
            }
            let fields = &record.fields;
            let Some(conclusion) = fields
                .get("conclusion_statement_id")
                .and_then(Value::as_str)
            else {
                continue;
            };
            let premises = ["premise_statement_ids", "commitment_statement_ids"]
                .iter()
                .filter_map(|key| fields.get(*key).and_then(Value::as_array))
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect();
            arguments.push(Known {
                argument_id: id.to_owned(),
                premises,
                conclusion: conclusion.to_owned(),
            });
        }
        let mut rivals: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for relation in corpus.records("relations") {
            let field = |key| relation.get(key).and_then(Value::as_str);
            if matches!(field("predicate"), Some("alternative_to" | "attacks"))
                && field("subject_kind") == Some("statement")
                && field("object_kind") == Some("statement")
                && let (Some(a), Some(b)) = (field("subject_id"), field("object_id"))
            {
                rivals.entry(a.to_owned()).or_default().insert(b.to_owned());
                rivals.entry(b.to_owned()).or_default().insert(a.to_owned());
            }
        }
        Self { arguments, rivals }
    }

    /// The verified arguments that, composed by forward chaining from
    /// `premises`, reach `target`; `None` when the closure misses it.
    pub fn derivation(&self, premises: &BTreeSet<String>, target: &str) -> Option<Vec<String>> {
        self.derivation_with(premises, &BTreeSet::new(), target)
            .map(|(path, _)| path)
    }

    /// [`Self::derivation`] with `background` statements granted besides
    /// `premises` (the logic a classical proof supplies implicitly, see
    /// [`CLASSICAL_BACKGROUND`]); also returns the background statements the
    /// composing arguments list as premises, which the found proof did not.
    pub fn derivation_with(
        &self,
        premises: &BTreeSet<String>,
        background: &BTreeSet<String>,
        target: &str,
    ) -> Option<(Vec<String>, BTreeSet<String>)> {
        if premises.contains(target) {
            return Some((Vec::new(), BTreeSet::new()));
        }
        if background.contains(target) {
            return Some((Vec::new(), BTreeSet::from([target.to_owned()])));
        }
        let mut have: BTreeSet<String> = premises.union(background).cloned().collect();
        let mut via: HashMap<String, usize> = HashMap::new();
        loop {
            let mut grew = false;
            for (index, argument) in self.arguments.iter().enumerate() {
                if !have.contains(&argument.conclusion) && argument.premises.is_subset(&have) {
                    have.insert(argument.conclusion.clone());
                    via.insert(argument.conclusion.clone(), index);
                    grew = true;
                }
            }
            if have.contains(target) || !grew {
                break;
            }
        }
        if !have.contains(target) {
            return None;
        }
        // The arguments the target's derivation uses, premises first.
        let mut used = Vec::new();
        let mut granted = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut stack = vec![target.to_owned()];
        while let Some(node) = stack.pop() {
            if let Some(&index) = via.get(&node)
                && seen.insert(index)
            {
                used.push(self.arguments[index].argument_id.clone());
                for premise in &self.arguments[index].premises {
                    if background.contains(premise) && !premises.contains(premise) {
                        granted.insert(premise.clone());
                    }
                }
                stack.extend(self.arguments[index].premises.iter().cloned());
            }
        }
        used.reverse();
        Some((used, granted))
    }
}

/// `strengthens` relations: strong statement -> weaker statements.
pub fn weaker_siblings(corpus: &Corpus) -> BTreeMap<String, BTreeSet<String>> {
    let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for relation in corpus.records("relations") {
        let field = |key| relation.get(key).and_then(Value::as_str);
        if field("predicate") == Some("strengthens")
            && field("subject_kind") == Some("statement")
            && field("object_kind") == Some("statement")
            && let (Some(strong), Some(weak)) = (field("subject_id"), field("object_id"))
        {
            out.entry(strong.to_owned())
                .or_default()
                .insert(weak.to_owned());
        }
    }
    out
}

/// The statements with a Lean declaration.
pub fn statements(corpus: &Corpus) -> BTreeMap<String, Statement> {
    corpus
        .records_by_id("statements")
        .filter_map(|(id, record)| {
            let fields = &record.fields;
            let declaration = fields.get("lean_declaration")?.as_str()?;
            Some((
                id.to_owned(),
                Statement {
                    id: id.to_owned(),
                    label: fields
                        .get("label")
                        .and_then(Value::as_str)
                        .unwrap_or(id)
                        .to_owned(),
                    declaration: declaration.to_owned(),
                    definitions: fields
                        .get("definition_ids")
                        .and_then(Value::as_array)
                        .into_iter()
                        .flatten()
                        .filter_map(Value::as_str)
                        .map(str::to_owned)
                        .collect(),
                },
            ))
        })
        .collect()
}

/// The premise pool from a frontier report.
pub fn pool_ids(corpus: &Corpus, report: &Value, pool: Pool) -> BTreeSet<String> {
    let keys = |key: &str| -> BTreeSet<String> {
        match &report[key] {
            Value::Object(map) => map.keys().cloned().collect(),
            Value::Array(items) => items
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect(),
            _ => BTreeSet::new(),
        }
    };
    let mut ids = keys("closed_statements");
    ids.extend(keys("established_statements"));
    match pool {
        Pool::Closed => {}
        Pool::Proved => {
            let transcriptions = keys("transcription_results");
            let arguments: HashMap<&str, &str> = corpus
                .records_by_id("arguments")
                .filter_map(|(id, r)| {
                    Some((id, r.fields.get("conclusion_statement_id")?.as_str()?))
                })
                .collect();
            for (id, result) in corpus.records_by_id("results") {
                if transcriptions.contains(id) {
                    continue;
                }
                if let Some(conclusion) = result
                    .fields
                    .get("argument_id")
                    .and_then(Value::as_str)
                    .and_then(|a| arguments.get(a))
                {
                    ids.insert((*conclusion).to_owned());
                }
            }
        }
        Pool::All => {
            ids.extend(
                corpus
                    .records_by_id("statements")
                    .map(|(id, _)| id.to_owned()),
            );
        }
    }
    ids
}

/// Target selectors: open premises reaching the root, or the registered
/// next tests (the frontier's next-step leaves).
pub fn selected_targets(report: &Value, selector: &str) -> Result<Vec<String>, String> {
    let ids: Vec<String> = match selector {
        "open-root" => {
            let reaching: BTreeSet<&str> = report["reaching_root_statements"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .collect();
            report["items"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|item| item["statement_id"].as_str())
                .filter(|id| reaching.contains(id))
                .map(str::to_owned)
                .collect()
        }
        "next-tests" => report["next_steps"]["leaves"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|leaf| leaf["statement_id"].as_str())
            .map(str::to_owned)
            .collect(),
        other => {
            return Err(format!(
                "unknown target selector {other:?}; use open-root or next-tests"
            ));
        }
    };
    let mut seen = BTreeSet::new();
    Ok(ids
        .into_iter()
        .filter(|id| seen.insert(id.clone()))
        .collect())
}

// --- Parameter-level sense tags -------------------------------------------------------

/// The parameter-level sense tags the binding policy uses (read by
/// [`crate::parameter_tags::ParameterTags`], #1794), and the registered sense
/// bridges (`sense_bridges` entries of arguments).
#[derive(Default)]
pub struct SenseTags {
    pub tags: Vec<parameter_tags::ParameterTag>,
    pub bridges: Vec<Value>,
}

/// Whether a tag names its whole binder (no fixed argument).
fn whole_binder(tag: &parameter_tags::ParameterTag) -> bool {
    tag.parameter.arguments.iter().all(|a| a == "_")
}

/// The identification key of a tag: its sense, and its fixed arguments when
/// any (`CausesIn _ _ esse`, key `sense|_ _ esse`). `scripts/Discover.lean`
/// identifies two binders by tag only when their keys agree *and* name whole
/// binders: a partial-application key (containing `|`) describes only that
/// application, so identifying the full relations would go beyond the tag.
fn tag_key(tag: &parameter_tags::ParameterTag) -> String {
    if whole_binder(tag) {
        tag.sense_id.clone()
    } else {
        format!("{}|{}", tag.sense_id, tag.parameter.arguments.join(" "))
    }
}

impl SenseTags {
    pub fn from_parts(
        tags: &parameter_tags::ParameterTags,
        arguments: impl IntoIterator<
            Item = impl std::ops::Deref<Target = serde_json::Map<String, Value>>,
        >,
    ) -> Self {
        let bridges = arguments
            .into_iter()
            .filter_map(|a| a.get("sense_bridges").and_then(Value::as_array).cloned())
            .flatten()
            .collect();
        Self {
            tags: tags.all().to_vec(),
            bridges,
        }
    }

    pub fn new(corpus: &Corpus) -> Result<Self, String> {
        let tags = parameter_tags::ParameterTags::from_corpus(corpus)?;
        Ok(Self::from_parts(&tags, corpus.records("arguments")))
    }

    /// `[declaration, binder, key]` for the binding policy of
    /// `scripts/Discover.lean` (see [`tag_key`]).
    pub fn for_declarations(&self, declarations: &[&str]) -> Vec<[String; 3]> {
        self.tags
            .iter()
            .filter(|t| declarations.contains(&t.parameter.declaration.as_str()))
            .map(|t| {
                [
                    t.parameter.declaration.clone(),
                    t.parameter.parameter.clone(),
                    tag_key(t),
                ]
            })
            .collect()
    }

    /// The senses each binder of `declaration` is tagged with as a whole
    /// binder (no fixed arguments), by binder name. These are the tags that
    /// `scripts/Discover.lean` identifies binders by; a partial-application tag
    /// (`CausesIn _ _ esse`) describes only that application and is left out.
    /// An untagged binder is absent: its sense is unknown.
    pub fn whole_binder_senses(&self, declaration: &str) -> BTreeMap<String, BTreeSet<String>> {
        let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for t in &self.tags {
            if t.parameter.declaration == declaration && whole_binder(t) {
                out.entry(t.parameter.parameter.clone())
                    .or_default()
                    .insert(t.sense_id.clone());
            }
        }
        out
    }

    /// `(term, sense)` pairs a declaration's parameters carry.
    pub fn senses_of(&self, declaration: &str) -> BTreeSet<(String, String)> {
        self.tags
            .iter()
            .filter(|t| t.parameter.declaration == declaration)
            .map(|t| (t.term.clone(), t.sense_id.clone()))
            .collect()
    }

    /// Statements registered as bridges between different senses of one term
    /// used by `a` and `b` (either direction).
    pub fn bridge_statements(&self, a: &str, b: &str) -> Vec<String> {
        let left = self.senses_of(a);
        let right = self.senses_of(b);
        let mut out = BTreeSet::new();
        for (term, s1) in &left {
            for (term2, s2) in &right {
                if term != term2 || s1 == s2 {
                    continue;
                }
                for bridge in &self.bridges {
                    let end = |k: &str| bridge[k].as_str().unwrap_or_default();
                    if end("term") == term
                        && ((end("from") == s1 && end("to") == s2)
                            || (end("from") == s2 && end("to") == s1))
                        && let Some(id) = bridge["statement_id"].as_str()
                    {
                        out.insert(id.to_owned());
                    }
                }
            }
        }
        out.into_iter().collect()
    }
}

// --- Retrieval --------------------------------------------------------------------

/// A ranked candidate premise.
#[derive(Clone, Debug, PartialEq)]
pub struct Candidate {
    pub id: String,
    /// Score against the target, or against `via` for a backfilled candidate.
    pub score: f64,
    /// The original direct candidate that admitted this second-hop addition.
    /// Retrieval provenance only, not a proof dependency; `None` is direct.
    pub via: Option<String>,
}

/// Ranks premises without displacing the direct candidates. When direct
/// ranking underfills `limit`, backfill through those original candidates in
/// their ranked order, using the same admission rules and scoped pool. Newly
/// added candidates never become anchors, and the ranked bundle stays within
/// `limit`. Each backfilled score is relative to its admitting anchor (`via`).
pub fn rank(
    target: &Statement,
    pool: &[&Statement],
    vocabulary: &BTreeMap<String, Vocabulary>,
    weaker: &BTreeMap<String, BTreeSet<String>>,
    tags: &SenseTags,
    limit: usize,
) -> Vec<Candidate> {
    let mut ranked = rank_direct(target, pool, vocabulary, weaker, tags, limit);
    if ranked.is_empty() || ranked.len() == limit {
        return ranked;
    }
    let statements: BTreeMap<&str, &Statement> = pool.iter().map(|s| (s.id.as_str(), *s)).collect();
    let anchors: Vec<&Statement> = ranked
        .iter()
        .filter_map(|c| statements.get(c.id.as_str()).copied())
        .collect();
    let mut selected_ids: BTreeSet<&str> = anchors
        .iter()
        .map(|s| s.id.as_str())
        .chain([target.id.as_str()])
        .collect();
    let mut selected_declarations: BTreeSet<&str> = anchors
        .iter()
        .map(|s| s.declaration.as_str())
        .chain([target.declaration.as_str()])
        .collect();
    for anchor in anchors {
        let remaining: Vec<&Statement> = pool
            .iter()
            .copied()
            .filter(|s| {
                !selected_ids.contains(s.id.as_str())
                    && !selected_declarations.contains(s.declaration.as_str())
            })
            .collect();
        if remaining.is_empty() {
            break;
        }
        // Keep every eligible result available: an alias skipped below must
        // not hide a later unique declaration behind a premature truncation.
        for mut candidate in rank_direct(
            anchor,
            &remaining,
            vocabulary,
            weaker,
            tags,
            remaining.len(),
        ) {
            let Some(statement) = statements.get(candidate.id.as_str()) else {
                continue;
            };
            // Two results from this same ranking may share a declaration.
            if selected_ids.contains(statement.id.as_str())
                || selected_declarations.contains(statement.declaration.as_str())
            {
                continue;
            }
            selected_ids.insert(statement.id.as_str());
            selected_declarations.insert(statement.declaration.as_str());
            candidate.via = Some(anchor.id.clone());
            ranked.push(candidate);
            if ranked.len() == limit {
                return ranked;
            }
        }
    }
    ranked
}

/// Ranks pool statements as premises for `target`. A candidate must share
/// project vocabulary or a definition with the target, and at least one
/// parameter name, so that its binders can be identified with the target's,
/// or a structure parameter with a field of a target parameter's type (the
/// projection binding `scripts/Discover.lean` may try, #1819).
/// Score: the share of the candidate's parameters that the target also has
/// or projects to (type fit), the share of its TruthCore constants the target uses
/// (precision) and of the target's constants it uses (recall), plus shared
/// definitions, the same module, a strength order with the target and a
/// projection fit. A ranking only: Lean decides whether the types compose.
fn rank_direct(
    target: &Statement,
    pool: &[&Statement],
    vocabulary: &BTreeMap<String, Vocabulary>,
    weaker: &BTreeMap<String, BTreeSet<String>>,
    tags: &SenseTags,
    limit: usize,
) -> Vec<Candidate> {
    let Some(goal) = vocabulary.get(&target.declaration) else {
        return Vec::new();
    };
    // The senses the target's whole binders are tagged with (authored tags
    // only; an untagged binder contributes nothing).
    let goal_senses: BTreeSet<String> = tags
        .whole_binder_senses(&target.declaration)
        .into_values()
        .flatten()
        .collect();
    let goal_binders: BTreeSet<&String> = goal.binders.iter().collect();
    let goal_types: BTreeSet<&str> = goal
        .binder_types
        .iter()
        .map(String::as_str)
        .filter(|t| !t.is_empty())
        .collect();
    let strength = |a: &str, b: &str| {
        weaker.get(a).is_some_and(|w| w.contains(b)) || weaker.get(b).is_some_and(|w| w.contains(a))
    };
    let mut ranked: Vec<Candidate> = pool
        .iter()
        .filter(|s| s.id != target.id && s.declaration != target.declaration)
        .filter_map(|s| {
            let v = vocabulary.get(&s.declaration)?;
            let shared = v.constants.intersection(&goal.constants).count()
                + usize::from(goal.constants.contains(&s.declaration))
                + usize::from(v.constants.contains(&target.declaration));
            let definitions = s.definitions.intersection(&target.definitions).count();
            let named = v
                .binders
                .iter()
                .filter(|b| goal_binders.contains(b))
                .count();
            // A binder not shared by name whose structure has a field of a
            // target binder's type (`m : Profile` with `m.ontic : Ontic`).
            let projecting = v
                .binders
                .iter()
                .enumerate()
                .filter(|(i, b)| {
                    !goal_binders.contains(b)
                        && v.binder_fields
                            .get(*i)
                            .is_some_and(|f| f.iter().any(|h| goal_types.contains(h.as_str())))
                })
                .count();
            // A projecting binder the candidate uses only through fields of a
            // target binder's type (`OnticFrameKT (m : Profile W B) :=
            // FrameSatisfies .KT m.ontic.frame`): the candidate is a statement
            // about that field's value, which projection binding supplies whole.
            let projection_only = v
                .binders
                .iter()
                .enumerate()
                .filter(|(i, b)| {
                    !goal_binders.contains(b)
                        && v.binder_uses.get(*i).is_some_and(|u| {
                            !u.is_empty() && u.iter().all(|h| goal_types.contains(h.as_str()))
                        })
                })
                .count();
            // A binder not shared by name or projection but tagged, as a whole
            // binder, with a sense one of the target's binders is tagged with:
            // `scripts/Discover.lean` identifies the two by that tag.
            let senses = tags.whole_binder_senses(&s.declaration);
            let shared_senses: BTreeSet<&String> = senses
                .values()
                .flatten()
                .filter(|sense| goal_senses.contains(*sense))
                .collect();
            let tagged = v
                .binders
                .iter()
                .enumerate()
                .filter(|(i, b)| {
                    !goal_binders.contains(b)
                        && !v
                            .binder_fields
                            .get(*i)
                            .is_some_and(|f| f.iter().any(|h| goal_types.contains(h.as_str())))
                        && senses
                            .get(*b)
                            .is_some_and(|ss| ss.iter().any(|sense| goal_senses.contains(sense)))
                })
                .count();
            let binders = named + projecting + tagged;
            // Shared vocabulary, a shared definition or a shared authored sense
            // admits a candidate; a parameter name alone never does.
            if (shared == 0 && definitions == 0 && shared_senses.is_empty()) || binders == 0 {
                return None;
            }
            // Precision matters most: a candidate whose vocabulary and parameters
            // lie inside the target's composes with it, however small it is.
            // The vocabulary is the project constants and the authored senses
            // of the whole binders: a relation binder (`MoreIn : B → B → R →
            // Prop`) mentions no constant, and its sense tag says which concept
            // it expresses, as a constant would.
            let candidate_senses: BTreeSet<&String> = senses.values().flatten().collect();
            let overlap = shared + shared_senses.len();
            let precision =
                overlap as f64 / (v.constants.len() + candidate_senses.len() + 1) as f64;
            let recall = overlap as f64 / (goal.constants.len() + goal_senses.len()).max(1) as f64;
            let fit = binders as f64 / v.binders.len().max(1) as f64;
            let mut score = 0.4 * precision.min(1.0) + 0.2 * recall + 0.5 * fit;
            score += 0.1 * definitions as f64;
            if v.module == goal.module {
                score += 0.1;
            }
            if strength(&s.id, &target.id) {
                score += 0.3;
            }
            // A projection fit is a type-level signal the constant overlap
            // understates: the structure brings its other fields' vocabulary
            // (`Profile` beyond `ontic`), which lowers precision and recall.
            if projecting > 0 {
                score += 0.3;
            }
            // Used only through that projection, the structure's other fields
            // are no part of the candidate's statement: their vocabulary, which
            // still dilutes the constant overlap, says nothing against it.
            if projection_only > 0 {
                score += 0.3;
            }

            Some(Candidate {
                id: s.id.clone(),
                score,
                via: None,
            })
        })
        .collect();
    ranked.sort_by(|a, b| b.score.total_cmp(&a.score).then_with(|| a.id.cmp(&b.id)));
    ranked.truncate(limit);
    ranked
}

// --- Lean search ------------------------------------------------------------------

/// One goal: a target and its candidate premises, in order.
#[derive(Clone, Debug, PartialEq)]
pub struct Trial {
    pub label: String,
    pub target: String,
    pub premises: Vec<String>,
    /// `(stronger, weaker)` when this trial replaces a premise of an earlier
    /// discovery by a weaker strength sibling.
    pub weakening: Option<(String, String, String)>,
    /// Registered sense-bridge statements added as optional premises because
    /// the target and a candidate carry different senses of one term.
    pub sense_bridges: Vec<String>,
}

fn lean_string(text: &str) -> String {
    format!("\"{}\"", text.replace('\\', "\\\\").replace('"', "\\\""))
}

/// The `#discover` command line of `trial`.
pub fn command_line(
    trial: &Trial,
    statements: &BTreeMap<String, Statement>,
    heartbeats: u64,
    zipperposition: Option<&str>,
    tags: &SenseTags,
    bridges: bool,
) -> String {
    let declarations: Vec<&str> = trial
        .premises
        .iter()
        .chain([&trial.target])
        .map(|id| statements[id].declaration.as_str())
        .collect();
    let config = json!({"tags": tags.for_declarations(&declarations), "bridges": bridges});
    let premises: Vec<&str> = trial
        .premises
        .iter()
        .map(|id| statements[id].declaration.as_str())
        .collect();
    format!(
        "#discover {} {heartbeats} {} {} {} from {}",
        lean_string(&trial.label),
        lean_string(zipperposition.unwrap_or_default()),
        lean_string(&config.to_string()),
        statements[&trial.target].declaration,
        premises.join(" ")
    )
}

/// `text` without its leading `import` lines, and those imports.
pub fn split_imports(text: &str) -> (Vec<String>, String) {
    let mut imports = Vec::new();
    let mut body = String::new();
    for line in text.lines() {
        if let Some(module) = line.strip_prefix("import ") {
            imports.push(module.trim().to_owned());
        } else {
            body.push_str(line);
            body.push('\n');
        }
    }
    (imports, body)
}

/// The scratch file: imports, the transcription probe of `truth prove-sweep`,
/// the search command and one line per trial.
pub fn scratch_text(discover: &str, modules: &BTreeSet<String>, lines: &[String]) -> String {
    let (own, body) = split_imports(discover);
    let imports: BTreeSet<&str> = own
        .iter()
        .map(String::as_str)
        .chain(modules.iter().map(String::as_str))
        .collect();
    let mut text = String::new();
    for module in imports {
        let _ = writeln!(text, "import {module}");
    }
    text.push('\n');
    text.push_str(prove_sweep::PRELUDE);
    text.push('\n');
    text.push_str(&body);
    text.push_str("\nset_option maxHeartbeats 0\n\n");
    for line in lines {
        text.push_str(line);
        text.push('\n');
    }
    text
}

/// The `DISCOVER-JSON` outcomes in `output`, by label.
pub fn parse_outcomes(output: &str) -> BTreeMap<String, Value> {
    let mut out = BTreeMap::new();
    for line in output.lines() {
        if let Some(at) = line.find(MARKER)
            && let Ok(value) = serde_json::from_str::<Value>(line[at + MARKER.len()..].trim())
            && let Some(label) = value["label"].as_str()
        {
            out.insert(label.to_owned(), value);
        }
    }
    out
}

fn scratch_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_nanos());
    std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()))
}

fn lake_command(root: &Path, tail: &[String]) -> Command {
    let mut command = Command::new("python3");
    command
        .args(["scripts/worker_env.py", "--", "lake"])
        .args(tail)
        .current_dir(root);
    command
}

fn run(command: Command, timeout: Duration) -> Result<Option<subprocess::Finished>, String> {
    subprocess::run_bounded(command, timeout).map_err(|failure| match failure {
        subprocess::Failure::Spawn(error) => format!("cannot start lake: {error}"),
        subprocess::Failure::Wait(error) => error.to_string(),
    })
}

fn keep_scratch() -> bool {
    std::env::var_os("TRUTH_DISCOVER_KEEP").is_some()
}

/// Runs the search on `trials` (one Lean process); the outcomes by label,
/// read from the log, so targets finished before a timeout are kept.
pub fn search(
    root: &Path,
    discover: &str,
    trials: &[Trial],
    statements: &BTreeMap<String, Statement>,
    vocabulary: &BTreeMap<String, Vocabulary>,
    options: &Options,
    tags: &SenseTags,
) -> Result<BTreeMap<String, Value>, String> {
    let mut modules: BTreeSet<String> = BTreeSet::new();
    for trial in trials {
        for id in trial.premises.iter().chain([&trial.target]) {
            let declaration = &statements[id].declaration;
            let module = vocabulary
                .get(declaration)
                .map(|v| v.module.clone())
                .filter(|m| !m.is_empty())
                .ok_or_else(|| format!("no module known for {declaration}"))?;
            modules.insert(module);
        }
    }
    let lines: Vec<String> = trials
        .iter()
        .map(|t| {
            command_line(
                t,
                statements,
                options.heartbeats,
                options.zipperposition.as_deref(),
                tags,
                options.bridges,
            )
        })
        .collect();
    let directory = scratch_dir("truth-discover");
    let path = directory.join("Discover.lean");
    let log = directory.join("discover.log");
    fs::create_dir_all(&directory)
        .and_then(|()| fs::write(&path, scratch_text(discover, &modules, &lines)))
        .map_err(|error| format!("{}: {error}", path.display()))?;
    // Each attempt is bounded by heartbeats; a target makes at most a few
    // dozen attempts (minimization, vacuity, witnesses).
    let per_target = 60 + options.heartbeats / 1000 * 3;
    let timeout = Duration::from_secs(300 + per_target * trials.len() as u64);
    let mut command = lake_command(
        root,
        &["env".into(), "lean".into(), path.display().to_string()],
    );
    command.env("TRUTH_DISCOVER_LOG", &log);
    let done = run(command, timeout);
    let logged = fs::read_to_string(&log).unwrap_or_default();
    let mut outcomes = parse_outcomes(&logged);
    let failure = match done {
        Err(message) => Some(message),
        Ok(None) => Some(format!("Lean timed out after {}s", timeout.as_secs())),
        Ok(Some(done)) => {
            outcomes.extend(parse_outcomes(&done.stdout));
            let errors: Vec<&str> = done
                .stdout
                .lines()
                .chain(done.stderr.lines())
                .filter(|line| line.contains(": error"))
                .take(3)
                .collect();
            (!done.success && outcomes.len() < trials.len()).then(|| errors.join("\n"))
        }
    };
    if keep_scratch() {
        eprintln!("discover: kept {}", path.display());
    } else {
        let _ = fs::remove_dir_all(&directory);
    }
    for trial in trials {
        outcomes.entry(trial.label.clone()).or_insert_with(|| {
            json!({"label": trial.label, "error": failure.clone().unwrap_or_else(|| "no output".into())})
        });
    }
    Ok(outcomes)
}

/// Runs `search` over `trials` in batches, `options.jobs` Lean processes at a time.
#[allow(clippy::too_many_arguments)]
pub fn search_all(
    root: &Path,
    discover: &str,
    trials: &[Trial],
    statements: &BTreeMap<String, Statement>,
    vocabulary: &BTreeMap<String, Vocabulary>,
    options: &Options,
    tags: &SenseTags,
    progress: &(dyn Fn(usize, usize) + Sync),
) -> BTreeMap<String, Value> {
    let batches: Vec<&[Trial]> = trials.chunks(options.batch.max(1)).collect();
    let total = batches.len();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let done = std::sync::atomic::AtomicUsize::new(0);
    let results = std::sync::Mutex::new(BTreeMap::new());
    std::thread::scope(|scope| {
        for _ in 0..options.jobs.max(1).min(total.max(1)) {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    let Some(batch) = batches.get(index) else {
                        break;
                    };
                    let outcomes =
                        search(root, discover, batch, statements, vocabulary, options, tags)
                            .unwrap_or_else(|message| {
                                batch
                                    .iter()
                                    .map(|t| {
                                        (
                                            t.label.clone(),
                                            json!({"label": t.label, "error": message}),
                                        )
                                    })
                                    .collect()
                            });
                    results.lock().expect("results lock").extend(outcomes);
                    progress(
                        done.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1,
                        total,
                    );
                }
            });
        }
    });
    results.into_inner().expect("results lock")
}

// --- Classification ---------------------------------------------------------------

/// What a trial found.
#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    /// A minimized implication that passed every filter.
    Discovery,
    /// The minimal premises prove `False`.
    Incompatibility,
    /// The target follows from no premise: a theorem of its vocabulary.
    VocabularyTheorem,
    /// Proved, but rejected by a filter.
    Filtered,
    /// No proof within the budget.
    Unresolved,
    Error,
}

impl Kind {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Discovery => "discovery",
            Self::Incompatibility => "incompatibility",
            Self::VocabularyTheorem => "vocabulary_theorem",
            Self::Filtered => "filtered",
            Self::Unresolved => "unresolved",
            Self::Error => "error",
        }
    }
}

/// One trial's verdict.
#[derive(Clone, Debug)]
pub struct Finding {
    pub trial: Trial,
    pub kind: Kind,
    /// Minimal premises (statement ids), or the inconsistent core.
    pub premises: Vec<String>,
    /// `(filter, detail)` for every filter that rejected or flagged it.
    pub filters: Vec<(String, String)>,
    pub outcome: Value,
    /// The certification run's verdict, once run: `Ok(axioms)` or the error.
    pub certified: Option<Result<Vec<String>, String>>,
}

/// Sense use of a candidate argument: for each term with several senses,
/// the sense labels, and whether a premise bridges them.
pub struct SenseCheck<'a> {
    index: senses::SenseIndex,
    statements: HashMap<&'a str, &'a serde_json::Map<String, Value>>,
    /// Statements recorded as sense bridges: (term, from, to, statement).
    bridges: Vec<Value>,
}

impl<'a> SenseCheck<'a> {
    /// No disambiguations: nothing mixes (tests, fixtures).
    pub fn empty() -> Self {
        Self {
            index: senses::SenseIndex::default(),
            statements: HashMap::new(),
            bridges: Vec::new(),
        }
    }

    pub fn new(corpus: &'a Corpus) -> Result<Self, String> {
        let disambiguations = corpus.entries("disambiguations");
        let index = senses::sense_index(disambiguations)?;
        let statements = corpus
            .records_by_id("statements")
            .map(|(id, r)| (id, &r.fields))
            .collect();
        let bridges = corpus
            .records("arguments")
            .into_iter()
            .filter_map(|a| a.get("sense_bridges").and_then(Value::as_array))
            .flatten()
            .cloned()
            .collect();
        Ok(Self {
            index,
            statements,
            bridges,
        })
    }

    /// Terms whose senses the argument mixes, as `(term, labels, bridges)`:
    /// the bridges are the registered `sense_bridges` entries (of any role)
    /// whose statement is one of the premises, as premise bridges, or is the
    /// conclusion, with `role: "conclusion"` (an argument that derives the
    /// bridge, which `truth check` accepts, #1845); a term without enough of
    /// them is unbridged.
    pub fn mixing(
        &self,
        premises: &[String],
        conclusion: &str,
    ) -> Vec<(String, Vec<String>, Vec<Value>)> {
        let argument = json!({
            "conclusion_statement_id": conclusion,
            "premise_statement_ids": premises,
        });
        let used = senses::argument_term_senses(
            argument.as_object().expect("object"),
            &self.statements,
            &self.index,
        );
        let mut out = Vec::new();
        for (term, ids) in used {
            if ids.len() < 2 {
                continue;
            }
            // A registration's role is where its own argument used the
            // statement; here only this argument's use counts: a registered
            // bridge statement among the premises is a premise bridge, and
            // one that is the conclusion is derived (role conclusion).
            let mut available: Vec<Value> = Vec::new();
            for b in &self.bridges {
                if b["term"].as_str() != Some(term.as_str()) {
                    continue;
                }
                let Some(statement) = b["statement_id"].as_str() else {
                    continue;
                };
                let mut b = b.clone();
                let Some(map) = b.as_object_mut() else {
                    continue;
                };
                if premises.iter().any(|p| p == statement) {
                    map.remove("role");
                } else if statement == conclusion {
                    map.insert("role".into(), json!("conclusion"));
                } else {
                    continue;
                }
                if !available.contains(&b) {
                    available.push(b);
                }
            }
            let bridged = senses::bridged(&term, &ids, &available);
            let labels = ids
                .iter()
                .map(|id| {
                    self.index
                        .by_id
                        .get(id)
                        .map_or(id.clone(), |s| s.label.clone())
                })
                .collect();
            out.push((term, labels, if bridged { available } else { Vec::new() }));
        }
        out
    }
}

fn indices(value: &Value) -> Vec<usize> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_u64)
        .map(|i| i as usize)
        .collect()
}

fn axioms(value: &Value) -> Vec<String> {
    value["axioms"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect()
}

/// Whether a proof outcome rests on `Classical.choice`, hence has excluded
/// middle (`Classical.em`) without a premise stating it.
pub fn classical(proof: &Value) -> bool {
    axioms(proof).iter().any(|a| a == "Classical.choice")
}

/// The axioms outside the allowance. No name is exempt: the search's auxiliary
/// declarations are theorems (`addDecl` of a `thmDecl`), so they never appear
/// among collected axioms, and an axiom named like one is still an axiom.
pub fn forbidden_axioms(axioms: &[String]) -> Vec<String> {
    axioms
        .iter()
        .filter(|a| !ALLOWED_AXIOMS.contains(&a.as_str()))
        .cloned()
        .collect()
}

/// The carrier and structure identifications the goal made by name across
/// modules (`scripts/Discover.lean`, binding policy): such a goal needs a sense
/// tag or a bridge before it can be a discovery, and stays out of spec drafts.
pub fn domain_flag(outcome: &Value) -> Option<String> {
    let names: Vec<&str> = outcome["domain_identified_by_name"]
        .as_array()?
        .iter()
        .filter_map(Value::as_str)
        .collect();
    (!names.is_empty()).then(|| {
        format!(
            "identified across modules by name only (needs a sense tag or a bridge): {}",
            names.join("; ")
        )
    })
}

/// The projection binding choice the goal was closed under, if any
/// (`scripts/Discover.lean`, projection binding, #1819): the target binder was
/// replaced by a field of a premise's structure binder. Always reported.
pub fn projection_flag(outcome: &Value) -> Option<String> {
    let choice = outcome["projection"].as_object()?;
    let field = |k: &str| choice.get(k).and_then(Value::as_str).unwrap_or_default();
    Some(format!(
        "binding choice: the target binder {} is bound to the projection {} (field {} of {}); \
         the theorem is a specialization of the target to the projection, not the target over \
         an arbitrary binder",
        field("binder"),
        field("bound_to"),
        field("field"),
        field("structure_binder")
    ))
}

/// The projection filters of one outcome (#1819): `projection_ambiguous` when
/// the target binder had another candidate projection (identification by type
/// alone, rejected), `projection_unused` when minimization dropped the premise
/// that introduced the structure (rejected), else the informational
/// `projection_binding`.
pub fn projection_filters(outcome: &Value) -> Vec<(String, String)> {
    let Some(detail) = projection_flag(outcome) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let choice = &outcome["projection"];
    if choice["ambiguous"].as_bool() == Some(true) {
        let alternatives: Vec<&str> = choice["alternatives"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        out.push((
            "projection_ambiguous".to_owned(),
            format!(
                "the target binder {} has several candidate projections ({}): binding one is identification by type alone",
                choice["binder"].as_str().unwrap_or_default(),
                alternatives.join(", ")
            ),
        ));
    }
    if outcome["projection_unused"].as_bool() == Some(true) {
        out.push((
            "projection_unused".to_owned(),
            format!(
                "minimization dropped the premise that introduced {}: the derivation does not use the structure it projects",
                choice["structure_binder"].as_str().unwrap_or_default()
            ),
        ));
    }
    if out.is_empty() {
        out.push(("projection_binding".to_owned(), detail));
    }
    out
}

/// The goals counted as proved: closed, or a vocabulary theorem, except those
/// closed only by a literal P/¬P core, which proves anything (#1819).
pub fn proved_count(findings: &[Finding]) -> usize {
    findings
        .iter()
        .filter(|f| !f.outcome["closed"].is_null() || !f.outcome["alone"].is_null())
        .filter(|f| !f.filters.iter().any(|(n, _)| n == "literal_negation"))
        .count()
}

/// The `(premise, negating premise)` pair of an inconsistent core in which
/// one member's declaration unfolds to the negation of the other's
/// (`literal_negation` of the Lean outcome, #1819).
pub fn literal_negation(trial: &Trial, outcome: &Value) -> Option<(String, String)> {
    let pair = indices(&outcome["literal_negation"]);
    match pair[..] {
        [a, b] => Some((
            trial.premises.get(a)?.clone(),
            trial.premises.get(b)?.clone(),
        )),
        _ => None,
    }
}

/// Applies the filters of #1784 to one Lean outcome.
pub fn classify(trial: &Trial, outcome: &Value, graph: &Graph, senses: &SenseCheck) -> Finding {
    let mut finding = Finding {
        trial: trial.clone(),
        kind: Kind::Unresolved,
        premises: Vec::new(),
        filters: Vec::new(),
        outcome: outcome.clone(),
        certified: None,
    };
    if outcome.get("error").is_some() {
        finding.kind = Kind::Error;
        return finding;
    }
    if !outcome["alone"].is_null() {
        finding.kind = Kind::VocabularyTheorem;
        let forbidden = forbidden_axioms(&axioms(&outcome["alone"]));
        if !forbidden.is_empty() {
            finding.kind = Kind::Filtered;
            finding
                .filters
                .push(("axioms".into(), format!("uses {}", forbidden.join(", "))));
        }
        return finding;
    }
    if outcome["closed"].is_null() {
        return finding;
    }
    if outcome["minimal"].is_null() {
        // Closed by the external prover, but Duper did not reconstruct it.
        finding.kind = Kind::Filtered;
        finding.filters.push((
            "reconstruction".into(),
            outcome["reconstruction"]
                .as_str()
                .unwrap_or("no Duper proof")
                .into(),
        ));
        return finding;
    }
    let ids = |list: &[usize]| -> Vec<String> {
        list.iter()
            .filter_map(|&i| trial.premises.get(i).cloned())
            .collect()
    };
    finding.premises = ids(&indices(&outcome["minimal"]));
    if !outcome["vacuous"].is_null() {
        finding.kind = Kind::Incompatibility;
        let core = indices(&outcome["vacuous_core"]);
        if !core.is_empty() {
            finding.premises = ids(&core);
        }
        // P and its literal negation: inconsistent by construction. Neither an
        // incompatibility nor support for the target, whatever else it proves.
        if let Some((a, b)) = literal_negation(trial, outcome) {
            finding.kind = Kind::Filtered;
            finding.filters.push((
                "literal_negation".into(),
                format!(
                    "{b} unfolds to the negation of {a}: a P/¬P pair by construction, \
                     not a discovered incompatibility; the goal's proof rests on it and supports nothing"
                ),
            ));
            return finding;
        }
        for (filter, detail) in projection_filters(outcome) {
            if filter != "projection_binding" {
                finding.kind = Kind::Filtered;
            }
            finding.filters.push((filter, detail));
        }
        let rival = finding.premises.iter().find_map(|a| {
            let rivals = graph.rivals.get(a)?;
            finding
                .premises
                .iter()
                .find(|b| rivals.contains(*b))
                .map(|b| (a.clone(), b.clone()))
        });
        if let Some((a, b)) = rival {
            finding.kind = Kind::Filtered;
            finding.filters.push((
                "known".into(),
                format!("the inconsistent core contains the recorded rivals {a} and {b}"),
            ));
        }
        if let Some(detail) = domain_flag(outcome) {
            finding.kind = Kind::Filtered;
            finding.filters.push(("domain_by_name".into(), detail));
        }
        // Incompatibilities skip text certification: their contradiction
        // proofs (the first and the core's) must stay within the allowed axioms.
        let mut used = axioms(&outcome["vacuous"]);
        used.extend(axioms(&outcome["vacuous_core_proof"]));
        used.sort();
        used.dedup();
        let forbidden = forbidden_axioms(&used);
        if !forbidden.is_empty() {
            finding.kind = Kind::Filtered;
            finding.filters.push((
                "axioms".into(),
                format!("the contradiction proof uses {}", forbidden.join(", ")),
            ));
        }
        return finding;
    }
    finding.kind = Kind::Discovery;
    if let Some(detail) = domain_flag(outcome) {
        finding.filters.push(("domain_by_name".into(), detail));
    }
    finding.filters.extend(projection_filters(outcome));
    let forbidden = forbidden_axioms(&axioms(&outcome["proof"]));
    if !forbidden.is_empty() {
        finding
            .filters
            .push(("axioms".into(), format!("uses {}", forbidden.join(", "))));
    }
    let set: BTreeSet<String> = finding.premises.iter().cloned().collect();
    // A classical proof (`Classical.choice`) has excluded middle without the
    // premise: a known argument that lists it explicitly still matches.
    let background: BTreeSet<String> = if classical(&outcome["proof"]) {
        CLASSICAL_BACKGROUND
            .iter()
            .map(|s| (*s).to_owned())
            .collect()
    } else {
        BTreeSet::new()
    };
    if let Some((path, granted)) = graph.derivation_with(&set, &background, &trial.target) {
        let granted: Vec<&str> = granted.iter().map(String::as_str).collect();
        let modulo = if granted.is_empty() {
            String::new()
        } else {
            format!(
                ", given {} (excluded middle), which those arguments list as a premise and the classical proof supplies implicitly",
                granted.join(", ")
            )
        };
        finding.filters.push((
            "known".into(),
            if path.is_empty() && granted.is_empty() {
                "the target is among the premises".into()
            } else if path.is_empty() {
                format!(
                    "the target is {} (excluded middle), which the classical proof supplies implicitly",
                    granted.join(", ")
                )
            } else {
                format!(
                    "composes from verified arguments {}{modulo}",
                    path.join(", ")
                )
            },
        ));
        if !granted.is_empty() {
            finding.filters.push((
                "implicit_excluded_middle".into(),
                format!(
                    "the proof is classical (Classical.choice): it uses excluded middle ({}) implicitly, where the known route lists it as an explicit premise",
                    granted.join(", ")
                ),
            ));
        }
    }
    if outcome["probe"].as_bool() == Some(true) {
        finding.filters.push((
            "transcription".into(),
            "one premise application closes the goal (prove-sweep probe)".into(),
        ));
    }
    if outcome["antecedent_refuted"].as_bool() == Some(true) {
        finding.filters.push((
            "vacuous_target".into(),
            "the premises refute the target's own antecedent, so the target holds vacuously".into(),
        ));
    }
    if outcome["witness"].is_null() {
        finding.filters.push((
            "witness".into(),
            "no one-point joint model found; consistency is unresolved (Duper found no contradiction)"
                .into(),
        ));
    }
    for (term, labels, bridges) in senses.mixing(&finding.premises, &trial.target) {
        if bridges.is_empty() {
            finding.filters.push((
                "senses".into(),
                format!(
                    "mixes {} without a premise bridging them",
                    labels.join(", ")
                ),
            ));
        } else {
            let by_conclusion = bridges
                .iter()
                .any(|b| b["role"].as_str() == Some("conclusion"));
            finding.filters.push((
                "sense_bridge".into(),
                format!(
                    "{term}: {} joined by a registered bridge {}",
                    labels.join(", "),
                    if by_conclusion {
                        "that is the conclusion (the derivation derives the bridge, role conclusion)"
                    } else {
                        "premise"
                    }
                ),
            ));
        }
    }
    // The witness and sense-bridge flags inform; every other filter rejects.
    if finding
        .filters
        .iter()
        .any(|(f, _)| !INFORMATIONAL.contains(&f.as_str()))
    {
        finding.kind = Kind::Filtered;
    }
    finding
}

// --- Certification ----------------------------------------------------------------

/// The theorem name of the `index`th discovery.
pub fn theorem_name(index: usize) -> String {
    format!("discovered{}", index + 1)
}

/// The Lean proof of a discovery: delta-expansion, then Duper. When the goal
/// reaches definitions of values (`equations` of the Lean outcome, such as
/// `convergenceFormula`, built by recursion), their defining equations
/// evaluate the closed terms to constructor form first (`simp only`), as in
/// the search (`proverTactic` of `scripts/Discover.lean`, #1845). The theorem
/// statement itself is unchanged.
pub fn proof_text(outcome: &Value) -> String {
    let names = |key: &str| -> Vec<&str> {
        outcome[key]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect()
    };
    let unfold = names("unfold");
    let equations = names("equations");
    let mut text = String::from("by\n");
    if !unfold.is_empty() {
        let _ = writeln!(text, "  delta {} at *", unfold.join(" "));
    }
    if equations.is_empty() {
        text.push_str("  duper [*]");
    } else {
        let _ = writeln!(text, "  try simp only [{}] at *", equations.join(", "));
        text.push_str("  all_goals duper [*]");
    }
    text
}

/// One theorem per discovery, under its heartbeat budget.
pub fn theorem_text(name: &str, outcome: &Value, heartbeats: u64) -> String {
    format!(
        "set_option maxHeartbeats {heartbeats} in\ntheorem {name} {} :=\n  {}\n",
        outcome["signature"].as_str().unwrap_or_default(),
        proof_text(outcome).replace('\n', "\n  ")
    )
}

/// The certification file: plain text, as a Solution would state it, with
/// `#print axioms` after each theorem; and each theorem's line range.
pub fn certification_text(
    modules: &BTreeSet<String>,
    theorems: &[(String, String)],
) -> (String, Vec<(String, usize, usize)>) {
    let mut text = String::new();
    for module in modules.iter().map(String::as_str).chain(["Duper"]) {
        let _ = writeln!(text, "import {module}");
    }
    text.push('\n');
    let mut ranges = Vec::new();
    for (name, body) in theorems {
        let start = text.lines().count() + 1;
        text.push_str(body);
        let _ = writeln!(text, "#print axioms {name}\n");
        ranges.push((name.clone(), start, text.lines().count()));
    }
    (text, ranges)
}

/// Each theorem's verdict from `lean --json` messages: `Ok(axioms)` when it
/// elaborated without error and `#print axioms` reported, else the error.
pub fn parse_certification(
    messages: &[prove_sweep::Message],
    ranges: &[(String, usize, usize)],
) -> BTreeMap<String, Result<Vec<String>, String>> {
    let mut out = BTreeMap::new();
    for (name, start, end) in ranges {
        let inside: Vec<&prove_sweep::Message> = messages
            .iter()
            .filter(|m| m.line >= *start && m.line <= *end)
            .collect();
        if let Some(error) = inside.iter().find(|m| m.severity == "error") {
            out.insert(
                name.clone(),
                Err(error.data.lines().next().unwrap_or("").to_owned()),
            );
            continue;
        }
        let quoted = format!("'{name}'");
        let report = inside.iter().find(|m| m.data.starts_with(&quoted));
        out.insert(
            name.clone(),
            match report {
                None => Err("no #print axioms output".into()),
                Some(m) if m.data.contains("does not depend on any axioms") => Ok(Vec::new()),
                Some(m) => Ok(m
                    .data
                    .split_once('[')
                    .and_then(|(_, rest)| rest.split_once(']'))
                    .map(|(list, _)| {
                        list.split(',')
                            .map(|a| a.trim().to_owned())
                            .filter(|a| !a.is_empty())
                            .collect()
                    })
                    .unwrap_or_default()),
            },
        );
    }
    out
}

/// Re-elaborates every discovery from its theorem text (one Lean run) and
/// records the verdict; a discovery that fails or uses another axiom is
/// filtered.
pub fn certify(
    root: &Path,
    findings: &mut [Finding],
    statements: &BTreeMap<String, Statement>,
    vocabulary: &BTreeMap<String, Vocabulary>,
    heartbeats: u64,
) -> Result<(), String> {
    let chosen: Vec<usize> = (0..findings.len())
        .filter(|&i| findings[i].kind == Kind::Discovery)
        .collect();
    if chosen.is_empty() {
        return Ok(());
    }
    let mut modules = BTreeSet::new();
    let mut theorems = Vec::new();
    for (n, &i) in chosen.iter().enumerate() {
        let f = &findings[i];
        for id in f.premises.iter().chain([&f.trial.target]) {
            if let Some(v) = vocabulary.get(&statements[id].declaration) {
                modules.insert(v.module.clone());
            }
        }
        theorems.push((
            theorem_name(n),
            theorem_text(&theorem_name(n), &f.outcome, heartbeats),
        ));
    }
    let (text, ranges) = certification_text(&modules, &theorems);
    let directory = scratch_dir("truth-discover-certify");
    let path = directory.join("DiscoverCertify.lean");
    fs::create_dir_all(&directory)
        .and_then(|()| fs::write(&path, &text))
        .map_err(|error| format!("{}: {error}", path.display()))?;
    let timeout = Duration::from_secs(
        300 + 60 * chosen.len() as u64 + heartbeats / 1000 * chosen.len() as u64,
    );
    let done = run(
        lake_command(
            root,
            &[
                "env".into(),
                "lean".into(),
                "--json".into(),
                path.display().to_string(),
            ],
        ),
        timeout,
    );
    if keep_scratch() {
        eprintln!("discover: kept {}", path.display());
    } else {
        let _ = fs::remove_dir_all(&directory);
    }
    let done =
        done?.ok_or_else(|| format!("certification timed out after {}s", timeout.as_secs()))?;
    let verdicts = parse_certification(&prove_sweep::parse_messages(&done.stdout), &ranges);
    for (n, &i) in chosen.iter().enumerate() {
        let verdict = verdicts
            .get(&theorem_name(n))
            .cloned()
            .unwrap_or_else(|| Err("no verdict".into()));
        let finding = &mut findings[i];
        match &verdict {
            Err(message) => {
                finding.kind = Kind::Filtered;
                finding.filters.push((
                    "certification".into(),
                    format!("theorem text rejected: {message}"),
                ));
            }
            Ok(axioms) => {
                let forbidden = forbidden_axioms(axioms);
                if !forbidden.is_empty() {
                    finding.kind = Kind::Filtered;
                    finding.filters.push((
                        "axioms".into(),
                        format!("certified proof uses {}", forbidden.join(", ")),
                    ));
                }
            }
        }
        finding.certified = Some(verdict);
    }
    Ok(())
}

/// Settles each weakening after certification (text re-elaboration and the
/// axiom check), which runs on originals and weakenings alike: a certified
/// weaker discovery supersedes its original, which is then filtered; a
/// weakening that failed certification leaves its original eligible, flagged
/// with the reason (`weakening_rejected`).
pub fn suppress_weakened(findings: &mut [Finding]) {
    // (original label, weaker label, Ok(()) when certified, else the reason)
    let settled: Vec<(String, String, Result<(), String>)> = findings
        .iter()
        .filter_map(|f| {
            let original = f.trial.weakening.as_ref()?.2.clone();
            let verdict = match (&f.kind, &f.certified) {
                (Kind::Discovery, _) => Ok(()),
                (_, Some(_)) => Err(f
                    .filters
                    .last()
                    .map(|(filter, detail)| format!("{filter}: {detail}"))
                    .unwrap_or_else(|| "not certified".into())),
                // Never reached certification: no weaker discovery to settle.
                _ => return None,
            };
            Some((original, f.trial.label.clone(), verdict))
        })
        .collect();
    let superseded: BTreeSet<&String> = settled
        .iter()
        .filter(|(_, _, v)| v.is_ok())
        .map(|(o, _, _)| o)
        .collect();
    for (original, weaker, verdict) in &settled {
        let Some(f) = findings
            .iter_mut()
            .find(|f| &f.trial.label == original && f.kind == Kind::Discovery)
        else {
            continue;
        };
        match verdict {
            Ok(()) => {
                f.filters.push((
                    "weakened".into(),
                    format!("superseded by the weaker bundle {weaker}"),
                ));
                f.kind = Kind::Filtered;
            }
            Err(reason) if !superseded.contains(original) => f.filters.push((
                "weakening_rejected".into(),
                format!("the weaker bundle {weaker} failed certification ({reason}); kept"),
            )),
            Err(_) => {}
        }
    }
}

// --- Spec draft --------------------------------------------------------------------

fn toml_string(text: &str) -> String {
    format!(
        "\"{}\"",
        text.replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\n', " ")
    )
}

fn short(text: &str, max: usize) -> String {
    if text.chars().count() <= max {
        text.to_owned()
    } else {
        let mut cut: String = text.chars().take(max.saturating_sub(1)).collect();
        cut.push('…');
        cut
    }
}

/// The `argument_batch.py` spec draft for the discoveries (`batch` is the
/// results module, `TruthCore.Results.Discover.<Name>`): one argument per
/// discovery, proved by the Solution draft's theorem of the same index.
pub fn render_spec(
    batch: &str,
    findings: &[&Finding],
    statements: &BTreeMap<String, Statement>,
    sense_check: &SenseCheck,
    date: &str,
) -> String {
    let mut text = format!(
        "# Draft written by `truth discover` ({date}). NOT a corpus record: review every\n\
         # argument (semantic challenge of consequential bridges, docs/systematic-corpus-loop.md),\n\
         # move the Solution draft to {path}/Solution.lean, then run\n\
         #   python3 scripts/argument_batch.py challenge {path}/Solution.lean <theorems> --write\n\
         #   python3 scripts/argument_batch.py records <this spec> --write --fix\n\
         # Each argument is a conditional support option: proof validity, not premise warrant.\n\n\
         [batch]\nvocab = \"TruthCore\"\nresults = {}\n",
        toml_string(batch),
        path = batch.replace('.', "/"),
    );
    let mut labels = BTreeSet::new();
    for (n, finding) in findings.iter().enumerate() {
        let target = &statements[&finding.trial.target];
        // At most 88 characters: the generator labels the inference
        // "<label> (inference)", and labels are at most 100.
        let mut label = format!("{} (discovered derivation)", short(&target.label, 60));
        let mut k = 2;
        while !labels.insert(label.clone()) {
            // At most 88 characters: the generator labels the inference
            // "<label> (inference)", and labels are at most 100.
            label = format!("{} (discovered derivation {k})", short(&target.label, 60));
            k += 1;
        }
        let premise_labels: Vec<&str> = finding
            .premises
            .iter()
            .map(|id| statements[id].label.as_str())
            .collect();
        let mut meaning = format!(
            "Discovered by truth discover: {} follows from {}. Duper proof over the delta-expanded \
             statement definitions, kernel-checked; parameters are identified by name within one module or by sense tag.",
            target.label,
            premise_labels.join("; ")
        );
        if let Some(choice) = projection_flag(&finding.outcome) {
            let _ = write!(meaning, " Explicit {choice}.");
        }
        let _ = write!(
            text,
            "\n[[argument]]\nid = {}\nlabel = {}\ntheorem = {}\npremises = [{}]\nconclusion = {}\n\
             rule = \"Duper superposition proof over the delta-expanded definitions\"\nmeaning = {}\n\
             axioms = [\"propext\", \"Classical.choice\", \"Quot.sound\"]\n",
            toml_string(&format!("discover-{}", n + 1)),
            toml_string(&label),
            toml_string(&theorem_name(n)),
            finding
                .premises
                .iter()
                .map(|p| toml_string(p))
                .collect::<Vec<_>>()
                .join(", "),
            toml_string(&finding.trial.target),
            toml_string(&meaning),
        );
        let bridges: Vec<Value> = sense_check
            .mixing(&finding.premises, &finding.trial.target)
            .into_iter()
            .flat_map(|(_, _, b)| b)
            .collect();
        for bridge in bridges {
            let field = |k: &str| bridge[k].as_str().unwrap_or_default().to_owned();
            let _ = write!(
                text,
                "\n[[argument.sense_bridges]]\nterm = {}\nfrom = {}\nto = {}\nstatement_id = {}\n",
                toml_string(&field("term")),
                toml_string(&field("from")),
                toml_string(&field("to")),
                toml_string(&field("statement_id")),
            );
            if field("role") == "conclusion" {
                text.push_str("role = \"conclusion\"\n");
            }
        }
    }
    text
}

/// The Solution draft: a Lean module stating every discovery with its Duper proof.
pub fn render_solution(
    batch: &str,
    findings: &[&Finding],
    statements: &BTreeMap<String, Statement>,
    vocabulary: &BTreeMap<String, Vocabulary>,
    heartbeats: u64,
) -> String {
    let mut modules = BTreeSet::new();
    for f in findings {
        for id in f.premises.iter().chain([&f.trial.target]) {
            if let Some(v) = vocabulary.get(&statements[id].declaration) {
                modules.insert(v.module.clone());
            }
        }
    }
    let mut text = String::from("module\n\n");
    for module in &modules {
        let _ = writeln!(text, "public import {module}");
    }
    text.push_str("import Duper\n\n");
    text.push_str(
        "/-!\n# Discovered derivations (draft written by `truth discover`)\n\n\
         Each theorem was found by Duper over the delta-expanded statement definitions\n\
         and re-elaborated from this text; review before recording (docs/discover.md).\n-/\n\n\
         @[expose] public section\n\n",
    );
    let _ = writeln!(text, "namespace {batch}\n");
    for (n, f) in findings.iter().enumerate() {
        let target = &statements[&f.trial.target];
        // `set_option … in` goes before the doc comment, which belongs to the
        // theorem command.
        let theorem = theorem_text(&theorem_name(n), &f.outcome, heartbeats);
        let (option, rest) = theorem.split_once('\n').unwrap_or(("", &theorem));
        let _ = writeln!(
            text,
            "{option}\n/-- {} -/",
            target.label.replace("-/", "- /")
        );
        text.push_str(rest);
        text.push('\n');
    }
    let _ = writeln!(text, "end {batch}");
    text
}

// --- Report ------------------------------------------------------------------------

pub fn finding_json(finding: &Finding, statements: &BTreeMap<String, Statement>) -> Value {
    let named = |id: &String| {
        json!({"statement_id": id, "label": statements.get(id).map(|s| s.label.as_str()),
               "lean_declaration": statements.get(id).map(|s| s.declaration.as_str())})
    };
    json!({
        "label": finding.trial.label,
        "kind": finding.kind.name(),
        "target": named(&finding.trial.target),
        "candidates": finding.trial.premises,
        "premises": finding.premises.iter().map(named).collect::<Vec<_>>(),
        "filters": finding.filters.iter().map(|(f, d)| json!({"filter": f, "detail": d})).collect::<Vec<_>>(),
        "weakening": finding.trial.weakening.as_ref().map(|(from, to, of)| json!({"replaced": from, "by": to, "of": of})),
        "certified": finding.certified.as_ref().map(|v| match v {
            Ok(axioms) => json!({"ok": true, "axioms": axioms}),
            Err(message) => json!({"ok": false, "error": message}),
        }),
        "lean": finding.outcome,
    })
}

// --- Orchestration -------------------------------------------------------------------

/// Builds Duper and the library (Lake owns freshness).
pub fn build(root: &Path) -> Result<(), String> {
    let done = run(
        lake_command(root, &["build".into(), "Duper".into(), "TruthCore".into()]),
        Duration::from_secs(4 * 3600),
    )?
    .ok_or("lake build timed out")?;
    if done.success {
        Ok(())
    } else {
        Err(format!(
            "lake build failed: {}",
            done.stderr
                .lines()
                .chain(done.stdout.lines())
                .find(|l| l.contains("error"))
                .unwrap_or("")
        ))
    }
}

/// The vocabulary of `declarations` (one `StatementConstants.lean` run).
pub fn export_vocabulary(
    root: &Path,
    declarations: &BTreeSet<&str>,
) -> Result<BTreeMap<String, Vocabulary>, String> {
    let stdout = export_constants(root, declarations, false)?;
    let value: Value = serde_json::from_str(stdout.trim())
        .map_err(|error| format!("vocabulary export is not JSON: {error}"))?;
    parse_vocabulary(&value)
}

/// The raw `StatementConstants.lean` output for `declarations` (one Lean
/// run, after `lake build`); with `closure`, also a row for every TruthCore
/// constant reachable from them (`--closure`, `truth definitions residue`).
pub fn export_constants(
    root: &Path,
    declarations: &BTreeSet<&str>,
    closure: bool,
) -> Result<String, String> {
    let directory = scratch_dir("truth-discover-vocabulary");
    let path = directory.join("declarations.txt");
    let list: String = declarations.iter().map(|d| format!("{d}\n")).collect();
    fs::create_dir_all(&directory)
        .and_then(|()| fs::write(&path, list))
        .map_err(|error| format!("{}: {error}", path.display()))?;
    let mut tail: Vec<String> = vec![
        "env".into(),
        "lean".into(),
        "--run".into(),
        CONSTANTS_LEAN.into(),
        "TruthCore".into(),
        path.display().to_string(),
    ];
    if closure {
        tail.push("--closure".into());
    }
    let done = run(lake_command(root, &tail), Duration::from_secs(1800));
    let _ = fs::remove_dir_all(&directory);
    let done = done?.ok_or("vocabulary export timed out")?;
    if !done.success {
        return Err(format!("vocabulary export failed: {}", done.stderr.trim()));
    }
    Ok(done.stdout)
}

/// A run, with the statements and vocabulary it used.
pub type Discovered = (
    Run,
    BTreeMap<String, Statement>,
    BTreeMap<String, Vocabulary>,
);

/// Everything a run produced.
pub struct Run {
    pub findings: Vec<Finding>,
    /// Targets skipped before search, with the reason.
    pub skipped: Vec<(String, String)>,
    pub trials: usize,
    pub seconds: u64,
}

/// The whole engine on `targets`: retrieval, search, classification, the
/// weakening round and certification.
pub fn discover(
    root: &Path,
    corpus: &Corpus,
    report: &Value,
    targets: &[String],
    options: &Options,
    progress: &(dyn Fn(&str) + Sync),
) -> Result<Discovered, String> {
    let started = Instant::now();
    let statements = statements(corpus);
    let in_scope = |declaration: &str| {
        options.modules.is_empty()
            || options
                .modules
                .iter()
                .any(|m| declaration.starts_with(m.as_str()))
    };
    let exact = !options.premises.is_empty();
    let pool: Vec<&Statement> = if exact {
        options
            .premises
            .iter()
            .map(|id| {
                let statement = statements
                    .get(id)
                    .filter(|s| !s.declaration.trim().is_empty())
                    .ok_or_else(|| format!("explicit premise {id}: no lean_declaration"))?;
                if targets.contains(id) {
                    return Err(format!("target is also a premise: {id}"));
                }
                Ok(statement)
            })
            .collect::<Result<_, _>>()?
    } else {
        let pool_set = pool_ids(corpus, report, options.pool);
        statements
            .values()
            .filter(|s| pool_set.contains(&s.id) && in_scope(&s.declaration))
            .collect()
    };
    let mut skipped = Vec::new();
    let mut chosen = Vec::new();
    for id in targets {
        match statements.get(id) {
            None => skipped.push((id.clone(), "no lean_declaration".to_owned())),
            Some(s) if !in_scope(&s.declaration) => {}
            Some(s) => chosen.push(s),
        }
    }
    let declarations: BTreeSet<&str> = pool
        .iter()
        .chain(chosen.iter())
        .map(|s| s.declaration.as_str())
        .collect();
    if exact {
        progress(&format!(
            "{} targets, exact bundle ({} premises); exporting declarations",
            chosen.len(),
            pool.len()
        ));
    } else {
        progress(&format!(
            "{} targets, pool {} ({} statements); exporting vocabulary",
            chosen.len(),
            options.pool.name(),
            pool.len()
        ));
    }
    let mut vocabulary = export_vocabulary(root, &declarations)?;
    if exact {
        for premise in &pool {
            if !vocabulary.contains_key(&premise.declaration) {
                return Err(format!(
                    "explicit premise {}: {} is not in the built library",
                    premise.id, premise.declaration
                ));
            }
        }
    } else {
        close_vocabulary(root, &mut vocabulary)?;
    }
    let weaker = weaker_siblings(corpus);
    let tags = SenseTags::new(corpus)?;
    let mut trials = Vec::new();
    for target in &chosen {
        if !vocabulary.contains_key(&target.declaration) {
            skipped.push((
                target.id.clone(),
                "declaration not in the built library".into(),
            ));
            continue;
        }
        let mut premises: Vec<String> = if exact {
            options.premises.clone()
        } else {
            rank(
                target,
                &pool,
                &vocabulary,
                &weaker,
                &tags,
                options.candidates,
            )
            .into_iter()
            .map(|candidate| candidate.id)
            .collect()
        };
        if premises.is_empty() {
            skipped.push((
                target.id.clone(),
                "no candidate premise shares its vocabulary".into(),
            ));
            continue;
        }
        // Different senses of one term on the target and a candidate: the
        // registered bridge statements join as optional premises in ranked
        // retrieval only. An exact bundle must name its bridges explicitly.
        let mut bridges = Vec::new();
        if !exact {
            for id in &premises {
                for b in tags.bridge_statements(&target.declaration, &statements[id].declaration) {
                    if b != target.id
                        && statements.contains_key(&b)
                        && !premises.contains(&b)
                        && !bridges.contains(&b)
                    {
                        bridges.push(b);
                    }
                }
            }
        }
        premises.extend(bridges.iter().cloned());
        trials.push(Trial {
            label: format!("t{}", trials.len() + 1),
            target: target.id.clone(),
            premises,
            weakening: None,
            sense_bridges: bridges,
        });
    }
    let missing: BTreeSet<&str> = trials
        .iter()
        .flat_map(|t| t.premises.iter())
        .map(|id| statements[id].declaration.as_str())
        .filter(|d| !vocabulary.contains_key(*d))
        .collect();
    if !missing.is_empty() {
        vocabulary.extend(export_vocabulary(root, &missing)?);
    }
    trials.retain(|t| {
        t.premises
            .iter()
            .all(|p| vocabulary.contains_key(&statements[p].declaration))
    });
    let discover = fs::read_to_string(root.join(DISCOVER_LEAN))
        .map_err(|error| format!("{DISCOVER_LEAN}: {error}"))?;
    let tell = |done: usize, total: usize| {
        progress(&format!(
            "search batch {done}/{total} ({}s)",
            started.elapsed().as_secs()
        ));
    };
    progress(&format!("searching {} goals", trials.len()));
    let outcomes = search_all(
        root,
        &discover,
        &trials,
        &statements,
        &vocabulary,
        options,
        &tags,
        &tell,
    );
    let graph = Graph::from_corpus(corpus);
    let sense_check = SenseCheck::new(corpus)?;
    let mut findings: Vec<Finding> = trials
        .iter()
        .map(|t| classify(t, &outcomes[&t.label], &graph, &sense_check))
        .collect();
    dedupe_incompatibilities(&mut findings);
    // Weakening: replace one premise of a discovery by a weaker sibling.
    let mut weakened = Vec::new();
    for finding in findings.iter().filter(|f| f.kind == Kind::Discovery) {
        for premise in &finding.premises {
            for weak in weaker.get(premise).into_iter().flatten() {
                if !statements.contains_key(weak) || finding.premises.contains(weak) {
                    continue;
                }
                let premises = finding
                    .premises
                    .iter()
                    .map(|p| {
                        if p == premise {
                            weak.clone()
                        } else {
                            p.clone()
                        }
                    })
                    .collect();
                weakened.push(Trial {
                    label: format!("{}w{}", finding.trial.label, weakened.len() + 1),
                    target: finding.trial.target.clone(),
                    premises,
                    weakening: Some((premise.clone(), weak.clone(), finding.trial.label.clone())),
                    sense_bridges: Vec::new(),
                });
            }
        }
    }
    if !weakened.is_empty() {
        let mut extra: BTreeSet<&str> = BTreeSet::new();
        for t in &weakened {
            for id in &t.premises {
                if !vocabulary.contains_key(&statements[id].declaration) {
                    extra.insert(statements[id].declaration.as_str());
                }
            }
        }
        if !extra.is_empty() {
            vocabulary.extend(export_vocabulary(root, &extra)?);
        }
        weakened.retain(|t| {
            t.premises
                .iter()
                .all(|p| vocabulary.contains_key(&statements[p].declaration))
        });
        progress(&format!("weakening: {} goals", weakened.len()));
        let outcomes = search_all(
            root,
            &discover,
            &weakened,
            &statements,
            &vocabulary,
            &Options {
                bridges: false,
                ..options.clone()
            },
            &tags,
            &tell,
        );
        for t in &weakened {
            let mut finding = classify(t, &outcomes[&t.label], &graph, &sense_check);
            // The original stays eligible until its weakening is certified
            // (`suppress_weakened`, after `certify`).
            if finding.kind != Kind::Discovery && finding.kind != Kind::Incompatibility {
                finding.kind = if finding.kind == Kind::Error {
                    Kind::Error
                } else {
                    Kind::Unresolved
                };
            }
            findings.push(finding);
        }
    }
    progress("certifying discoveries");
    certify(
        root,
        &mut findings,
        &statements,
        &vocabulary,
        options.heartbeats,
    )?;
    suppress_weakened(&mut findings);
    let trials_count = findings.len();
    Ok((
        Run {
            findings,
            skipped,
            trials: trials_count,
            seconds: started.elapsed().as_secs(),
        },
        statements,
        vocabulary,
    ))
}

// --- Missing bridges ----------------------------------------------------------------

/// A missing bridge: the candidate proposition that would connect two
/// vocabularies, and the goals it unlocks.
#[derive(Clone, Debug, PartialEq)]
pub struct Bridge {
    /// `Declaration.binder` (or `.binder.field`) of the antecedent relation.
    pub from: String,
    /// The same for the consequent relation.
    pub to: String,
    /// Arguments fixed to an element binder (`esse`).
    pub fixed: Vec<String>,
    /// The bridge as Lean prints it in its first goal's context.
    pub text: String,
    /// Targets it unlocks, and the goal labels.
    pub targets: BTreeSet<String>,
    pub goals: Vec<String>,
    /// Premises the unlocked proofs used besides the bridge.
    pub premises: BTreeSet<String>,
    /// Binders only the bridge mentions (a fixed argument from a statement the
    /// proof does not use): the bridge then also assumes such an element.
    pub assumed_binders: BTreeSet<String>,
    /// Some unlocked goal identified a carrier or structure across modules by
    /// name: the bridge then also needs a tag or bridge for that domain.
    pub domain_identified_by_name: bool,
    /// Those identifications (`A.B = C.B`).
    pub domain_identifications: BTreeSet<String>,
    /// The antecedent is the target's whole conjunctive antecedent
    /// (`∀ g, A g → B g → … → q g`), tried in place of the single-conjunct
    /// bridges `∀ g, A g → q g` (#1819).
    pub conjunctive: bool,
    /// The conjunct relations whose single-conjunct bridges it replaces.
    pub replaces_single_conjuncts: BTreeSet<String>,
    /// One conjunct of a conjunctive antecedent made sufficient, reported
    /// only because no conjunctive bridge passed; ranked after the others.
    pub single_conjunct: bool,
}

/// Notes on a ranked bridge's form, for the text report: a conjunctive
/// antecedent and the single-conjunct bridges it stands for.
pub fn bridge_notes(bridge: &Bridge) -> Vec<String> {
    if bridge.single_conjunct {
        return vec![
            "one conjunct of a conjunctive antecedent made sufficient; reported (demoted) because no conjunctive bridge passed"
                .to_owned(),
        ];
    }
    if !bridge.conjunctive {
        return Vec::new();
    }
    let names: Vec<&str> = bridge
        .replaces_single_conjuncts
        .iter()
        .map(String::as_str)
        .collect();
    vec![format!(
        "conjunctive antecedent; single-conjunct bridges from {} were not tried (each is stronger and uninformative)",
        names.join(", ")
    )]
}

/// The qualifications of a ranked bridge, for the text report: the elements it
/// assumes and the domains its goals identified by name only. Empty for an
/// unqualified bridge. (A bridge's form is noted by [`bridge_notes`].)
pub fn bridge_qualifications(bridge: &Bridge) -> Vec<String> {
    let mut out = Vec::new();
    if !bridge.assumed_binders.is_empty() {
        let names: Vec<&str> = bridge.assumed_binders.iter().map(String::as_str).collect();
        out.push(format!(
            "assumes an element no used statement introduces: {}",
            names.join(", ")
        ));
    }
    if bridge.domain_identified_by_name {
        let names: Vec<&str> = bridge
            .domain_identifications
            .iter()
            .map(String::as_str)
            .collect();
        out.push(format!(
            "identified across modules by name only (needs a sense tag or a bridge): {}",
            names.join("; ")
        ));
    }
    out
}

/// The missing bridges of failed goals, ranked by the number of targets they
/// unlock, then goals, then name; single-conjunct bridges last.
pub fn rank_bridges(findings: &[Finding]) -> Vec<Bridge> {
    let mut by_key: BTreeMap<(String, String, Vec<String>), Bridge> = BTreeMap::new();
    for finding in findings {
        for b in finding.outcome["bridges"].as_array().into_iter().flatten() {
            let text = |k: &str| b[k].as_str().unwrap_or_default().to_owned();
            let fixed: Vec<String> = b["fixed"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect();
            let entry = by_key
                .entry((text("from"), text("to"), fixed.clone()))
                .or_insert_with(|| Bridge {
                    from: text("from"),
                    to: text("to"),
                    fixed,
                    text: text("text"),
                    targets: BTreeSet::new(),
                    goals: Vec::new(),
                    premises: BTreeSet::new(),
                    assumed_binders: BTreeSet::new(),
                    domain_identified_by_name: false,
                    domain_identifications: BTreeSet::new(),
                    conjunctive: b["conjunctive"].as_bool() == Some(true),
                    replaces_single_conjuncts: b["replaces_single_conjuncts"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter_map(Value::as_str)
                        .map(str::to_owned)
                        .collect(),
                    single_conjunct: b["single_conjunct"].as_bool() == Some(true),
                });
            entry.targets.insert(finding.trial.target.clone());
            entry.goals.push(finding.trial.label.clone());
            entry.domain_identified_by_name |= domain_flag(b).is_some();
            entry.domain_identifications.extend(
                b["domain_identified_by_name"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .map(str::to_owned),
            );
            entry.assumed_binders.extend(
                b["assumed_binders"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .map(str::to_owned),
            );
            for i in indices(&b["used"]) {
                if let Some(p) = finding.trial.premises.get(i) {
                    entry.premises.insert(p.clone());
                }
            }
        }
    }
    let mut rows: Vec<Bridge> = by_key.into_values().collect();
    rows.sort_by(|a, b| {
        a.single_conjunct
            .cmp(&b.single_conjunct)
            .then(b.targets.len().cmp(&a.targets.len()))
            .then(b.goals.len().cmp(&a.goals.len()))
            .then_with(|| (&a.from, &a.to).cmp(&(&b.from, &b.to)))
    });
    rows
}

pub fn bridge_json(bridge: &Bridge) -> Value {
    json!({
        "from": bridge.from, "to": bridge.to, "fixed": bridge.fixed,
        "proposition": bridge.text,
        "unlocks_targets": bridge.targets, "goals": bridge.goals,
        "with_premises": bridge.premises,
        "assumed_binders": bridge.assumed_binders,
        "domain_identified_by_name": bridge.domain_identified_by_name,
        "domain_identifications": bridge.domain_identifications,
        "conjunctive": bridge.conjunctive,
        "replaces_single_conjuncts": bridge.replaces_single_conjuncts,
        "single_conjunct": bridge.single_conjunct,
        "status": "candidate proposition: a research question, not a premise of any record",
    })
}

/// Replaces each declaration's constants by their transitive closure through
/// the project constants they mention (exported in up to three more rounds),
/// so that ranking sees the vocabulary a statement reaches when unfolded.
pub fn close_vocabulary(
    root: &Path,
    vocabulary: &mut BTreeMap<String, Vocabulary>,
) -> Result<(), String> {
    for _ in 0..3 {
        let missing: BTreeSet<String> = vocabulary
            .values()
            .flat_map(|v| v.constants.iter())
            .filter(|c| c.starts_with("TruthCore.") && !vocabulary.contains_key(*c))
            .cloned()
            .collect();
        if missing.is_empty() {
            break;
        }
        let missing: BTreeSet<&str> = missing.iter().map(String::as_str).collect();
        let exported = export_vocabulary(root, &missing)?;
        for name in &missing {
            // Unexportable constants still count as reached (no further closure).
            vocabulary.entry((*name).to_owned()).or_default();
        }
        vocabulary.extend(exported);
    }
    let closed = transitive_constants(vocabulary);
    for (name, constants) in closed {
        if let Some(v) = vocabulary.get_mut(&name) {
            v.constants = constants;
        }
    }
    Ok(())
}

/// Each declaration's constants, closed under the constants they mention.
pub fn transitive_constants(
    vocabulary: &BTreeMap<String, Vocabulary>,
) -> BTreeMap<String, BTreeSet<String>> {
    vocabulary
        .iter()
        .map(|(name, v)| {
            let mut seen: BTreeSet<String> = BTreeSet::new();
            let mut stack: Vec<&String> = v.constants.iter().collect();
            while let Some(c) = stack.pop() {
                if c != name
                    && seen.insert(c.clone())
                    && let Some(next) = vocabulary.get(c)
                {
                    stack.extend(next.constants.iter());
                }
            }
            (name.clone(), seen)
        })
        .collect()
}

#[cfg(test)]
mod tests;

/// Keeps the first incompatibility of each inconsistent core; later goals
/// that hit the same core are filtered as duplicates.
pub fn dedupe_incompatibilities(findings: &mut [Finding]) {
    let mut seen: BTreeSet<Vec<String>> = BTreeSet::new();
    for finding in findings
        .iter_mut()
        .filter(|f| f.kind == Kind::Incompatibility)
    {
        let mut core = finding.premises.clone();
        core.sort();
        if !seen.insert(core) {
            finding.kind = Kind::Filtered;
            finding.filters.push((
                "duplicate".into(),
                "same inconsistent core as an earlier goal".into(),
            ));
        }
    }
}
