//! Exhaustive explicit-reference retrieval. Edges record mentions, never equivalence,
//! entailment, source fidelity, or philosophical warrant.
use crate::{Corpus, notes};
use serde::Serialize;
use serde_json::Value;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    path::Path,
};

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct Node {
    pub key: String,
    pub kind: String,
    pub id: String,
    pub label: String,
    pub path: String,
    pub content: Value,
}
#[derive(Clone, Debug, Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct Provenance {
    pub path: String,
    /// JSON pointer, or a note section anchor. Object-key references end in /@key.
    pub field: String,
    /// One-based text line, when the reference is in text.
    pub line: Option<usize>,
    /// One-based line within a JSON string; never a physical source-file line.
    pub text_line: Option<usize>,
    pub mention: String,
    pub how: String,
}
#[derive(Clone, Debug, Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edge {
    pub from: String,
    pub to: String,
    pub relation: String,
    pub provenance: Provenance,
}
#[derive(Clone, Debug, Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct Unresolved {
    pub from: String,
    pub provenance: Provenance,
}
#[derive(Clone, Debug, Serialize)]
pub struct Step {
    pub predecessor: String,
    pub edge: usize,
    pub reverse: bool,
}
#[derive(Clone, Debug, Serialize)]
pub struct Expansion {
    pub seeds: Vec<String>,
    pub unresolved_seeds: Vec<String>,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    /// Deterministic shortest explanation tree; edge indices address `edges`.
    pub predecessors: BTreeMap<String, Step>,
    pub unresolved: Vec<Unresolved>,
    pub availability: Availability,
}
#[derive(Clone, Debug, Serialize)]
pub struct Availability {
    pub corpus: bool,
    pub notes: bool,
    pub issue_snapshot: bool,
    pub boundary: String,
}
/// A graph built once from loaded authority records and explicit note mentions.
pub struct EvidenceGraph {
    nodes: BTreeMap<String, Node>,
    aliases: BTreeMap<String, BTreeSet<String>>,
    edges: Vec<Edge>,
    adjacency: BTreeMap<String, Vec<usize>>,
    unresolved: Vec<Unresolved>,
    availability: Availability,
}
impl EvidenceGraph {
    /// `snapshot` accepts a gh JSON array or an object with `items`, `issues`,
    /// and/or `pull_requests` arrays. Nothing is fetched over the network.
    pub fn build(root: &Path, corpus: &Corpus, snapshot: Option<&Value>) -> Result<Self, String> {
        let mut graph = Self {
            nodes: BTreeMap::new(), aliases: BTreeMap::new(), edges: Vec::new(),
            adjacency: BTreeMap::new(), unresolved: Vec::new(),
            availability: Availability { corpus: true, notes: root.join("docs").is_dir(), issue_snapshot: snapshot.is_some(), boundary: "explicit references only; a mention is not equivalence, entailment, verification or warrant; absent offline issue history remains unknown".into() },
        };
        let mut documents = Vec::new();
        for &kind in crate::KINDS {
            for record in corpus.entries(kind) {
                let Some(id) = record.fields.get("id").and_then(Value::as_str) else {
                    continue;
                };
                let value = Value::Object(record.fields.clone());
                let key = graph.add_node(kind, id, &record.path, &value);
                if kind == "disambiguations"
                    && let Some(senses) = value.get("senses").and_then(Value::as_array)
                {
                    for (index, sense) in senses.iter().enumerate() {
                        if let Some(id) = sense.get("id").and_then(Value::as_str) {
                            let sense_key = graph.add_node("senses", id, &record.path, sense);
                            graph.edges.push(Edge {
                                from: key.clone(),
                                to: sense_key.clone(),
                                relation: "contains_sense".into(),
                                provenance: Provenance {
                                    path: record.path.clone(),
                                    field: format!("/senses/{index}"),
                                    text_line: None,
                                    line: None,
                                    mention: id.into(),
                                    how: "containment".into(),
                                },
                            });
                            documents.push((sense_key, record.path.clone(), sense.clone()));
                        }
                    }
                }
                documents.push((key, record.path.clone(), value));
            }
        }
        let senses = crate::lexicon::Senses::new(corpus);
        if let Some(lexicon) = crate::lexicon::Lexicon::load(root, corpus, &senses)? {
            for entry in lexicon.entries {
                let value = Value::Object(entry.fields);
                let key = graph.add_node("lexicon", &entry.id, &entry.path, &value);
                documents.push((key, entry.path, value));
            }
        }
        if let Some(snapshot) = snapshot {
            let mut arrays = Vec::new();
            if let Some(items) = snapshot.as_array() {
                arrays.push(("", items));
            } else if let Some(object) = snapshot.as_object() {
                for name in ["items", "issues", "pull_requests"] {
                    if let Some(items) = object.get(name).and_then(Value::as_array) {
                        arrays.push((name, items));
                    }
                }
            }
            if arrays.is_empty() {
                return Err(
                    "issue snapshot must be an array or contain items/issues/pull_requests arrays"
                        .into(),
                );
            }
            // Bare PR numbers belong to this corpus. A mixed snapshot needs
            // qualified URLs to distinguish deliveries with the same number.
            use crate::brief::issue::{checkout_repository, github_item, matches_checkout};
            let repositories: BTreeSet<_> = arrays
                .iter()
                .flat_map(|(_, items)| items.iter())
                .map(|item| {
                    item.get("url")?
                        .as_str()
                        .and_then(github_item)
                        .map(|(repo, _)| repo.to_ascii_lowercase())
                })
                .collect();
            let checkout = checkout_repository(root);
            let scoped_pr_numbers = repositories.len() == 1
                && repositories
                    .first()
                    .and_then(Option::as_deref)
                    .is_some_and(|repo| matches_checkout(repo, checkout.as_deref()));
            for (container, items) in arrays {
                for (index, item) in items.iter().enumerate() {
                    let Some(number) = item
                        .get("number")
                        .and_then(Value::as_u64)
                        .filter(|n| *n > 0)
                    else {
                        return Err(format!(
                            "snapshot {container}/{index} needs a positive integer number"
                        ));
                    };
                    let is_pr = container == "pull_requests"
                        || item
                            .get("url")
                            .and_then(Value::as_str)
                            .is_some_and(|url| url.contains("/pull/"))
                        || item.get("mergedAt").is_some()
                        || item.get("headRefName").is_some();
                    let kind = if is_pr { "pull_requests" } else { "issues" };
                    let path = format!("offline-snapshot/{container}/{index}");
                    let key = graph.add_node(kind, &number.to_string(), &path, item);
                    graph.alias(&format!("#{number}"), &key);
                    if is_pr && scoped_pr_numbers {
                        graph.alias(&format!("PR-{number}"), &key);
                    }
                    if let Some(url) = item.get("url").and_then(Value::as_str) {
                        graph.alias(url, &key);
                    }
                    documents.push((key, path, item.clone()));
                }
            }
        }
        let mut lookup = notes::Lookup::of_corpus(corpus);
        for node in graph
            .nodes
            .values()
            .filter(|node| matches!(node.kind.as_str(), "lexicon" | "senses"))
        {
            if let Some(fields) = node.content.as_object() {
                lookup.add(&node.kind, &node.path, fields);
            }
        }
        let mut sections = Vec::new();
        for (path, bytes) in notes::read_all(root)? {
            let text = std::str::from_utf8(&bytes).map_err(|error| format!("{path}: {error}"))?;
            let note = notes::parse(&path, text);
            for section in &note.sections {
                let id = note.key(section);
                let key = graph.add_node(
                    "notes",
                    &id,
                    &path,
                    &serde_json::json!({"label":section.heading,"body":section.body,"line":section.line,"anchor":section.anchor}),
                );
                graph.alias(&id, &key);
                sections.push((key, path.clone(), section.clone()));
            }
        }
        for (key, path, value) in &documents {
            graph.scan_json(key, path, value, "", &lookup);
        }
        for (key, path, section) in sections {
            let (links, unresolved) = lookup.links(&section);
            for link in links {
                let to = format!("{}:{}", link.kind, link.id);
                graph.edges.push(Edge {
                    from: key.clone(),
                    to,
                    relation: "mentions".into(),
                    provenance: Provenance {
                        path: path.clone(),
                        field: section.anchor.clone(),
                        text_line: None,
                        line: Some(link.line),
                        mention: link.mention,
                        how: link.how.as_str().into(),
                    },
                });
            }
            for link in unresolved {
                graph.unresolved.push(Unresolved {
                    from: key.clone(),
                    provenance: Provenance {
                        path: path.clone(),
                        field: section.anchor.clone(),
                        text_line: None,
                        line: Some(link.line),
                        mention: link.mention,
                        how: link.how.as_str().into(),
                    },
                });
            }
            graph.scan_text(
                &key,
                &path,
                &section.anchor,
                &section.heading,
                Some(section.line),
            );
            graph.scan_text(
                &key,
                &path,
                &section.anchor,
                &section.body,
                Some(section.line + usize::from(section.level > 0)),
            );
        }
        // Several explicit resolvers can recognize one occurrence. Retain a
        // single canonical edge for that occurrence, not one per mechanism.
        graph
            .edges
            .sort_by(|a, b| occurrence(a).cmp(&occurrence(b)).then_with(|| a.cmp(b)));
        graph.edges.dedup_by(|a, b| occurrence(a) == occurrence(b));
        graph.edges.sort();
        graph.unresolved.sort();
        graph.unresolved.dedup();
        for (index, edge) in graph.edges.iter().enumerate() {
            graph
                .adjacency
                .entry(edge.from.clone())
                .or_default()
                .push(index);
            graph
                .adjacency
                .entry(edge.to.clone())
                .or_default()
                .push(index);
        }
        Ok(graph)
    }
    fn alias(&mut self, alias: &str, key: &str) {
        self.aliases
            .entry(alias.into())
            .or_default()
            .insert(key.into());
    }
    fn add_node(&mut self, kind: &str, id: &str, path: &str, value: &Value) -> String {
        let key = format!("{kind}:{id}");
        let label = value
            .get("label")
            .or_else(|| value.get("title"))
            .and_then(Value::as_str)
            .unwrap_or(id)
            .to_owned();
        self.nodes.insert(
            key.clone(),
            Node {
                key: key.clone(),
                kind: kind.into(),
                id: id.into(),
                label,
                path: path.into(),
                content: value.clone(),
            },
        );
        for alias in [
            Some(id),
            Some(key.as_str()),
            Some(path),
            value.get("legacy_id").and_then(Value::as_str),
            value.get("label").and_then(Value::as_str),
        ]
        .into_iter()
        .flatten()
        {
            self.alias(alias, &key);
        }
        key
    }
    pub fn resolve(&self, reference: &str) -> Vec<String> {
        self.aliases
            .get(reference)
            .map(|keys| keys.iter().cloned().collect())
            .unwrap_or_default()
    }
    /// Resolve explicit references embedded in a query. Exact whole-record
    /// labels and inline-code labels use the existing note mention rules;
    /// prose word overlap never supplies a seed. URL fragments retain the
    /// full host/repository identity of the offline snapshot URL.
    pub fn query_references(&self, text: &str) -> Vec<String> {
        let mut found: BTreeSet<String> = self.resolve(text).into_iter().collect();
        let section = notes::Section {
            anchor: String::new(),
            heading: String::new(),
            level: 0,
            line: 1,
            body: text.into(),
        };
        for mention in notes::mentions(&section) {
            if mention.label {
                found.extend(self.resolve(&mention.text));
            } else {
                found.extend(self.explicit_targets(&mention.text));
            }
        }
        for token in text.split(|c: char| {
            c.is_whitespace()
                || matches!(
                    c,
                    '`' | '"' | '\'' | '(' | ')' | '[' | ']' | '<' | '>' | ',' | ';'
                )
        }) {
            let token = token.trim_end_matches(['.', ':', '!']);
            found.extend(self.explicit_targets(token));
            if token.starts_with("https://")
                && (token.contains("/issues/") || token.contains("/pull/"))
            {
                found.extend(self.resolve(token.split('#').next().unwrap_or(token)));
            }
        }
        found.into_iter().collect()
    }
    pub fn nodes(&self) -> &BTreeMap<String, Node> {
        &self.nodes
    }
    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }
    fn explicit_targets(&self, text: &str) -> Vec<String> {
        self.resolve(text)
            .into_iter()
            .filter(|key| {
                self.nodes.get(key).is_some_and(|node| {
                    (text == node.id && !matches!(node.kind.as_str(), "issues" | "pull_requests"))
                        || text == node.key
                        || text == node.path
                        || text.starts_with("docs/")
                        || text.starts_with("https://")
                        || text.starts_with('#')
                        || (node.kind == "pull_requests" && text.starts_with("PR-"))
                        || node.kind == "senses"
                        || text.starts_with("STMT-")
                        || text.starts_with("DEF-")
                        || text.starts_with("DISAMB-")
                        || text.starts_with("ATTEMPT-")
                })
            })
            .collect()
    }
    fn scan_json(
        &mut self,
        from: &str,
        path: &str,
        value: &Value,
        field: &str,
        lookup: &notes::Lookup,
    ) {
        // An explicit stack keeps arbitrarily nested decoded values off the call stack.
        let mut pending = vec![(field.to_owned(), value)];
        while let Some((field, value)) = pending.pop() {
            match value {
                Value::Object(object) => {
                    for (key, value) in object.iter().rev() {
                        let pointer =
                            format!("{field}/{}", key.replace('~', "~0").replace('/', "~1"));
                        self.scan_string(from, path, &format!("{pointer}/@key"), key, lookup);
                        // Identity is registration, not an outgoing semantic reference.
                        if !field.is_empty() || (key != "id" && key != "legacy_id") {
                            pending.push((pointer, value));
                        }
                    }
                }
                Value::Array(array) => {
                    for (index, value) in array.iter().enumerate().rev() {
                        pending.push((format!("{field}/{index}"), value));
                    }
                }
                Value::String(text) => self.scan_string(from, path, &field, text, lookup),
                _ => {}
            }
        }
    }
    fn scan_string(
        &mut self,
        from: &str,
        path: &str,
        field: &str,
        text: &str,
        lookup: &notes::Lookup,
    ) {
        let edge_start = self.edges.len();
        let unresolved_start = self.unresolved.len();
        let exact = self.explicit_targets(text);
        if !exact.is_empty() {
            for to in exact {
                self.reference(from, &to, path, field, text, "exact", None);
            }
            return;
        }
        let section = notes::Section {
            anchor: String::new(),
            heading: String::new(),
            level: 0,
            line: 1,
            body: text.into(),
        };
        let (links, unresolved) = lookup.links(&section);
        for link in links {
            self.reference(
                from,
                &format!("{}:{}", link.kind, link.id),
                path,
                field,
                &link.mention,
                link.how.as_str(),
                Some(link.line),
            );
        }
        for link in unresolved {
            self.unresolved.push(Unresolved {
                from: from.into(),
                provenance: Provenance {
                    path: path.into(),
                    field: field.into(),
                    text_line: None,
                    line: Some(link.line),
                    mention: link.mention,
                    how: link.how.as_str().into(),
                },
            });
        }
        self.scan_text(from, path, field, text, Some(1));
        for edge in &mut self.edges[edge_start..] {
            edge.provenance.text_line = edge.provenance.line.take();
        }
        for link in &mut self.unresolved[unresolved_start..] {
            link.provenance.text_line = link.provenance.line.take();
        }
    }
    // Scanner event fields directly become edge provenance; keep construction in one place.
    #[allow(clippy::too_many_arguments)]
    fn reference(
        &mut self,
        from: &str,
        to: &str,
        path: &str,
        field: &str,
        mention: &str,
        how: &str,
        line: Option<usize>,
    ) {
        {
            self.edges.push(Edge {
                from: from.into(),
                to: to.into(),
                relation: "references".into(),
                provenance: Provenance {
                    path: path.into(),
                    field: field.into(),
                    line,
                    text_line: None,
                    mention: mention.into(),
                    how: how.into(),
                },
            });
        }
    }
    fn scan_text(&mut self, from: &str, path: &str, field: &str, text: &str, start: Option<usize>) {
        for (offset, line) in text.lines().enumerate() {
            // Exact tokens augment the note resolver for sense labels, note links,
            // URLs and offline issue references. No vocabulary or similarity edges.
            for token in line.split(|c: char| {
                c.is_whitespace()
                    || matches!(
                        c,
                        '`' | '"' | '\'' | '(' | ')' | '[' | ']' | '<' | '>' | ',' | ';'
                    )
            }) {
                let token = token.trim_end_matches(['.', ':', '!']);
                if token.starts_with("https://")
                    && (token.contains("/issues/") || token.contains("/pull/"))
                {
                    let base = token.split('#').next().unwrap_or(token);
                    let targets = self.resolve(base);
                    if targets.is_empty() {
                        self.unresolved.push(Unresolved {
                            from: from.into(),
                            provenance: Provenance {
                                path: path.into(),
                                field: field.into(),
                                text_line: None,
                                line: start.map(|n| n + offset),
                                mention: token.into(),
                                how: "issue_url".into(),
                            },
                        });
                    }
                    for to in targets {
                        self.reference(
                            from,
                            &to,
                            path,
                            field,
                            token,
                            "issue_url",
                            start.map(|n| n + offset),
                        );
                    }
                }
                let relative = note_target(path, token);
                if let Some(target) = &relative {
                    let targets = self.resolve(target);
                    if targets.is_empty() {
                        self.unresolved.push(Unresolved {
                            from: from.into(),
                            provenance: Provenance {
                                path: path.into(),
                                field: field.into(),
                                text_line: None,
                                line: start.map(|n| n + offset),
                                mention: token.into(),
                                how: "note_path".into(),
                            },
                        });
                    }
                    for to in targets {
                        self.reference(
                            from,
                            &to,
                            path,
                            field,
                            token,
                            "note_path",
                            start.map(|n| n + offset),
                        );
                    }
                }
                for to in self.explicit_targets(token) {
                    self.reference(
                        from,
                        &to,
                        path,
                        field,
                        token,
                        "explicit_token",
                        start.map(|n| n + offset),
                    );
                }
                if token.starts_with('#')
                    && token[1..].chars().all(|c| c.is_ascii_digit())
                    && token.len() > 1
                    && self.resolve(token).is_empty()
                {
                    self.unresolved.push(Unresolved {
                        from: from.into(),
                        provenance: Provenance {
                            path: path.into(),
                            field: field.into(),
                            text_line: None,
                            line: start.map(|n| n + offset),
                            mention: token.into(),
                            how: "issue_reference".into(),
                        },
                    });
                }
            }
        }
    }
    /// Complete undirected reference component, with deterministic BFS explanations.
    /// Presentation budgets belong to callers, after this expansion.
    pub fn expand(&self, references: &[String]) -> Expansion {
        let mut seeds = BTreeSet::new();
        let mut unresolved_seeds = BTreeSet::new();
        for reference in references {
            let found = self.resolve(reference);
            if found.is_empty() {
                unresolved_seeds.insert(reference.clone());
            }
            seeds.extend(found);
        }
        let mut seen = seeds.clone();
        let mut queue: VecDeque<String> = seeds.iter().cloned().collect();
        let mut predecessors = BTreeMap::new();
        let mut reached_edges = BTreeSet::new();
        while let Some(node) = queue.pop_front() {
            for &index in self.adjacency.get(&node).into_iter().flatten() {
                reached_edges.insert(index);
                let edge = &self.edges[index];
                let reverse = edge.to == node;
                let next = if reverse { &edge.from } else { &edge.to };
                if seen.insert(next.clone()) {
                    queue.push_back(next.clone());
                    predecessors.insert(
                        next.clone(),
                        Step {
                            predecessor: node.clone(),
                            edge: index,
                            reverse,
                        },
                    );
                }
            }
        }
        let remap: BTreeMap<usize, usize> = reached_edges
            .iter()
            .enumerate()
            .map(|(new, &old)| (old, new))
            .collect();
        for step in predecessors.values_mut() {
            if let Some(index) = remap.get(&step.edge) {
                step.edge = *index;
            }
        }
        Expansion {
            seeds: seeds.into_iter().collect(),
            unresolved_seeds: unresolved_seeds.into_iter().collect(),
            nodes: seen
                .iter()
                .filter_map(|key| self.nodes.get(key).cloned())
                .collect(),
            edges: reached_edges
                .into_iter()
                .map(|index| self.edges[index].clone())
                .collect(),
            predecessors,
            unresolved: self
                .unresolved
                .iter()
                .filter(|link| seen.contains(&link.from))
                .cloned()
                .collect(),
            availability: self.availability.clone(),
        }
    }
}

fn occurrence(edge: &Edge) -> (&str, &str, &str, &str, Option<usize>, Option<usize>, &str) {
    (
        &edge.from,
        &edge.to,
        &edge.provenance.path,
        &edge.provenance.field,
        edge.provenance.line,
        edge.provenance.text_line,
        &edge.provenance.mention,
    )
}

/// Resolve explicit Markdown note destinations using the source file's directory.
fn note_target(source: &str, destination: &str) -> Option<String> {
    if destination.contains("://") {
        return None;
    }
    let (file, anchor) = destination
        .split_once('#')
        .map_or((destination, None), |(file, anchor)| (file, Some(anchor)));
    if !(file.ends_with(".md")
        || (file.is_empty() && anchor.is_some_and(|a| !a.chars().all(|c| c.is_ascii_digit()))))
    {
        return None;
    }
    let joined = if file.is_empty() {
        source.to_owned()
    } else if file.starts_with("docs/") {
        file.to_owned()
    } else {
        format!(
            "{}/{}",
            source.rsplit_once('/').map_or("", |(parent, _)| parent),
            file
        )
    };
    let mut parts = Vec::new();
    for part in joined.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            _ => parts.push(part),
        }
    }
    let path = parts.join("/");
    if !path.starts_with("docs/") {
        return None;
    }
    Some(match anchor {
        Some(anchor) => format!("{path}#{anchor}"),
        None => path,
    })
}

impl Expansion {
    /// Complete node inventory and one deterministic explanation path per node.
    /// Raw content and alternative edges are available in the full evidence view.
    pub fn navigation(&self) -> Value {
        let selected: BTreeSet<usize> = self.predecessors.values().map(|step| step.edge).collect();
        let remap: BTreeMap<usize, usize> = selected
            .iter()
            .enumerate()
            .map(|(new, old)| (*old, new))
            .collect();
        let edges: Vec<&Edge> = selected.iter().map(|index| &self.edges[*index]).collect();
        let predecessors: BTreeMap<&str, Value> = self
            .predecessors
            .iter()
            .map(|(key, step)| {
                (
                    key.as_str(),
                    serde_json::json!({"predecessor":step.predecessor,
                "edge":remap[&step.edge],"reverse":step.reverse}),
                )
            })
            .collect();
        let nodes: Vec<Value> = self
            .nodes
            .iter()
            .map(|node| {
                serde_json::json!({
                    "key":node.key,"kind":node.kind,"id":node.id,"label":node.label,"path":node.path
                })
            })
            .collect();
        serde_json::json!({"seeds":self.seeds,"unresolved_seeds":self.unresolved_seeds,
            "nodes":nodes,"edges":edges,"predecessors":predecessors,"unresolved":self.unresolved,
            "availability":self.availability,"presentation":{
                "complete_node_inventory":true,"total_edges":self.edges.len(),
                "omitted_alternative_edges":self.edges.len()-selected.len(),
                "node_content_included":false,
                "full_evidence":"Use --full-evidence, or truth evidence TARGET --json for all node content and every edge"}})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };
    static SERIAL: AtomicU64 = AtomicU64::new(0);
    struct Fixture(std::path::PathBuf);
    impl Fixture {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!(
                "truth-evidence-{}-{}",
                std::process::id(),
                SERIAL.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(root.join("corpus")).unwrap();
            Self(root)
        }
        fn record(&self, kind: &str, value: Value) {
            let directory = self.0.join("corpus").join(kind);
            fs::create_dir_all(&directory).unwrap();
            fs::write(
                directory.join(format!("{}.json", value["id"].as_str().unwrap())),
                serde_json::to_vec_pretty(&value).unwrap(),
            )
            .unwrap();
        }
        fn note(&self, text: &str) {
            fs::create_dir_all(self.0.join("docs/notes")).unwrap();
            fs::write(self.0.join("docs/notes/evidence.md"), text).unwrap();
        }
        fn graph(&self, snapshot: Option<&Value>) -> EvidenceGraph {
            EvidenceGraph::build(&self.0, &Corpus::load(&self.0).unwrap(), snapshot).unwrap()
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    #[test]
    fn complete_reverse_cyclic_component_has_no_node_cap() {
        let fixture = Fixture::new();
        for n in 0..231 {
            fixture.record("statements", json!({"id":format!("STMT-{n}"),"paraphrase":format!("statement {n}"),"nested":{"references":[format!("STMT-{}",(n+1)%231)]}}));
        }
        fixture.record(
            "statements",
            json!({"id":"STMT-ISOLATED","paraphrase":"unconnected"}),
        );
        let graph = fixture.graph(None);
        let forward = graph.expand(&["STMT-0".into()]);
        assert_eq!(forward.nodes.len(), 231);
        assert_eq!(forward.predecessors.len(), 230);
        assert!(!forward.edges.is_empty());
        assert!(forward.predecessors.values().any(|step| step.reverse));
        assert_eq!(
            serde_json::to_value(&forward).unwrap(),
            serde_json::to_value(graph.expand(&["STMT-0".into()])).unwrap()
        );
        for (node, step) in &forward.predecessors {
            let edge = &forward.edges[step.edge];
            assert!(edge.from == *node || edge.to == *node);
            assert!(edge.from == step.predecessor || edge.to == step.predecessor);
        }
    }
    #[test]
    fn nested_keys_definitions_senses_sources_notes_and_offline_history_connect() {
        let fixture = Fixture::new();
        fixture.record(
            "statements",
            json!({"id":"STMT-SEED","paraphrase":"target"}),
        );
        fixture.record("definitions",json!({"id":"DEF-ONE","term":"one","definition":"first","basis":"analyst","nested":{"deep":{"STMT-SEED":{"definition_id":"DEF-TWO"}}}}));
        fixture.record("definitions",json!({"id":"DEF-TWO","term":"two","definition":"second","basis":"analyst","definition_id":"DEF-ONE"}));
        fixture.record("disambiguations",json!({"id":"DISAMB-ONE","term":"one","resolution":"explicit","senses":[{"id":"SENSE-ONE","label":"ONE_1","definition_id":"DEF-ONE"}]}));
        fixture.record("attempts",json!({"id":"ATTEMPT-ONE","findings":{"target":"STMT-SEED","finding":"DEF-TWO remains conditional","issue":"#27"}}));
        fixture.record("sources",json!({"id":"SOURCE-ONE","kind":"book","author":"author","work":"work","citation_system":"page","work_urn":"urn:one","catalog_url":"https://example.org"}));
        fixture.record("passages",json!({"id":"snapshot","snapshot":{"source_id":"SOURCE-ONE"},"passages":[{"id":"PASSAGE-ONE","text":"selected witness"}]}));
        fixture.record("claims",json!({"id":"CLAIM-ONE","statement_id":"STMT-SEED","source_id":"SOURCE-ONE","passage_id":"PASSAGE-ONE","locator":"page 1","interpretation":"reading","status":"draft"}));
        fixture.note("# Research\nSTMT-SEED links #27.\n## Reply\nSee evidence.md#research and STMT-MISSING and missing.md#gap.\n");
        let snapshot = json!({"items":[{"number":27,"title":"Followup","body":"DEF-TWO and #28","comments":[{"body":"STMT-SEED"}]},{"number":28,"url":"https://github.com/example/repo/pull/28","body":"PASSAGE-ONE"}]});
        let graph = fixture.graph(Some(&snapshot));
        let result = graph.expand(&["STMT-SEED".into()]);
        for key in [
            "definitions:DEF-ONE",
            "definitions:DEF-TWO",
            "senses:SENSE-ONE",
            "sources:SOURCE-ONE",
            "passages:PASSAGE-ONE",
            "claims:CLAIM-ONE",
            "notes:docs/notes/evidence.md#reply",
            "issues:27",
            "pull_requests:28",
            "attempts:ATTEMPT-ONE",
        ] {
            assert!(
                result.nodes.iter().any(|node| node.key == key),
                "missing {key}"
            );
        }
        assert!(
            result
                .edges
                .iter()
                .any(|edge| edge.provenance.field == "/nested/deep/STMT-SEED/@key")
        );
        assert!(
            result
                .edges
                .iter()
                .any(|edge| edge.provenance.path == "docs/notes/evidence.md"
                    && edge.provenance.line == Some(2))
        );
        assert!(
            result
                .unresolved
                .iter()
                .any(|link| link.provenance.mention == "STMT-MISSING")
        );
        assert!(
            result
                .unresolved
                .iter()
                .any(|link| link.provenance.mention == "missing.md#gap")
        );
        assert!(
            result
                .edges
                .iter()
                .any(|edge| edge.provenance.how == "note_path"
                    && edge.to == "notes:docs/notes/evidence.md#research")
        );
        assert!(result.availability.issue_snapshot);
        assert!(
            result
                .nodes
                .iter()
                .find(|node| node.key == "attempts:ATTEMPT-ONE")
                .unwrap()
                .content
                .get("findings")
                .is_some()
        );
        assert_eq!(
            graph.expand(&["does not exist".into()]).unresolved_seeds,
            vec!["does not exist"]
        );
    }
    #[test]
    fn canonical_lexicon_backlinks_and_single_scalar_occurrences() {
        let fixture = Fixture::new();
        fixture.record(
            "definitions",
            json!({"id":"DEF-ONE","term":"one","definition":"first","basis":"analyst"}),
        );
        fixture.record("lexicon", json!({"id":"12345678-1234-4234-8234-123456789abc","label":"first (technical)","lemma":"first","class":"technical","definition_ids":["DEF-ONE"]}));
        fixture.note("# Lexicon\n12345678-1234-4234-8234-123456789abc\n");
        fixture.record(
            "attempts",
            json!({"id":"ATTEMPT-PROSE","summary":"A finding.\nUse DEF-ONE here."}),
        );
        let graph = fixture.graph(None);
        let result = graph.expand(&["DEF-ONE".into()]);
        assert!(result.nodes.iter().any(|node| node.kind == "lexicon"));
        let links: Vec<_> = result
            .edges
            .iter()
            .filter(|edge| edge.from.starts_with("lexicon:") && edge.to == "definitions:DEF-ONE")
            .collect();
        assert_eq!(links.len(), 1);
        assert_eq!(links[0].provenance.field, "/definition_ids/0");
        assert_eq!(links[0].provenance.line, None);
        assert_eq!(links[0].provenance.text_line, None);
        let prose: Vec<_> = result
            .edges
            .iter()
            .filter(|edge| {
                edge.from == "attempts:ATTEMPT-PROSE" && edge.to == "definitions:DEF-ONE"
            })
            .collect();
        assert_eq!(prose.len(), 1);
        assert_eq!(prose[0].provenance.line, None);
        assert_eq!(prose[0].provenance.text_line, Some(2));
        assert!(
            result
                .unresolved
                .iter()
                .all(|link| link.provenance.mention != "12345678-1234-4234-8234-123456789abc")
        );
        assert!(graph.query_references("Ordinary first prose").is_empty());
    }
    #[test]
    fn issue_urls_keep_host_and_repository_identity_and_queries_resolve_explicit_mentions() {
        let fixture = Fixture::new();
        fixture.record("statements", json!({"id":"STMT-SEED","paraphrase":"seed"}));
        fixture.record("attempts", json!({"id":"ATTEMPT-LOCAL","summary":"STMT-SEED https://github.com/local/repo/issues/27#issuecomment-1"}));
        fixture.record("attempts", json!({"id":"ATTEMPT-FOREIGN-REPO","summary":"https://github.com/foreign/repo/issues/27"}));
        fixture.record("attempts", json!({"id":"ATTEMPT-FOREIGN-HOST","summary":"https://other.example/local/repo/issues/27"}));
        fixture.record("disambiguations",json!({"id":"DISAMB-ONE","term":"one","resolution":"explicit","senses":[{"id":"SENSE-ONE","label":"ONE_1"}]}));
        fixture.note("# Research\nSTMT-SEED\n");
        let snapshot = json!([{"number":27,"url":"https://github.com/local/repo/issues/27"}]);
        let graph = fixture.graph(Some(&snapshot));
        let result = graph.expand(&["#27".into()]);
        assert!(result.nodes.iter().any(|node| node.id == "ATTEMPT-LOCAL"));
        assert!(
            !result
                .nodes
                .iter()
                .any(|node| node.id.starts_with("ATTEMPT-FOREIGN"))
        );
        for id in ["ATTEMPT-FOREIGN-REPO", "ATTEMPT-FOREIGN-HOST"] {
            assert!(
                graph
                    .expand(&[id.into()])
                    .unresolved
                    .iter()
                    .any(|link| link.provenance.how == "issue_url")
            );
        }
        let seeds = graph.query_references(
            "Investigate STMT-SEED with ONE_1, #27 and docs/notes/evidence.md#research.",
        );
        for expected in [
            "statements:STMT-SEED",
            "senses:SENSE-ONE",
            "issues:27",
            "notes:docs/notes/evidence.md#research",
        ] {
            assert!(seeds.contains(&expected.to_owned()), "missing {expected}");
        }
        assert_eq!(
            graph.query_references("See https://github.com/local/repo/issues/27#issuecomment-3"),
            vec!["issues:27"]
        );
        assert!(
            graph
                .query_references("See https://github.com/foreign/repo/issues/27")
                .is_empty()
        );
    }
    #[test]
    fn attempt_pr_evidence_resolves_only_to_a_pr_in_a_scoped_snapshot() {
        let fixture = Fixture::new();
        fixture.record(
            "attempts",
            json!({"id":"ATTEMPT-LOCAL","evidence":["PR-28","PR-27"]}),
        );
        let local = json!([{"number":27,"url":"https://github.com/o/r/issues/27"},
            {"number":28,"url":"https://github.com/o/r/pull/28"}]);
        let graph = fixture.graph(Some(&local));
        assert_eq!(graph.resolve("PR-28"), vec!["pull_requests:28"]);
        assert!(graph.resolve("PR-27").is_empty());
        assert!(
            graph
                .edges()
                .iter()
                .any(|e| e.from == "attempts:ATTEMPT-LOCAL"
                    && e.to == "pull_requests:28"
                    && e.provenance.field == "/evidence/0")
        );
        let mut mixed = local;
        mixed
            .as_array_mut()
            .unwrap()
            .push(json!({"number":9,"url":"https://github.com/other/repo/pull/9"}));
        assert!(fixture.graph(Some(&mixed)).resolve("PR-28").is_empty());
        let unscoped = json!([{"number":28,"kind":"pull_request"}]);
        assert!(fixture.graph(Some(&unscoped)).resolve("PR-28").is_empty());
    }
    #[test]
    fn ordinary_prose_cooccurrence_never_creates_an_edge() {
        let fixture = Fixture::new();
        fixture.record(
            "statements",
            json!({"id":"STMT-A","label":"being","paraphrase":"being"}),
        );
        fixture.record(
            "statements",
            json!({"id":"STMT-B","label":"other","paraphrase":"ordinary being in prose"}),
        );
        let graph = fixture.graph(None);
        assert_eq!(graph.expand(&["STMT-A".into()]).nodes.len(), 1);
        assert!(!graph.expand(&["STMT-A".into()]).availability.issue_snapshot);
    }
}
