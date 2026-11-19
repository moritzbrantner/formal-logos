//! Parameter-level sense tags (#1784).
//!
//! A sense record in `corpus/disambiguations/*.json` may list the Lean
//! parameters that express it:
//!
//! ```json
//! "lean_parameters": [
//!   {"declaration": "TruthCore.Causality.Round2Grounding.EsseEffectDependsOnItsCause",
//!    "parameter": "CausesIn", "arguments": ["_", "_", "esse"]}
//! ]
//! ```
//!
//! In that declaration, that binder (applied to the fixed `arguments`,
//! positionally, `_` leaving a place open) expresses the sense. Tags are
//! authored after reading the declaration's doc comment and the sense's
//! definition; they are never inferred from names. An untagged parameter is
//! **unknown**, not "no sense". A tag is a reading aid for retrieval and
//! composition (the prover of #1784): it proves nothing, identifies no two
//! declarations and changes no closure.
//!
//! [`ParameterTags`] is the reader (sense → tagged parameters, and the
//! reverse); [`validate`] is the offline rule `truth check` applies.

use crate::brief::retrieval::LeanSource;
use serde::Serialize;
use serde_json::{Map, Value};
use std::collections::{BTreeMap, HashMap};
use std::path::Path;

type Obj = Map<String, Value>;

/// A Lean binder of one declaration, applied to optional fixed arguments.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct TaggedParameter {
    pub declaration: String,
    pub parameter: String,
    /// Positional fixed arguments; `_` leaves a place open. Empty: the binder
    /// itself, unapplied.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub arguments: Vec<String>,
}

impl TaggedParameter {
    /// `CausesIn _ _ esse` in `Round2Grounding.EsseEffectDependsOnItsCause`.
    pub fn display(&self) -> String {
        let mut applied = self.parameter.clone();
        for argument in &self.arguments {
            applied.push(' ');
            applied.push_str(argument);
        }
        format!("{applied} in {}", self.declaration)
    }
}

/// One tag: a sense and a parameter that expresses it.
#[derive(Clone, Debug, Serialize)]
pub struct ParameterTag {
    pub sense_id: String,
    pub sense_label: String,
    pub term: String,
    pub definition_id: String,
    pub disambiguation_id: String,
    #[serde(flatten)]
    pub parameter: TaggedParameter,
}

/// Every parameter tag of the corpus, by sense and by parameter.
#[derive(Default)]
pub struct ParameterTags {
    tags: Vec<ParameterTag>,
    by_sense: BTreeMap<String, Vec<usize>>,
    by_parameter: BTreeMap<TaggedParameter, Vec<usize>>,
    by_declaration: BTreeMap<String, Vec<usize>>,
}

fn text<'a>(record: &'a Obj, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn is_ident(word: &str) -> bool {
    let mut chars = word.chars();
    chars.next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && chars.all(|c| c.is_alphanumeric() || c == '_' || c == '\'' || c == '!' || c == '?')
}

/// Parse one `lean_parameters` entry; the error names what is wrong.
fn parse_entry(entry: &Value) -> Result<TaggedParameter, String> {
    let object = entry.as_object().ok_or("each entry must be an object")?;
    if let Some(key) = object
        .keys()
        .find(|key| !matches!(key.as_str(), "declaration" | "parameter" | "arguments"))
    {
        return Err(format!(
            "unknown key {key:?}; an entry is {{declaration, parameter[, arguments]}}"
        ));
    }
    let declaration = object
        .get("declaration")
        .and_then(Value::as_str)
        .filter(|name| name.starts_with("TruthCore.") && name.split('.').all(is_ident))
        .ok_or("declaration must be a fully qualified TruthCore Lean name")?;
    let parameter = object
        .get("parameter")
        .and_then(Value::as_str)
        .filter(|name| is_ident(name))
        .ok_or("parameter must be a binder name")?;
    let arguments = match object.get("arguments") {
        None => Vec::new(),
        Some(Value::Array(items)) => {
            let arguments: Vec<String> = items
                .iter()
                .map(|item| {
                    item.as_str()
                        .map(str::trim)
                        .filter(|argument| !argument.is_empty())
                        .map(str::to_owned)
                        .ok_or("arguments must be non-empty strings")
                })
                .collect::<Result<_, _>>()?;
            if arguments.iter().all(|argument| argument == "_") {
                return Err(
                    "arguments must fix at least one place; omit them to tag the binder itself"
                        .into(),
                );
            }
            arguments
        }
        Some(_) => return Err("arguments must be a list of strings".into()),
    };
    Ok(TaggedParameter {
        declaration: declaration.to_owned(),
        parameter: parameter.to_owned(),
        arguments,
    })
}

impl ParameterTags {
    /// Read the tags of `disambiguations` (path, fields). Fails on a
    /// malformed entry, a duplicate entry within one sense, or one parameter
    /// tagged with two senses of one term.
    pub fn read<'a>(
        disambiguations: impl IntoIterator<Item = (&'a str, &'a Obj)>,
    ) -> Result<Self, String> {
        let mut tags = ParameterTags::default();
        let mut by_term: HashMap<(String, TaggedParameter), (String, String)> = HashMap::new();
        for (path, fields) in disambiguations {
            let term = text(fields, "term_label");
            let senses = fields.get("senses").and_then(Value::as_array);
            for sense in senses.into_iter().flatten().filter_map(Value::as_object) {
                let Some(entries) = sense.get("lean_parameters") else {
                    continue;
                };
                let label = text(sense, "label");
                let entries = entries
                    .as_array()
                    .filter(|entries| !entries.is_empty())
                    .ok_or_else(|| {
                        format!("{path}: sense {label}: lean_parameters must be a non-empty list")
                    })?;
                let mut seen = Vec::new();
                for entry in entries {
                    let parameter = parse_entry(entry).map_err(|error| {
                        format!("{path}: sense {label}: lean_parameters: {error}")
                    })?;
                    if seen.contains(&parameter) {
                        return Err(format!(
                            "{path}: sense {label}: lean_parameters lists {} twice",
                            parameter.display()
                        ));
                    }
                    seen.push(parameter.clone());
                    let sense_id = text(sense, "id").to_owned();
                    let key = (term.to_owned(), parameter.clone());
                    if let Some((other, other_label)) = by_term.get(&key) {
                        if *other != sense_id {
                            return Err(format!(
                                "{path}: {} is tagged with two senses of {term}: {other_label} and {label}",
                                parameter.display()
                            ));
                        }
                        // The same sense listed in two records: one tag.
                        continue;
                    }
                    by_term.insert(key, (sense_id.clone(), label.to_owned()));
                    tags.push(ParameterTag {
                        sense_id,
                        sense_label: label.to_owned(),
                        term: term.to_owned(),
                        definition_id: text(sense, "definition_id").to_owned(),
                        disambiguation_id: text(fields, "id").to_owned(),
                        parameter,
                    });
                }
            }
        }
        Ok(tags)
    }

    /// The tags of a loaded corpus.
    pub fn from_corpus(corpus: &crate::Corpus) -> Result<Self, String> {
        let records: Vec<(String, &Obj)> = corpus
            .records_by_id("disambiguations")
            .map(|(_, record)| (record.path.clone(), &record.fields))
            .collect();
        Self::read(
            records
                .iter()
                .map(|(path, fields)| (path.as_str(), *fields)),
        )
    }

    fn push(&mut self, tag: ParameterTag) {
        let index = self.tags.len();
        self.by_sense
            .entry(tag.sense_id.clone())
            .or_default()
            .push(index);
        self.by_parameter
            .entry(tag.parameter.clone())
            .or_default()
            .push(index);
        self.by_declaration
            .entry(tag.parameter.declaration.clone())
            .or_default()
            .push(index);
        self.tags.push(tag);
    }

    fn select(&self, indices: Option<&Vec<usize>>) -> Vec<&ParameterTag> {
        indices
            .into_iter()
            .flatten()
            .map(|&index| &self.tags[index])
            .collect()
    }

    /// Every tag, in record order.
    pub fn all(&self) -> &[ParameterTag] {
        &self.tags
    }

    pub fn is_empty(&self) -> bool {
        self.tags.is_empty()
    }

    /// The parameters tagged with sense `sense_id`.
    pub fn parameters_of(&self, sense_id: &str) -> Vec<&ParameterTag> {
        self.select(self.by_sense.get(sense_id))
    }

    /// The senses (at most one per term) tagged on exactly this parameter.
    pub fn senses_of(&self, parameter: &TaggedParameter) -> Vec<&ParameterTag> {
        self.select(self.by_parameter.get(parameter))
    }

    /// Every tag on a parameter of `declaration`.
    pub fn in_declaration(&self, declaration: &str) -> Vec<&ParameterTag> {
        self.select(self.by_declaration.get(declaration))
    }

    /// Sense id → tagged parameters.
    pub fn by_sense(&self) -> BTreeMap<&str, Vec<&TaggedParameter>> {
        let mut map: BTreeMap<&str, Vec<&TaggedParameter>> = BTreeMap::new();
        for tag in &self.tags {
            map.entry(tag.sense_id.as_str())
                .or_default()
                .push(&tag.parameter);
        }
        map
    }

    /// Tagged parameter → sense ids.
    pub fn by_parameter(&self) -> BTreeMap<&TaggedParameter, Vec<&str>> {
        let mut map: BTreeMap<&TaggedParameter, Vec<&str>> = BTreeMap::new();
        for tag in &self.tags {
            map.entry(&tag.parameter)
                .or_default()
                .push(tag.sense_id.as_str());
        }
        map
    }
}

/// The binder names of a declaration's signature: the names before `:` in
/// each top-level `(…)`, `{…}`, `⦃…⦄`, `{{…}}` or `[…]` group that precedes
/// the declaration's own type (`:`) or body (`:=`, `where`, `|`). A lexical
/// reading of the source block, not Lean elaboration; section `variable`s
/// are not part of the signature.
pub fn signature_binders(block: &str) -> Vec<String> {
    let mut binders = Vec::new();
    let mut depth = 0usize;
    let mut group = String::new();
    let mut chars = block.chars().peekable();
    let mut previous = ' ';
    while let Some(c) = chars.next() {
        match c {
            '(' | '{' | '[' | '⦃' => {
                if depth > 0 {
                    group.push(c);
                }
                depth += 1;
            }
            ')' | '}' | ']' | '⦄' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    if let Some((names, _)) = split_binder(&group) {
                        binders.extend(names.split_whitespace().map(str::to_owned));
                    }
                    group.clear();
                } else {
                    group.push(c);
                }
            }
            _ if depth > 0 => group.push(c),
            ':' if depth == 0 => break,
            '|' if depth == 0 && previous.is_whitespace() => break,
            'w' if depth == 0 && previous.is_whitespace() => {
                let rest: String = chars.clone().take(5).collect();
                if rest.starts_with("here") && rest[4..].chars().all(char::is_whitespace) {
                    break;
                }
            }
            _ => {}
        }
        previous = c;
    }
    binders
}

/// `x y : T` → (`x y`, `T`), at the group's top level.
fn split_binder(group: &str) -> Option<(&str, &str)> {
    let mut depth = 0usize;
    for (index, c) in group.char_indices() {
        match c {
            '(' | '{' | '[' | '⦃' => depth += 1,
            ')' | '}' | ']' | '⦄' => depth = depth.saturating_sub(1),
            ':' if depth == 0 && !group[index + 1..].starts_with('=') => {
                let names = &group[..index];
                return names
                    .split_whitespace()
                    .all(is_ident)
                    .then_some((names, &group[index + 1..]));
            }
            _ => {}
        }
    }
    None
}

/// The offline rule of `truth check`: tags are well formed and not
/// conflicting ([`ParameterTags::read`]); each declaration exists under
/// `TruthCore/` (the exact qualified name, through the source locator `brief`
/// and `novelty` use); the binder occurs in its signature; and a fixed
/// argument that is a bare name is also a binder of that signature (a
/// constant is written fully qualified).
pub fn validate<'a>(
    root: &Path,
    disambiguations: impl IntoIterator<Item = (&'a str, &'a Obj)>,
) -> Result<ParameterTags, String> {
    let disambiguations: Vec<(&str, &Obj)> = disambiguations.into_iter().collect();
    let tags = ParameterTags::read(disambiguations.iter().copied())?;
    if tags.is_empty() {
        return Ok(tags);
    }
    let path_of: HashMap<&str, &str> = disambiguations
        .iter()
        .map(|(path, fields)| (text(fields, "id"), *path))
        .collect();
    let mut lean = LeanSource::new(root);
    let mut binders: HashMap<String, Option<Vec<String>>> = HashMap::new();
    for tag in tags.all() {
        let path = path_of
            .get(tag.disambiguation_id.as_str())
            .copied()
            .unwrap_or_default();
        let parameter = &tag.parameter;
        let found = binders
            .entry(parameter.declaration.clone())
            .or_insert_with(|| {
                lean.qualified_block(&parameter.declaration)
                    .map(|(_, _, block)| signature_binders(&block))
            });
        let Some(found) = found else {
            return Err(format!(
                "{path}: sense {}: lean_parameters declaration {} was not found under TruthCore/",
                tag.sense_label, parameter.declaration
            ));
        };
        if !found.contains(&parameter.parameter) {
            return Err(format!(
                "{path}: sense {}: {} is not a binder of the signature of {}",
                tag.sense_label, parameter.parameter, parameter.declaration
            ));
        }
        for argument in &parameter.arguments {
            if argument != "_" && is_ident(argument) && !found.contains(argument) {
                return Err(format!(
                    "{path}: sense {}: fixed argument {argument} of {} is not a binder of {}; write a constant fully qualified",
                    tag.sense_label, parameter.parameter, parameter.declaration
                ));
            }
        }
    }
    Ok(tags)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn signature_binders_stop_at_the_type_and_body() {
        let block = "def EsseEffectDependsOnItsCause (CausesIn : B → B → R → Prop) (esse : R)\n    (DependsForBeing : B → B → Prop) : Prop :=\n  ∀ c x, c ≠ x → CausesIn c x esse → DependsForBeing x c";
        assert_eq!(
            signature_binders(block),
            ["CausesIn", "esse", "DependsForBeing"]
        );
        let block = "def ConcurrentlyActualized {W B T P : Type} [Preorder T] [inst : Foo T] (h : History W B T) ⦃G : BeingGiving W B T⦄ : Prop :=\n  ∀ (q : B), True";
        assert_eq!(
            signature_binders(block),
            ["W", "B", "T", "P", "inst", "h", "G"]
        );
        let block = "structure Frame (B : Type) where\n  (Moves : B → B → Prop)";
        assert_eq!(signature_binders(block), ["B"]);
        let block = "inductive BroadMotion {B R : Type} (moved : B → R → Prop) (x : B) (r : R) : Prop\n  | intro : moved x r → BroadMotion moved x r";
        assert_eq!(signature_binders(block), ["B", "R", "moved", "x", "r"]);
    }

    fn disambiguation(id: &str, term: &str, senses: Value) -> Obj {
        json!({"id": id, "term_label": term, "senses": senses})
            .as_object()
            .cloned()
            .unwrap()
    }

    fn entry(declaration: &str, parameter: &str, arguments: Option<Value>) -> Value {
        let mut value = json!({"declaration": declaration, "parameter": parameter});
        if let Some(arguments) = arguments {
            value["arguments"] = arguments;
        }
        value
    }

    #[test]
    fn reader_maps_senses_and_parameters_both_ways() {
        let d = "TruthCore.A.Dep";
        let first = disambiguation(
            "D1",
            "CAUSE",
            json!([
                {"id": "s1", "label": "CAUSE_1", "definition_id": "d1",
                 "lean_parameters": [entry(d, "CausesIn", None)]},
                {"id": "s2", "label": "CAUSE_2", "definition_id": "d2",
                 "lean_parameters": [entry(d, "CausesIn", Some(json!(["_", "_", "esse"])))]}
            ]),
        );
        let second = disambiguation(
            "D2",
            "DEPENDS",
            json!([{"id": "s3", "label": "DEPENDS_1", "definition_id": "d3",
                     "lean_parameters": [entry(d, "CausesIn", None)]}]),
        );
        let tags = ParameterTags::read([("a.json", &first), ("b.json", &second)]).unwrap();
        assert_eq!(tags.all().len(), 3);
        assert_eq!(
            tags.parameters_of("s2")[0].parameter.arguments,
            ["_", "_", "esse"]
        );
        let bare = TaggedParameter {
            declaration: d.into(),
            parameter: "CausesIn".into(),
            arguments: vec![],
        };
        let senses: Vec<&str> = tags
            .senses_of(&bare)
            .iter()
            .map(|t| t.sense_label.as_str())
            .collect();
        assert_eq!(senses, ["CAUSE_1", "DEPENDS_1"]);
        assert_eq!(tags.in_declaration(d).len(), 3);
        assert_eq!(tags.by_parameter()[&bare], ["s1", "s3"]);
        assert_eq!(bare.display(), "CausesIn in TruthCore.A.Dep");
    }

    #[test]
    fn reader_rejects_conflicts_duplicates_and_bad_shapes() {
        let d = "TruthCore.A.Dep";
        let conflict = disambiguation(
            "D1",
            "CAUSE",
            json!([
                {"id": "s1", "label": "CAUSE_1", "definition_id": "d1",
                 "lean_parameters": [entry(d, "CausesIn", None)]},
                {"id": "s2", "label": "CAUSE_2", "definition_id": "d2",
                 "lean_parameters": [entry(d, "CausesIn", None)]}
            ]),
        );
        let error = ParameterTags::read([("a.json", &conflict)]).err().unwrap();
        assert!(
            error.contains("two senses of CAUSE: CAUSE_1 and CAUSE_2"),
            "{error}"
        );
        // The same term in another record conflicts too.
        let other = disambiguation(
            "D2",
            "CAUSE",
            json!([{"id": "s5", "label": "CAUSE_5", "definition_id": "d5",
                     "lean_parameters": [entry(d, "CausesIn", None)]}]),
        );
        let first = disambiguation(
            "D1",
            "CAUSE",
            json!([{"id": "s1", "label": "CAUSE_1", "definition_id": "d1",
                     "lean_parameters": [entry(d, "CausesIn", None)]}]),
        );
        assert!(ParameterTags::read([("a.json", &first), ("b.json", &other)]).is_err());
        for bad in [
            json!([entry(d, "CausesIn", None), entry(d, "CausesIn", None)]),
            json!([entry("Other.Dep", "CausesIn", None)]),
            json!([entry(d, "Causes In", None)]),
            json!([entry(d, "CausesIn", Some(json!(["_", "_"])))]),
            json!([entry(d, "CausesIn", Some(json!(["", "x"])))]),
            json!([{"declaration": d, "parameter": "C", "sense": "x"}]),
            json!([]),
        ] {
            let record = disambiguation(
                "D1",
                "CAUSE",
                json!([{"id": "s1", "label": "CAUSE_1", "definition_id": "d1",
                         "lean_parameters": bad}]),
            );
            assert!(ParameterTags::read([("a.json", &record)]).is_err());
        }
    }

    #[test]
    fn validate_reads_the_lean_signature() {
        let root =
            std::env::temp_dir().join(format!("truth-parameter-tags-{}", std::process::id()));
        std::fs::create_dir_all(root.join("TruthCore/A")).unwrap();
        std::fs::write(
            root.join("TruthCore/A/B.lean"),
            "module\n\nnamespace TruthCore.A.B\n\n/-- doc -/\ndef Dep (CausesIn : Nat → Nat → Prop) (esse : Nat)\n    (D : Nat → Prop) : Prop :=\n  ∀ x, CausesIn x esse → D x\n\nend TruthCore.A.B\n",
        )
        .unwrap();
        let record = |parameter: Value| {
            disambiguation(
                "D1",
                "CAUSE",
                json!([{"id": "s1", "label": "CAUSE_1", "definition_id": "d1",
                         "lean_parameters": [parameter]}]),
            )
        };
        let ok = record(entry(
            "TruthCore.A.B.Dep",
            "CausesIn",
            Some(json!(["_", "esse"])),
        ));
        assert_eq!(validate(&root, [("a.json", &ok)]).unwrap().all().len(), 1);
        for (bad, message) in [
            (entry("TruthCore.A.Dep", "CausesIn", None), "was not found"),
            (
                entry("TruthCore.A.B.Dep", "Causes", None),
                "is not a binder",
            ),
            (
                entry("TruthCore.A.B.Dep", "CausesIn", Some(json!(["_", "x"]))),
                "fixed argument x",
            ),
        ] {
            let error = validate(&root, [("a.json", &record(bad))]).err().unwrap();
            assert!(error.contains(message), "{error}");
        }
        let constant = record(entry(
            "TruthCore.A.B.Dep",
            "CausesIn",
            Some(json!(["_", "TruthCore.A.B.esse"])),
        ));
        assert!(validate(&root, [("a.json", &constant)]).is_ok());
        std::fs::remove_dir_all(&root).unwrap();
    }
}
