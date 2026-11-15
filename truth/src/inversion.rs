//! Materializing a derived `contrapositive` edge of `truth tree` as an
//! ordinary corpus argument (#1674 phase 2): `truth tree X
//! --materialize-edge contrapositive:<argument>:<premise>`.
//!
//! The edge is computed in the view; this module writes, only on that
//! explicit request, the three source files that make it a corpus argument:
//!
//! - a batch spec `specs/inversion-<name>.toml` for
//!   `scripts/argument_batch.py records`, declaring the argument as an
//!   `instantiation` transcription (AGENTS.md invariant 16);
//! - a vocabulary module `TruthCore/Logic/Inversions/<Name>.lean` with a
//!   negation definition for each negated proposition the corpus does not
//!   already state (an existing statement whose declaration is defined as
//!   that negation is reused instead);
//! - a Solution module `TruthCore/Results/Logic/Inversions/<Name>/Solution.lean`
//!   whose one theorem instantiates `TruthCore.Logic.Inversion.contrapositive`
//!   at the original result theorem.
//!
//! The Challenge, the records, the import aggregators and the verification
//! are then the ordinary batch workflow; the plan lists those commands. The
//! Lean text is read from the original Solution's theorem header, so a header
//! this parser cannot classify is refused with a reason rather than guessed.

use crate::Corpus;
use crate::transcription::{Definitions, analyze_result, ident_prefix};
use crate::tree::{MATERIALIZED_RESULTS, MATERIALIZED_VOCABULARY, materialized_name};
use serde::Serialize;
use serde_json::{Map, Value};
use std::fs;
use std::path::Path;

/// The files and follow-up commands of one materialization.
#[derive(Debug, Clone, Serialize)]
pub struct Plan {
    pub key: String,
    pub name: String,
    /// The theorem the generated Solution proves.
    pub theorem: String,
    pub spec: String,
    /// (repository-relative path, content).
    #[serde(skip)]
    pub files: Vec<(String, String)>,
    pub paths: Vec<String>,
    /// Negations the corpus already states, reused: (role, statement id).
    pub reused: Vec<(String, String)>,
    pub commands: Vec<String>,
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

fn tail(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// The head constant's last component of a Lean type written in a header.
fn head(lean_type: &str) -> Option<&str> {
    ident_prefix(lean_type.trim()).map(tail)
}

/// At most `width` characters, cut at a word boundary with `…`.
fn clip(text: &str, width: usize) -> String {
    let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let Some((cut, _)) = text.char_indices().nth(width) else {
        return text;
    };
    let head = &text[..cut];
    let head = head.rsplit_once(' ').map_or(head, |(words, _)| words);
    format!("{}…", head.trim_end_matches([',', ';', ':', '.']))
}

/// Lower-case the first letter unless the second is upper-case too (an
/// acronym or a sense label).
fn lower_first(text: &str) -> String {
    let mut chars = text.chars();
    match (chars.next(), chars.next()) {
        (Some(first), second) if !second.is_some_and(char::is_uppercase) => {
            first.to_lowercase().collect::<String>() + &text[first.len_utf8()..]
        }
        _ => text.to_owned(),
    }
}

/// A TOML basic string.
fn toml(text: &str) -> String {
    serde_json::to_string(text).unwrap_or_default()
}

fn toml_list(items: &[String]) -> String {
    format!(
        "[{}]",
        items
            .iter()
            .map(|item| toml(item))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// `RoweDeductiveCoreContra1` -> `rowe-deductive-core-contra-1`.
fn kebab(name: &str) -> String {
    let chars: Vec<char> = name.chars().collect();
    let mut out = String::new();
    for (position, &c) in chars.iter().enumerate() {
        if let Some(&previous) = position.checked_sub(1).and_then(|p| chars.get(p)) {
            let next_lower = chars
                .get(position + 1)
                .is_some_and(char::is_ascii_lowercase);
            let boundary = (c.is_ascii_uppercase()
                && (!previous.is_ascii_uppercase() || next_lower))
                || (c.is_ascii_digit() && !previous.is_ascii_digit());
            if boundary {
                out.push('-');
            }
        }
        out.push(c.to_ascii_lowercase());
    }
    out
}

/// How a negated proposition is written in the generated Lean.
struct Negation {
    /// The Lean term (a definition applied to the explicit vocabulary).
    application: String,
    /// An existing statement stating it, if any.
    statement: Option<String>,
    /// A new definition for the vocabulary module, if needed.
    definition: Option<String>,
    /// For a new statement: its label, Lean name, paraphrase and links.
    new_statement: Option<NewStatement>,
    /// A module to import for an existing declaration of ours.
    module: Option<String>,
}

struct NewStatement {
    label: String,
    lean: String,
    paraphrase: String,
    definitions: Vec<String>,
    disambiguations: Vec<String>,
}

struct Context<'a> {
    corpus: &'a Corpus,
    definitions: Definitions,
    vocabulary_groups: Vec<String>,
    explicit: Vec<String>,
    name: String,
}

impl Context<'_> {
    /// An existing statement whose Lean declaration is defined as `¬ T` for
    /// the header type `lean_type`, applied to the same identifiers.
    fn existing_negation(&self, lean_type: &str) -> Option<(String, String)> {
        let tokens: Vec<&str> = lean_type.split_whitespace().collect();
        let (target_head, arguments) = tokens.split_first()?;
        if !arguments.iter().all(|a| ident_prefix(a) == Some(*a)) {
            return None;
        }
        let mut found = Vec::new();
        for (id, record) in self.corpus.records_by_id("statements") {
            let Some(declaration) = string(&record.fields, "lean_declaration") else {
                continue;
            };
            let Some((parameters, body)) = self.definitions.get(tail(&declaration)) else {
                continue;
            };
            let Some(negated) = body
                .strip_prefix('¬')
                .map(str::trim)
                .map(|inner| inner.trim_start_matches('(').trim_end_matches(')'))
            else {
                continue;
            };
            let body_tokens: Vec<&str> = negated.split_whitespace().collect();
            let Some((body_head, body_arguments)) = body_tokens.split_first() else {
                continue;
            };
            if tail(body_head) != tail(target_head) || body_arguments.len() != arguments.len() {
                continue;
            }
            // Each definition parameter must be one of the body's arguments;
            // it takes the matching argument of the header type.
            let mut applied = Vec::new();
            for parameter in parameters {
                match body_arguments.iter().position(|a| a == parameter) {
                    Some(position) => applied.push(arguments[position].to_owned()),
                    None => break,
                }
            }
            if applied.len() != parameters.len()
                || body_arguments
                    .iter()
                    .any(|argument| !parameters.iter().any(|p| p == argument))
            {
                continue;
            }
            let application = std::iter::once(declaration.clone())
                .chain(applied)
                .collect::<Vec<_>>()
                .join(" ");
            found.push((id.to_owned(), application));
        }
        // Reuse only an unambiguous match.
        (found.len() == 1).then(|| found.remove(0))
    }

    fn negation(&self, statement: &str, lean_type: &str) -> Result<Negation, String> {
        if let Some((existing, application)) = self.existing_negation(lean_type) {
            return Ok(Negation {
                application,
                statement: Some(existing),
                definition: None,
                new_statement: None,
                module: None,
            });
        }
        let record = self
            .corpus
            .get("statements", statement)
            .map(|record| &record.fields)
            .ok_or_else(|| format!("unknown statement {statement}"))?;
        let label = string(record, "label").unwrap_or_else(|| statement.to_owned());
        let negation_label = format!("Negation: {}", clip(&label, 88));
        let head = head(lean_type).ok_or_else(|| format!("no head constant in `{lean_type}`"))?;
        let lean = format!("Not{head}");
        let qualified = format!("{MATERIALIZED_VOCABULARY}.{}.{lean}", self.name);
        // A negation statement registered by an earlier materialization
        // (same label) is reused with its own declaration.
        for (id, other) in self.corpus.records_by_id("statements") {
            if string(&other.fields, "label").as_deref() == Some(negation_label.as_str()) {
                let declaration = string(&other.fields, "lean_declaration")
                    .ok_or_else(|| format!("statement {id} has no lean_declaration"))?;
                let module = declaration
                    .strip_prefix(&format!("{MATERIALIZED_VOCABULARY}."))
                    .and_then(|rest| rest.rsplit_once('.'))
                    .map(|(module, _)| format!("{MATERIALIZED_VOCABULARY}.{module}"));
                return Ok(Negation {
                    application: std::iter::once(declaration)
                        .chain(self.explicit.iter().cloned())
                        .collect::<Vec<_>>()
                        .join(" "),
                    statement: Some(id.to_owned()),
                    definition: None,
                    new_statement: None,
                    module,
                });
            }
        }
        let binders = self.vocabulary_groups.join(" ");
        let definition = format!(
            "/-- {negation_label}. The negation of `{}` (statement {statement}). -/\ndef {lean}{}{binders} : Prop :=\n  ¬ ({lean_type})\n",
            string(record, "lean_declaration").unwrap_or_default(),
            if binders.is_empty() { "" } else { " " }
        );
        let paraphrase = format!(
            "The negation of statement {statement}, introduced by a materialized contraposition: it is not the case that the following holds. {}",
            string(record, "paraphrase").unwrap_or_default()
        );
        Ok(Negation {
            application: std::iter::once(qualified)
                .chain(self.explicit.iter().cloned())
                .collect::<Vec<_>>()
                .join(" "),
            statement: None,
            definition: Some(definition),
            new_statement: Some(NewStatement {
                label: negation_label,
                lean,
                paraphrase,
                definitions: strings(record, "definition_ids"),
                disambiguations: strings(record, "disambiguation_ids"),
            }),
            module: None,
        })
    }
}

/// The materialization of the contrapositive of `argument` at `premise`,
/// composed with the result `result_id`.
pub fn plan_contrapositive(
    root: &Path,
    corpus: &Corpus,
    key: &str,
    argument: &str,
    premise: &str,
    result_id: &str,
) -> Result<Plan, String> {
    let record = corpus
        .get("arguments", argument)
        .map(|record| &record.fields)
        .ok_or_else(|| format!("unknown argument {argument}"))?;
    let result = corpus
        .get("results", result_id)
        .map(|record| &record.fields)
        .ok_or_else(|| format!("unknown result {result_id}"))?;
    // A generated argument inherits its statements' senses: a source that
    // mixes senses only through a legacy allowlist entry or a sense bridge
    // would give an argument `truth check` rejects. Those are refused.
    if record.contains_key("sense_bridges") {
        return Err(format!(
            "{argument} relates senses through sense_bridges; materialize its contraposition by hand, carrying the bridges that stay premises"
        ));
    }
    let allowlisted = fs::read_to_string(root.join("corpus/sense-index-allowlist.json"))
        .ok()
        .and_then(|text| serde_json::from_str::<Value>(&text).ok())
        .is_some_and(|allowlist| allowlist["arguments"].get(argument).is_some());
    if allowlisted {
        return Err(format!(
            "{argument} mixes senses under the legacy sense-index allowlist; a new argument over its statements would fail `truth check` until their sense links are repaired"
        ));
    }
    let module = string(result, "solution_module").ok_or("the result has no solution_module")?;
    let theorem = string(result, "theorem").ok_or("the result has no theorem")?;
    let mut premises: Vec<String> = Vec::new();
    for item in strings(record, "premise_statement_ids") {
        if !premises.contains(&item) {
            premises.push(item);
        }
    }
    let position = premises
        .iter()
        .position(|item| item == premise)
        .ok_or_else(|| format!("{premise} is not a premise of {argument}"))?
        + 1;
    let conclusion = string(record, "conclusion_statement_id").unwrap_or_default();
    let name = materialized_name(&module, &theorem, position);
    let analysis = analyze_result(root, &module, &theorem)
        .ok_or_else(|| format!("theorem {theorem} not found in {module}"))?;
    let declaration = |statement: &str| {
        corpus
            .get("statements", statement)
            .and_then(|record| string(&record.fields, "lean_declaration"))
    };
    // Classify the header: a `(h : T)` group whose head is a premise's
    // declaration is that premise's hypothesis; every other group is
    // vocabulary, kept verbatim.
    let mut hypotheses: Vec<(String, String, String)> = Vec::new();
    let mut vocabulary_groups = Vec::new();
    let mut explicit = Vec::new();
    let mut call = Vec::new();
    for (bracket, names, lean_type) in &analysis.groups {
        let matching: Vec<&String> = premises
            .iter()
            .filter(|item| declaration(item).is_some_and(|d| Some(tail(&d)) == head(lean_type)))
            .collect();
        if *bracket == '(' && !matching.is_empty() {
            if names.len() != 1 || matching.len() != 1 {
                return Err(format!(
                    "the hypothesis group ({} : {lean_type}) of {theorem} does not bind exactly one premise",
                    names.join(" ")
                ));
            }
            hypotheses.push((matching[0].clone(), names[0].clone(), lean_type.clone()));
            call.push(names[0].clone());
            continue;
        }
        let close = match bracket {
            '(' => ')',
            '{' => '}',
            _ => ']',
        };
        vocabulary_groups.push(format!("{bracket}{} : {lean_type}{close}", names.join(" ")));
        if *bracket == '(' {
            explicit.extend(names.iter().cloned());
            call.extend(names.iter().cloned());
        }
    }
    if hypotheses.len() != premises.len() {
        return Err(format!(
            "{theorem} names {} premise hypotheses by head constant, its argument {} premises; a header whose premises are not `(h : P …)` groups is not materialized",
            hypotheses.len(),
            premises.len()
        ));
    }
    if head(&analysis.goal) != declaration(&conclusion).as_deref().map(tail) {
        return Err(format!(
            "the goal `{}` of {theorem} does not have the conclusion's declaration as its head",
            analysis.goal
        ));
    }
    let source = fs::read_to_string(root.join(module.replace('.', "/") + ".lean"))
        .map_err(|error| format!("{module}: {error}"))?;
    let namespace = source
        .lines()
        .find_map(|line| line.strip_prefix("namespace "))
        .map(str::trim)
        .map(str::to_owned);
    let opens: Vec<String> = source
        .lines()
        .filter(|line| line.starts_with("open "))
        .map(str::to_owned)
        .collect();
    let context = Context {
        corpus,
        definitions: Definitions::load(root),
        vocabulary_groups,
        explicit,
        name: name.clone(),
    };
    let negated_conclusion = context.negation(&conclusion, &analysis.goal)?;
    let (_, premise_hypothesis, premise_type) = hypotheses
        .iter()
        .find(|(item, _, _)| item == premise)
        .cloned()
        .ok_or("the premise has no hypothesis")?;
    let negated_premise = context.negation(premise, &premise_type)?;

    let vocabulary_module = format!("{MATERIALIZED_VOCABULARY}.{name}");
    let results_module = format!("{MATERIALIZED_RESULTS}.{name}");
    let full_theorem = format!("{results_module}.contrapositive");
    let opens_block = {
        let mut lines = Vec::new();
        if let Some(namespace) = &namespace {
            lines.push(format!("open {namespace}"));
        }
        lines.extend(opens.iter().cloned());
        lines.join("\n")
    };
    let mut files = Vec::new();
    let new_definitions: Vec<&String> = [&negated_conclusion, &negated_premise]
        .iter()
        .filter_map(|negation| negation.definition.as_ref())
        .collect();
    let mut imports = vec![module.clone(), "TruthCore.Logic.Inversion".to_owned()];
    if !new_definitions.is_empty() {
        imports.push(vocabulary_module.clone());
        let text = format!(
            "module\n\npublic import {module}\n\n@[expose] public section\n\n/-!\nNegations for a materialized contraposition (#1674 phase 2), generated by\n`truth tree --materialize-edge {key}`.\n\nThey negate the propositions of result `{theorem}`; they add no\nvocabulary of their own. Classical equivalents (for example `¬¬P` and `P`)\nare not identified here.\n-/\n\nnamespace {vocabulary_module}\n\n{opens_block}\n\n{}\nend {vocabulary_module}\n",
            new_definitions
                .iter()
                .map(|definition| definition.as_str())
                .collect::<Vec<_>>()
                .join("\n")
        );
        files.push((vocabulary_module.replace('.', "/") + ".lean", text));
    }
    for negation in [&negated_conclusion, &negated_premise] {
        if let Some(module) = &negation.module
            && !imports.contains(module)
        {
            imports.push(module.clone());
        }
    }
    let mut taken: Vec<&str> = call.iter().map(String::as_str).collect();
    taken.extend(context.explicit.iter().map(String::as_str));
    let mut negated_hypothesis = "hNotConclusion".to_owned();
    while taken.contains(&negated_hypothesis.as_str()) {
        negated_hypothesis.push('\'');
    }
    let binders = context
        .vocabulary_groups
        .iter()
        .map(|group| format!("    {group}\n"))
        .collect::<String>();
    let others = hypotheses
        .iter()
        .filter(|(item, _, _)| item != premise)
        .map(|(_, name, lean_type)| format!("    ({name} : {lean_type})\n"))
        .collect::<String>();
    let solution = format!(
        "module\n\n{}\n\n@[expose] public section\n\n/-!\nA materialized contraposition (#1674 phase 2), generated by\n`truth tree --materialize-edge {key}`.\n\nIt instantiates `TruthCore.Logic.Inversion.contrapositive` at the verified\nresult `{theorem}`: the negation of that result's conclusion, with its other\npremises, gives the negation of premise {position}. This is a logical\ntransformation of an existing result (an `instantiation` transcription,\nAGENTS.md invariant 16), not a new argument for either negation.\n-/\n\nnamespace {results_module}\n\n{opens_block}\n\n/-- Logical transcription (instantiation): contraposition of `{theorem}`\nat its premise `{premise_hypothesis}`. -/\ntheorem contrapositive\n{binders}    ({negated_hypothesis} : {})\n{others}    : {} :=\n  TruthCore.Logic.Inversion.contrapositive\n    (fun {premise_hypothesis} => {theorem} {}) {negated_hypothesis}\n\nend {results_module}\n",
        imports
            .iter()
            .map(|import| format!("public import {import}"))
            .collect::<Vec<_>>()
            .join("\n"),
        negated_conclusion.application,
        negated_premise.application,
        call.join(" ")
    );
    let solution_path = results_module.replace('.', "/") + "/Solution.lean";
    files.push((solution_path.clone(), solution));

    let label = |statement: &str| {
        corpus
            .get("statements", statement)
            .and_then(|record| string(&record.fields, "label"))
            .unwrap_or_else(|| statement.to_owned())
    };
    let handle = |negation: &Negation| match (&negation.statement, &negation.new_statement) {
        (Some(id), _) => id.clone(),
        (None, Some(new)) => new.label.clone(),
        _ => String::new(),
    };
    let mut spec = format!(
        "# Generated by `truth tree --materialize-edge {key}` (#1674 phase 2).\n# The contraposition of argument {argument} (result {result_id}) at its\n# premise {premise}. Regenerate the records with\n# `python3 scripts/argument_batch.py records {{this spec}} --write --fix`.\n\n[batch]\nvocab = {}\nresults = {}\n",
        toml(&vocabulary_module),
        toml(&results_module)
    );
    for negation in [&negated_conclusion, &negated_premise] {
        if let Some(new) = &negation.new_statement {
            spec.push_str(&format!(
                "\n[[statement]]\nid = {}\nlabel = {}\nlean = {}\nparaphrase = {}\ndefinitions = {}\ndisambiguations = {}\n",
                toml(&new.label),
                toml(&new.label),
                toml(&new.lean),
                toml(&new.paraphrase),
                toml_list(&new.definitions),
                toml_list(&new.disambiguations)
            ));
        }
    }
    let mut spec_premises = vec![handle(&negated_conclusion)];
    spec_premises.extend(
        hypotheses
            .iter()
            .filter(|(item, _, _)| item != premise)
            .map(|(item, _, _)| item.clone()),
    );
    // At most 88 characters: the generated inference label appends
    // " (inference)" and labels are limited to 100. The two labels share
    // the 57 characters left by the fixed words.
    let (premise_label, conclusion_label) = (label(premise), label(&conclusion));
    let room = 57;
    let conclusion_length = conclusion_label.chars().count();
    let premise_width = room - conclusion_length.min(room / 2);
    let premise_text = clip(&premise_label, premise_width);
    let conclusion_text = clip(&conclusion_label, room - premise_text.chars().count());
    let argument_label = format!(
        "Contraposition: not {}, from not {}",
        lower_first(&premise_text),
        lower_first(&conclusion_text)
    );
    let meaning = format!(
        "Contraposition of the verified argument {argument} at its premise {premise}: the negation of its conclusion {conclusion}, together with its other premises, gives the negation of that premise. The proof instantiates TruthCore.Logic.Inversion.contrapositive at the result theorem {theorem}."
    );
    let description = format!(
        "Logical transcription (instantiation): the proof instantiates the generic contraposition lemma TruthCore.Logic.Inversion.contrapositive at the verified result {theorem}. It adds no structure beyond that result, so by the transcription rule it closes its conclusion only when every premise, including the negated conclusion, is already closed."
    );
    spec.push_str(&format!(
        "\n[[argument]]\nid = {}\nlabel = {}\ntheorem = \"contrapositive\"\npremises = {}\nconclusion = {}\nrule = \"contraposition (modus tollens) of a verified result\"\nmeaning = {}\ndescription = {}\ntranscription = \"instantiation\"\n",
        toml(&argument_label),
        toml(&argument_label),
        toml_list(&spec_premises),
        toml(&handle(&negated_premise)),
        toml(&meaning),
        toml(&description)
    ));
    if let Some(senses) = record.get("term_senses").and_then(Value::as_object)
        && !senses.is_empty()
    {
        let pairs: Vec<String> = senses
            .iter()
            .filter_map(|(term, sense)| sense.as_str().map(|s| format!("{term} = {}", toml(s))))
            .collect();
        spec.push_str(&format!("senses = {{{}}}\n", pairs.join(", ")));
    }
    let spec_path = format!("specs/inversion-{}.toml", kebab(&name));
    files.push((spec_path.clone(), spec));
    let reused = [
        ("negated_conclusion", &negated_conclusion),
        ("negated_premise", &negated_premise),
    ]
    .into_iter()
    .filter_map(|(role, negation)| {
        negation
            .statement
            .as_ref()
            .map(|id| (role.to_owned(), id.clone()))
    })
    .collect();
    let solution_module = format!("{results_module}.Solution");
    let commands = vec![
        format!(
            "python3 scripts/argument_batch.py challenge {solution_path} contrapositive --write"
        ),
        format!("python3 scripts/argument_batch.py records {spec_path} --write --fix"),
        "scripts/root-imports.sh --write".to_owned(),
        format!("python3 scripts/worker_env.py -- lake build {solution_module}"),
        "python3 scripts/corpus.py bind-check --result <new result id>".to_owned(),
        "scripts/verify-result.sh <new result id>".to_owned(),
    ];
    Ok(Plan {
        key: key.to_owned(),
        name,
        theorem: full_theorem,
        spec: spec_path,
        paths: files.iter().map(|(path, _)| path.clone()).collect(),
        files,
        reused,
        commands,
    })
}

/// Write the plan's files under `root`. Nothing is written when a file
/// exists with other content; an identical file is left alone.
pub fn write_plan(root: &Path, plan: &Plan) -> Result<Vec<(String, &'static str)>, String> {
    for (path, content) in &plan.files {
        let target = root.join(path);
        if target.exists() && fs::read_to_string(&target).ok().as_deref() != Some(content) {
            return Err(format!("{path} exists with other content; nothing written"));
        }
    }
    let mut written = Vec::new();
    for (path, content) in &plan.files {
        let target = root.join(path);
        if target.exists() {
            written.push((path.clone(), "unchanged"));
            continue;
        }
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent).map_err(|error| format!("{path}: {error}"))?;
        }
        fs::write(&target, content).map_err(|error| format!("{path}: {error}"))?;
        written.push((path.clone(), "written"));
    }
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::path::PathBuf;

    struct Dir(PathBuf);

    impl Drop for Dir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn write(root: &Path, relative: &str, text: &str) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    /// ARG (P1, P2 ⊢ C) with result theorem `M.Results.T.t`; the corpus
    /// already states ¬P1 as `NoP1`.
    fn fixture() -> Dir {
        use std::sync::atomic::{AtomicU32, Ordering};
        static NEXT: AtomicU32 = AtomicU32::new(0);
        let root = std::env::temp_dir().join(format!(
            "truth-inversion-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let statements = [
            ("P1", "M.Vocab.P1", "P1 holds."),
            ("P2", "M.Vocab.P2", "P2 holds."),
            ("C", "M.Vocab.C", "C holds."),
            ("NP1", "M.Vocab.NoP1", "P1 fails."),
        ];
        for (id, lean, paraphrase) in statements {
            write(
                &root,
                &format!("corpus/statements/{id}.json"),
                &json!({"id": id, "label": format!("statement {id}"), "paraphrase": paraphrase,
                    "lean_declaration": lean, "definition_ids": ["DEF-1"]})
                .to_string(),
            );
        }
        write(
            &root,
            "corpus/arguments/ARG.json",
            &json!({"id": "ARG", "label": "C from P1 and P2", "premise_statement_ids": ["P1", "P2"],
                "conclusion_statement_id": "C", "inference_ids": ["I-1"], "meaning": "m",
                "term_senses": {"TERM": "SENSE-1"}})
            .to_string(),
        );
        write(
            &root,
            "corpus/results/RES.json",
            &json!({"id": "RES", "argument_id": "ARG", "theorem": "M.Results.T.t",
                "solution_module": "M.Results.T.Solution", "challenge_module": "M.Results.T.Challenge",
                "comparator_config": "c", "status": "solution-present"})
            .to_string(),
        );
        write(
            &root,
            "TruthCore/Vocab.lean",
            "namespace M.Vocab\ndef P1 (x : Nat) : Prop := x = 1\ndef NoP1 (y : Nat) : Prop := ¬ P1 y\nend M.Vocab\n",
        );
        write(
            &root,
            "M/Results/T/Solution.lean",
            "module\n\npublic import M.Vocab\n\n@[expose] public section\n\nnamespace M.Results.T\nopen M.Vocab\n\ntheorem t {α : Type} (x : Nat) (h1 : P1 x)\n    (h2 : P2 x) : C x := by\n  exact sorry\n\nend M.Results.T\n",
        );
        Dir(root)
    }

    fn file<'a>(plan: &'a Plan, suffix: &str) -> &'a str {
        plan.files
            .iter()
            .find(|(path, _)| path.ends_with(suffix))
            .map(|(_, text)| text.as_str())
            .unwrap_or_else(|| panic!("no {suffix} in {:?}", plan.paths))
    }

    #[test]
    fn a_contrapositive_reuses_an_existing_negation() {
        let dir = fixture();
        let corpus = Corpus::load(&dir.0).unwrap();
        let plan =
            plan_contrapositive(&dir.0, &corpus, "contrapositive:ARG:P1", "ARG", "P1", "RES")
                .unwrap();
        assert_eq!(plan.name, "TContra1");
        assert_eq!(
            plan.theorem,
            "TruthCore.Results.Logic.Inversions.TContra1.contrapositive"
        );
        assert_eq!(
            plan.reused,
            [("negated_premise".to_owned(), "NP1".to_owned())]
        );
        let solution = file(&plan, "Solution.lean");
        for needle in [
            "public import M.Results.T.Solution",
            "public import TruthCore.Logic.Inversion",
            "public import TruthCore.Logic.Inversions.TContra1",
            "open M.Results.T\nopen M.Vocab",
            "    {α : Type}\n    (x : Nat)\n    (hNotConclusion : TruthCore.Logic.Inversions.TContra1.NotC x)\n    (h2 : P2 x)\n    : M.Vocab.NoP1 x :=",
            "TruthCore.Logic.Inversion.contrapositive\n    (fun h1 => M.Results.T.t x h1 h2) hNotConclusion",
        ] {
            assert!(
                solution.contains(needle),
                "{needle} missing from\n{solution}"
            );
        }
        let vocabulary = file(&plan, "Inversions/TContra1.lean");
        assert!(vocabulary.contains("def NotC {α : Type} (x : Nat) : Prop :=\n  ¬ (C x)"));
        let spec = file(&plan, ".toml");
        assert_eq!(plan.spec, "specs/inversion-t-contra-1.toml");
        for needle in [
            "vocab = \"TruthCore.Logic.Inversions.TContra1\"",
            "label = \"Negation: statement C\"",
            "lean = \"NotC\"",
            "paraphrase = \"The negation of statement C, introduced by a materialized contraposition: it is not the case that the following holds. C holds.\"",
            "definitions = [\"DEF-1\"]",
            "premises = [\"Negation: statement C\", \"P2\"]",
            "conclusion = \"NP1\"",
            "transcription = \"instantiation\"",
            "description = \"Logical transcription (instantiation):",
            "senses = {TERM = \"SENSE-1\"}",
        ] {
            assert!(spec.contains(needle), "{needle} missing from\n{spec}");
        }
        // Written once; a rerun leaves identical files alone; other
        // content is never overwritten.
        let written = write_plan(&dir.0, &plan).unwrap();
        assert!(written.iter().all(|(_, status)| *status == "written"));
        let again = write_plan(&dir.0, &plan).unwrap();
        assert!(again.iter().all(|(_, status)| *status == "unchanged"));
        fs::write(dir.0.join(&plan.spec), "edited").unwrap();
        assert!(
            write_plan(&dir.0, &plan)
                .unwrap_err()
                .contains("other content")
        );
    }

    #[test]
    fn a_contrapositive_negates_both_ends_when_needed() {
        let dir = fixture();
        let corpus = Corpus::load(&dir.0).unwrap();
        let plan = plan_contrapositive(&dir.0, &corpus, "k", "ARG", "P2", "RES").unwrap();
        assert_eq!(plan.name, "TContra2");
        assert!(plan.reused.is_empty());
        let vocabulary = file(&plan, "Inversions/TContra2.lean");
        assert!(vocabulary.contains("def NotC "));
        assert!(vocabulary.contains("def NotP2 "));
        let solution = file(&plan, "Solution.lean");
        assert!(
            solution.contains("(h1 : P1 x)\n    : TruthCore.Logic.Inversions.TContra2.NotP2 x :=")
        );
        assert!(solution.contains("(fun h2 => M.Results.T.t x h1 h2)"));
        assert!(
            plan_contrapositive(&dir.0, &corpus, "k", "ARG", "C", "RES")
                .unwrap_err()
                .contains("not a premise")
        );
    }

    #[test]
    fn headers_without_named_premise_hypotheses_are_refused() {
        let dir = fixture();
        write(
            &dir.0,
            "M/Results/T/Solution.lean",
            "namespace M.Results.T\ntheorem t (x : Nat) : P1 x → P2 x → C x := sorry\nend M.Results.T\n",
        );
        let corpus = Corpus::load(&dir.0).unwrap();
        let error = plan_contrapositive(&dir.0, &corpus, "k", "ARG", "P1", "RES").unwrap_err();
        assert!(error.contains("not materialized"), "{error}");
    }

    #[test]
    fn sense_mixing_sources_are_refused() {
        let dir = fixture();
        write(
            &dir.0,
            "corpus/sense-index-allowlist.json",
            &json!({"arguments": {"ARG": {"TERM": ["S1", "S2"]}}}).to_string(),
        );
        let corpus = Corpus::load(&dir.0).unwrap();
        let error = plan_contrapositive(&dir.0, &corpus, "k", "ARG", "P1", "RES").unwrap_err();
        assert!(error.contains("allowlist"), "{error}");
    }

    #[test]
    fn helpers() {
        assert_eq!(
            kebab("RoweDeductiveCoreContra1"),
            "rowe-deductive-core-contra-1"
        );
        assert_eq!(kebab("TContra1"), "t-contra-1");
        assert_eq!(kebab("MARG1Contra2"), "marg-1-contra-2");
        assert_eq!(clip("one two three four", 9), "one two…");
        assert_eq!(lower_first("No being"), "no being");
        assert_eq!(lower_first("GOD_4 exists"), "GOD_4 exists");
    }
}
