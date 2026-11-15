//! `truth lexicon …`: the prose lexicon (#1652, `docs/lexicon.md`).
//!
//! - `show WORD` — the entries a word resolves to, their senses and uses;
//! - `untraced [--limit N]` — untraced words by frequency (the L2 worklist);
//! - `coverage [--limit N]` — token and type coverage, top untraced words;
//! - `check` — the lexicon part of `truth check` on its own;
//! - `bootstrap [--write]` — function-word and technical entries;
//! - `allowlist [--write]` — regenerate the shrink-only allowlist (seeds it
//!   when absent, otherwise only removes what is no longer needed);
//! - `ratchet --base REV` — fail when the allowlist grew since REV.

use super::{Accepts, Args, Command, Output, usage};
use serde_json::{Value, json};
use std::{fs, process};
use truth::definition_status;
use truth::lexicon::{self, Loaded, bootstrap};

pub const COMMAND: Command = Command {
    name: "lexicon",
    run,
};

fn error(message: impl Into<String>) -> super::Failure {
    (
        1,
        json!({"code": "lexicon_error", "message": message.into()}),
    )
}

fn loaded(args: &Args) -> Result<Loaded, super::Failure> {
    lexicon::load(&args.root).map_err(error)?.ok_or_else(|| {
        error(format!(
            "{} does not exist; run `truth lexicon bootstrap --write`",
            lexicon::DIRECTORY
        ))
    })
}

fn limit(args: &Args, default: usize) -> Result<usize, super::Failure> {
    if args.research.all || args.research.related.is_some() || args.research.frontier.is_some() {
        return Err(usage(
            "lexicon takes --limit N, not --all, --related or --frontier-json",
        ));
    }
    match args.research.limit {
        None => Ok(default),
        Some(n) if n > 0 => Ok(n as usize),
        Some(_) => Err(usage("--limit requires a positive integer")),
    }
}

fn run(args: &Args, operands: &[&str]) -> Output {
    let Some((sub, rest)) = operands.split_first() else {
        return Err(usage(
            "lexicon requires show, untraced, coverage, check, bootstrap, allowlist or ratchet",
        ));
    };
    let revisions = *sub == "ratchet";
    args.check_options(Accepts {
        revisions,
        ..Accepts::default()
    })?;
    if args.frontier.head.is_some() {
        return Err(usage("lexicon ratchet takes --base only"));
    }
    if args.write && !matches!(*sub, "bootstrap" | "allowlist") {
        return Err(usage(
            "--write applies only to lexicon bootstrap and lexicon allowlist",
        ));
    }
    if args.research.flags && !matches!(*sub, "show" | "untraced" | "coverage") {
        return Err(usage(
            "--limit applies only to lexicon show, untraced and coverage",
        ));
    }
    match (*sub, rest) {
        ("show", [word]) => {
            let loaded = loaded(args)?;
            let mut value = lexicon::show(&loaded, word, limit(args, 15)?);
            add_formal_status(args, &loaded, &mut value)?;
            let text = show_text(&value);
            Ok((value, Some(text)))
        }
        ("untraced", []) => {
            let loaded = loaded(args)?;
            let rows = lexicon::untraced(&loaded, limit(args, 50)?);
            let text = rows
                .iter()
                .map(|row| {
                    format!(
                        "{:>6}  {:<24} {} fields, e.g. {}",
                        row["occurrences"],
                        row["word"].as_str().unwrap_or_default(),
                        row["fields"],
                        row["example"].as_str().unwrap_or_default()
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
            Ok((json!({"schema_version": 1, "untraced": rows}), Some(text)))
        }
        ("coverage", []) => {
            let loaded = loaded(args)?;
            let config = lexicon::read_config(&args.root).map_err(error)?;
            let mut value = lexicon::coverage(&loaded, &config, limit(args, 25)?);
            let formal = formal_definitions(args, &loaded)?;
            value["formal_status"] = truth::definition_status::coverage_split(&loaded, &formal);
            let text = coverage_text(&value);
            Ok((value, Some(text)))
        }
        ("check", []) => match lexicon::check(&args.root).map_err(error)? {
            None => Err(error(format!("{} does not exist", lexicon::DIRECTORY))),
            Some(report) => {
                let summary = report.summary();
                let mut text: Vec<String> = report
                    .new_violations
                    .iter()
                    .map(|line| format!("warning: lexicon: {line}"))
                    .collect();
                text.push(summary.clone());
                Ok((
                    json!({"schema_version": 1, "ok": true, "summary": summary, "strict": report.strict, "new_violations": report.new_violations, "warnings": report.warnings}),
                    Some(text.join("\n")),
                ))
            }
        },
        ("bootstrap", []) => {
            let corpus = truth::Corpus::load(&args.root)
                .map_err(|e| error(format!("{}: {}", e.path, e.message)))?;
            let senses = lexicon::Senses::new(&corpus);
            let plan = bootstrap::plan(&args.root, &corpus, &senses).map_err(error)?;
            if args.write {
                fs::create_dir_all(args.root.join(lexicon::DIRECTORY))
                    .map_err(|e| error(e.to_string()))?;
                for (path, content) in &plan.writes {
                    fs::write(args.root.join(path), content)
                        .map_err(|e| error(format!("{path}: {e}")))?;
                }
            }
            let text = format!(
                "lexicon bootstrap{}: created {} technical and {} function entries, updated {}, unchanged {}",
                if args.write {
                    ""
                } else {
                    " (dry run; --write to apply)"
                },
                plan.created.get("technical").unwrap_or(&0),
                plan.created.get("function").unwrap_or(&0),
                plan.updated,
                plan.unchanged
            );
            Ok((
                json!({"schema_version": 1, "written": args.write, "created": plan.created, "updated": plan.updated, "unchanged": plan.unchanged, "paths": plan.writes.iter().map(|(p, _)| p).collect::<Vec<_>>()}),
                Some(text),
            ))
        }
        ("allowlist", []) => {
            let loaded = loaded(args)?;
            let existing = lexicon::read_allowlist(&args.root).map_err(error)?;
            let needed = lexicon::needed_allowlist(&loaded.scans, existing.as_ref());
            let rendered = lexicon::render_allowlist(&needed);
            // Compare the bytes, so a schema-1 file is rewritten as schema 2.
            let changed = fs::read_to_string(args.root.join(lexicon::ALLOWLIST)).ok()
                != Some(rendered.clone());
            if args.write && changed {
                fs::write(args.root.join(lexicon::ALLOWLIST), &rendered)
                    .map_err(|e| error(e.to_string()))?;
            }
            let text = format!(
                "{}: {} fields{}{}",
                lexicon::ALLOWLIST,
                needed.len(),
                if existing.is_none() {
                    " (seeded from the current corpus)"
                } else {
                    ""
                },
                match (changed, args.write) {
                    (false, _) => "; unchanged",
                    (true, true) => "; written",
                    (true, false) => "; would change (--write to apply)",
                }
            );
            Ok((
                json!({"schema_version": 1, "fields": needed.len(), "changed": changed, "written": args.write && changed}),
                Some(text),
            ))
        }
        ("ratchet", []) => {
            let Some(base) = args.frontier.base.as_deref() else {
                return Err(usage("lexicon ratchet requires --base REV"));
            };
            let head = lexicon::read_allowlist(&args.root)
                .map_err(error)?
                .unwrap_or_default();
            let shown = process::Command::new("git")
                .arg("-C")
                .arg(&args.root)
                .args(["show", &format!("{base}:{}", lexicon::ALLOWLIST)])
                .output()
                .map_err(|e| error(format!("git show: {e}")))?;
            if !shown.status.success() {
                let text = format!(
                    "lexicon ratchet: {} is new at {base}; nothing to compare",
                    lexicon::ALLOWLIST
                );
                return Ok((
                    json!({"schema_version": 1, "ok": true, "grown": []}),
                    Some(text),
                ));
            }
            let base_list =
                lexicon::parse_allowlist(&String::from_utf8_lossy(&shown.stdout)).map_err(error)?;
            let grown = lexicon::ratchet(&base_list, &head);
            if grown.is_empty() {
                let removed = base_list.len().saturating_sub(head.len());
                return Ok((
                    json!({"schema_version": 1, "ok": true, "grown": []}),
                    Some(format!(
                        "lexicon ratchet: ok ({removed} fields fewer than {base})"
                    )),
                ));
            }
            let mut message = format!(
                "{} may only shrink (#1652): trace the words (lexicon entries or forms) or link a sense instead of allowlisting them",
                lexicon::ALLOWLIST
            );
            for line in &grown {
                message.push_str("\n  ");
                message.push_str(line);
            }
            Err((
                1,
                json!({"code": "lexicon_ratchet", "message": message, "grown": grown}),
            ))
        }
        _ => Err(usage(
            "usage: truth lexicon (show WORD | untraced | coverage | check | bootstrap [--write] | allowlist [--write] | ratchet --base REV)",
        )),
    }
}

/// The formal status of every definition (#1652 L3), from the committed
/// cache; no Lean runs.
fn formal_definitions(
    args: &Args,
    loaded: &Loaded,
) -> Result<Vec<definition_status::Definition>, super::Failure> {
    Ok(definition_status::load(&args.root, &loaded.corpus)
        .map_err(error)?
        .definitions)
}

/// Adds `formal` to every definition and sense `show` lists: word → sense →
/// definition → Lean declaration and its computed kind, or the prose
/// fallback and why.
fn add_formal_status(
    args: &Args,
    loaded: &Loaded,
    value: &mut Value,
) -> Result<(), super::Failure> {
    let formal = formal_definitions(args, loaded)?;
    let describe = |id: &str| -> Value {
        formal
            .iter()
            .find(|definition| definition.id == id)
            .map(|definition| {
                definition_status::describe(
                    definition,
                    loaded.corpus.get("definitions", id).map(|r| &r.fields),
                )
            })
            .unwrap_or(Value::Null)
    };
    for entry in value["entries"].as_array_mut().into_iter().flatten() {
        for definition in entry["definitions"].as_array_mut().into_iter().flatten() {
            let id = definition["id"].as_str().unwrap_or_default().to_owned();
            definition["formal"] = describe(&id);
        }
        for disambiguation in entry["disambiguations"]
            .as_array_mut()
            .into_iter()
            .flatten()
        {
            for sense in disambiguation["senses"]
                .as_array_mut()
                .into_iter()
                .flatten()
            {
                let id = sense["definition_id"]
                    .as_str()
                    .unwrap_or_default()
                    .to_owned();
                sense["formal"] = describe(&id);
            }
        }
    }
    Ok(())
}

fn clip(text: &str, n: usize) -> String {
    let mut out: String = text.chars().take(n).collect();
    if text.chars().count() > n {
        out.push('…');
    }
    out
}

/// The lines of one `formal` description, indented by `pad`.
fn formal_lines(formal: &Value, pad: &str) -> Vec<String> {
    let mut lines = Vec::new();
    let status = formal["status"].as_str().unwrap_or_default();
    if let Some(declaration) = formal["lean_declaration"].as_str() {
        let mut line = format!("{pad}lean: {declaration} — {status}");
        if let Some(kind) = formal["kind"].as_str() {
            line.push_str(&format!(
                " ({kind}: {})",
                formal["reason"].as_str().unwrap_or_default()
            ));
        }
        lines.push(line);
        if let Some(head) = formal["head"].as_str() {
            lines.push(format!("{pad}  unfolds to {head}"));
        }
        let constants: Vec<&str> = formal["constants"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        if !constants.is_empty() {
            lines.push(format!("{pad}  uses {}", constants.join(", ")));
        }
    } else {
        lines.push(format!("{pad}lean: none — {status}"));
    }
    let prose = &formal["prose"];
    match prose["source"].as_str() {
        Some("formal_gap") => {
            let gap = &prose["formal_gap"];
            lines.push(format!(
                "{pad}prose (formal_gap, {}): {}",
                gap["kind"].as_str().unwrap_or_default(),
                clip(gap["meaning"].as_str().unwrap_or_default(), 200)
            ));
            for field in ["examples", "exclusions", "open_obligations"] {
                let items: Vec<&str> = gap[field]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .collect();
                if !items.is_empty() {
                    lines.push(format!("{pad}  {field}: {}", items.join("; ")));
                }
            }
        }
        Some(_) => lines.push(format!(
            "{pad}prose fallback ({}): {}",
            prose["reason"].as_str().unwrap_or_default(),
            clip(prose["definition"].as_str().unwrap_or_default(), 200)
        )),
        None => {}
    }
    lines
}

fn show_text(value: &Value) -> String {
    let mut lines = Vec::new();
    let word = value["word"].as_str().unwrap_or_default();
    if value["traced"] != json!(true) {
        lines.push(format!("{word}: untraced (no lexicon entry or form)"));
    }
    for entry in value["entries"].as_array().into_iter().flatten() {
        lines.push(format!(
            "{} [{}] {} — {}",
            entry["lemma"].as_str().unwrap_or_default(),
            entry["class"].as_str().unwrap_or_default(),
            entry["path"].as_str().unwrap_or_default(),
            entry["label"].as_str().unwrap_or_default()
        ));
        for field in ["category", "gloss", "technical_separation"] {
            if let Some(text) = entry[field].as_str() {
                lines.push(format!("  {field}: {text}"));
            }
        }
        if let Some(forms) = entry["forms"].as_array().filter(|f| !f.is_empty()) {
            let forms: Vec<&str> = forms.iter().filter_map(Value::as_str).collect();
            lines.push(format!("  forms: {}", forms.join(", ")));
        }
        for definition in entry["definitions"].as_array().into_iter().flatten() {
            lines.push(format!(
                "  definition {} — {}",
                &definition["id"].as_str().unwrap_or_default()
                    [..8.min(definition["id"].as_str().unwrap_or_default().len())],
                definition["label"].as_str().unwrap_or_default()
            ));
            lines.extend(formal_lines(&definition["formal"], "    "));
        }
        for disambiguation in entry["disambiguations"].as_array().into_iter().flatten() {
            let senses: Vec<&str> = disambiguation["senses"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|s| s["label"].as_str())
                .collect();
            lines.push(format!(
                "  disambiguation {} — {} ({})",
                &disambiguation["id"].as_str().unwrap_or_default()[..8],
                disambiguation["label"].as_str().unwrap_or_default(),
                senses.join(", ")
            ));
            for sense in disambiguation["senses"].as_array().into_iter().flatten() {
                let id = sense["definition_id"].as_str().unwrap_or_default();
                lines.push(format!(
                    "    {} → definition {}",
                    sense["label"].as_str().unwrap_or_default(),
                    &id[..8.min(id.len())]
                ));
                lines.extend(formal_lines(&sense["formal"], "      "));
            }
        }
    }
    lines.push(format!("used in {} prose fields", value["fields_using"]));
    for use_ in value["uses"].as_array().into_iter().flatten() {
        lines.push(format!(
            "  {}/{} {}: {}{}",
            use_["kind"].as_str().unwrap_or_default(),
            &use_["id"].as_str().unwrap_or_default()
                [..8.min(use_["id"].as_str().unwrap_or_default().len())],
            use_["field"].as_str().unwrap_or_default(),
            use_["label"].as_str().unwrap_or_default(),
            if use_["unlinked"] == json!(true) {
                "  [links none of its senses]"
            } else {
                ""
            }
        ));
    }
    lines.join("\n")
}

fn percent(part: &Value, whole: &Value) -> String {
    let (part, whole) = (part.as_f64().unwrap_or(0.0), whole.as_f64().unwrap_or(0.0));
    if whole == 0.0 {
        return "n/a".into();
    }
    format!("{:.1}%", 100.0 * part / whole)
}

fn coverage_text(value: &Value) -> String {
    let mut lines = vec![
        format!(
            "entries: {} {}",
            value["entries"], value["entries_by_class"]
        ),
        format!(
            "tokens: {} of {} traced ({}); by class {}; sense tags {}",
            value["tokens_traced"],
            value["tokens"],
            percent(&value["tokens_traced"], &value["tokens"]),
            value["tokens_by_class"],
            value["tokens_sense_tags"]
        ),
        format!(
            "types: {} of {} traced ({})",
            value["types_traced"],
            value["types"],
            percent(&value["types_traced"], &value["types"])
        ),
        format!(
            "prose fields fully traced: {} of {}; unlinked multi-sense uses: {}",
            value["fields_fully_traced"], value["fields"], value["unlinked_multi_sense_uses"]
        ),
        {
            let coverage = value["token_coverage"].as_f64().unwrap_or(0.0);
            let threshold = value["strict_token_coverage"].as_f64().unwrap_or(0.0);
            format!(
                "strict threshold: {:.1}% of tokens; now {:.1}% ({} more tokens to trace); strict mode {}",
                100.0 * threshold,
                100.0 * coverage,
                value["tokens_to_threshold"],
                if value["strict"] == json!(true) {
                    "on"
                } else if coverage >= threshold {
                    "off — threshold reached, set strict in corpus/lexicon-config.json"
                } else {
                    "off (new or changed fields warn)"
                }
            )
        },
        {
            let formal = &value["formal_status"];
            let buckets = &formal["buckets"];
            let n = |key: &str| buckets[key].as_u64().unwrap_or(0);
            format!(
                "technical tokens by formal status ({} tokens): settled by a Lean definition {}; Lean primitive/constraint with formal_gap prose {}; without prose (backlog) {}; definition without a Lean declaration {}; technical entry without a definition {}; status not computed {}. Prose-only (ordinary, function, name) tokens: {}",
                formal["technical_tokens"],
                n("lean_defined"),
                n("lean_gap_with_prose"),
                n("lean_gap_without_prose"),
                n("definition_without_lean"),
                n("technical_without_definition"),
                n("not_computed"),
                formal["prose_only"]
            ) + &format!(
                "\n  (a token counts in the weakest status over the definitions its entries reach); most frequent without prose: {}",
                formal["top_without_prose"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .take(10)
                    .map(|row| format!(
                        "{} {}",
                        row["word"].as_str().unwrap_or_default(),
                        row["occurrences"]
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        },
        "top untraced:".into(),
    ];
    for row in value["top_untraced"].as_array().into_iter().flatten() {
        lines.push(format!(
            "  {:>6}  {}",
            row["occurrences"],
            row["word"].as_str().unwrap_or_default()
        ));
    }
    for warning in value["entry_warnings"].as_array().into_iter().flatten() {
        lines.push(format!("warning: {}", warning.as_str().unwrap_or_default()));
    }
    lines.join("\n")
}
