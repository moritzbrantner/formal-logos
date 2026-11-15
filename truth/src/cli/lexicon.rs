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
            let value = lexicon::show(&loaded, word, limit(args, 15)?);
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
            let value = lexicon::coverage(&loaded, &config, limit(args, 25)?);
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
