//! `truth senses (report | allowlist | ratchet --base REV) [--write]`: Python
//! `scripts/sense_index.py report|allowlist|ratchet` (#954 B6).
//!
//! - `report [--write]` — the arguments that mix senses of one term without a
//!   sense bridge, as the generated `docs/notes/sense-index-migration.md`
//!   (printed, or written with `--write`); `--json` prints the mixing entries
//!   and the senses without a distinct Lean declaration;
//! - `allowlist [--write]` — regenerate `corpus/sense-index-allowlist.json`,
//!   or fail when it is stale;
//! - `ratchet --base REV` — fail when the allowlist gained an entry since REV
//!   (#1233); list entries that no longer fail and can be removed.

use super::{Accepts, Args, Command, Output, corpus_error, load, raw, raw_with_stderr, usage};
use serde_json::{Value, json};
use std::fs;
use truth::senses::{self, ALLOWLIST, NOTE};

pub const COMMAND: Command = Command {
    name: "senses",
    run,
};

const USAGE: &str =
    "usage: truth senses (report [--write] | allowlist [--write] | ratchet --base REV)";

fn failure(message: impl Into<String>) -> super::Failure {
    (
        1,
        json!({"code": "senses_error", "message": message.into()}),
    )
}

fn entries_text(entries: &[Vec<String>]) -> Vec<String> {
    entries.iter().map(|entry| entry.join(" / ")).collect()
}

fn run(args: &Args, operands: &[&str]) -> Output {
    let ratchet = operands.first() == Some(&"ratchet");
    args.reject_research()?;
    if operands.len() != 1 || args.bridge_flags {
        return Err(usage(USAGE));
    }
    args.check_options(Accepts {
        revisions: ratchet,
        ..Accepts::default()
    })?;
    if args.frontier.head.is_some() {
        return Err(usage("senses ratchet takes --base only"));
    }
    if args.write && ratchet {
        return Err(usage(
            "--write applies only to senses report and senses allowlist",
        ));
    }
    let (corpus, _, _) = load(args)?;
    let report = senses::report(&corpus).map_err(corpus_error)?;
    match operands[0] {
        "report" => {
            if args.write {
                fs::write(args.root.join(NOTE), report.text())
                    .map_err(|error| failure(format!("{NOTE}: {error}")))?;
                Ok((json!({"schema_version": 1, "written": NOTE}), None))
            } else if args.machine {
                let mut value = serde_json::to_value(&report).unwrap_or(Value::Null);
                value["schema_version"] = json!(1);
                Ok((value, None))
            } else {
                Err(raw(0, report.text()))
            }
        }
        "allowlist" => {
            let data = report.allowlist();
            let text = report.allowlist_text();
            let target = args.root.join(ALLOWLIST);
            let stale = fs::read_to_string(&target).ok().as_deref() != Some(text.as_str());
            if args.write {
                fs::write(&target, &text)
                    .map_err(|error| failure(format!("{ALLOWLIST}: {error}")))?;
            } else if stale {
                let message = format!("{ALLOWLIST} is stale; run with --write");
                return Err(if args.machine {
                    (1, json!({"code": "stale_allowlist", "message": message}))
                } else {
                    raw_with_stderr(1, String::new(), message + "\n")
                });
            }
            let summary = format!(
                "{} allowlisted argument(s), {} allowlisted sense(s) without a distinct Lean declaration",
                data["arguments"].as_object().map_or(0, |map| map.len()),
                data["senses_without_lean_declaration"]
                    .as_array()
                    .map_or(0, Vec::len)
            );
            Ok((
                json!({"schema_version": 1, "allowlist": data, "changed": stale, "written": args.write && stale}),
                Some(summary),
            ))
        }
        "ratchet" => {
            let Some(base) = args.frontier.base.as_deref() else {
                return Err(usage("senses ratchet requires --base REV"));
            };
            let head = senses::read_allowlist(&args.root).map_err(corpus_error)?;
            let outcome =
                senses::ratchet(&args.root, &corpus, &report, &head, base).map_err(failure)?;
            let stale = entries_text(&outcome.stale);
            let added = entries_text(&outcome.added);
            let value = json!({"schema_version": 1, "base": base, "ok": added.is_empty(),
                               "compared": outcome.compared, "stale": outcome.stale,
                               "added": outcome.added});
            let mut stdout: String = stale
                .iter()
                .map(|entry| format!("no longer needed, remove from {ALLOWLIST}: {entry}\n"))
                .collect();
            if !outcome.compared {
                stdout.push_str(&format!(
                    "sense ratchet: {ALLOWLIST} is new at {base}; nothing to compare\n"
                ));
            } else if added.is_empty() {
                let count = stale.len();
                stdout.push_str(&format!(
                    "sense ratchet: ok ({count} removable entr{})\n",
                    if count == 1 { "y" } else { "ies" }
                ));
            }
            if added.is_empty() {
                return if args.machine {
                    Ok((value, None))
                } else {
                    Err(raw(0, stdout))
                };
            }
            let mut stderr: String = added
                .iter()
                .map(|entry| format!("sense ratchet: entry added to {ALLOWLIST}: {entry}\n"))
                .collect();
            stderr.push_str(
                "sense ratchet: the legacy allowlists may only shrink (#1233); split the argument per sense, \
                 list a sense bridge, or give the sense its own Lean declaration instead\n",
            );
            if args.machine {
                let mut error = value;
                error["code"] = json!("sense_ratchet");
                error["message"] = json!(stderr.trim_end());
                Err((1, error))
            } else {
                Err(raw_with_stderr(1, stdout, stderr))
            }
        }
        _ => Err(usage(USAGE)),
    }
}
