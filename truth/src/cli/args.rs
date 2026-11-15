//! The shared option parser and the option checks commands share.

use super::{Failure, HELP, usage};
use serde_json::json;
use std::{ffi::OsString, path::PathBuf};
use truth::{bridges, orphans, thickness};

#[derive(Default)]
pub struct BridgeArgs {
    pub constants: Option<String>,
    pub queue: Option<String>,
    pub targets: Vec<String>,
    pub limit: Option<usize>,
    pub options: bridges::Options,
}

#[derive(Default)]
pub struct FrontierArgs {
    pub reaching_root: bool,
    pub routes: bool,
    pub base: Option<String>,
    pub head: Option<String>,
}

/// The `bind-check` options.
#[derive(Default)]
pub struct BindArgs {
    /// Whether any of them was given.
    pub flags: bool,
    /// `--result ID`, repeatable.
    pub results: Vec<String>,
    /// `--affected`
    pub affected: bool,
    /// `--lean-json FILE`: a saved `scripts/BindTypes.lean` output.
    pub lean_json: Option<String>,
    /// `--print-lean-input`: print the exporter input and stop.
    pub print_input: bool,
}

/// The options of `unused-premises`, `lean-reuse` and `context --proof-use`
/// (the commands that orchestrate the proof-term exporters).
#[derive(Default)]
pub struct ProofArgs {
    /// `--strict` (`unused-premises`)
    pub strict: bool,
    /// `--review` (`lean-reuse`)
    pub review: bool,
    /// `--proof-use` (`context`)
    pub proof_use: bool,
    /// `--exemptions FILE` (`unused-premises`)
    pub exemptions: Option<String>,
    /// `--bind-json FILE`: a saved `bind-check --json` report (`unused-premises`).
    pub bind_json: Option<String>,
    /// `--usage-json FILE`: a saved exporter output (`unused-premises`, `lean-reuse`).
    pub usage_json: Option<String>,
    /// `--proof-use-json FILE`: a saved `scripts/LeanReuse.lean` output (`context`).
    pub proof_use_json: Option<String>,
}

impl ProofArgs {
    /// The options given, by their command-line names.
    pub fn given(&self) -> Vec<&'static str> {
        [
            ("--strict", self.strict),
            ("--review", self.review),
            ("--proof-use", self.proof_use),
            ("--exemptions", self.exemptions.is_some()),
            ("--bind-json", self.bind_json.is_some()),
            ("--usage-json", self.usage_json.is_some()),
            ("--proof-use-json", self.proof_use_json.is_some()),
        ]
        .into_iter()
        .filter_map(|(name, given)| given.then_some(name))
        .collect()
    }

    /// Rejects the options outside `allowed` that apply to `command`'s siblings.
    pub fn only(&self, command: &str, allowed: &[&str]) -> Result<(), Failure> {
        match self
            .given()
            .into_iter()
            .find(|name| !allowed.contains(name))
        {
            Some(name) => Err(usage(format!("{name} does not apply to {command}"))),
            None => Ok(()),
        }
    }
}

#[derive(Default)]
pub struct ResearchArgs {
    pub flags: bool,
    pub all: bool,
    pub limit: Option<i64>,
    pub related: Option<i64>,
    pub frontier: Option<String>,
}

/// Every option of every command, parsed in one pass in token order.
pub struct Args {
    pub machine: bool,
    pub root: PathBuf,
    pub positional: Vec<String>,
    pub bridge: BridgeArgs,
    pub bridge_flags: bool,
    pub queue: bool,
    pub senses: bool,
    pub group_by: Option<orphans::GroupBy>,
    pub frontier_root: String,
    pub frontier: FrontierArgs,
    pub research: ResearchArgs,
    pub bind: BindArgs,
    pub proof: ProofArgs,
}

/// The shared options a command accepts besides `--root` and `--json`;
/// [`Args::check_options`] rejects the others, in the original order.
#[derive(Clone, Copy, Default)]
pub struct Accepts {
    /// `--queue`
    pub queue: bool,
    /// `--frontier-root`
    pub frontier_root: bool,
    /// `--by` and `--senses`
    pub orphans: bool,
    /// `--reaching-root` and `--routes`
    pub frontier: bool,
    /// `--base` and `--head`
    pub revisions: bool,
}

fn number(value: Option<&str>, flag: &str) -> Result<usize, Failure> {
    value
        .and_then(|value| value.parse().ok())
        .filter(|&value: &usize| value > 0)
        .ok_or_else(|| usage(format!("{flag} requires a positive integer")))
}

fn integer(value: Option<&str>, flag: &str) -> Result<i64, Failure> {
    value
        .and_then(|value| value.parse().ok())
        .ok_or_else(|| usage(format!("{flag} requires an integer")))
}

/// Arguments stay OS-native so a non-UTF-8 `--root` path works; every other
/// argument must be UTF-8 text and is otherwise a usage error.
pub fn parse(args: &[OsString]) -> Result<Args, Failure> {
    let mut parsed = Args {
        machine: args.iter().any(|arg| arg == "--json"),
        root: PathBuf::from("."),
        positional: Vec::new(),
        bridge: BridgeArgs::default(),
        bridge_flags: false,
        queue: false,
        senses: false,
        group_by: None,
        frontier_root: thickness::DEFAULT_ROOT.to_owned(),
        frontier: FrontierArgs::default(),
        research: ResearchArgs::default(),
        bind: BindArgs::default(),
        proof: ProofArgs::default(),
    };
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let arg = arg.to_str().ok_or_else(|| {
            (
                2,
                json!({"code":"usage", "message": "arguments other than the --root path must be UTF-8"}),
            )
        })?;
        match arg {
            "--json" => {}
            "--queue" => parsed.queue = true,
            "--senses" => parsed.senses = true,
            "--by" => {
                parsed.group_by = Some(
                    args.next()
                        .and_then(|value| value.to_str())
                        .and_then(orphans::GroupBy::parse)
                        .ok_or_else(|| usage("--by requires module or family"))?,
                );
            }
            "--reaching-root" => parsed.frontier.reaching_root = true,
            "--affected" => {
                parsed.bind.flags = true;
                parsed.bind.affected = true;
            }
            "--print-lean-input" => {
                parsed.bind.flags = true;
                parsed.bind.print_input = true;
            }
            "--result" | "--lean-json" => {
                parsed.bind.flags = true;
                let value = args
                    .next()
                    .and_then(|value| value.to_str())
                    .ok_or_else(|| usage(format!("{arg} requires a UTF-8 value")))?
                    .to_owned();
                if arg == "--result" {
                    parsed.bind.results.push(value);
                } else {
                    parsed.bind.lean_json = Some(value);
                }
            }
            "--routes" => parsed.frontier.routes = true,
            "--strict" => parsed.proof.strict = true,
            "--review" => parsed.proof.review = true,
            "--proof-use" => parsed.proof.proof_use = true,
            "--exemptions" | "--bind-json" | "--usage-json" | "--proof-use-json" => {
                let value = args
                    .next()
                    .and_then(|value| value.to_str())
                    .ok_or_else(|| usage(format!("{arg} requires a UTF-8 path")))?
                    .to_owned();
                let proof = &mut parsed.proof;
                match arg {
                    "--exemptions" => proof.exemptions = Some(value),
                    "--bind-json" => proof.bind_json = Some(value),
                    "--usage-json" => proof.usage_json = Some(value),
                    _ => proof.proof_use_json = Some(value),
                }
            }
            "--base" | "--head" => {
                let value = args
                    .next()
                    .and_then(|value| value.to_str())
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| usage(format!("{arg} requires a revision")))?
                    .to_owned();
                if arg == "--base" {
                    parsed.frontier.base = Some(value);
                } else {
                    parsed.frontier.head = Some(value);
                }
            }
            "--frontier-root" => {
                parsed.frontier_root = args
                    .next()
                    .and_then(|value| value.to_str())
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| {
                        (
                            2,
                            json!({"code":"usage", "message": "--frontier-root requires a statement ID"}),
                        )
                    })?
                    .to_owned();
            }
            "--root" => {
                parsed.root = args.next().map(PathBuf::from).ok_or_else(|| {
                    (
                        2,
                        json!({"code":"usage", "message": "--root requires a path"}),
                    )
                })?;
            }
            "--all" => {
                parsed.research.flags = true;
                parsed.research.all = true;
            }
            "--limit" | "--related" | "--frontier-json" => {
                parsed.research.flags = true;
                let value = args.next().and_then(|value| value.to_str());
                match arg {
                    "--limit" => parsed.research.limit = Some(integer(value, arg)?),
                    "--related" => parsed.research.related = Some(integer(value, arg)?),
                    _ => {
                        parsed.research.frontier = Some(
                            value
                                .ok_or_else(|| usage(format!("{arg} requires a UTF-8 path")))?
                                .to_owned(),
                        )
                    }
                }
            }
            "--constants" | "--queue-file" | "--target" | "--targets" | "--top" | "--pool" => {
                parsed.bridge_flags = true;
                let value = args
                    .next()
                    .and_then(|value| value.to_str())
                    .map(str::to_owned);
                let text = value
                    .clone()
                    .ok_or_else(|| usage(format!("{arg} requires a UTF-8 value")))?;
                let bridge = &mut parsed.bridge;
                match arg {
                    "--constants" => bridge.constants = Some(text),
                    "--queue-file" => bridge.queue = Some(text),
                    "--target" => bridge.targets.push(text),
                    "--targets" => bridge.limit = Some(number(value.as_deref(), arg)?),
                    "--top" => bridge.options.top = number(value.as_deref(), arg)?,
                    _ => bridge.options.pool = number(value.as_deref(), arg)?,
                }
            }
            value if value.starts_with('-') => {
                return Err((
                    2,
                    json!({"code":"usage", "message":format!("unknown option {value}")}),
                ));
            }
            value => parsed.positional.push(value.to_owned()),
        }
    }
    Ok(parsed)
}

impl Args {
    /// Whether `--frontier-root` names a statement other than the default.
    pub fn frontier_root_set(&self) -> bool {
        self.frontier_root != thickness::DEFAULT_ROOT
    }

    /// Whether `--reaching-root`, `--routes`, `--base` or `--head` was given.
    pub fn frontier_flags(&self) -> bool {
        self.frontier.reaching_root
            || self.frontier.routes
            || self.frontier.base.is_some()
            || self.frontier.head.is_some()
    }

    /// The `--all`, `--limit`, `--related` and `--frontier-json` error, raised
    /// by every command except `related`, `dossier` and `context`.
    pub fn reject_research(&self) -> Result<(), Failure> {
        if self.research.flags {
            return Err(usage(
                "--all, --limit, --related and --frontier-json apply only to related, dossier and context",
            ));
        }
        Ok(())
    }

    /// The error for a malformed command line (no command, an unknown
    /// command, wrong operands or bridge options outside `bridges`): the
    /// research-option error when one was given, otherwise the usage text.
    pub fn shape_error(&self) -> Failure {
        match self.reject_research() {
            Err(failure) => failure,
            Ok(()) => usage(HELP),
        }
    }

    /// Rejects the shared options `accepts` leaves out, in the order and
    /// with the messages the CLI has always used.
    pub fn check_options(&self, accepts: Accepts) -> Result<(), Failure> {
        if !accepts.queue && self.queue {
            return Err(usage("--queue applies only to thickness"));
        }
        if !accepts.frontier_root && self.frontier_root_set() {
            return Err(usage(
                "--frontier-root applies only to thickness, frontier, frontier-diff, next-steps, orphans, dossier, context and unused-premises",
            ));
        }
        if !accepts.orphans && (self.senses || self.group_by.is_some()) {
            return Err(usage("--by and --senses apply only to orphans"));
        }
        if self.senses && self.group_by.is_some() {
            return Err(usage("--senses and --by are alternatives"));
        }
        if !accepts.frontier && (self.frontier.reaching_root || self.frontier.routes) {
            return Err(usage("--reaching-root and --routes apply only to frontier"));
        }
        if !accepts.revisions && (self.frontier.base.is_some() || self.frontier.head.is_some()) {
            return Err(usage("--base and --head apply only to frontier-diff"));
        }
        Ok(())
    }

    /// The common prologue of a command without research options: rejects
    /// research options, then any operand count other than `operands` or a
    /// bridge option (unless `bridge_options`), then the shared options
    /// outside `accepts`.
    pub fn simple(
        &self,
        operands: &[&str],
        expected: usize,
        bridge_options: bool,
        accepts: Accepts,
    ) -> Result<(), Failure> {
        self.reject_research()?;
        if operands.len() != expected || (self.bridge_flags && !bridge_options) {
            return Err(usage(HELP));
        }
        self.check_options(accepts)
    }
}
