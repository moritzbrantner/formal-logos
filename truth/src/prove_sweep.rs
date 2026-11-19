//! The cheap proof-discovery sweep (`truth prove-sweep`, docs/prove-sweep.md).
//!
//! Every frozen Challenge theorem (a `theorem … := by sorry` in a
//! `Challenge.lean`) is restated in a generated scratch file that imports the
//! Challenge's imports, once per tactic of a fixed portfolio, each copy under
//! its own `maxHeartbeats` budget. Lean elaborates many Challenges per run;
//! its JSON messages are mapped back to the copies by line, so one failing
//! copy never hides another. A transcription probe (`assumption`, or one
//! premise applied and the rest closed by `assumption`) flags likely
//! transcriptions (AGENTS.md invariant 16).
//!
//! The sweep is advisory and writes nothing: a closed copy still needs a
//! real Solution, Comparator and the usual gates, and a failure is
//! `unresolved`, never a refutation.

use crate::{
    structure::{self, os_error, rglob},
    subprocess::Finished,
};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

/// The portfolio, tried in order: (label, tactic).
pub const PORTFOLIO: &[(&str, &str)] = &[
    ("decide", "decide"),
    ("omega", "omega"),
    ("tauto", "tauto"),
    ("simp_all", "simp_all"),
    ("aesop", "aesop"),
    ("grind", "grind"),
    ("unfold+grind", "intros; prove_sweep_unfold; grind"),
    ("unfold+aesop", "intros; prove_sweep_unfold; aesop"),
];

/// The label of a target closed only by the transcription probe.
pub const PROBE_LABEL: &str = "premise-application";
const PROBE_TACTIC: &str = "prove_sweep_probe";
const PROBE_INFO: &str = "prove-sweep-probe: ";
const SORRY_WARNING: &str = "declaration uses `sorry`";

/// Imports the portfolio needs besides the Challenge's own (`tauto` is
/// Mathlib's; Aesop ships with Mathlib; `decide`, `omega`, `simp_all` and
/// `grind` are core).
const PORTFOLIO_IMPORTS: &[&str] = &["Mathlib.Tactic.Tauto", "Aesop"];

/// The scratch file's own tactics: `prove_sweep_unfold` delta-unfolds the
/// project (`TruthCore`) definitions in the goal and hypotheses, repeatedly;
/// `prove_sweep_probe` closes the goal by `assumption`, or by applying one
/// hypothesis and closing every remaining goal by `assumption`, `rfl`,
/// `True.intro` or one `constructor` split, and logs how.
pub const PRELUDE: &str = r#"open Lean Meta Elab Tactic in
elab "prove_sweep_unfold" : tactic => do
  for _ in [0:8] do
    let env ← getEnv
    let g ← getMainGoal
    let names ← g.withContext do
      let mut found : NameSet := {}
      let mut types := #[← g.getType]
      for decl in ← getLCtx do
        unless decl.isImplementationDetail do types := types.push decl.type
      for ty in types do
        for n in (← instantiateMVars ty).getUsedConstants do
          if (`TruthCore).isPrefixOf n then
            if let some (.defnInfo _) := env.find? n then found := found.insert n
      return found
    if names.isEmpty then return
    let ids := names.toArray.map mkIdent
    try evalTactic (← `(tactic| delta $ids* at *)) catch _ => return

open Lean Meta Elab Tactic in
elab "prove_sweep_probe" : tactic => do
  evalTactic (← `(tactic| intros))
  let g ← getMainGoal
  g.withContext do
    if (← observing? g.assumption).isSome then
      logInfo "prove-sweep-probe: assumption"
      setGoals []
      return
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless ← isProp decl.type do continue
      let saved ← saveState
      try
        let goals ← g.apply (mkFVar decl.fvarId)
        for sub in goals do
          unless ← sub.isAssigned do
            setGoals [sub]
            evalTactic (← `(tactic| first | assumption | rfl | exact True.intro | (constructor <;> assumption)))
        logInfo m!"prove-sweep-probe: apply {decl.userName}"
        setGoals []
        return
      catch _ => restoreState saved
    throwError "prove-sweep-probe: no single premise application"
"#;

// --- Challenge parsing ----------------------------------------------------------

/// A frozen Challenge theorem whose whole proof is `sorry`.
#[derive(Clone, Debug, PartialEq)]
pub struct Target {
    /// The fully qualified name.
    pub theorem: String,
    /// The byte range the copies replace (doc comment through `sorry`).
    pub span: (usize, usize),
    /// Binders and type: the text between the name and `:=`.
    pub statement: String,
}

/// A Challenge file: its module, imports, body (imports removed, module
/// syntax made ordinary) and targets (spans into the body).
#[derive(Clone, Debug)]
pub struct Challenge {
    pub module: String,
    pub imports: Vec<String>,
    pub body: String,
    pub targets: Vec<Target>,
}

/// `text` with comments and string literals blanked (same byte offsets),
/// and the ranges of the doc comments (`/-- … -/`).
fn mask(text: &str) -> (Vec<u8>, Vec<(usize, usize)>) {
    let bytes = text.as_bytes();
    let mut out = bytes.to_vec();
    let mut docs = Vec::new();
    let mut i = 0;
    let blank = |out: &mut Vec<u8>, from: usize, to: usize| {
        for byte in &mut out[from..to] {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
    };
    while i < bytes.len() {
        if bytes[i..].starts_with(b"--") {
            let end = bytes[i..]
                .iter()
                .position(|&b| b == b'\n')
                .map_or(bytes.len(), |n| i + n);
            blank(&mut out, i, end);
            i = end;
        } else if bytes[i..].starts_with(b"/-") {
            let doc = bytes[i..].starts_with(b"/--");
            let (mut depth, mut j) = (1, i + 2);
            while j < bytes.len() && depth > 0 {
                if bytes[j..].starts_with(b"/-") {
                    depth += 1;
                    j += 2;
                } else if bytes[j..].starts_with(b"-/") {
                    depth -= 1;
                    j += 2;
                } else {
                    j += 1;
                }
            }
            if doc {
                docs.push((i, j));
            }
            blank(&mut out, i, j);
            i = j;
        } else if bytes[i] == b'"' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j] != b'"' {
                j += if bytes[j] == b'\\' { 2 } else { 1 };
            }
            let end = (j + 1).min(bytes.len());
            blank(&mut out, i, end);
            i = end;
        } else {
            i += 1;
        }
    }
    (out, docs)
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.' || b == b'\'' || b >= 0x80
}

/// Whether `word` occurs at `at` in `masked` as a whole token.
fn token_at(masked: &[u8], at: usize, word: &str) -> bool {
    masked[at..].starts_with(word.as_bytes())
        && (at == 0 || !is_ident_byte(masked[at - 1]))
        && masked
            .get(at + word.len())
            .is_none_or(|&b| !is_ident_byte(b))
}

/// Turns a module-style Challenge into ordinary syntax and takes out its
/// imports: `(imports, body)`, the body with the same line structure.
fn split_imports(text: &str) -> (Vec<String>, String) {
    let mut imports = Vec::new();
    let mut body = Vec::new();
    for line in text.split('\n') {
        let trimmed = line.trim_start();
        let import = trimmed
            .strip_prefix("public import ")
            .or_else(|| trimmed.strip_prefix("import "));
        if let Some(rest) = import {
            imports.extend(rest.split_whitespace().map(str::to_owned));
            body.push(String::new());
        } else if trimmed == "module" {
            body.push(String::new());
        } else if trimmed.starts_with("@[expose] public section") {
            body.push(line.replacen("@[expose] public section", "section", 1));
        } else if let Some(rest) = line.strip_prefix("public ") {
            body.push(rest.to_owned());
        } else {
            body.push(line.to_owned());
        }
    }
    (imports, body.join("\n"))
}

/// The Challenge targets in `body`: theorems whose whole proof is `sorry`
/// (`:= sorry`, `:= by sorry`).
pub fn parse_targets(body: &str) -> Vec<Target> {
    let (masked, docs) = mask(body);

    let mut targets = Vec::new();
    // namespace stack: Some(name) for a namespace, None for a section
    let mut scopes: Vec<(Option<String>, Option<String>)> = Vec::new();
    let mut i = 0;
    while i < masked.len() {
        let at_line = i == 0 || masked[i - 1] == b'\n';
        if !at_line {
            i += 1;
            continue;
        }
        let end = masked[i..]
            .iter()
            .position(|&b| b == b'\n')
            .map_or(masked.len(), |n| i + n);
        let line = String::from_utf8_lossy(&masked[i..end]).into_owned();
        let words: Vec<&str> = line.split_whitespace().collect();
        let first = words.first().copied().unwrap_or("");
        match first {
            "namespace" if words.len() > 1 => scopes.push((Some(words[1].to_owned()), None)),
            "section" | "noncomputable" if words.contains(&"section") => {
                let name = words
                    .iter()
                    .skip_while(|w| **w != "section")
                    .nth(1)
                    .map(|w| w.to_string());
                scopes.push((None, name));
            }
            "end" => {
                let name = words.get(1).map(|w| w.to_string());
                // `end X` closes the innermost scope named X, `end` a section.
                if let Some(index) = scopes.iter().rposition(|(ns, section)| match &name {
                    Some(name) => ns.as_ref() == Some(name) || section.as_ref() == Some(name),
                    None => ns.is_none() && section.is_none(),
                }) {
                    scopes.truncate(index);
                }
            }
            _ => {}
        }
        // a declaration header on this line
        let mut k = i;
        let mut header = None;
        while k < end {
            if masked[k].is_ascii_whitespace() {
                k += 1;
                continue;
            }
            if masked[k..].starts_with(b"@[") {
                k += masked[k..]
                    .iter()
                    .position(|&b| b == b']')
                    .map_or(end - k, |n| n + 1);
                continue;
            }
            let mut matched = false;
            for word in ["private", "protected", "nonrec"] {
                if token_at(&masked, k, word) {
                    k += word.len();
                    matched = true;
                }
            }
            if matched {
                continue;
            }
            for word in ["theorem", "lemma"] {
                if token_at(&masked, k, word) {
                    header = Some(k + word.len());
                }
            }
            break;
        }
        let Some(after_keyword) = header else {
            i = end + 1;
            continue;
        };
        let name_start = after_keyword
            + masked[after_keyword..]
                .iter()
                .position(|b| !b.is_ascii_whitespace())
                .unwrap_or(0);
        let name_end = name_start
            + masked[name_start..]
                .iter()
                .position(|&b| b.is_ascii_whitespace() || b"(:{[".contains(&b))
                .unwrap_or(masked.len() - name_start);
        let name = &body[name_start..name_end];
        // the `:=` at bracket depth 0
        let mut depth = 0i32;
        let mut j = name_end;
        let mut assign = None;
        while j < masked.len() {
            match masked[j] {
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => depth -= 1,
                b':' if depth <= 0 && masked.get(j + 1) == Some(&b'=') => {
                    assign = Some(j);
                    break;
                }
                _ => {}
            }
            j += 1;
        }
        let Some(assign) = assign else {
            i = end + 1;
            continue;
        };
        // the proof runs to the next command (a line starting in column 0)
        let mut proof_end = masked.len();
        let mut p = assign + 2;
        while p < masked.len() {
            if masked[p] == b'\n' && masked.get(p + 1).is_some_and(|b| !b.is_ascii_whitespace()) {
                proof_end = p;
                break;
            }
            p += 1;
        }
        let proof: String = String::from_utf8_lossy(&masked[assign + 2..proof_end])
            .split_whitespace()
            .collect();
        if proof == "sorry" || proof == "bysorry" {
            let decl_start = i;
            let before = body[..decl_start].trim_end();
            let start = docs
                .iter()
                .find(|(_, doc_end)| *doc_end == before.len())
                .map_or(decl_start, |(doc_start, _)| *doc_start);
            let sorry_end = assign
                + 2
                + String::from_utf8_lossy(&masked[assign + 2..proof_end])
                    .trim_end()
                    .len();
            let mut namespace: Vec<String> =
                scopes.iter().filter_map(|(ns, _)| ns.clone()).collect();
            let theorem = match name.strip_prefix("_root_.") {
                Some(name) => name.to_owned(),
                None => {
                    namespace.push(name.to_owned());
                    namespace.join(".")
                }
            };
            targets.push(Target {
                theorem,
                span: (start, sorry_end),
                statement: body[name_end..assign].trim_end().to_owned(),
            });
        }
        i = proof_end.max(end);
    }
    targets
}

impl Challenge {
    pub fn parse(module: &str, text: &str) -> Self {
        let (imports, body) = split_imports(text);
        let targets = parse_targets(&body);
        Challenge {
            module: module.to_owned(),
            imports,
            body,
            targets,
        }
    }
}

/// Every Challenge under `TruthCore/`, by module name.
pub fn discover(root: &Path) -> Result<Vec<Challenge>, String> {
    let mut out = Vec::new();
    for path in rglob(&root.join("TruthCore"), "Challenge.lean") {
        if path.file_name().is_none_or(|name| name != "Challenge.lean") {
            continue;
        }
        let text = fs::read_to_string(&path).map_err(|error| os_error(&error, &path))?;
        let module = structure::relative(root, &path.with_extension("")).replace('/', ".");
        out.push(Challenge::parse(&module, &text));
    }
    Ok(out)
}

/// Whether `name` is selected by `filters` (exact, or a dotted suffix or
/// prefix of it); every name when there are none.
pub fn selected(name: &str, filters: &[String], prefix: bool) -> bool {
    filters.is_empty()
        || filters.iter().any(|filter| {
            name == filter
                || if prefix {
                    name.strip_prefix(filter.as_str())
                        .is_some_and(|rest| rest.starts_with('.'))
                } else {
                    name.strip_suffix(filter.as_str())
                        .is_some_and(|rest| rest.ends_with('.'))
                }
        })
}

// --- scratch generation -----------------------------------------------------------

/// What a generated copy tries.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Attempt {
    /// A portfolio entry (index into [`PORTFOLIO`]).
    Tactic(usize),
    Probe,
    /// `sorry`: shows the statement elaborates, and that Lean got this far.
    Control,
}

/// One generated copy: the target it restates, what it tries and its lines
/// (1-based, inclusive) in the scratch file.
#[derive(Clone, Debug)]
pub struct Copy {
    pub target: usize,
    pub attempt: Attempt,
    pub lines: (usize, usize),
}

/// A scratch file and the line map of its copies and chunks.
pub struct Scratch {
    pub text: String,
    pub copies: Vec<Copy>,
    /// Per chunk (Challenge): its index in the batch and lines.
    pub chunks: Vec<(usize, (usize, usize))>,
}

/// The scratch file for `challenges` (with the global index of each one's
/// first target): imports, the prelude, then each Challenge body with its
/// targets replaced by copies. With several Challenges each body is wrapped
/// in a `section`, so their `open`s do not leak.
pub fn generate(challenges: &[(&Challenge, usize)], heartbeats: u64) -> Scratch {
    let mut imports: BTreeSet<&str> = PORTFOLIO_IMPORTS.iter().copied().collect();
    for (challenge, _) in challenges {
        imports.extend(challenge.imports.iter().map(String::as_str));
    }
    let mut text: String = imports.iter().map(|m| format!("import {m}\n")).collect();
    text.push('\n');
    text.push_str(PRELUDE);
    let wrap = challenges.len() > 1;
    let mut copies = Vec::new();
    let mut chunks = Vec::new();
    let line = |text: &str| text.matches('\n').count() + 1;
    for (index, (challenge, first)) in challenges.iter().enumerate() {
        text.push('\n');
        let chunk_start = line(&text);
        if wrap {
            text.push_str("section\n");
        }
        let mut cursor = 0;
        for (offset, target) in challenge.targets.iter().enumerate() {
            let global = first + offset;
            text.push_str(&challenge.body[cursor..target.span.0]);
            let attempts = (0..PORTFOLIO.len())
                .map(Attempt::Tactic)
                .chain([Attempt::Probe, Attempt::Control]);
            for attempt in attempts {
                let (suffix, tactic) = match attempt {
                    Attempt::Tactic(k) => (k.to_string(), PORTFOLIO[k].1),
                    Attempt::Probe => ("probe".to_owned(), PROBE_TACTIC),
                    Attempt::Control => ("control".to_owned(), "sorry"),
                };
                let start = line(&text);
                text.push_str(&format!(
                    "set_option maxHeartbeats {heartbeats} in\ntheorem «prove_sweep_{global}_{suffix}»{} := by\n  {tactic}\n",
                    target.statement
                ));
                copies.push(Copy {
                    target: global,
                    attempt,
                    lines: (start, line(&text) - 1),
                });
                if attempt != Attempt::Control {
                    text.push('\n');
                }
            }
            cursor = target.span.1;
        }
        text.push_str(&challenge.body[cursor..]);
        if wrap {
            text.push_str("\nend\n");
        }
        chunks.push((index, (chunk_start, line(&text))));
    }
    Scratch {
        text,
        copies,
        chunks,
    }
}

// --- Lean messages and outcomes -----------------------------------------------------

/// A Lean message (`lean --json`): severity, line and text.
#[derive(Clone, Debug, PartialEq)]
pub struct Message {
    pub severity: String,
    pub line: usize,
    pub data: String,
}

/// The messages of `lean --json` output; other lines are ignored.
pub fn parse_messages(stdout: &str) -> Vec<Message> {
    stdout
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .filter_map(|value| {
            Some(Message {
                severity: value.get("severity")?.as_str()?.to_owned(),
                line: value.get("pos")?.get("line")?.as_u64()? as usize,
                data: value.get("data")?.as_str()?.to_owned(),
            })
        })
        .collect()
}

/// The verdict on one target.
#[derive(Clone, Debug, PartialEq)]
pub struct Outcome {
    pub theorem: String,
    pub module: String,
    /// `closed`, `unresolved` or `error`.
    pub status: &'static str,
    /// The first portfolio label that closed it (or [`PROBE_LABEL`]).
    pub closed_by: Option<String>,
    /// How the transcription probe closed it, if it did.
    pub transcription: Option<String>,
    pub message: Option<String>,
}

impl Outcome {
    pub fn to_json(&self) -> Value {
        let mut out = Map::new();
        out.insert("theorem".into(), json!(self.theorem));
        out.insert("module".into(), json!(self.module));
        out.insert("status".into(), json!(self.status));
        out.insert("closed_by".into(), json!(self.closed_by));
        out.insert(
            "likely_transcription".into(),
            json!(self.transcription.is_some()),
        );
        if let Some(how) = &self.transcription {
            out.insert("transcription_by".into(), json!(how));
        }
        if let Some(message) = &self.message {
            out.insert("message".into(), json!(message));
        }
        Value::Object(out)
    }
}

/// What the messages say about each copy: (errors, `sorry` warning, infos).
#[derive(Default)]
struct CopyMessages {
    errors: Vec<String>,
    sorry: bool,
    infos: Vec<String>,
}

fn first_line(text: &str) -> String {
    text.lines().next().unwrap_or_default().to_owned()
}

/// The outcomes of a run's targets, and the chunks that need a run of
/// their own: an error outside every copy, or a control that failed or was
/// never reached, makes the batch inconclusive for that chunk.
pub fn classify(
    scratch: &Scratch,
    messages: &[Message],
    names: &BTreeMap<usize, (String, String)>,
    chunk_of: &BTreeMap<usize, usize>,
) -> (Vec<(usize, Outcome)>, BTreeSet<usize>) {
    let mut per_copy: Vec<CopyMessages> = scratch
        .copies
        .iter()
        .map(|_| CopyMessages::default())
        .collect();
    let mut retry = BTreeSet::new();
    let mut stray: Option<String> = None;
    let first_chunk_line = scratch.chunks.first().map_or(usize::MAX, |(_, (s, _))| *s);
    for message in messages {
        match scratch
            .copies
            .iter()
            .position(|c| (c.lines.0..=c.lines.1).contains(&message.line))
        {
            Some(index) => {
                let slot = &mut per_copy[index];
                match message.severity.as_str() {
                    "error" => slot.errors.push(message.data.clone()),
                    "warning" if message.data.contains(SORRY_WARNING) => slot.sorry = true,
                    "information" => slot.infos.push(message.data.clone()),
                    _ => {}
                }
            }
            None if message.severity == "error" => {
                stray.get_or_insert_with(|| first_line(&message.data));
                if message.line < first_chunk_line {
                    retry.extend(scratch.chunks.iter().map(|(chunk, _)| *chunk));
                } else if let Some((chunk, _)) = scratch
                    .chunks
                    .iter()
                    .find(|(_, (s, e))| (*s..=*e).contains(&message.line))
                {
                    retry.insert(*chunk);
                }
            }
            None => {}
        }
    }
    let mut outcomes = Vec::new();
    let targets: BTreeSet<usize> = scratch.copies.iter().map(|c| c.target).collect();
    for target in targets {
        let chunk = chunk_of[&target];
        let (theorem, module) = names[&target].clone();
        let mut outcome = Outcome {
            theorem,
            module,
            status: "unresolved",
            closed_by: None,
            transcription: None,
            message: None,
        };
        let copies: Vec<(&Copy, &CopyMessages)> = scratch
            .copies
            .iter()
            .zip(&per_copy)
            .filter(|(c, _)| c.target == target)
            .collect();
        let control = copies
            .iter()
            .find(|(c, _)| c.attempt == Attempt::Control)
            .map(|(_, m)| *m);
        match control {
            Some(m) if !m.errors.is_empty() => {
                outcome.status = "error";
                outcome.message = Some(first_line(&m.errors[0]));
                retry.insert(chunk);
            }
            Some(m) if m.sorry => {
                let closed = |m: &CopyMessages| m.errors.is_empty() && !m.sorry;
                outcome.closed_by = copies.iter().find_map(|(c, m)| match c.attempt {
                    Attempt::Tactic(k) if closed(m) => Some(PORTFOLIO[k].0.to_owned()),
                    _ => None,
                });
                outcome.transcription = copies
                    .iter()
                    .find(|(c, m)| c.attempt == Attempt::Probe && closed(m))
                    .and_then(|(_, m)| {
                        m.infos
                            .iter()
                            .find_map(|info| info.strip_prefix(PROBE_INFO).map(str::to_owned))
                    });
                if outcome.closed_by.is_none() && outcome.transcription.is_some() {
                    outcome.closed_by = Some(PROBE_LABEL.to_owned());
                }
                if outcome.closed_by.is_some() {
                    outcome.status = "closed";
                }
            }
            _ => {
                outcome.status = "error";
                outcome.message = Some(
                    stray
                        .clone()
                        .unwrap_or_else(|| "Lean did not reach this theorem".to_owned()),
                );
                retry.insert(chunk);
            }
        }
        outcomes.push((target, outcome));
    }
    (outcomes, retry)
}

// --- running ------------------------------------------------------------------------------

/// Options of one sweep.
pub struct Options {
    pub heartbeats: u64,
    /// Challenges per Lean run.
    pub batch: usize,
}

fn lake(root: &Path, tail: &[String], timeout: Duration) -> Result<Option<Finished>, String> {
    let args: Vec<String> = ["scripts/worker_env.py", "--", "lake"]
        .iter()
        .map(|s| s.to_string())
        .chain(tail.iter().cloned())
        .collect();
    structure::run_bounded(root, "python3", &args, timeout)
}

/// Runs Lean on `scratch`: its messages, or why there are none.
fn run_lean(root: &Path, scratch: &Scratch) -> Result<Vec<Message>, String> {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_nanos());
    let directory =
        std::env::temp_dir().join(format!("truth-prove-sweep-{}-{nanos}", std::process::id()));
    let path = directory.join("ProveSweep.lean");
    fs::create_dir_all(&directory)
        .and_then(|()| fs::write(&path, &scratch.text))
        .map_err(|error| os_error(&error, &path))?;
    // generous: each copy is bounded by its heartbeats
    let timeout = Duration::from_secs(300 + 20 * scratch.copies.len() as u64);
    let done = lake(
        root,
        &[
            "env".into(),
            "lean".into(),
            "--json".into(),
            // every failed attempt is an error; Lean stops after `maxErrors` (100)
            "-DmaxErrors=1000000".into(),
            path.display().to_string(),
        ],
        timeout,
    );
    // `TRUTH_PROVE_SWEEP_KEEP` keeps the scratch file for debugging.
    if std::env::var_os("TRUTH_PROVE_SWEEP_KEEP").is_some() {
        eprintln!("prove-sweep: kept {}", path.display());
    } else {
        let _ = fs::remove_dir_all(&directory);
    }
    match done? {
        None => Err(format!("Lean timed out after {}s", timeout.as_secs())),
        Some(done) => {
            let messages = parse_messages(&done.stdout);
            if messages.is_empty() && !done.success {
                Err(format!("Lean failed: {}", first_line(done.stderr.trim())))
            } else {
                Ok(messages)
            }
        }
    }
}

/// Builds the modules the Challenges import (Lake owns freshness); a
/// failure is reported, and the affected targets then fail as errors.
pub fn build_imports(root: &Path, challenges: &[&Challenge]) -> Result<(), String> {
    let modules: BTreeSet<&str> = challenges
        .iter()
        .flat_map(|c| c.imports.iter().map(String::as_str))
        .filter(|m| m.starts_with("TruthCore"))
        .collect();
    if modules.is_empty() {
        return Ok(());
    }
    let tail: Vec<String> = ["build"]
        .into_iter()
        .chain(modules)
        .map(str::to_owned)
        .collect();
    match lake(root, &tail, Duration::from_secs(4 * 3600))? {
        Some(done) if done.success => Ok(()),
        Some(done) => Err(format!(
            "lake build failed: {}",
            first_line(done.stderr.trim())
                .chars()
                .take(300)
                .collect::<String>()
        )),
        None => Err("lake build timed out".into()),
    }
}

/// Sweeps `challenges` (only their listed targets): batches of
/// `options.batch` Challenges per Lean run, each inconclusive chunk again on
/// its own. `progress` is told each finished run.
pub fn sweep(
    root: &Path,
    challenges: &[Challenge],
    options: &Options,
    progress: &mut dyn FnMut(usize, usize),
) -> Vec<Outcome> {
    let mut names = BTreeMap::new();
    let mut chunk_of = BTreeMap::new();
    let mut firsts = Vec::new();
    let mut next = 0;
    for (index, challenge) in challenges.iter().enumerate() {
        firsts.push(next);
        for target in &challenge.targets {
            names.insert(next, (target.theorem.clone(), challenge.module.clone()));
            chunk_of.insert(next, index);
            next += 1;
        }
    }
    let mut results: BTreeMap<usize, Outcome> = BTreeMap::new();
    let indices: Vec<usize> = (0..challenges.len())
        .filter(|&i| !challenges[i].targets.is_empty())
        .collect();
    let batches: Vec<&[usize]> = indices.chunks(options.batch.max(1)).collect();
    let total = batches.len();
    for (done, batch) in batches.into_iter().enumerate() {
        let mut pending: Vec<Vec<usize>> = vec![batch.to_vec()];
        while let Some(group) = pending.pop() {
            let members: Vec<(&Challenge, usize)> =
                group.iter().map(|&i| (&challenges[i], firsts[i])).collect();
            let scratch = generate(&members, options.heartbeats);
            // chunk index within this scratch → challenge index
            let local: BTreeMap<usize, usize> = group.iter().copied().enumerate().collect();
            let chunk_local: BTreeMap<usize, usize> = chunk_of
                .iter()
                .filter_map(|(target, challenge)| {
                    group
                        .iter()
                        .position(|g| g == challenge)
                        .map(|position| (*target, position))
                })
                .collect();
            match run_lean(root, &scratch) {
                Ok(messages) => {
                    let (outcomes, retry) = classify(&scratch, &messages, &names, &chunk_local);
                    let rerun = group.len() > 1;
                    for (target, outcome) in outcomes {
                        let chunk = chunk_local[&target];
                        if rerun && retry.contains(&chunk) {
                            continue;
                        }
                        results.insert(target, outcome);
                    }
                    if rerun {
                        for chunk in retry {
                            pending.push(vec![local[&chunk]]);
                        }
                    }
                }
                Err(_) if group.len() > 1 => {
                    pending.extend(group.iter().map(|&i| vec![i]));
                }
                Err(message) => {
                    for (target, (theorem, module)) in &names {
                        if chunk_of[target] == group[0] {
                            results.insert(
                                *target,
                                Outcome {
                                    theorem: theorem.clone(),
                                    module: module.clone(),
                                    status: "error",
                                    closed_by: None,
                                    transcription: None,
                                    message: Some(message.clone()),
                                },
                            );
                        }
                    }
                }
            }
        }
        progress(done + 1, total);
    }
    results.into_values().collect()
}

/// Counts per status and per closing tactic, in portfolio order.
pub fn summary(outcomes: &[Outcome]) -> Value {
    let count = |status: &str| outcomes.iter().filter(|o| o.status == status).count();
    let mut by_tactic = Map::new();
    for label in PORTFOLIO
        .iter()
        .map(|(label, _)| *label)
        .chain([PROBE_LABEL])
    {
        let n = outcomes
            .iter()
            .filter(|o| o.closed_by.as_deref() == Some(label))
            .count();
        by_tactic.insert(label.to_owned(), json!(n));
    }
    json!({
        "targets": outcomes.len(),
        "closed": count("closed"),
        "unresolved": count("unresolved"),
        "error": count("error"),
        "closed_by": by_tactic,
        "likely_transcriptions": outcomes.iter().filter(|o| o.transcription.is_some()).count(),
    })
}

#[cfg(test)]
mod tests;
