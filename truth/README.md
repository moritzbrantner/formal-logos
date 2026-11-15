# Truth Core CLI

From the repository root with Rust stable (edition 2024) and Python 3:

```sh
cargo build --locked -p truth
target/debug/truth status
target/debug/truth check
target/debug/truth inspect STMT-CATHOLICISM-TRUE --json
target/debug/truth bridges --constants constants.json --target STMT-EXISTING-IN-ACT-AT
target/debug/truth thickness --queue --json
target/debug/truth frontier --reaching-root --routes
target/debug/truth --json frontier-diff --base HEAD^1
target/debug/truth related STMT-GOD-EXISTS
target/debug/truth dossier STMT-GOD-EXISTS
target/debug/truth context ARGUMENT-ID --json
target/debug/truth tree STMT-GOD-EXISTS --down 2 --up 2
target/debug/truth orphans
target/debug/truth orphans --senses --json
target/debug/truth issues --from issues.json --for STMT-GOD-EXISTS
target/debug/truth next
target/debug/truth next-steps --frontier-root STMT-CATHOLICISM-TRUE
target/debug/truth results
cargo fmt --all --check
cargo clippy --locked -p truth --all-targets -- -D warnings
cargo test --locked -p truth
python3 scripts/verify_truth_cli.py target/debug/truth
```

CI runs the `truth-cli` job (format, Clippy, tests and the Python/Rust parity
script, about 16 minutes) only when the exact-head impact plan
(`scripts/affected_results.py select`) selects a full run: a change to Rust,
Cargo, `scripts/`, CI or another unclassified input, a formal change pushed to
`main`, and the nightly and manual runs. A PR that changes only corpus data,
result records, Lean modules or prose changes neither implementation and skips
it; corpus-driven divergence is caught on the next `main` run.

After fetching Cargo dependencies, add `--offline` to the build to work without
network access. The executable uses only local files. Use `--root PATH` to
select another checkout. Paths in results are relative to that checkout.

Version 1 JSON uses stdout for results and stderr for errors. Exit codes are
0 for success, 1 for corpus input errors, 2 for usage errors (and, as in
Python, for an unusable issue snapshot), and 3 for an unknown exact ID. `inspect` includes every matching kind and its canonical
record fields, including shared argument/result IDs. Passage entries are
expanded with their shared snapshot fields as in the Python reader.
`input_identity` is a non-cryptographic fingerprint of the sorted record
paths and bytes read, including local changes.

`status` counts each record kind and reports structural validation. The
loader checks JSON objects, IDs and per-kind uniqueness, passage manifest
shape, and selected required scalar and list fields. It also counts
configuration records. On malformed input Python and Rust can report
different first errors because they validate different scopes. The full
corpus validation, including cross-record links, semantic constraints, and
evidence bindings, is `truth check` (below) or Python `scripts/corpus.py
check`. Python continues to own the unmigrated commands, agent
service and Explorer consumers. Lean and the existing
verifier retain proof authority. Neither Rust command writes a database or
cache.

## Adding a command

Each subcommand is one module under `truth/src/cli/` (`status.rs`,
`check.rs`, `frontier_diff.rs`, …) exporting a `COMMAND` (its name and `run`
function); `truth/src/cli/mod.rs` lists them in `COMMANDS`, so a new command
is one new file plus one registry line and a `HELP` line. The computation
belongs in a library module under `truth/src/`; the CLI module only checks
its options, loads the corpus (`cli::load`) and returns the JSON value and
text that `cli::main` prints. `cli/args.rs` parses every option in one pass,
in token order, so existing option errors keep their precedence; a command
rejects the shared options it does not take with `Args::simple` or
`Args::check_options`. A port of a Python command that runs `validate()`
first (`bind-check`, `next`, the ID lists, …) calls `cli::validate_first`
before its own work: it runs the full `check` validation and, on a broken
corpus, fails as Python does, with the first `corpus error: …` and exit
code 2. `next`, `next-steps`, `arguments`, `results`, `bind-check` and
`unused-premises` call it; the earlier ports perform only the structural load.

Parity tests live in `scripts/truth_parity/`, one module per command, with
shared fixtures and the `ParityCase` base class in `common.py`; a new
command adds its module there and imports its test classes in
`scripts/verify_truth_cli.py`, the entry point CI runs.

## `lexicon`

`truth lexicon (show WORD | untraced | coverage | check | bootstrap | allowlist | ratchet --base REV)`
traces corpus prose to `corpus/lexicon/` (#1652, `docs/lexicon.md`). It has no Python
counterpart: `truth check` runs the lexicon check after the ported validation (a
per-field warning, or an error once `corpus/lexicon-config.json` sets `strict`, for a new
or changed prose field that is not fully traced; one `warning: lexicon: …`
summary line, kept out of `warnings` and ignored by the parity test, for the allowlisted
backlog), and CI runs `lexicon ratchet` so `corpus/lexicon-allowlist.json` only shrinks.
The library is `truth/src/lexicon/`.

## `check`

`truth check [--json]` ports `python3 scripts/corpus.py check`: `validate()`
and every warning of `check_warnings()`, rule for rule and in Python's order,
so a broken corpus reports the same first error. On success stdout is
Python's `corpus ok: …` counts line and stderr carries Python's `warning: …`
lines in Python's order, byte for byte; on failure stderr is Python's
`corpus error: …` line. Rust exits 1 on a corpus error (Python exits 2;
2 is the CLI's usage code). `--json` prints `counts`, `warnings` and
`summary`, or a `corpus_error` object.

The port is complete, and `truth check` is the corpus gate: CI's corpus job
and the worker contract (`AGENTS.md`, `docs/worker-startup.md`) run it, as
they run `truth frontier` and `truth frontier-diff` for the premise report.
`scripts/corpus.py check` stays until its retirement; the `truth-cli` job's
parity script keeps the two in agreement.

Ported: record loading and ID indexes; the per-kind passage manifest schema
(`source_evidence.validate_manifest`: text witness, media span, web snapshot,
bibliographic span); finite-model registrations;
configuration cases (`validate_case`, their result configs and the
transcription rejection); attempts; sorted `edition_urns`; source fields;
source-evidence bindings (source kinds, locator-prefix overlaps, web-snapshot and
bibliographic precedence, claim binding, basis and witness); statements (Lean declaration tails, unique
declarations, `self_evident` markings with disagreement and owner approval,
settlement actions); definitions, disambiguations and prose ID citations;
claims (references, status, attribution shape); inferences; arguments
(grounded derivation, term links, sense/disambiguation rule); relations
(entity references, premise-program kinds, `root_route`); candidates; result
Comparator configs (paths, modules, theorem names, axiom policy through the
Mathlib import closure, NanoDa); case splits; schema, `strengthens` and
`strength_comparison` registrations; strength order; `strong_version_needed`;
unused definitions; candidate/result collisions. Warnings: unflagged opaque Prop atoms (from the transcription heuristics
`frontier` shares), uncounted refutations, `supports` without a note, constant category predicates (#1103),
strong versions used without `strong_version_needed`, and unmet floor bases,
computed from the same least fixpoint `thickness` uses.

Known message differences: an invalid-JSON error carries serde's parser
message after the shared `cannot read JSON:` prefix; when several entries of
one JSON object are invalid (`strong_version_needed`, profile
`applications`), Rust may name a different first entry, because serde_json
sorts object keys; values Python would crash on (a list where an ID is
expected) are reported, not raised as a traceback. A web snapshot's
`encoding` is checked against the standard Python codecs and their usual
aliases (`codecs.lookup`); a rare codec outside that list is reported
unknown by Rust only.

`scripts/verify_truth_cli.py` compares both on the real corpus (stdout and
every warning line) and on a fixture checkout with a copy of `scripts/*.py`,
so the unmodified Python validator runs on it: the passing fixture (one
warning of each kind, the opaque-atom warning on a variant) and 149
deliberately broken variants, one per rule (56 for the passage manifest
schema), each of which must give the same `corpus error:` line. On the real
corpus (2026-11-07, 3731 statements) the release binary took 0.9–2.6 s and
Python 6.3–16.5 s on the same loaded machine (best of three: 0.9 s vs 6.3 s).

## `bind-check`

`truth bind-check [--json] [--result ID]... [--affected --base REV [--head REV]]
[--lean-json FILE] [--print-lean-input]` ports `python3 scripts/corpus.py
bind-check` (#162): after validating the corpus it binds every argument record
(premises, conclusion, commitments, theory-bundle conjuncts, declared senses)
to its result theorem's Lean type, and binds both sides of each schema
registration. Lean stays the verifier: Rust writes the input of
`scripts/BindTypes.lean` byte for byte as Python's `json.dump` does
(`--print-lean-input` prints it), runs `lake env lean --run` on it (or reads a
saved output with `--lean-json`) and applies Python's binding rules to the
description, including the pinned undeclared bindings, the exact-expression
contracts of `scripts/contracts/` and the sense and sense-alias checks. The
full run also reports stale pins and, when Lean runs, compiles the registered
finite-model certificates and requires each to be zero-axiom
(`finite_models.verify_models`). `--result` (repeatable; a uuid, legacy id or
label) and `--affected` (results `scripts/affected_results.py` selects for the
diff from `--base`, which stays Python) scope the run and skip the stale-pin
and model checks. Stdout is Python's byte for byte, the sorted indented
`--json` report as well as the humanized text, with exit 1 on a mismatch,
stale pin or sense alias; corpus errors exit 2 as `corpus error: …` (a JSON
error object under `--json`).

CI's corpus job and the worker contract run it; `corpus.py bind-check` stays
until its retirement. `scripts/truth_parity/bind_check.py` compares both from
one recorded exporter output on the `check` fixture (scoped success, stale
pins, unbound and missing hypotheses, theory bundles, consistency
commitments, pinned-type failures, schema registrations, sense problems and
aliases, expression contracts, scope and validate-first errors) and checks the
real corpus's exporter input byte for byte; with `TRUTH_BIND_LEAN_JSON` set to
a recorded exporter output it also compares the real-corpus reports. On the
real corpus (2026-11-15, 2151 results, 111 models) the full run with Lean took
17.9 s in Rust and 28.1 s in Python, and from a saved exporter output 3.9 s
against 14.9 s, on the same loaded machine; the outputs were identical.

## `structure` and `structure-report`

`truth structure STATEMENT [--json] [--unfold DECLARATION]...` and
`truth structure-report [--output FILE] [--build-input | --check-input]` port
`python3 scripts/corpus.py structure` and `structure-report`
(`scripts/proposition_structure.py`, `docs/proposition-structure.md`). Lean
stays the authority for the elaborated expressions: Rust locates the project
modules as Python's source locator does, has Lake build them and runs
`scripts/PropositionStructure.lean` through `scripts/worker_env.py`, with
Python's timeouts and messages, then assembles the same reports: the input
manifest and digest, the Git head, the compiled inputs, the scoped node ids,
semantic links, support and frontier statuses. `structure` prints the
statement's report as Python's indented JSON (humanized without `--json`);
`structure-report` writes the first-slice explorer artifact byte for byte as
Python does and prints `wrote PATH`; `--check-input` validates an artifact's
recorded inventories, hashes and digest without Lean. `--extractor-json FILE`
replays a saved exporter stdout instead of running Lean. Errors exit 2 as
`corpus error: …` (a JSON error object under `--json`). The artifact's
manifest still binds `scripts/proposition_structure.py` and
`scripts/corpus.py`, as Python's does, until R3 retires them. Each Rust report
also records `revision.producer_sha256`, the fingerprint of the truth crate
that wrote it (its sources, manifest and `Cargo.lock`, computed by
`truth/build.rs`), outside the input digest; `--check-input` rejects an
artifact whose producer is missing or differs from the running binary, so a
Rust change makes cached artifacts stale. Lake and the exporter run in their
own process group (`truth/src/subprocess.rs`, shared with `bind-check`'s
finite-model certificates): a timeout kills the whole group and bounds pipe
draining, so a compiler started by `lake build` cannot outlive the timeout.

CI, Pages, the explorer's `structure-inputs` script and its `--check-input`
call run it; `corpus.py structure` stays until its retirement.
`scripts/truth_parity/proposition_structure.py` runs Python with its two Lean
subprocesses replaced by a recorded exporter stdout and Rust with
`--extractor-json`, on the `check` fixture (text and `--json` reports, ID
resolution, the error paths, fresh, stale and forged artifacts) and on the
real corpus's first slice (byte-identical artifact apart from Rust's
`producer_sha256`, which the harness strips and checks separately). On the real corpus
(2026-11-15, warm Lake build) `structure-report` took 4.3 s in Rust and 9.0 s
in Python with Lean, 1.7 s against 6.3 s from the recorded exporter output,
and `--check-input` 1.7 s against 2.5 s; the artifacts were identical.

## `unused-premises`, `lean-reuse`, `context --proof-use`

These port the proof-term exporter commands of `scripts/corpus.py` (#954
A2). Lean stays the verifier: Rust writes each exporter's input byte for
byte as Python's `json.dump` does, runs it with `lake env lean --run` through
the code `bind-check` uses (`bind_check::run_exporter`), or reads a saved
output, and applies Python's joins and classifications to what Lean printed.

- `truth unused-premises [--strict] [--exemptions FILE] [--frontier-root
  STATEMENT] [--bind-json FILE] [--usage-json FILE]` (#571) validates first,
  binds every result with `scripts/BindTypes.lean` (Python's input without
  sense constants, and bindings without sense problems, as Python's command
  does) or reads a saved `bind-check --json` report, runs
  `scripts/UnusedPremises.lean` on the same input or reads its saved output,
  and reports each bound premise or theory-bundle conjunct the proof term
  never uses, flagged when it is open on a path to the frontier root.
  Exemptions come from `scripts/unused-premise-exemptions.json` (or
  `--exemptions FILE`); `--strict` exits 1 on an unexempted finding or a
  stale exemption. Python's `--root STATEMENT` is `--frontier-root` here.
  Stdout is Python's byte for byte, text and the sorted `--json` report; CI's
  corpus job runs `truth unused-premises --strict`.
- `truth lean-reuse --review [--usage-json FILE]` (#959) runs
  `scripts/LeanReuse.lean` on every result theorem (or reads its saved
  output) and classifies each result reached through a Solution's import
  closure or its proof term as theorem-used and graph-linked, theorem-used
  but not in the argument graph, or import only. Text is Python's byte for
  byte; `--json` is Python's report plus `input_identity`. Advisory only.
- `truth context TARGET --proof-use` (or `--proof-use-json FILE`) runs the
  same exporter on the target argument's result theorems and replaces each
  result's import reuse by that classification, as Python's flag does.

Exporter failures, a missing `lake`, a theorem the exporter did not inspect
and malformed saved output are `corpus error: …` with exit code 2, as in
Python; Rust reports serde's message for an unreadable saved file where
Python raised a traceback or printed its own JSON parser's message.
`scripts/truth_parity/proof_use.py` compares every command with Python on
the `check` fixture under a stand-in `lake` that records the exporter input
and prints a recorded output, so both the inputs (byte for byte) and the
reports are compared, including findings, bundle conjuncts, the root-path
flag, exemptions and their errors, skipped results, validate-first,
classifications and usage-map errors; on the real corpus it compares the
exporter inputs and, given `TRUTH_UNUSED_BIND_JSON`, `TRUTH_UNUSED_USAGE_JSON`
and `TRUTH_LEAN_REUSE_JSON` (recorded outputs for the checkout), the
reports. On the real corpus (2026-11-15, 2151 results, same loaded machine)
`unused-premises` with Lean took 21.5–24.7 s in Rust and 26.9–44.8 s in
Python, and from saved outputs 4.1 s against 11.8 s; `lean-reuse --review`
from a saved output took 0.75 s against 2.6 s (with Lean, both are dominated
by the exporter's ~30 s); the outputs were identical.

## `thickness`

`truth thickness [--queue] [--frontier-root STATEMENT-ID]` ports
`python3 scripts/corpus.py thickness [--queue] [--root STATEMENT-ID]`
(`--root` already selects the checkout here; the frontier root defaults to
`STMT-CATHOLICISM-TRUE`). Its `--json` output is the Python JSON object plus
`input_identity`; its text output is byte-identical to Python's.
`scripts/verify_truth_cli.py` checks both on the real corpus and on a fixture
corpus. Presentation only: it closes nothing and changes no route cost.

Its inputs (transcription kinds, reaching-root statements, source depths,
upward walks, counted refutations) come from the Rust `frontier` below, so the
two commands share one closure computation. No Python runs. `input_identity`
covers the corpus records only, not the Lean files the transcription
heuristics read.

`truth thickness --base REV` ports `corpus.py thickness --base REV`: the
head report plus the derivation sets and summary counts that changed from the
base revision. The base is read as `frontier-diff` reads it (below): a `git
archive` extract whose frontier report the Rust engine computes when that
revision's `scripts/corpus.py` is the checkout's, and that revision's own
`corpus.py frontier --json` otherwise; a pre-migration base is mapped to uuids
as Python maps it (its records by the checkout's `scripts/migrate_uuid.py`).
The JSON adds `engines` (`rust` or `python` for the base; the head is always
Rust). `--queue` with `--base`, and a revision that cannot be read, fail as
Python's `corpus error:` with exit 2.

Not ported: the full `validate()` that the Python command runs first (Rust
performs only the structural load).

## `frontier` and `frontier-diff`

`truth frontier [--reaching-root] [--routes] [--frontier-root STATEMENT-ID]`
ports `python3 scripts/corpus.py frontier [--reaching-root] [--routes]
[--root STATEMENT-ID]`. Its text output is byte-identical to Python's; its
`--json` output is the Python JSON object plus `input_identity`, including
`next_steps` (the next-work projection with its what-if probes), which, as in
Python, is computed only for `--json` without `--routes`. Rust computes the
whole report itself: the strength order and the set-aside of its registration
arguments; every transcription heuristic (declared kinds, single application,
assembly, opaque Prop atoms, goal as premise consequent after one unfolding of
a `TruthCore/` definition, short proofs); closure rules (a)-(d) with floor
bases, defended statements and strength propagation in one least fixpoint;
closure reasons; per-route open-premise costs; source depths; open items with
their route-aware walks; statement statuses and stages; and the next-step
probes, which rerun the same fixpoint with one leaf established.

`truth frontier-diff --base REV [--head REV] [--frontier-root STATEMENT-ID]`
ports `corpus.py frontier-diff`: the delta between the reaching-root frontier
of the base revision and of the head revision or working tree. Python runs
each revision's own `corpus.py` on a `git archive` extract, so a change of the
frontier rules between revisions shows in the delta. Rust computes a revision
with its own engine only when that revision's `scripts/corpus.py` is
byte-identical (same Git blob) to the checkout's, the rules this port is
verified against; otherwise it runs that revision's Python, exactly as
`corpus.py frontier-diff` does. The working tree is always computed in Rust.
The JSON adds `engines` (`rust` or `python` for base and head) and
`input_identity`; the text output is byte-identical to Python's. It needs
`git` and `tar`, and `python3` for the fallback.

Measured on the real corpus (release build, best of three, one machine,
2026-11-07): `frontier` 10.5 s in Python vs 0.7 s, `frontier --json` (with
next steps) 10.1 s vs 1.3 s, `frontier --reaching-root --routes` 5.3 s vs
0.35 s, `frontier-diff --base HEAD~1` 17.7 s vs 1.8 s (both revisions in Rust).
Python's figures include its full `validate()`.

`scripts/verify_truth_cli.py` checks every form on the real corpus (JSON
equal after dropping `input_identity`/`engines`, text byte-identical; the
diff against `HEAD`) and on a fixture covering every floor basis, an
owner-approved and a stale marking, counted and uncounted refutations,
transcription closure, the warning heuristics, witnesses, a case split and an
unknown root. Not ported: the full `validate()` that Python runs first (Rust
performs only the structural load, so a corpus that Python rejects can still
produce a Rust report). CI's premise-report step runs the Rust commands; the
Explorer build still calls `corpus.py`, which is the next consumer slice. Lean and Comparator keep proof authority: a "verified" argument is one
with a result record.

## `related`, `dossier`, `context`

These port `scripts/corpus.py related`, `dossier` and `context` (research
navigation, #954 slice 3). The logic lives in library modules with
serde-serializable result structs (`truth::related`, `truth::dossier`,
`truth::context`); `main.rs` only selects output. Text output is
byte-identical to Python's; `--json` prints the Python JSON object plus
`input_identity` (`dossier --all` prints exactly the Python object, keyed by
statement ID). Navigation only: nothing here closes a statement, changes a
route cost or certifies anything.

- `truth related STATEMENT-ID [--limit N]` (default 10; 1 to 200 shown) ranks
  over the loaded corpus in memory. Python ranks over its disposable SQLite
  projection `.cache/research-index.sqlite`; Rust needs and writes no cache.
  The paraphrase-overlap score sums word weights in sorted word order, so
  candidates whose scores differ only in the last floating-point bit may
  order differently from Python (none in the sampled corpus).
- `truth dossier (STATEMENT-ID | --all) [--frontier-json FILE] [--limit N]`
  (default 8, 0 = all).
- `truth context TARGET [--frontier-json FILE] [--limit N] [--related N]`
  (defaults 6 and 8; `--related 0` skips the ranking). TARGET is an argument
  ID, a result ID or a statement concluded by exactly one argument. The frozen
  Lean statement and companion theorems are read from each result's Challenge
  module, imports from the Solution modules and permitted axioms from the
  Comparator config, as Python does.

`dossier` and `context` consume the frontier report. Without
`--frontier-json` they compute it in-process with the Rust `frontier` (the
port of `corpus.py frontier`, below) on the same checkout and root
(`--frontier-root`, default `STMT-CATHOLICISM-TRUE`). With `--frontier-json
FILE` they read a saved `python3 scripts/corpus.py frontier --json [--root
STATEMENT-ID]` report instead (Rust cannot check that it is current), and
`--frontier-root` only checks that report's root. Either way Rust reads only
the fields these views consume (`truth::dossier::FrontierView`).

Errors: an unknown ID exits 3 (`unknown_id`); a non-statement `related`
target or an ambiguous `context` target exits 2;
an unreadable or non-frontier report or an unknown frontier root exits 1.
Python prints the same messages with exit code 2.

Not ported (use Python): the
full `validate()` that `dossier --all` runs first, `research_index.py`'s other
subcommands (`build`, `search`, `show`, `duplicates`, `summary`, `parity`,
`export`, `bundle`, `compare`) and the Explorer's `dossier --all` consumer.
`scripts/verify_truth_cli.py` checks parity on a sample of 30+ statements
(closed, stated, supported, bare, off-frontier and floor-marked), all 3,760
`dossier --all` entries, 15 `context` targets (12 argument IDs, which here
coincide with their result IDs, and 3 uniquely concluded statements) with
several `--limit` values, and the error cases, from a saved Python report;
and, for a subset plus `dossier --all`, that the in-process frontier gives the
same output.

## `tree`

`truth tree STATEMENT [--down N] [--up N] [--budget N]` draws the argument
graph re-rooted at any statement, with the definitions of every statement in
view (#1674). It has no Python counterpart. All statuses come from one
frontier report computed with STATEMENT as the frontier root
(`frontier::current_frontier`); the command creates no second closure
semantics and closes nothing.

- **Down (support, `--down`, default 3 argument levels):** the arguments
  concluding the statement are OR alternatives (verified non-transcription
  first, then transcriptions, then arguments without a result; each by label),
  each with its inference steps and its premises as an AND bundle, recursively.
- **Up (dependents, `--up`, default 3):** the arguments using the statement as a
  premise, their other premises (`co_premise`, not expanded) and their
  conclusions, recursively toward the case root (`is_case_root`).
- **Strength orders:** every `strengthens` relation with an end in view; a
  missing end joins as an unexpanded `strength_neighbor` while the budget allows.
- **Terms:** each statement's `definition_ids` and `disambiguation_ids` and the
  sense labels its definitions carry; each definition's `lean_declaration` and
  `formal_status` (`null` until the lexicon's formal-status data, #1652 L3,
  exists).

The walk is breadth-first, so each node sits at its shallowest depth; a shared
node appears once (`(shown above)` in the text), and an edge back to a node on
the current path is marked `cycle` and not followed. `--budget` (default 400)
caps statement plus argument nodes; an argument is added with all its new
premises or not at all. Every cut leaves a `truncated` entry (`side`, `reason`
`depth` or `budget`, `omitted_arguments`) and a `… truncated` text line.

JSON (`schema_version` 1, with `input_identity`): `root`, `case_root`,
`options`, `statements` (status, depth, closed reason, established,
`reaches_tree_root`, role, depths, definitions, senses), `arguments` (premises,
steps, results with theorem and transcription kind, the root route entry),
`edges`, `definitions`, `disambiguations`, `truncated`, `node_count`. Each edge
has a `kind` (`supports`: argument → conclusion, `uses`: argument → premise,
`strengthens`: strong → weak statement), `extra_premises`, `verified`,
`derivation` and `cycle`. The kinds `contrapositive` and `inverse_conditional`
are reserved (`reserved_edge_kinds`) for derived inversions: from a verified
P1, …, Pn ⊢ C, ¬C with the other premises gives ¬Pi; an inverse C ∧ ¬B ⊢ A
needs an explicit exhaustiveness premise C → A ∨ B in `extra_premises`. The
unconditioned inverse C ⊢ A is invalid and is never emitted.

## `attribution-check`

`truth attribution-check --base REV [--materialize] [--max-chars N]` is
`corpus.py attribution-check` (#989; `scripts/attribution_check.py`), the
pre-push attribution self-check for stating claims (`truth::attribution`).
The working tree is the head. It selects the claims added or changed since
`REV` in an attributed field (`statement_id`, `source_id`, `locator`,
`interpretation`, `attribution`), compared by id so a moved file is not new,
those whose statement paraphrase changed and those whose resolved passage
manifest changed apart from labels; a pre-migration base is read under the
uuid ids. For each it prints the premise beside the claim locator and the
cached passage text (`.cache/truth-core/sources`, clipped to `--max-chars`,
default 6000, 0 never), and fails unless the claim records an `attribution`
of the required shape. The check is offline: missing or stale cached text is
reported as not checked. `--materialize` runs `python3
scripts/source_evidence.py materialize PASSAGE` for each selected passage
(network acquisition stays Python) and fails on its errors.

Text is Python's byte for byte: the report on stdout (records named `label
[uuid8]`), the problems on stderr with exit code 1, and `attribution-check
error: …` on stderr with exit code 2 (an unknown base, a claim that does not
resolve to one passage, an invalid manifest). Python crashes with a traceback
on a malformed record (invalid JSON in a changed file); Rust reports it as
such an error. `--json` prints `base`, `claims` (id, reason, premise,
locator, interpretation, passage, text or why it was not checked,
attribution), `problems` and `ok` on stdout with the same exit code; Python
has no JSON output. `scripts/truth_parity/attribution.py` compares both on
the cases of `test_attribution_check.py` on fixture repositories (including
a readable-id base and a stub `materialize`) and on the real corpus against
several base revisions. CI's attribution step runs it.

`truth check` already includes every offline rule of `python3
scripts/source_evidence.py check` (`validate_manifest` and
`validate_bindings`, with Python's messages; the `check` parity fixture covers
them). Only the summary line counting bibliographic and permanently
unavailable passages is Python's; the separate command is no longer a gate.

## `issues` and `dossier --issues-from`

`truth issues --from FILE [--for ID]` is `corpus.py issues --from FILE`: the
read-only reconciliation of `truth-core-acceptance` blocks (#949) in an
offline `gh issue list --state open --limit 1000 --json
number,title,body,url,comments` snapshot against this checkout
(`truth::issues`, the port of `scripts/issue_acceptance.py`). Each issue is
`delivered`, `missing`, `malformed` or `untracked`; the JSON adds the
requirements and a reverse index from IDs to issue numbers, and `--for ID`
(a uuid, legacy id or label of a result, statement, configuration, attempt or
argument) keeps the issues naming it. Statement closures come from the Rust
frontier on the checkout; a `theorems` requirement also needs a declaration
of exactly that name in the result's Solution module source. `truth dossier
STATEMENT|--all --issues-from FILE` adds each statement's
`targeting_issues` (and the text line `Issue targets (offline acceptance
snapshot): …`), using the closures of the dossier's frontier report.

Unlike Python, `truth issues` requires `--from`: it never calls GitHub.
Snapshot errors (unreadable file, invalid JSON, a non-array, an issue without
a positive integer number) exit 2 with Python's `corpus error: …` message;
only the wording of a JSON parse error differs. Text is byte-identical and
JSON semantically identical (plus `input_identity`);
`scripts/truth_parity/issues.py` checks this on the cases of
`test_issue_acceptance.py` on a fixture checkout and on the recorded snapshot
`scripts/truth_parity/fixtures/issues-snapshot.json` extended with blocks
naming real corpus records.
## `next`, `next-steps`, `arguments`, `results`, `sort-lists`

Ports of the navigation subcommands of `scripts/corpus.py`
(`truth/src/navigation.rs`):

- `truth next` validates first and prints the source candidate with the least
  `(priority, id)` as Python prints it: `json.dumps(candidate, indent=2,
  ensure_ascii=False)` with keys in file order (`truth/src/pyjson.rs`) and
  uuids humanized. Without candidates it prints `no candidates` and exits 1.
  `--json` prints the candidate record itself.
- `truth next-steps [--frontier-root STATEMENT]` validates first and prints
  the frontier's `next_steps` projection (`frontier --json` computes the same
  projection; there is no second engine): text as
  `next_steps.format_next_steps`, `--json` as Python's `next-steps --json`
  plus `input_identity`. Python's `--root STATEMENT` is `--frontier-root`
  here, as for `frontier`.
- `truth arguments` and `truth results` validate first and print the IDs in
  file order, one per line, not humanized; `--json` lists them under `ids`.
- `truth sort-lists` sorts the order-free lists (`edition_urns` of sources)
  in place, without validating first, and rewrites each changed record as
  Python does (indent 2 when the file was indented, keys in file order,
  trailing newline). A list with a non-string item is reported, not sorted.

`scripts/truth_parity/navigation.py` compares every command with Python on
the real corpus and on the `check` fixture (byte-identical text and stdout,
the rewritten files, the same `corpus error:` line and exit code 2 on broken
variants). `scripts/verify-all.sh` lists results with `truth results`; the
explorer's next-work browser test reads `truth next-steps`. The Python
implementations stay until their retirement (#954, R2).

## `orphans`

`truth orphans [--frontier-root STATEMENT-ID] [--by module|family]` lists
verified results (status `solution-present` or `verified`) whose argument
conclusion does not reach the frontier root (default
`STMT-CATHOLICISM-TRUE`) and which do not support a verified recorded refutation
of an `alternative_to` rival of a root-path node. Support follows premises and
commitments backwards through verified arguments, including transitive support.
Open assumptions permit conditional connection; this does not close them or
establish root truth. Solution imports alone remain advisory contacts. `thickness --queue` ranks only statements that
already reach the root, so such work is otherwise invisible to round
selection. Reaching the root is the same route-aware walk as `thickness`;
`scripts/verify_truth_cli.py` checks the disconnected set against Python's
`reaching_root_statements` plus `corpus.refutation_support`.

`truth orphans --base REV` ports `scripts/orphan_summary.py --base REV`, the
Markdown table CI adds to a PR's job summary: the disconnected count at the
base revision and at the working tree, and their difference. The base is read
as `frontier-diff` reads it: the Rust engine when the revision's
`scripts/corpus.py` is the checkout's, otherwise the revision's own Python
(`orphan_summary`'s historical snippet, which tolerates a revision without
refutation support). A base that cannot be read or computed is reported as
unavailable (stderr names the error; `--json` has `base_error`) and does not
fail the command; a head failure does. The text is byte-identical to
Python's for the default root (Python always names `STMT-CATHOLICISM-TRUE`;
Rust names the `--frontier-root` used); `--json` gives `base_count`,
`head_count`, `delta` and `engines`. It excludes `--by` and `--senses`.

Results are grouped by Lean module area (`--by module`, the default: the
first namespace component below `TruthCore`, after `Results`, so
`TruthCore.Results.Modal.K.Solution` is `TruthCore.Modal`) or by family
(`--by family`: weakly connected components of the statements the
disconnected arguments join; a hub statement shared by more than eight of
them, such as `STMT-CONFIGURATION-FALSE`, joins nothing). Each group reports its result count, the
non-transcription and transcription counts (declared kinds and the Lean-text
heuristics), how many of its arguments touch the root path anyway (a root-path
premise, or a relation on a root-path statement or its rival), its conclusion
statements, and up to five nearest root-path contacts, ranked by tier:

0. Lean import reuse: a root-path result's Solution imports a group Solution,
   or a group Solution imports a root-path result's Solution.
1. Shared vocabulary module: a root-path statement's `lean_declaration` lives
   in a module a group Solution imports or a group conclusion is declared in
   (modules imported by more than 5% of results are ignored as too common).
2. Shared `definition_ids`/`disambiguation_ids` with a group conclusion.
3. Paraphrase overlap of two or more words, weighted as in
   `corpus.py related`.

Contacts are discovery leads, not equivalences or entailments. Text output
lists eight conclusions per group; `--json` lists every result and conclusion.

`truth orphans --senses` lists root-path disambiguations (linked, directly or
through a sense definition, from a statement reaching the root or an argument
concluding one) without a certified sense fork. A fork needs a coverage
statement, an exclusivity statement and a verified joint theorem by cases that
takes the coverage statement as a premise (`docs/corpus-model.md`, "Sense
forks"). Each part is read from the disambiguation's `coverage_statement_id`,
`exclusivity_statement_id` and `fork_result_ids`; without a field, the
heuristic fallback accepts a statement linking the disambiguation whose ID ends
in `-SENSES-EXHAUSTIVE` (coverage) or `-SENSE-UNIQUE`/`-SENSES-EXCLUSIVE`
(exclusivity), and a verified result whose argument links the disambiguation
and takes that coverage premise. Entries are ordered by the number of
root-path links and name the missing parts. Neither report closes anything or
writes records.

## `bridges`

`bridges` ranks advisory bridge candidates for underived statements by the
Lean constants their declarations share, from a `scripts/StatementConstants.lean`
export (`--constants`) and either `--target ID` or a
`truth thickness --queue --json` or `corpus.py thickness --queue --json` file (`--queue-file`, first `--targets N`,
default 10). It is a search heuristic, not a proof or equivalence judgment;
see `docs/bridge-candidates.md` for the pipeline and the optional Lean trial.

## `configurations`, `models`, `territory`

These port the Lean-free parts of `corpus.py configurations`, `models` and
`territory` (#954 slice B2): `truth::configurations` (`implication_closure`,
`configuration_report`), `truth::finite_models` (`model_report`) and
`truth::territory` (`territory_report`). Text output is byte-identical to
Python's; `--json` prints the Python JSON (plus `input_identity` for `models`
and `territory`; `configurations` prints Python's list as is). A corpus error
prints Python's `corpus error: …` with exit code 2.

- `truth configurations --registered [--case ID] [--seed STATEMENT]
  [--premise STATEMENT]...`: the registered projection (no certified status).
  It validates the models and cases first, as Python's `configuration_context`
  does (`truth::check::registered_configurations`), not the whole corpus.
  Without `--registered` Python builds the modules and checks every
  certificate and original theorem in Lean; Rust refuses and names the Python
  command (exit 2). The verified projection is ported in the library and
  unit-tested against Python's fixture cases; slice A6 wires it to
  `configuration-report`.
- `truth models`: every registered model and its co-failure candidates.
  `--check`, `--argument` and `--verify` Lean-check all registered models in
  Python, so Rust refuses them and names the Python command; `--premise`
  without either fails as in Python.
- `truth territory [--frontier-root STATEMENT] [--max-atoms N]`: Python's
  `--root` is `--frontier-root` here. Like Python it runs the full `check`
  validation first (`cli::validate_first`) and reads the in-process Rust
  frontier. Position IDs hash with a built-in SHA-256. The global position
  count is exact (Python's unbounded int): the text prints every digit; a
  count beyond `u64` has no exact JSON number here, so `--json` then fails
  with `unrepresentable_count` (exit 1) and names the Python command instead
  of printing a wrong number.

`scripts/truth_parity/configurations.py` compares them on the real corpus
(every case, filtering by uuid and legacy id, seed and premise selections and
their errors; `models`; `territory` with the default bound, `--max-atoms` 40
and -3 and an unknown root) and on a fixture checkout with an incompatibility
core, an implication rule, a model a fixed constant excludes, co-failures, a
refutation core and a model that satisfies it (a `DEFECT` line), a broken
corpus and seven broken registrations.
