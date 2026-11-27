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
target/debug/truth index search 'common nature'
target/debug/truth dossier STMT-GOD-EXISTS
target/debug/truth context ARGUMENT-ID --json
target/debug/truth tree STMT-GOD-EXISTS --down 2 --up 2
target/debug/truth orphans
target/debug/truth orphans --senses --json
target/debug/truth connectivity --list-isolated 20
target/debug/truth connectivity --base origin/main
target/debug/truth issues --from issues.json --for STMT-GOD-EXISTS
target/debug/truth brief STMT-GOD-EXISTS --issues-from snapshot.json
target/debug/truth brief --question 'ultimate explanation, brute fact or infinite regress'
target/debug/truth novelty 'DependsForBeing ↔ ¬CanBeWithout' --issues-from snapshot.json
target/debug/truth next
target/debug/truth next-steps --frontier-root STMT-CATHOLICISM-TRUE
target/debug/truth results
target/debug/truth --json support-graph
target/debug/truth countermodel TruthCore.Results.Causality.SelfOperationLife.pureActLives --all
cargo fmt --all --check
cargo clippy --locked -p truth --all-targets -- -D warnings
cargo test --locked -p truth
```

CI runs the `truth-cli` job (format, Clippy, and the Rust tests, which include
the golden replay below) only when the exact-head impact plan
(`scripts/affected_results.py select`) selects it: a change to this crate or
the root Cargo workspace (the "tooling" kind, which selects no Comparator results but keeps the corpus,
Lean binding, explorer and report checks that run the CLI on the real corpus),
or a full run: other `scripts/`, CI or another unclassified input, a formal
change pushed to `main`, and the nightly and manual runs. A PR that changes only corpus data,
result records, Lean modules or prose does not change the CLI and skips it.

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
evidence bindings, is `truth check` (below). Lean and the existing
verifier retain proof authority. Neither Rust command writes a database or
cache.

The corpus directory must exist. Missing optional record collections are empty;
unreadable collections, dangling collection links, and non-file JSON entries
are errors rather than silently omitted records.

Use `truth index formalization` to locate embedded Lean proofs, executable comparisons, and Python or JavaScript examples that need inspection. The JSON `section` field opens the same passage with `truth index show`. Append `check` to flag embedded Lean proof bodies; queries such as `#check` and executable research diagnostics remain available.

When moving a comparison into Lean, check that the new declaration covers the original examples, including the cases that distinguish rivals. Keep the applicable interpretation, evidence, and conditions for revising the judgment in their existing records. An earlier executable comparison can remain alongside its source until the replacement covers it.

Use `truth index duplicates notes` to locate repeated research sections. Append `check` to return a failing status when copies are present.

## Statement synthesis

`truth synthesis` opens the classical-theism God-existence statement. Give a
statement UUID, legacy ID, exact label or Lean declaration to read another
proposition. Search registered Lean proofs by theorem name or in your own words. Both forms run offline and accept
`--root PATH`.

```sh
target/release/truth synthesis STMT-GOD-EXISTS
target/release/truth synthesis 0881e859-c4c3-53ff-9bec-b61294e12d51
target/release/truth synthesis --question TruthCore.Results.Modal.RevisionUptake.screening
target/release/truth synthesis --question "Do observations identify a common giver?"
target/release/truth --json synthesis STMT-GOD-EXISTS
```

An ambiguous Lean short name such as `GodExists` lists the matching declarations
and a command for each meaning.

To inspect a particular argument, pass its ID. A result ID from an investigation opens that result’s frozen Lean declaration alongside its owning argument. The report links investigations that cite that specific result and includes their complete findings in JSON. For example, try the closed-collection argument for a common uncaused source:

```sh
truth synthesis 3de4bd49-567b-44de-8472-88a24ea1311a --without 20babef7-6ae7-4b48-b72a-f417e8e63136
truth --json synthesis 3de4bd49-567b-44de-8472-88a24ea1311a --compare-premises
```

The comparison starts with that argument’s retained premises and commitments. It follows rules backed by registered solutions, including zero-input results. It reports whether the selected argument still applies, other producers of the conclusion supported by those same inputs, and a dependency-ordered derivation when one exists. The target is excluded from the starting facts and from intermediate derivations. A withheld input can be derived through another route. The result concerns conditional reachability of statement IDs. Verifying that the witnesses and interpretations match across an inferred path requires a separate Lean composition.

`--without` also reads prior investigations and scoped assessments of the withheld
inputs. JSON gives each matching attempt once in `previous_investigations`, even
when it targets several withheld inputs. `withheld_assessments` uses each current
judgment’s own statement IDs.

The statement view leads with the formal target and the frozen Lean theorem for a supporting route, with its Solution and verification configuration. It quotes
scoped judgments and a live test, and compares the actual premises of its
immediate arguments. A complete illustrative route provides a command for each
premise and separately listed commitment. Each quoted assessment retains its full wording, review
state and source. The text shows two target judgments by default. Use
`--limit N` to display more. The first example prefers reviewed records,
a scope naming just the target, then an attempt citing a result for the
target, then a smaller scope. A different review state gets the second slot
when present. These rules select examples for reading. The scope written by
the researcher governs the judgment, even when a record names just one
statement. Question JSON returns matching registered theorem records in `lean_results`, including the Challenge signature, Solution path and argument premise IDs. A fully qualified library declaration outside the argument registry returns its source in `lean_declaration`. Both lookups work without research notes. A question also retrieves findings from the attempts and offers statement
commands for following the argument. Results labeled as earlier investigations
provide historical evidence. A current assessment carries its own scope and
review state. When a question phrase is missing from the leading finding,
the command can also quote a matching research note with its section and line.
Question JSON returns that passage in `note_match` when available.
Results explicitly cited by a matching investigation appear in `cited_lean_results`.
When several cited conclusions belong to the same current assessment, the closest match
in their registered labels and paraphrases leads. The other scoped citations retain their recorded order.
A direct result that the investigation also cites carries its provenance in `cited_by`.

The complete statement JSON includes these fields.

| Field | What to read |
| --- | --- |
| `formal_status` | The frontier's ordinary closure, establishment and refutation for the target. A conditional proof may leave establishment false. |
| `target_assessment_ids`, `assessments` | All current records explicitly indexing this target, and the deduplicated record dictionary for the target and its immediate premises. Each has the assessment, scope, live test, evidence, full note locator, review state, reviewed revision and publication state. |
| `routes`, `results`, `premises` | Every registered producing argument, its ordinary premises and separate commitments, result witnesses, and the formal status and current assessment IDs of each immediate premise. Argument status distinguishes derivations, transcriptions and unverified proposals. |
| `shared_premises`, `shared_assessments` | The exact argument IDs reusing an immediate premise and the exact premise and argument IDs linked to a single assessment. This identifies citation reuse. Distinct records can still share evidence. |
| `objections` | Registered attacks, alternatives and refutation relations directed at the target or an immediate premise, with their original notes and paths. The relation alone does not establish defeat. |
| `consumers`, `related_statements` | Downstream arguments with all co-premises, separate commitments and conclusion IDs, and the additional statement descriptions needed to read them. |
| `target_attempt_paths` | Target-indexed investigations, including earlier attempts without a current assessment. An empty current-assessment list can coexist with substantial prior work. |
| `previous_investigations` | Each attempt targeting the statement or one of its immediate premises, in attempt ID order. Entries retain the attempt’s original statement IDs, kind, outcome, summary, blocker, evidence and source path. |

The text can show one earlier finding about an input or target outside that
attempt’s current judgment scope. Its outcome describes the investigation.
`--limit` affects text display. JSON retains every matching investigation,
assessment and immediate argument. Read a premise with `truth synthesis PREMISE_ID` to
continue down its branch. `truth dossier PREMISE_ID` includes historical
attempts and source records. `truth support-graph STATEMENT` exports the
complete backward slice of result-backed arguments. Direct consideration of a
premise remains available alongside all conditional derivations. Neither the
size of the route overlap nor the number of records grades warrant.

## Registered support graph

`truth --json support-graph [STATEMENT ...]` exports the complete backward
slice for the requested targets, defaulting to God-existence and the same
necessary classical God-root. Targets accept UUIDs, legacy IDs or labels.
The deterministic JSON contains the statement dictionary, one implication
edge per result-backed argument, every result witness, terminal inputs,
and immediate conjunctions after literal premise-set absorption. Missing
references fail instead of silently shortening the graph. `input_identity`
covers loaded corpus bytes; `graph_sha256` covers the selected graph.
Optional `source_head` and `worktree_dirty` describe the checkout.

This is the input to symbolic support analysis, not a support-count command.
It includes conditional transcriptions and strength implications, preserves
cycles and real zero-premise rules, and imports no frontier/floor status as a
fact. Analysis must use the least fixed point and disable each current
target's direct input, even when that target is terminal. Direct-or-derived
inputs and terminal-only inputs are different bases. An input set to false
means the premise is not supplied, not that its negation is accepted.
Graph support does not replace Lean composition, binding or verification.

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

A new command's tests are Rust unit tests in its library module and, for
whole-command behaviour, integration tests under `truth/tests/` (for example
`base_revision.rs`, `frontier_fixture.rs`).

## Golden snapshots of the Python oracle

Before the Python implementations retired (#954 R1-R3), the Python side of
every fixture parity comparison was frozen in `truth/tests/golden/<module>/<test>.json`,
and `cargo test --locked -p truth --test golden` (part of `cargo test`, so
of the `truth-cli` CI job) replays each case against the Rust binary alone:
no `corpus.py`, no Lean. A case holds the fixture checkout (files, and the
Git history where the fixture is a repository), any directories outside it
(recorded exporter output, a stand-in `lake`, artifacts), the `truth`
command line and the output Python gave: exit code, stdout and stderr byte
for byte, or `--json` output semantically without `input_identity`, as the
parity test compared it. The format and its normalizations (temporary paths
as `⟪root⟫`/`⟪ext:N⟫`, commit ids as `⟪commit:N⟫`, the structure producer
fingerprint as `⟪producer⟫`, `{"repo": PATH}` references to repository files)
are documented in `truth/tests/golden.rs`.

No Python oracle remains (#954 R3 deleted `scripts/corpus.py`, the report
scripts, the parity harness `scripts/truth_parity/` and its recorder), so the
goldens pin the Rust behaviour. A deliberate output change updates the
affected expectations with

```sh
TRUTH_GOLDEN_BLESS=1 cargo test --locked -p truth --test golden -- --nocapture
```

which rewrites the `expect` of every differing case with the binary's output
(tokenized as the recorder did, in its format); the resulting golden diff is
reviewed with the change. Blessing rewrites expectations only: a case whose
fixture tree holds a saved artifact that the change makes stale needs that
fixture edited instead, and a case whose scenario no longer exists is
deleted. R3 changed goldens this way for the head-rules base revisions
(`revisions/`) and for the report inventories that no longer list the retired
Python scripts (`configuration_report/`, `strength/`,
`proposition_structure/`); each such file's `about` says so.

## `lexicon`

`truth lexicon (show WORD | untraced | coverage | check | bootstrap | allowlist | ratchet --base REV)`
traces corpus prose to `corpus/lexicon/` (#1652, `docs/lexicon.md`). It has no Python
counterpart: `truth check` runs the lexicon check after the ported validation (a
per-field warning, or an error once `corpus/lexicon-config.json` sets `strict`, for a new
or changed prose field that is not fully traced; one `warning: lexicon: …`
summary line, kept out of `warnings` and ignored by the parity test, for the allowlisted
backlog), and CI runs `lexicon ratchet` so `corpus/lexicon-allowlist.json` only shrinks.
The library is `truth/src/lexicon/`.

## `definitions`

`truth definitions (status [--limit N] | refresh [--write] [--lean-json FILE]
[--print-lean-input] | allowlist [--write] | ratchet --base REV)` computes the
formal status of every definition record (#1652 L3, docs/corpus-model.md,
"Formal status of definitions"). It has no Python counterpart. `refresh` runs
`scripts/DefinitionStatus.lean` through `bind_check::run_exporter` (or reads a
saved output with `--lean-json`) and writes `corpus/definition-status.json`
with `--write`. Without `--write` it compares and exits 1 when a fresh
committed entry disagrees with Lean, or, in strict mode, when an entry is stale
or missing. CI runs it where bind-check builds. `status` reads the cache
without Lean and prints counts by status and Lean kind, the definitions still
without `formal_gap` prose, and the findings. `truth check` adds the findings
and one `warning: definitions: …` summary line (kept out of `warnings`;
the parity test ignores it). It reports nothing without the cache file.
`allowlist` and `ratchet` keep `corpus/definition-prose-allowlist.json`
shrink-only, as for the lexicon. The library is
`truth/src/definition_status.rs`; its unit tests replay a recorded exporter
output (`truth/src/testdata/definition-status-exporter.json`).

## `check`

`truth check [--json]` ports the retired `python3 scripts/corpus.py check`: `validate()`
and every warning of `check_warnings()`, rule for rule and in Python's order,
so a broken corpus reports the same first error. On success stdout is
Python's `corpus ok: …` counts line and stderr carries Python's `warning: …`
lines in Python's order, byte for byte; on failure stderr is Python's
`corpus error: …` line. Rust exits 1 on a corpus error (Python exits 2;
2 is the CLI's usage code). `--json` prints `counts`, `warnings` and
`summary`, or a `corpus_error` object.

The port is complete, and `truth check` is the corpus gate: CI's corpus job
and the worker contract (`AGENTS.md`, `docs/worker-startup.md`) run it, as
they run `truth frontier` and `truth frontier-diff` for the premise report,
and `scripts/merge_queue.py` runs it after merging main. `scripts/corpus.py
check` was retired in #954 R3.

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

Until #954 R3 the retired parity script compared both on the real corpus
(stdout and every warning line) and on a fixture checkout with a copy of
`scripts/*.py`; the frozen goldens `truth/tests/golden/check/` keep its
fixture cases: the passing fixture (one
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

CI's corpus job and the worker contract run it; `corpus.py bind-check` was
retired in #954 R2. The frozen goldens `truth/tests/golden/bind_check/` (recorded by the retired `scripts/truth_parity/bind_check.py`) compare both from
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
the retired `python3 scripts/corpus.py structure` and `structure-report`
(`scripts/proposition_structure.py`, #954 R3; `docs/proposition-structure.md`). Lean
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
manifest binds the exporter, the toolchain files, `scripts/worker_env.py`, the
project Lean sources and the corpus records; since R3 it no longer lists the
retired Python scripts. Each Rust report
also records `revision.producer_sha256`, the fingerprint of the truth crate
that wrote it (its sources, manifest and `Cargo.lock`, computed by
`truth/build.rs`), outside the input digest; `--check-input` rejects an
artifact whose producer is missing or differs from the running binary, so a
Rust change makes cached artifacts stale. Lake and the exporter run in their
own process group (`truth/src/subprocess.rs`, shared with `bind-check`'s
finite-model certificates): a timeout kills the whole group and bounds pipe
draining, so a compiler started by `lake build` cannot outlive the timeout.

CI, Pages, the explorer's `structure-inputs` script and its `--check-input`
call run it. Until R3 the retired `scripts/truth_parity/proposition_structure.py`
ran Python with its two Lean subprocesses replaced by a recorded exporter
stdout and Rust with `--extractor-json`, on the `check` fixture (text and `--json` reports, ID
resolution, the error paths, fresh, stale and forged artifacts) and on the
real corpus's first slice (byte-identical artifact apart from Rust's
`producer_sha256`, which the harness strips and checks separately); the frozen
goldens `truth/tests/golden/proposition_structure/` keep its fixture cases. On the real corpus
(2026-11-15, warm Lake build) `structure-report` took 4.3 s in Rust and 9.0 s
in Python with Lean, 1.7 s against 6.3 s from the recorded exporter output,
and `--check-input` 1.7 s against 2.5 s; the artifacts were identical.

## `strength-comparisons` and `strength-report`

`truth strength-comparisons [COMPARISON] [--registered] [--json]` and
`truth strength-report [--output FILE] [--build-input | --check-input]
[--json]` port the retired `python3 scripts/corpus.py strength-comparisons` and
`strength-report` (`scripts/strength_comparisons.py`, #954 R3;
`docs/proposition-structure.md`). Lean, Comparator and NanoDa stay the
authorities: Rust validates the `strength_comparison` registrations and their
results' Comparator contracts with the rules `truth check` uses, then, as
Python does and through `scripts/worker_env.py`, has Lake build the modules,
binds the evidence results with `scripts/BindTypes.lean`, has
`scripts/CheckStrength.lean` check every complete certificate application and
the definitional degeneracy guard, attaches the
`scripts/PropositionStructure.lean` structure of the compared declarations
and runs `scripts/verify-result.sh` on each evidence result. It only refuses
incomplete checker responses and projects the checked roles to their labels.
`strength-comparisons` prints one status line per comparison (humanized) or
the reports as Python's JSON; a COMPARISON is matched by its exact id, as in
Python, and `--registered` prints the provenance-only projection without
Lean. `strength-report` writes the `.cache` bundle byte for byte as Python
does (sorted keys, atomic replace, refused outside the clone's `.cache`) and
`--check-input` validates its producer, input manifest, digest and
projection without rerunning proofs, with Python's equality (key order free,
`2 == 2.0`). Errors exit 2 as `corpus error: …` (a JSON error object under
`--json`). Since R3 the bundle's manifest no longer lists the retired Python
scripts. `--recorded-exporters DIR` replays recorded `BindTypes.json`,
`CheckStrength.json` and `PropositionStructure.json` without Lake or
Comparator, for the golden replay only; it is never a verification, so it
needs `TRUTH_PARITY_REPLAY=1` and refuses to write a bundle named
`strength-comparisons.json`, the only path the explorer reads.

CI, Pages, the explorer's `strength-inputs` script and its `--check-input`
call run it. Until R3 the retired `scripts/truth_parity/strength.py` ran Python
with its Lean subprocesses replaced by the recorded outputs and Rust with
`--recorded-exporters`, on the `check` fixture with two comparisons (text and
`--json` reports, a selected comparison, `--registered`, invalid registrations
and Comparator contracts, binding, coverage, degeneracy and exporter failures,
fresh, stale, forged and symlinked bundles) and on the real corpus
(`--registered` always; the live reports, the bundle and `--check-input`
given recorded exporter output); the frozen goldens `truth/tests/golden/strength/`
keep its fixture cases. On the real corpus
(2026-11-15, warm Lake build, 7 comparisons) the live `strength-report`,
dominated by `verify-result.sh`, took 186 s in Rust and 159 s in Python on a
loaded machine, with byte-identical bundles; from the recorded exporter output
it took 0.9 s against 3.4 s, `--check-input` 0.57 s against 0.72 s and
`--registered` 0.38 s against 0.25 s (Rust also loads the structural
corpus).

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
The frozen goldens `truth/tests/golden/proof_use/` (recorded by the retired `scripts/truth_parity/proof_use.py`) compare every command with Python on
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
The frozen goldens `truth/tests/golden/thickness/` and `revisions/` keep the
retired parity script's fixture cases. Presentation only: it closes nothing and changes no route cost.

Its inputs (transcription kinds, reaching-root statements, source depths,
upward walks, counted refutations) come from the Rust `frontier` below, so the
two commands share one closure computation. No Python runs. `input_identity`
covers the corpus records only, not the Lean files the transcription
heuristics read.

`truth thickness --base REV` ports `corpus.py thickness --base REV`: the
head report plus the derivation sets and summary counts that changed from the
base revision. The base is read as `frontier-diff` reads it (below): its
`git archive` extract, judged by this binary's rules. The JSON adds `engines`
(always `rust` for base and head). `--queue` with `--base`, and a revision
that cannot be read, fail as Python's `corpus error:` with exit 2.

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

`truth frontier --fixture FILE` (`-` for stdin) computes the same report on a
fixture instead of the checkout at `--root`: a JSON object with optional
`statements`, `arguments`, `results`, `relations`, `claims` and `inferences`
lists (the inputs of Python `frontier_report`, in the given order) and a
`transcription_flags` list (Python `transcription_flags` entries; absent fields
are empty). No corpus validation runs and no Lean source is read; any other
key is an error (exit 1, `fixture_error`). `--frontier-root` resolves against
the fixture's records, and `input_identity` hashes the fixture bytes. The
Explorer's synthetic-corpus tests, the Python corpus-content tests
(`scripts/truth_cli.py`'s `frontier_fixture`), the shared rule (d) fixture
(`truth/tests/frontier_fixture.rs`) and the golden `test_fixture_input` use it
(#954 B12/R3), so fixture tests need no Python oracle.

`truth frontier-diff --base REV [--head REV] [--frontier-root STATEMENT-ID]`
ports `corpus.py frontier-diff`: the delta between the reaching-root frontier
of the base revision and of the head revision or working tree.

**Head rules on base data** (owner decision for #954 R3, 2026-11-16): a
revision is read from its `git archive` extract (its committed corpus and Lean
sources, in a temporary directory, offline) and judged by this binary's own
rules (`frontier::base_tree`). The revision's own tooling is never run and its
`truth` is never built, so base and head are judged by one rule set: a PR that
changes the frontier rules shows the effect of that change as a delta, and a
PR that changes no rule and no data shows none. A revision from before the
uuid migration is first converted to uuid identity by the checkout's
`scripts/migrate_uuid.py` (a data migration). `thickness --base` and
`orphans --base` read their base the same way. The JSON adds `engines`
(always `rust`, kept for compatibility) and `input_identity`; the text output
is unchanged. It needs `git` and `tar` (and `python3` only for a
pre-migration base). `truth/tests/base_revision.rs` covers the extract path.

Measured on the real corpus (release build, best of three, one machine,
2026-11-07): `frontier` 10.5 s in Python vs 0.7 s, `frontier --json` (with
next steps) 10.1 s vs 1.3 s, `frontier --reaching-root --routes` 5.3 s vs
0.35 s, `frontier-diff --base HEAD~1` 17.7 s vs 1.8 s (both revisions in Rust).
Python's figures include its full `validate()`.

Until R3 the retired parity script checked every form on the real corpus (JSON
equal after dropping `input_identity`/`engines`, text byte-identical; the
diff against `HEAD`) and on a fixture covering every floor basis, an
owner-approved and a stale marking, counted and uncounted refutations,
transcription closure, the warning heuristics, witnesses, a case split and an
unknown root; the frozen goldens `truth/tests/golden/frontier/` keep the
fixture cases. Not ported: the full `validate()` that Python runs first (Rust
performs only the structural load, so a corpus that Python rejects can still
produce a Rust report). CI's premise-report step and the Explorer build run the Rust commands. Lean and Comparator keep proof authority: a "verified" argument is one
with a result record.

## `related`, `dossier`, `context`

These port `scripts/corpus.py related`, `dossier` and `context` (research
navigation, #954 slice 3). The logic lives in library modules with
serde-serializable result structs (`truth::related`, `truth::dossier`,
`truth::context`); `main.rs` only selects output. Text output is
byte-identical to Python's; `--json` prints the Python JSON object plus
`input_identity` (`dossier --all` prints exactly the Python object, keyed by
statement ID). Rust adds one part Python lacks (#952): the note sections that
name the target explicitly, as `note_mentions` in JSON and a final "Notes
mentioning the target records" text block (`context`: the argument, its
results and its conclusion). The parity tests drop both. Navigation only:
nothing here closes a statement, changes a route cost or certifies anything.

- `truth related STATEMENT-ID [--limit N]` (default 10 shown; JSON retains all matches) ranks
  over the loaded corpus in memory. Python ranks over its disposable SQLite
  projection `.cache/research-index.sqlite`; Rust needs and writes no cache
  (the separate `truth index`, below, keeps one for search and lookup).
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
  Comparator config, as Python does. Rust adds the elaborated types below.

**Elaborated types (#960, Rust only).** After running Lean, `truth
bind-check` (full or scoped, but not from a saved `--lean-json`) records
each described result theorem in `.cache/bind-types.json`
(`truth::bind_types`; `$TRUTH_BIND_TYPES_CACHE` overrides the path): the
exporter's binder names, head constants and types as Lean pretty-printed them
with full names, the result type and theory-bundle conjuncts, and an input
digest over the Lean toolchain, Lake manifest and configuration,
`scripts/BindTypes.lean`, the Solution module, every repository module in its
source import closure and their `.olean.hash` files. A scoped run merges into
the existing cache. `context` only reads it and never runs Lean: for each
result whose entry still matches the result record and whose digest it
recomputes unchanged, the text pack adds an `elaborated` block (parameters,
each hypothesis or bundle conjunct `h.N` with its type and bound statement or
`unbound`, the conclusion, unbound premises; hypothesis lines are cut at
about 1 KB per result, and `--json` carries the full signature and every
hypothesis under `lean[].elaborated`). The binding is recomputed from the
cached types and the current records with `bind-check`'s rules, without
expression contracts or sense checks, so it is advisory and never
verification evidence. When the cache is absent, unreadable or stale for a
result, the text pack adds exactly one line saying so under the Lean heading
and otherwise keeps the source-text view; `--json` always carries the
`bind_types` summary. Actual axioms are not shown: no Comparator or NanoDa
output is kept locally (CI logs only), so only the permitted axioms of the
Comparator config appear. Python's `context` has none of this; the parity
tests point Rust at an absent cache and drop the notice line and the
`bind_types` summary before comparing.

`dossier` and `context` consume the frontier report. Without
`--frontier-json` they compute it in-process with the Rust `frontier` (the
port of `corpus.py frontier`, below) on the same checkout and root
(`--frontier-root`, default `STMT-CATHOLICISM-TRUE`). With `--frontier-json
FILE` they read a saved `truth frontier --json [--frontier-root
STATEMENT-ID]` report instead (Rust cannot check that it is current), and
`--frontier-root` only checks that report's root. Either way Rust reads only
the fields these views consume (`truth::dossier::FrontierView`).

Errors: an unknown ID exits 3 (`unknown_id`); a non-statement `related`
target or an ambiguous `context` target exits 2;
an unreadable or non-frontier report or an unknown frontier root exits 1.
Python prints the same messages with exit code 2.

Not ported: the full `validate()` that the retired Python `dossier --all`
ran first (run `truth check` for it).
The retired parity script checked parity on a sample of 30+ statements
(closed, stated, supported, bare, off-frontier and floor-marked), all 3,760
`dossier --all` entries, 15 `context` targets (12 argument IDs, which here
coincide with their result IDs, and 3 uniquely concluded statements) with
several `--limit` values, and the error cases, from a saved Python report;
and, for a subset plus `dossier --all`, that the in-process frontier gives the
same output.

## `tree`

`truth tree STATEMENT [--down N] [--up N] [--budget N] [--materialize-edge KEY]`
draws the argument graph re-rooted at any statement, with the definitions of
every statement in view (#1674). It has no Python counterpart. All statuses come from one
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
premises or not at all. The two sides share the budget so that neither can
crowd out the other: when the statement has dependents (`--up` above 0 and an
argument using it), the support walk first stops at `budget - (budget - 1) / 2`
nodes, the dependent walk may then use everything left, and the support walk
resumes, in the same breadth-first order, with whatever the dependents did not
use. A side that needs less leaves its share to the other. A co-premise that
the upward walk later reaches as a conclusion becomes a `dependent`, and one
the resumed support walk reaches becomes a `support` statement. The resumed
support walk expands every premise that has no `down_depth` yet, whichever
walk admitted it: a `dependent` it reaches keeps its role (the first walk to
admit a statement names it) and carries both `up_depth` and `down_depth`. Every cut leaves
a `truncated` entry (`side`, `reason` `depth` or `budget`, `omitted_arguments`)
and a `… truncated` text line.

JSON (`schema_version` 2, with `input_identity`): `root`, `case_root`,
`options`, `statements` (status, depth, closed reason, established,
`reaches_tree_root`, role, depths, definitions, senses), `arguments` (premises,
steps, results with theorem, Solution module and transcription kind, the root
route entry), `edges`, `definitions`, `disambiguations`, `truncated`,
`node_count`. Each edge has a `kind` (`supports`: argument → conclusion,
`uses`: argument → premise, `strengthens`: strong → weak statement, and the
derived kinds below), `extra_premises`, `verified`, `derivation`, `cycle` and
`inversion` (`null` for record edges).

**Inversions (#1674 phase 2).** Re-rooting turns arguments around, and only
some inversions are valid; the generic lemmas are in
`TruthCore/Logic/Inversion.lean` (zero axioms, constructive). The view derives
two edge kinds and creates no records:

- `contrapositive`, for every premise Pi of every verified non-transcription
  argument P1, …, Pn ⊢ C in view: ¬C with the other premises gives ¬Pi
  (`from` C, `to` Pi, `inversion.negated` true, the other premises in
  `extra_premises`). It instantiates `TruthCore.Logic.Inversion.contrapositive`
  at the argument's result theorem (`derivation`, `inversion.source_theorem`).
  It is `verified` only when its materialized result exists.
- `inverse_conditional`, at the tree root A, for each argument in view that
  uses A and concludes a C with at least one other recorded argument: C, with
  the premise bundle of every other alternative failing, gives A
  (`inverse_premise_of_exhaustive_at`), but only under the exhaustiveness
  premise that C holds only through its recorded arguments. That premise is
  listed in `inversion.requires` (role `exhaustiveness`, the alternatives in
  `argument_ids`); no corpus record type states such coverage, so it is
  reported as an unregistered open premise, and the edge is never verified.

The unconditioned inverse C ⊢ A is invalid (A = B = false, C = true;
`unconditioned_inverse_invalid`) and is never emitted. Each derived edge has an
`inversion.key` (`contrapositive:<argument>:<premise>`), printed raw in the
text's Inversions section. That section lists the contrapositives toward the
root and every inverse edge, and counts the rest.

`--materialize-edge KEY` turns one `contrapositive` edge of the view into
source files, only on that explicit request (`inversion.rs`): a batch spec
`specs/inversion-<name>.toml`, a vocabulary module
`TruthCore/Logic/Inversions/<Name>.lean` defining each negation the corpus
does not already state (an existing statement whose declaration is defined as
that negation, such as `NoGratuitousSuffering`, is reused), and a Solution
`TruthCore/Results/Logic/Inversions/<Name>/Solution.lean` whose theorem
`contrapositive` instantiates the lemma at the original theorem. The argument
is declared an `instantiation` transcription (invariant 16): it closes its
conclusion only when every premise, including the negated conclusion, is
closed. It prints the remaining ordinary steps (`argument_batch.py challenge`
and `records --write --fix`, `root-imports.sh --write`, `lake build`,
`bind-check`, `verify-result.sh`). Existing files with other content are never
overwritten. A source whose header premises are not `(h : P …)` groups, that
has `sense_bridges`, or that is in the legacy sense allowlist is refused, since
the generated argument could not bind or pass `truth check`. An
`inverse_conditional` edge is not materialized until its exhaustiveness
premise is registered.

**Batch mode (`--out-dir DIR STATEMENT...`)** writes, for each statement,
`DIR/<uuid>.json` with exactly the JSON of the single command (same options),
and prints a summary (`written`, `out_dir`, `options`). Closure, establishment,
statuses, depths and transcription kinds do not depend on the frontier root,
so one shared report supplies them (`frontier::ViewReports`); only
`reaching_root_statements` and the root's routes are recomputed per statement,
by the same walk and route computation the full report uses. On the real corpus
this takes about 35 s for all 4,587 statements against about 1.2 s per single
call. The corpus explorer uses it to prebuild its `/tree` pages
(`docs/github-pages.md`).

## `index`

`truth index (build | search WORDS [--limit N] | show ID | duplicates | summary
| parity | export PATH | bundle --case ID [--premise S]... | compare --case ID
[--left S]... [--right S]...)` ports `scripts/research_index.py` (#954 slice
B7; `truth::index`, rusqlite with bundled SQLite and FTS5). The database
`.cache/truth-index.sqlite` is a disposable projection of every
`corpus/**/*.json` file, never an authority. It is bound to the builder
version and an FNV-1a digest of every indexed path and byte string (the hash
of `input_identity`); every query reuses it while that binding holds and
rebuilds it otherwise, and `build` rebuilds it unconditionally. Publication is
atomic: a failed build leaves the previous database. Tables, rows, the search
expression, FTS5 ranking and the queries are Python's; `bundle` and `compare`
run the registered-only `truth::configurations` engine. Output is the Python
JSON (indented; compact with `--json`; object keys sorted). `export` prints the
original bytes. Errors exit 1 (Python's messages), usage errors 2.

Research notes (#952): the index also projects `docs/notes/**/*.md` (up to
1 MiB each) into Rust-only tables, with their paths and bytes in the
digest. `search` appends up to `--limit` note sections, typed `"kind":
"note"`, after the records. `show docs/notes/x.md[#anchor]` shows a note or
one section. `show RECORD` adds `mentioned_by_notes`. Links come only from
explicit uuid, legacy ID, record-path or code-span label mentions
(`truth::notes`; `docs/notes/research-index.md`, "Research notes").

Differences from Python: Python's query commands reject a stale index, and its
digest hashes the script, so the two use separate files
(`.cache/research-index.sqlite` there). Rust also resolves a legacy id or
label, optionally `kind:`-prefixed, for `show`, `--case`, `--premise`,
`--left` and `--right`. Python's `related` subcommand is `truth related`.
Python has no note tables or note hits. The retired
`scripts/truth_parity/index.py` compared every record table row for row (all
but the digest) and the JSON of every subcommand, without the note parts, on
the real corpus and a fixture; the frozen goldens `truth/tests/golden/index/`
keep its fixture query cases, and the unit tests of `truth::index` cover
stale refresh, failed-rebuild preservation and corrupt-projection detection.

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
has no JSON output. The frozen goldens `truth/tests/golden/attribution/` (recorded by the retired `scripts/truth_parity/attribution.py`) compare both on
the cases of `test_attribution_check.py` on fixture repositories (including
a readable-id base and a stub `materialize`) and on the real corpus against
several base revisions. CI's attribution step runs it.

`truth check` already includes every offline rule of `python3
scripts/source_evidence.py check` (`validate_manifest` and
`validate_bindings`, with Python's messages; the `check` parity fixture covers
them). Only the summary line counting bibliographic and permanently
unavailable passages is Python's; the separate command is no longer a gate.

## Explicit evidence traversal

`truth evidence TARGET [--issues-from FILE] [--limit N]` follows explicit
references in both directions without depth or candidate limits. `--json`
returns complete typed nodes, their record/section content, every reference
edge and deterministic shortest predecessor paths. Each edge identifies its
JSON field or note line and resolution method. Cycles are visited once;
unresolved references and absent offline issue history remain visible.

This graph reuses canonical corpus loading and note resolution. It includes
nested field and object-key references, senses, attempts, claims, passages,
sources, all `docs/**/*.md` research text, and optional issue/PR snapshots.
Relative Markdown links and anchored note links are resolved locally. A
reference is navigation evidence, never entailment or a synonym assertion.
Foreign issue URLs are not matched by number alone.

`brief`, `novelty`, `context`, `dossier` and `related` expose the same evidence
graph. Question discovery keeps explicit references separate from ambiguous
canonical lexicon mappings. Default JSON keeps every discovered node and its shortest explanation path,
with explicit counts of omitted alternative edges and content. Add
`--full-evidence` for every edge and complete node content; the dedicated
`evidence --json` command always returns that full view. Text prints bounded
summaries and omitted counts. Semantic equivalence, interpretation
fidelity and assumption agreement require comparison beyond retrieval.

## `brief` and `novelty`

Scoped `current_assessment` entries from existing attempts appear first, with
reviewed revision, publication disposition and next test. Historical heading
dates do not imply supersession. Declared meaning/warrant/judgment `revisions`
expose potential downstream uses and unresolved reassessments without changing
formal validity, in consumer tiers (`premise_use`, `import`, `reference`,
`prose`; #1757): registered premise use is always listed and addressed per
consumer, the other tiers may share a `group` disposition, and a consumer
reassessed as unchanged screens what lies downstream only through it. See [the canonical record format](../docs/premise-dossiers.md#current-assessment-and-publication-disposition)
and [declared revisions](../docs/premise-dossiers.md#declared-revisions-and-downstream-reassessment).
`truth currentness [--frontier-root STATEMENT] [--limit N]` (#1751,
`truth::currentness`) is the read-only per-root view of which open premises
have a covering current assessment, only legacy attempts, or none, with
advisory heuristic flags; see [currentness view](../docs/premise-dossiers.md#currentness-view).


`truth brief (TARGET | --question TEXT)` and `truth novelty (TEXT |
--statement STATEMENT)` (#1643, #954 slice B9; `truth::brief`) retrieve the
cumulative record before a worker judges a premise's maturity or calls a
result new. Both are read-only views over existing authorities; they add no
status, judgment or record.

- `brief TARGET` (a statement, or an argument or result read through its
  conclusion; notes citing one of its result theorems by its last two name
  components count as naming it): identity and revision; senses and definitions; **formal
  status** from the frontier only (closure, `established`, root reach, open
  leaves; a closure such as `proved` is not establishment); every argument
  concluding it with its results and unestablished premises (a verified
  result with an unestablished premise is reported as a conditional
  consequence); arguments using it; rivals, objections and refutations of
  rivals; strength orders and equivalences; attempts, newest first; the note
  sections naming it or its arguments (explicit mentions, `truth::notes`),
  with the judgment- and rival-headed sections of those notes quoted with
  their dates and listed newest first, never reconciled; issues and PRs from
  the snapshot that name it, target it in an acceptance block or are
  referenced from those notes; `truth related` neighbours; and an `absent`
  list of what is not recorded or unknown.
- `brief --assessments-for ID,ID,...`: compact JSON projection for the current-case
  page. Reads each note once, retains every assessment/rival excerpt from notes
  explicitly mentioning a requested statement or its concluding argument/result,
  and supplies path, line and matched-record provenance. Empty lists mean unknown;
  note-wide context is not an assessment of every mentioned statement. Reuses the
  existing brief section extraction (the reference graph is built only when
  revision declarations require impact analysis), with no reconciliation,
  endorsement or strength ranking. IDs/labels/aliases use the normal resolver.
- `brief --question TEXT` opens with matching judgments and investigations from
  the same search used by `truth synthesis --question`. The broader brief also
  includes the notes the `truth index` FTS5 projection ranks
  for any query word (by stem prefix) or identifier, each scored paragraph by
  paragraph and heading by heading (coverage = query items found in one
  unit), a note whose title covers half the question ranked first, with its best
  paragraphs, recorded assessments, superseded/retired markers and recent
  first-parent git history (the PRs that changed it); the statements the best
  sections name; records by prose coverage; issue numbers the matched
  sections reference; and snapshot items ranked by evidence weight
  (referenced from a matched section or a matched note's title, or a PR that changed a matched note,
  naming a matched note, naming a statement those notes name, lexical).
- `novelty TEXT`: exact IDs/labels/paths in the text; corpus statements whose
  Lean declaration uses the text's identifiers (structural), and arguments
  using several of them; note paragraphs, read with each note's own notation
  (`` `D(x,y)` for the existing `DependsForBeing x y` ``) so `D(y,x) ↔
  ¬B(y,x)` matches `DependsForBeing ↔ ¬CanBeWithout`; record prose; and
  snapshot issues/PRs. The classification is `already-recorded` (some unit
  has identical normalized proposition text), `partially-recorded` (candidate
  prior work exists but semantic identity is unknown) or
  `no-match-found`, never
  "novel"; each hit says its evidence kind (an uncertified note, a statement
  whose status is the frontier's, workflow history). `--statement ID` checks a
  statement's original paraphrase against everything except that
  statement. Text identity does not certify equivalence of interpretations or assumptions.

A listed issue or PR that hands its scope on ("Superseded by #N", "the
distinct successor #N", "Remaining scope continues in #N") shows `scope
handed to #N [STATE]`. #1644 benchmarks both commands against the earlier
lookup workflow (`scripts/retrieval_benchmark.py`,
`docs/notes/retrieval-benchmark-1644.md`).

Both take `--limit N` (entries per text section, default 6; JSON retains complete candidate discovery,
independent of this presentation limit; `--full-evidence` adds full graph content) and `--frontier-json`/`--frontier-root` as `dossier`. Hits
are ordered deterministically (coverage, then evidence kind, then path,
line, number or id). Note and record search reuses `.cache/truth-index.sqlite`
while its digest matches and rebuilds it otherwise; the JSON `index` field
records which. `--issues-from FILE` reads an offline snapshot, either a `gh
issue list`/`gh pr list --json number,title,body,url,state,comments,updatedAt`
array or `{"captured_at": ISO, "items": [...]}` (merge issues and PRs with
`--state all` so closed and superseded work is searchable). Without it the
output says issue history is **unknown**, never that there is none; a
snapshot without closed items, or captured before the checkout's HEAD
commit, is flagged. Errors: an unknown target exits 3; an unreadable
snapshot exits 2; index errors exit 1. Python has no counterpart.

### Starting from a GitHub issue

Use the issue number when a worker returns an older finding or an open issue
appears ready for assignment. Run the brief on the revision whose research
you want to use. For dispatch, that is current `main`.

```bash
python3 scripts/issue_snapshot.py 1792 > /tmp/truth-1792.json
target/release/truth brief '#1792' --issues-from /tmp/truth-1792.json
```

The first command reads the issue and its paginated GitHub timeline. It keeps
the issue body, comments, and the same-repository issues and PRs that referenced
it. It can find a merged delivery while the issue is still open. The second
command runs offline. The text brief shows excerpts from the assigned issue's
comments with their links when available. Explicit follow-up headings receive
priority, followed by comments from an identified repository owner or issue
author. A follow-up may add to the original request. Compare the assessment’s
scope, reviewed revision, source note and next test with each relevant PR's
state. An issue mention can
refer to an objection or an earlier draft. Compare what the PR delivered with
the actual request before closing or dispatching it.

An assessment can name the exact note section that mentions the issue. The
brief follows that link even when the assessment omits the issue number.
It also shows records explicitly named in that section and attempts citing a
related PR in their `evidence`. Each result identifies the reference that led
to it. A batch PR can deliver several investigations. Match the attempt's scope
and the section containing the finding before treating it as the issue's answer.

If a merged investigation is missing from a brief, compare its Git revision
with the references currently recorded on its attempts. The
[delivery audit](../docs/premise-dossiers.md#attempt-records) can inspect every
attempt changed since the last checkpoint in one run.

The text gives a bounded view. `--json` includes the original request and
comments, all matching records and all directly referenced note sections.
A previously captured snapshot can be reused. Without a snapshot, the issue
brief can still find directly referenced checkout records. Outbound-only links,
private or unreferenced work and changes since capture can require another
source. A wider all-state issue/PR snapshot in the supported format also works.

### Checking a returned worker revision

Use the commit from the handoff and either its PR number or its owning attempt.
This example looks up the undrawn-triangle investigation from #1790.

```bash
python3 scripts/reconcile_worker_report.py c96f355e4913031e832475c0b7b3bdda7f94fe9e --pr 1988
```

The report compares the worker commit with the recorded review, the published
head and the selected main revision. For #1988, the worker commit is the exact
revision with qualified acceptance. The later publication includes that
revision. Read the returned assessment for the finding, its limits and the
test that could reopen it.

The command uses local `origin/main` by default. Refresh that ref when you need
current publication status, or select a known revision with `--main`. An ordinary
local PR merge supplies the head and merge commits. Otherwise the command can
look up the PR with `gh` or read a saved `gh pr view` JSON record supplied with
`--snapshot` (see `--help` for fields). A squash, divergent histories or
missing objects can leave the relation unresolved. Inspect the cited changes
and review scope before deciding what needs another review.

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
the frozen goldens `truth/tests/golden/issues/` (recorded by the retired `scripts/truth_parity/issues.py`) check this on the cases of
`test_issue_acceptance.py` on a fixture checkout and on the recorded snapshot
`scripts/truth_parity/fixtures/issues-snapshot.json` (retired with it) extended
with blocks naming real corpus records.

## `workers`

`truth workers [--authored-only-by MODEL] [--open] [--frontier-root STATEMENT]`
(owner direction, 2026-11-26; `truth/src/workers.rs`) is the revisit query over
the attempt records' optional `workers` lists (`docs/premise-dossiers.md`). For
each statement named in some attempt's `statement_ids` it prints the latest
attempt (by date, then id) with its kind and outcome, the models that authored
attempts on the statement (`role: "author"`), the models that reviewed them,
how many of its attempts record no author, and whether the frontier computed
in-process for the root leaves the statement open (not closed) and whether it
reaches the root. Statements are listed by latest attempt, newest first.

- `--authored-only-by MODEL` keeps statements whose recorded authors are
  exactly `MODEL` (the `model` string, for example `gpt-6.2-sol`). Attempts
  without an author entry are counted, not treated as another model, so check
  the "attempts without an author entry" count before reading "only".
- `--open` keeps statements the computed frontier does not close.

For example, `truth workers --authored-only-by gpt-6.2-sol --open` lists open
propositions so far worked on only by that model, as candidates to revisit with
another one. `truth dossier`, `truth context` and `truth brief` show the same
entries under each attempt (`worker: author codex/gpt-6.2-sol (high) 2026-11-26
PR-2020`), and their JSON carries the `workers` list. The view writes nothing;
a worker entry records who did the work, not evidence about its targets.

## `bottlenecks`

`truth bottlenecks [--stage N]... [--min-arguments N] [--min-routes N]
[--limit N] [--authored-only-by MODEL] [--frontier-root STATEMENT]` (owner
direction, 2026-11-26; `truth/src/bottlenecks.rs`) lists the open premises
where several arguments or routes stop, for choosing which premises get a
focused negation-side review ([when several arguments stop at the same
premise](../docs/systematic-corpus-loop.md#when-several-arguments-stop-at-the-same-premise)).
It reads the reaching-root frontier computed in-process for the root and
adds no closure rule of its own. For each open premise it prints:

- **routes**: the root routes (`truth frontier --routes`) that need it. A
  route's open premises are the leaves of its expanded route; a stated or
  supported premise proved from open premises stays such a leaf, so a route
  needs a premise when it is a leaf or when every verified derivation of a
  proved leaf needs it. The JSON also gives `routes_using_it_in_some_proof`
  (some chain of verified derivations uses it);
- **stage routes**: per stage, the verified derivations of the stage
  conclusion (for stage 1 the existence of God) that need it, in the same
  sense. Every root route rests on the stage conclusions, so stage routes
  separate premises that the root routes share;
- **args**: the distinct arguments that take it as a premise;
- **reach**: its transitive dependent statements;
- **stages**, the frontier **support** class (`bare`, `supported`: only
  supporting or unpinned claims, `stated`: a pinned stating claim) with
  `+derivation` when a verified derivation is a conditional support option,
  its recorded **rivals** (refuted ones counted) and **objections**, and the
  models that authored attempts on it (as in `truth workers`).

Premises are ranked by routes, then the stage routes of the selected stages
(of every stage without `--stage`), then arguments, then reach.

- `--stage N` (repeatable) keeps premises on which a stage-N conclusion rests.
- `--min-arguments N` (default 2) and `--min-routes N` (default 0) set the
  thresholds; `--limit N` prints the first N after ranking.
- `--authored-only-by MODEL` keeps premises whose recorded attempt authors are
  exactly `MODEL`, so a second model can take premises one model has worked
  on alone.

For example, `truth bottlenecks --stage 1 --stage 2 --min-arguments 3
--limit 20` lists the shared open premises of the God-existence and divine
attribute stages. The counts describe shared dependency, not philosophical
merit or the strength of a premise (`AGENTS.md`); a listed premise is a
candidate for review, not a finding about it. The view writes nothing.

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

The frozen goldens `truth/tests/golden/navigation/` (recorded by the retired `scripts/truth_parity/navigation.py`) compare every command with Python on
the real corpus and on the `check` fixture (byte-identical text and stdout,
the rewritten files, the same `corpus error:` line and exit code 2 on broken
variants). `scripts/verify-all.sh` lists results with `truth results`; the
explorer's next-work browser test reads `truth next-steps`. The Python
implementations stay until their retirement (#954, R2).

## `orphans`

`truth orphans [--frontier-root STATEMENT-ID] [--by module|family] [--all]` lists
verified results (status `solution-present` or `verified`) whose argument
conclusion does not reach the frontier root (default
`STMT-CATHOLICISM-TRUE`) and which do not support a verified recorded refutation
of an `alternative_to` rival of a root-path node. Support follows premises and
commitments backwards through verified arguments, including transitive support.
Open assumptions permit conditional connection; this does not close them or
establish root truth. Solution imports alone remain advisory contacts. `thickness --queue` ranks only statements that
already reach the root, so such work is otherwise invisible to round
selection. Reaching the root is the same route-aware walk as `thickness`;
The retired parity script checked the disconnected set against Python's
`reaching_root_statements` plus `corpus.refutation_support`.

Each verified result also gets a **placement state** (owner decision,
2026-11-27; `docs/corpus-model.md`, "Result placement"), the first that
applies: `reaching` (the connected notion above), `placed_diagnostic` (a
premise-free result whose result or argument `tests` a root-path statement or
a root-path argument), `placed_rival` (an `alternative_to` or `attacks`
relation between its conclusion and a root-path statement, either direction;
its argument `attacks` or `refutes` one; or a root-path argument `attacks` or
`refutes` its conclusion), `planned` (a valid `connection_plan` on its conclusion targeting
a root-path statement) and `unplaced`. A root-path argument has a verified
result and either concludes a root-path statement or is itself a verified
refutation counted as connected above; an unverified argument record places
nothing. `--json` gives `state_counts` over all
verified results, `transcription_state_counts` for the transcriptions among
them, per group `placed_count`, `planned_count`, `unplaced_count` and
`state_counts`, and per result its `state` and `placed_by` (the relation or
plan target). The text lists, per group, only the unplaced conclusions and
omits groups without one; `--all` lists every disconnected result with its
state and transcription kind. Contact lines read `contact (on root path):`:
they name root-path statements as leads, not disconnected results.

`truth orphans --base REV --gate` is the **placement gate**. It computes the
states at the head and at the base (read like `frontier-diff`, "head rules on
base data") and judges each verified head result that is new (no verified
result with its ID at the base), whose argument changed (another argument id,
conclusion, premise or commitment set), or that was placed at the base and is
unplaced now. It exits 1 when a judged result is `unplaced`, naming the
conclusion, the result and the change, and stating the honest options: a real
derivation to a root-path statement, a `tests` link for a diagnostic, a typed
rival relation, or a `connection_plan` naming the exact missing bridge
(contrived edges and tautological bridges are not acceptable; reviewers check
every new edge). Unplaced results that are not judged are the backlog, counted
but never failed. An unreadable base is a `revision_error` (exit 1). `--gate`
requires `--base`; `--base` excludes `--by`, `--senses` and `--all`. CI runs it
on every pull request against `HEAD^1`, beside `connectivity --base`, which
still judges statements; `scripts/preflight.sh` runs it against the merge base.

`truth orphans --base REV` ports `scripts/orphan_summary.py --base REV`, the
Markdown table CI adds to a PR's job summary: the disconnected count at the
base revision and at the working tree, and their difference. The base is read
as `frontier-diff` reads it: its `git archive` extract, judged by this
binary's rules ("head rules on base data"). A base that cannot be read or computed is reported as
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
lists eight unplaced conclusions per group; `--all` and `--json` list every
disconnected result.

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

## `type-lints`

`truth type-lints [--base REV]` reports advisory metadata warnings over the
elaborated types `bind-check` cached: whole-argument `tests` relations whose
subject's certificate does not reach a registered logical premise such as
`ExcludedMiddle`, and statements that link a definition whose defined Lean
constant their bound type does not reach, naming another sense of the same
disambiguation when the type uses one. Only fresh cache entries are read, so
run `bind-check` (or `bind-check --affected --base REV`) after `lake build`
first. With `--base`, only records new or changed since that revision are
judged. It always exits 0 (docs/corpus-model.md, "Type metadata lints").

## `connectivity`

`truth connectivity [--frontier-root STATEMENT-ID] [--list-isolated N]` is a
**diagnostic** for the cohesive-graph goal (owner direction, 2026-11-26): it
shows which statements share no recorded contact with the frontier root
(default `STMT-CATHOLICISM-TRUE`), so that work connecting them can be found.
Its counts describe the graph's shape. They are not a progress score, a
measure of philosophical merit, or a quantity to optimize, and contact is not
warrant: the command closes, supports and attacks nothing.

It reports, over all statements:

- **reach root via argument chains**: statements from which the root is
  reached by following premises and commitments up to conclusions, through
  any recorded argument whatever its verification status (unlike the
  route-aware `frontier --reaching-root`);
- **root component**: the undirected connected component of the root, whose
  edges are each argument (premises and commitments to the conclusion), each
  relation of any predicate, `tests` included (a statement endpoint stands for
  itself, a claim for its statement, an argument for its conclusion and
  premises, a result for its argument's; `background_statement_ids` join the
  object), and each attempt (the statements it names);
- **other components**: the statements with some edge outside the root
  component, the number of their components and their sizes (largest first);
- **isolated**: statements with no edge at all.

The statements outside the root component are classified, isolated and
island statements separately, by the first match of: the conclusion of a
premise-free argument (a control, model or consistency check: record what it
tests with a `tests` relation, `docs/corpus-model.md`); a source reading (a
claim states it); the conclusion of an argument whose premises are off the
root component; named only by an attempt; unused. `--list-isolated N` lists N
isolated statements with their class (premise-free results first, then by
label). `--json` gives every non-root component's statement IDs. The method
matches the measurement script of the 2026-11-26 baseline, extended only by
the `result` endpoint of `tests` relations. The report ends with every
recorded `connection_plan` (`docs/corpus-model.md`), with its target, missing
bridge and blocker: *outstanding* while its statement is outside the root's
typed component (below), *ready for plan review* once it has joined it. CI
prints the text report to the job summary.

`truth connectivity --base REV` is the **gate on new disconnection** (owner
direction, 2026-11-26: disconnected work must not accumulate again). It reads
the base revision's committed corpus like `frontier-diff`, `thickness --base`
and `orphans --base` ("head rules on base data") and computes the root's
**typed component** at both revisions: the report's edges except attempt
co-citation, which records research activity rather than a typed contact. It
judges each statement outside the typed component at the head that is new
(present at the head, absent at the base), was in the typed component at the
base, or carried a `connection_plan` at the base. Such a statement passes only
with a valid `connection_plan` (the shape `truth check` requires, checked by
the gate itself) whose `target_statement_id` is in the head's typed
component; statements outside it at the base that never had a plan are not
judged. The command exits 1 and lists each offending statement as
`label [uuid8]`, with the reason (no plan, an invalid plan, or a plan target off the typed
component). It also lists the outstanding planned statements and the plans
ready for plan review: joining the component does not show that the named
bridge was delivered. The gate checks that work is linked, not the
substantive root-route obligation. `--base` and `--list-isolated` are
alternatives; an unreadable base is a `revision_error` (exit 1). On a pull
request CI runs it against `HEAD^1` (checkout is the merge commit) and fails
on it; `scripts/preflight.sh` runs it against the merge base.


## `bridges`

`bridges` ranks advisory bridge candidates for underived statements by the
Lean constants their declarations share, from a `scripts/StatementConstants.lean`
export (`--constants`) and either `--target ID` or a
`truth thickness --queue --json` file (`--queue-file`, first `--targets N`,
default 10). It is a search heuristic, not a proof or equivalence judgment;
see `docs/bridge-candidates.md` for the pipeline and the optional Lean trial.

## `bridge-experiments`

`truth bridge-experiments RESULT --profile-module MODULE [--limit N]
[--frontier-root STATEMENT]` ports `corpus.py bridge-experiments` (#953;
`truth::bridge_experiments`, the port of `scripts/bridge_experiments.py`): the
read-only discovery of recorded cross-argument joins where one result's
Solution directly imports another's, both under the one named Lean profile
module and both conclusions in the explicit focus of an attempt with an open
blocker. Lean imports and import closures are the `context` pack's; the
frontier is computed in-process. Python's `--root STATEMENT` is
`--frontier-root`. Text is byte-identical, errors are Python's `corpus error:
…` with exit code 2, and `--json` is Python's report plus `input_identity`;
the frozen goldens `truth/tests/golden/bridge_experiments/` (recorded by the retired `scripts/truth_parity/bridge_experiments.py`) compare both on the cases of
`test_bridge_experiments.py` and on results the real corpus's attempts cite.
It ranks what to read first; it proves, refutes and closes nothing.

## `countermodel`

`truth countermodel THEOREM [--omit HYP]... [--all] [--size N] [--module
MODULE] [--no-check]` (`truth::countermodel`) searches finite omission
countermodels and renders them as `delta …; decide` certificates, which Lean
checks unless `--no-check` is given (docs/countermodels.md). It replaces
`scripts/countermodel.py` and keeps its search order, so the same theorem
yields the same models: the golden replays in `truth/src/testdata/countermodel/`
compare recorded `scripts/Countermodel.lean` skeletons of six results against
the reports the Python finder gave. Exit code 1 when Lean rejects a
certificate, 2 when the theorem is unavailable or outside the fragment.

## `prove-sweep`

`truth prove-sweep [--theorem NAME]... [--module MODULE]... [--heartbeats N]
[--batch N]` (`truth::prove_sweep`) tries a fixed tactic portfolio and a
transcription probe on every frozen Challenge theorem. It runs one `lake env
lean --json` per batch of Challenges and reports, per target, `closed` (with
the first closing tactic), `unresolved` or `error`, plus a likely-transcription
flag (docs/prove-sweep.md). Progress goes to stderr. It is advisory and writes
nothing; its unit tests cover Challenge parsing, scratch generation and
message classification without Lean.

## `discover`

`truth discover (--target STATEMENT | --targets open-root|next-tests)...
[--module PREFIX]... [--premise STATEMENT]...
[--premise-pool closed|proved|all] [--candidates N]
[--limit N] [--heartbeats N] [--batch N] [--jobs N] [--zipperposition PATH]
[--write-spec PATH]` (`truth::discover`) searches for new implications between
corpus propositions with Duper (#1784, docs/discover.md): candidate retrieval,
goal generation over the statements' own Lean declarations
(`scripts/Discover.lean`), minimization, the vacuity, transcription,
known-composition, sense and axiom filters, a certification run of the
rendered theorem text, and a ranked list of missing bridges. `--write-spec`
writes an `argument_batch.py` spec draft and a Solution draft, never corpus
records. Unit tests cover goal generation, the filters and report parsing
without Lean; CI runs one fixed known derivation end to end.

Repeated `--premise` supplies an exact ordered bundle through that same
pipeline, bypassing retrieval and automatic bridge insertion. Open premises
are allowed; `--module` filters only targets in this mode. Do not combine an
exact bundle with `--premise-pool` or `--candidates`. The JSON records the
selection mode and canonical input IDs separately from the minimized proof.

## `senses`

`truth senses (report [--write] | allowlist [--write] | ratchet --base REV)`
ports `scripts/sense_index.py report|allowlist|ratchet` (#1233): the arguments
that use several senses of one disambiguated term without a connecting sense
bridge, and the senses without a distinct Lean declaration (`truth::senses`,
the same sense index `truth check` validates with). `report` prints (or
writes) `docs/notes/sense-index-migration.md`; `--json` gives the mixing
entries and undeclared senses. `allowlist` regenerates
`corpus/sense-index-allowlist.json` with `--write` and otherwise fails when it
is stale. `ratchet --base REV` lists the entries that are no longer needed and
fails (exit 1) when the allowlist gained an entry since REV, arguments compared
by the uuid their key resolves to; CI's sense-index step runs it. Text,
stderr and exit codes are Python's byte for byte
(frozen in `truth/tests/golden/senses/`; the retired `scripts/truth_parity/senses.py`
also compared the real corpus against several bases); `sense_index.py migrate`, a
one-shot migration, stays Python.

`truth senses parameters [--json]` lists the authored parameter-level sense
tags (`senses[].lean_parameters`, #1784; rules in `docs/corpus-model.md`,
"Sense-indexed terms") by sense. `truth::parameter_tags::ParameterTags` is the
reader other commands reuse (sense → tagged parameters, parameter → senses,
declaration → tags); `truth check` runs `parameter_tags::validate`. An
untagged parameter is unknown.

## `semantics`

```text
truth [--root PATH] [--json] semantics TARGET [--frontier-root STATEMENT] [--limit N]
truth [--root PATH] [--json] semantics [--premise STATEMENT]... --conclusion STATEMENT
      [--definition DEF]... [--bridge STATEMENT[@SENSE,SENSE]]... [--strict]
```

One read-only view of the semantic dependencies of a proposition or a
derivation (`truth::semantics`), so an agent resolves meanings and checks
sense compatibility before proposing a new argument. It adds no sense engine:
the term-sense computation, bridge connectivity and legacy allowlist are the
ones `truth check` uses (`truth::senses`, `check::validate_argument_senses`),
and formal status comes from `corpus/definition-status.json`
(`truth definitions status`).

- **Statement mode** (TARGET a statement): the proposition (label, paraphrase,
  `lean_declaration`); each linked definition with the sense label(s) it
  realizes, its Lean declaration, formal status (settled by Lean, primitive,
  constraint, unresolved, no Lean declaration, or not computed) with its
  `formal_gap` kind, and basis (sourced or stipulative); the disambiguations it
  links or reaches through a linked definition, with the sense it takes and a
  `resolution` excerpt; the senses it uses per term, flagging each sense
  without a distinct `lean_declaration` (`bind-check` cannot catch equivocation
  on it); then the arguments concluding it and those using it as a premise or
  commitment (each list bounded by `--limit`, default 10; arguments whose
  conclusion reaches the frontier root first, marked `[root route]`, then file
  order). For each argument and term: the senses, the premise, conclusion,
  commitment or argument-level `definition_ids` carrying each, and a verdict:
  `single sense`, `bridged` (naming the `sense_bridges` statement and role),
  `allowlisted mixing — equivocation risk (legacy)`, `mixing control`, or
  `unbridged mixing` (which `truth check` rejects). A summary counts verdicts
  per term use and per argument over all connected arguments (an argument in
  both lists counts once) and lists the equivocation risks.
- **Argument mode** (TARGET an argument, or a result for its argument): the same
  verdicts for the argument, the compact semantics of its conclusion, premises
  and commitments, and a verdict summary over its support ancestry (every
  argument concluding one of its premises, transitively; not route-aware).
- **Preflight** (`[--premise …]... --conclusion …`): builds the candidate
  argument in memory from its premises, conclusion, argument-level
  `--definition DEF`s (repeatable; `argument_batch.py records` writes a batch's
  `definitions` into each argument's `definition_ids`, and `truth check` counts
  their senses) and bridges, and runs `truth check`'s own sense rules
  (`check::validate_argument_senses`) on it as on a new argument (the legacy
  allowlist does not apply): the disambiguations it must link, the senses per
  term with the statement (or argument-level definition) carrying each, the
  unbridged mixings with the bridge each needs, the used senses without a
  distinct Lean declaration, and `check`'s own message. The verdict is
  `truth check`'s for an argument with exactly these fields; it does not model
  `commitment_statement_ids` or `term_senses`, so a candidate that adds them
  can be judged differently. `--bridge STATEMENT@SENSE,SENSE` (uuid or label of
  each sense) adds that `sense_bridges` entry; the suffix is read as senses only
  when both resolve, otherwise the whole token names the statement (a label may
  contain `@`). A bare `--bridge STATEMENT` bridges the senses of each term the
  statement itself links; one that relates no pair is reported and not added.
  A bridge statement other than the conclusion is added as a premise, as
  `truth check` requires. Exit 0, or 1 with `--strict` while an unbridged
  mixing remains; an unknown statement, definition or bridge sense exits 3.
  `truth/tests/semantics.rs` writes the candidate as a new argument file and
  checks that `truth check` gives the same verdict, including for a mixing
  introduced only by an argument-level definition.

Each statement view also lists the authored parameter-level sense tags on its
Lean declaration (`parameter_tags`; text "parameter senses: CausesIn _ _ esse =
CAUSING_AN_EFFECT_3; …"), from `truth::parameter_tags` (#1784). A parameter
not listed is unknown.

A `single sense` verdict says the records link one sense per term, not that
the prose or the Lean statement is free of equivocation. `--json` gives the
same content with `input_identity`; the text names each record as
`label [uuid8]`. An unknown TARGET or statement exits 3.

## `configurations`, `configuration-report`, `models`, `territory`

These port `corpus.py configurations`, `configuration-report`, `models` and
`territory` (#954 slices B2 and A6): `truth::configurations`
(`implication_closure`, `configuration_report`), `truth::configuration_live`
(`verify_case`, `verify_compositions`, the live reports),
`truth::configuration_explorer` (the verified explorer bundle),
`truth::finite_models` (`model_report`) and `truth::territory`
(`territory_report`). Text output is byte-identical to Python's; `--json`
prints the Python JSON (plus `input_identity` for `models` and `territory`;
`configurations` prints Python's list as is). A corpus error prints Python's
`corpus error: …` with exit code 2.

The Lean-backed paths orchestrate; they never compute a verdict. They write
the same certificate and composition sources as Python, run `lake build`,
`lake env lean` and `scripts/verify-result.sh` with Python's timeouts (each
process tree killed on expiry, `truth::subprocess`), read only exit status and
`#print axioms` lines, and bind original theorems through
`scripts/BindTypes.lean`. They call `lake` from PATH, as Python does: run them
under `python3 scripts/worker_env.py --`.

- `truth configurations [--registered] [--case ID] [--seed STATEMENT]
  [--premise STATEMENT]...`: with `--registered`, the registered projection
  (no certified status); otherwise every selected case is verified in Lean
  first and no report is printed if any step fails. It validates the models
  and cases first, as Python's `configuration_context` does
  (`truth::check::registered_configurations`), not the whole corpus.
- `truth configuration-report (--output PATH | --check PATH |
  --build-input)`: `--output` live-verifies every case, replays the decision
  tree's family cores and atomically writes the bundle inside `.cache`, byte
  for byte as Python writes it plus `producer.producer_sha256` (the crate
  fingerprint `build.rs` computes, outside the input digest). It refuses an
  output outside `.cache` before running Lean (Python only after). `--check`
  and `--build-input` (with `TRUTH_CORE_CONFIGURATION_REPORT` /
  `TRUTH_CORE_REQUIRE_CONFIGURATION_REPORT`) check freshness without Lean,
  as Python does, and then require the fingerprint to match the running
  binary. `--json` prints Python's indented projection without the input
  hashes.
- `truth models [--check STATEMENT | --argument ARGUMENT] [--premise
  STATEMENT]... [--verify]`: every registered model, its classification and
  co-failure candidates; `--check`, `--argument` and `--verify` also
  Lean-check every registered model (Python `verify_models`); `--premise`
  without a target fails as in Python.
- `truth territory [--frontier-root STATEMENT] [--max-atoms N]`: Python's
  `--root` is `--frontier-root` here. Like Python it runs the full `check`
  validation first (`cli::validate_first`) and reads the in-process Rust
  frontier. Position IDs hash with a built-in SHA-256. The global position
  count is exact (Python's unbounded int): the text prints every digit; a
  count beyond `u64` has no exact JSON number here, so `--json` then fails
  with `unrepresentable_count` (exit 1) and names the Python command instead
  of printing a wrong number.

The frozen goldens `truth/tests/golden/configurations/` (recorded by the retired `scripts/truth_parity/configurations.py`) compare them on the real corpus
(every case, filtering by uuid and legacy id, seed and premise selections and
their errors; `models`; `territory` with the default bound, `--max-atoms` 40
and -3 and an unknown root) and on a fixture checkout with an incompatibility
core, an implication rule, a model a fixed constant excludes, co-failures, a
refutation core and a model that satisfies it (a `DEFECT` line), a broken
corpus and seven broken registrations.
Until R3 the retired `scripts/truth_parity/configuration_report.py` ran the Lean-backed paths of
both implementations on that fixture as a Git checkout with a recorded
toolchain on PATH (a `lake` that answers builds, prints Lean's `#print
axioms` lines and describes the theorems as `BindTypes.lean` would, and a
`verify-result.sh` stub), so no Lean runs: it compares the logged toolchain
calls, the bundle byte for byte except the fingerprint line, `--check` and
`--build-input` outcomes on fresh, stale and malformed bundles, live
`configurations` and `models --check / --argument / --verify`, and the error
and exit code of a failure at every step (build, certificate, forbidden
axiom, `verify-result.sh`, model certificates, composition, binding, a
verification defect, no `lake`); the frozen goldens
`truth/tests/golden/configuration_report/` keep those cases.
