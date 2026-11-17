# Research retrieval benchmark: brief and novelty against the documented lookup (#1644)

Measured 2026-11-16 at `c393bc7d1` (after #1686), with one offline GitHub
snapshot (1,688 issues and PRs, closed items and comments included, captured
08:16Z). This is a retrieval evaluation. It changes no premise, frontier,
proof status or issue scope, and the conclusions below concern tooling only.

## Question and method

Does `truth brief` / `truth novelty` (#1643, PR #1686) retrieve prior work
that a worker needs before calling a question unexplored or a result new,
better than the workflow documented before it? Does that justify the MCP
adapter of #1645?

- **Answer key.** `scripts/testdata/retrieval-benchmark.json` contains 24
  questions: researched-but-open (4 + 2 held out), false novelty (5 + 1 held
  out), formal validity against warrant (4), workflow history (5) and
  negative controls (3). For each question it pins the notes, issues/PRs,
  records and rivals a correct answer must surface, plus the boundaries the
  output must state. Every reference was found by grepping notes, corpus
  records and the snapshot, not from the output of the tools being tested.
  `--check-key` verifies that each pinned reference resolves.
- **Snapshot hygiene.** #1643, #1644 and PR #1686 state the benchmark's own
  answers, so they are removed from the snapshot that both workflows read.
  Both workflows also run in a detached worktree of HEAD that leaves out
  this note and the answer key (`evaluation_excludes`), so the note index
  cannot retrieve the answers. A rerun this way gave the same scores.
- **Baseline.** The documented route (AGENTS.md "Premise dossiers and
  attempts", `research-index.md`): `truth index search` for the case's words
  (notes have been indexed since #952); `truth related` and `truth dossier
  --issues-from` for each seed statement (the case's own seeds, otherwise the
  first two statements the search surfaced); and `truth context` for a named
  argument or result. The baseline has no free-text issue search. Its only
  issue lookup is the dossier's list of acceptance-block targets.
- **Candidate.** The single `brief` or `novelty` call of each case, run on
  the same checkout with the same snapshot.
- **Scoring.** Scoring is lexical, as in #962: a reference counts as surfaced
  when its token appears in the text output. *False novelty* means the
  output shows none of the case's primary prior work, or says
  `no-match-found`. *Distinctions* are regular expressions over the output:
  a conditional consequence, an open rival, issue state and successor,
  unknown or stale issue data, and the containment caveat. Run it with
  `python3 scripts/retrieval_benchmark.py --snapshot S.json [--truth BIN]
  [--json OUT]`.

The answer key was fixed before the candidate was run, with one exception:
D4's `absent` pattern was corrected after it matched the candidate's correct
sentence "not evidence that no prior work exists". B5, H1 and H2 were held
out. Their results did not change across the revisions below (2/2 each).

## Results

| Measure (24 cases) | Baseline | #1686 as merged | Revised (this PR) |
| --- | --- | --- | --- |
| Reference recall | 49/68 | 52/68 | 57/68 |
| — issues/PRs | 15/28 | 24/28 | 27/28 |
| — notes | 23/29 | 19/29 | 21/29 |
| — records | 9/9 | 7/9 | 7/9 |
| — rivals/objections | 2/2 | 2/2 | 2/2 |
| Missed known work (non-controls) | 19/67 | 15/67 | 10/67 |
| False novelty (no primary prior work shown) | 0/21 | 1/21 | 1/21 |
| Cases missing some primary reference | 4 | 3 | 2 |
| Boundaries stated (distinctions) | 8/19 | 17/19 | 19/19 |
| Negative-control verdicts correct | no verdict | 2/3 | 2/3 |
| Calls | 105 | 24 | 24 |
| Output, total (median per case) | 2.2 MB (60 KB) | 209 KB (7.8 KB) | 214 KB (7.8 KB) |
| Wall time, total (median per case) | 73 s (3.2 s) | 48 s (2.1 s) | 49 s (2.1 s) |

Wall times are for one warm `.cache/truth-index.sqlite`. Each `brief` or
`novelty` call spends most of its 1.4–2.8 s computing the frontier and
loading the corpus. Each baseline `dossier` call spends the same.

### Historical failures

- **Underreported research (A1, D5).** Both workflows reach
  `ultimate-adequacy-integration-735.md`. Only the candidate quotes its
  judgment that universal coverage "has not been established". It also shows
  #735, #750, #736 and #1445. The baseline output states no assessment
  boundary (the distinction fails) and misses #1445, #746 and #613. When the
  snapshot predates the checkout (D5), only the candidate flags it.
- **False novelty of `D(x,y) ↔ ¬CanBeWithout(x,y)` (B1, D4).** The candidate
  classifies the formula as `already-recorded` from the note paragraph that
  derives it in the note's own notation. It shows #1589, says that
  containment is not a certified entailment, and reports issue history as
  unknown when no snapshot is supplied. The baseline finds the note through
  `index search` but not #1589, and states neither boundary.

Neither workflow presents the dispute as settled. A verified result with an
open premise is reported as a conditional consequence (C1, C3). The rival
that the frontier keeps open stays visible as open (C2). The McTaggart
refutation is counted, and its only premise is the target itself.

### Failures and false positives that remain

- **Prose paraphrase (B2, false novelty).** "Depending for its being is
  equivalent to being unable to be without" does not find the note that
  derives the biconditional in symbols. The tool matches words and the
  note's notation, and no embedding is used (#1643's non-goal). The baseline
  found the note only because its search words differed.
- **Scattered long paragraphs outrank a dedicated note's title in `novelty`
  (B3).** The note "What weak explanatory coverage actually adds" now matches
  4/6 through its heading. It is still listed after 5/6 paragraphs of long
  notes that happen to contain the words. #677, the exact prior PR, is found,
  so the verdict is right.
- **Converse with the same symbols (E2, false positive).** `CanBeWithout(x,y)
  → DependsForBeing(x,y)` is called `already-recorded` because a unit
  contains both identifiers and an arrow. The caveat "containment is not
  equivalence" is printed, but the verdict does not encode direction.
- **Same word, other sense (E3).** "Act is prior to potency in time" is
  called `already-recorded` from `SIMPLY_PRIOR_1` records, which are about
  priority that is not temporal. The sense tags are shown on every hit and
  are the only signal. The pinned statement `197ac723` is not listed.
- **Notes the baseline finds and the candidate does not.** There are three:
  `explanatory-selection-736.md` for A1 (the baseline's `index search` ranks
  it, while the brief's text output does not), the priority note for B2
  (above), and `weak-explanation-conservative-expansion.md` for B3 (above).
  The candidate finds one note the baseline misses, the theorem-citing
  `unique-feedback-explanation-311.md` for C1. Neither workflow finds
  `stopping-points-746.md` for A1, `psr-strength-755.md` for A4, or the
  #1378 notes on C3's open premise. The brief names that premise but does not
  follow it, so a second `brief` call on the premise is needed.
- **Records (B2, E3).** The candidate misses 2 of the 9 pinned records,
  both in the cases above. The baseline's `related`/`dossier` calls surface
  them.

## Revisions made to #1643

Each revision fixes a concrete miss in the table above. Each one has a
deterministic fixture in `truth/src/brief/tests.rs`
(`benchmark_1644_dedicated_notes_successors_and_theorem_names`) alongside the
#1643 tests for the two historical failures.

1. **Dedicated notes first (A3).** In question mode, a note whose title
   covers at least half of the question, and at least two items, ranks before
   long notes that touch the question in more paragraphs. Short plurals now
   match their singular (`points` finds `point`). Before this,
   `stopping-points-746.md` ranked 12th for its own question.
2. **The note's own issue (D1).** An issue number in a matched note's title
   (`… (#1584)`) weighs as much as a number referenced from a strong section.
3. **Successors (D1, D2).** A listed issue or PR that says "Superseded by
   #N", "the distinct successor #N" or "Remaining scope continues in #N" is
   shown with `scope handed to #N [STATE]`. "Successor to #N" names a
   predecessor and is ignored. Successors are workflow history, not a
   statement that anything is settled.
4. **Lean theorem names (C1).** In target mode, a note section that cites
   one of the target's result theorems by its last two components
   (`OriginExerciseBridge.noSelfOriginFromNoSelfProduction`) counts as a note
   naming the target. `unique-feedback-explanation-311.md` and #1526 are now
   found. Like an ID mention, a theorem name is not an entailment or a
   status.
5. **Headings as units.** A note heading is scored as text of its own, so a
   title that states the question is matched even if no body paragraph
   repeats it.

## Decision

**#1643 improves decision-relevant retrieval.** The baseline already avoids
gross false novelty when a worker runs `index search` over notes. What it
lacks is issue and PR history (15/28 against 27/28) and the boundaries a
worker needs before judging maturity: assessments, conditional consequence,
open rivals, issue state and successors, and unknown or stale snapshots (8/19
against 19/19). The candidate supplies these in one call, with a tenth of the
output and a quarter of the calls. Its remaining errors are published above:
B2 and E2 are not fixed, and lexical containment is the stated limit.

**This benchmark does not authorize the hosted/MCP step (#1645).** Every
gain was obtained with the offline CLI, and the per-call latency of about
2 s does not block a research workflow. Step 3 would be justified only by a
workflow need that the CLI cannot meet. Two candidates are an agent session
that cannot run the binary against a checkout, and a session that issues
many queries and needs the frontier and index loaded once rather than per
call. This benchmark measures neither. #1645 stays optional until such a need
is shown.

## Maintenance cost and reuse

The `brief` modules come to about 4,700 lines, including tests. This PR adds
about 330, mostly fixtures. The benchmark is about 270 lines of Python plus
the answer key. It is not a CI gate, because it needs a live GitHub
snapshot. Rerun it when the ranking rules change, and keep the held-out
cases unchanged. #962's `context_benchmark.py` measures a different thing:
recall of the context IDs a PR actually used. Its 0.63 recall at 73 KB
cannot be compared with these numbers.


## Independent offline correctness tier (2026-11-17)

This separate tier supersedes the development measurements for the graph-first
candidate. The original historical 24-case key and lexical results above remain
unchanged. In particular, historical E3 accepted `already-recorded` for a
priority hit that did not certify its temporal reading; the new tier rejects
that semantic inference.

Run without a GitHub export or network access:

```sh
python3 scripts/retrieval_benchmark.py --correctness \
  --baseline /tmp/truth-retrieval-baseline --truth /tmp/truth-retrieval-candidate \
  --json /tmp/retrieval-independent-comparison.json
python3 -m unittest discover -s scripts -p 'test_retrieval_correctness_benchmark.py'
```

The authored oracle, `scripts/testdata/retrieval-correctness-oracle.json`, is
never copied into the indexed fixture. Semantic judgments were fixed before
candidate runs. The fixture combines the frozen research golden inputs, five
propositions, 220 reverse-reference records, 24 cyclic notes with 96 linked
sections, and a local issue/PR cycle. It exceeds the old 200-record, 16-note and
80-section limits. Graph recall scores exact node identities; source coverage
counts source and passage separately. Four edges' endpoints and field/path
provenance are checked independently. Retrieval of a source reference does not
certify source fidelity, verification or philosophical warrant.

Semantic recall and precision use the first five **statement** candidates.
Relevance concerns the same load-bearing subject or inference, not equivalence:
a converse or negation can be relevant prior work without being the recorded
proposition. Novelty correctness separately permits `already-recorded` only
for exact normalized proposition text. Six cases cover identity, converse,
negation, quantifier strength, account/time priority and timeless/endless
existence. These small authored samples do not estimate general semantic
reasoning accuracy or corpus-wide completeness.

Four historical questions use identical copies of `corpus` and `docs/notes`,
excluding the answer-bearing benchmark note/key; other documentation and issue
history are outside this measured workload. B2 asks the dependence paraphrase,
B3 targets the dedicated weak-explanation note, E2 asks an unrecorded converse,
and E3 asks temporal priority. Relevant prior work and novelty judgments are
scored separately.

| Measure | Baseline | Measured candidate |
| --- | --- | --- |
| Semantic recall at five | 6/6 | 6/6 |
| Precision among first five statement candidates | 6/12 | 6/12 |
| Synthetic novelty correctness | 3/6 | 6/6 |
| Historical novelty correctness | 1/4 | 4/4 |
| Historical pinned-reference recall | 2/5 | 5/5 |
| Explicit graph records / note files / sections | unavailable | 222/222; 24/24; 96/96 |
| Source/passage; issue/PR; exact edge provenance | unavailable | 2/2; 2/2; 4/4 |

The direct evidence graph has 372 unique nodes and 877 provenance-bearing edges,
even with `--limit 1`; missing baseline graph capability is unavailable evidence,
not an invented zero recall. Historical B2 improves from 0/2 to 2/2 pinned
references, B3 and E2 remain 1/1, and E3 improves from 0/1 to 1/1. Perfect recall
figures apply only to these specified fixtures and pinned questions.

An initial duplicate-graph serialization problem was repaired before this
measurement. Default human text is compact; requested JSON includes the full
navigation inventory and can remain large on connected historical components:

| Historical question | Baseline JSON bytes / seconds | Candidate JSON bytes / seconds |
| --- | --- | --- |
| B2 dependence paraphrase | 19,306 / 2.91 | 19,531,554 / 5.89 |
| B3 dedicated explanation note | 19,667 / 1.39 | 3,963,451 / 4.95 |
| E2 unrecorded converse | 15,999 / 1.40 | 64,234 / 2.87 |
| E3 temporal priority | 20,027 / 1.46 | 22,431,527 / 7.40 |

On the same fixture and measured artifact, ordinary human text emits 4,224
bytes for B2 (6.97 seconds) and 4,595 bytes for E3 (7.57 seconds). These single
shared-machine timing samples are informational, not controlled latency gates.
The measurements support improved coverage and novelty correctness on the
sample; they show neither better precision nor better performance. Large JSON
navigation inventories and graph-construction latency remain limitations.

The compact observations are committed in
`scripts/testdata/retrieval-correctness-measurement.json`: commands, matched
identities, separate metrics, environment, output sizes/hashes and timings.
Unchanged baseline observations were reused after candidate repairs.

Baseline SHA-256 is
`5231d02d74cb78c87705a2aae9bcc1dd4ef4a92243a513c8a0053e8f77fdde7c`
(16,329,200 bytes), built from clean
`f0eb8145916d8c3af4346f959bdc2d63adceb9a9` before edits.
Measured candidate SHA-256 is
`6dc4a935785430589b0a5313b1150bb1c8733bafeb2bf9910523d1fca82bd323`
(16,559,768 bytes). Its 155-file source-context manifest includes sorted tracked
**and untracked** paths under `truth`, with each file's SHA-256; the digest is
`479e70f091b49276c63b9dbb1d625dfe0001224cbc6b5c6b4e74784366c48208`.
A dirty `git diff` hash alone would omit the new graph and CLI files. Subsequent
Clippy-only refactors preserve semantics; this report identifies the measured
candidate rather than claiming its artifact hash belongs to the final commit.
Five harness checks and Python compilation checks pass. No premise, proof
status or frontier changes.
