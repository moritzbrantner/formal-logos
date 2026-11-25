# Premise dossiers and research attempts

`target/release/truth dossier STMT-ACT-SIMPLY-PRIOR-TO-POTENCY` collects the
statement, Lean declaration, source readings/support, linked definitions and
senses, alternatives/objections, arguments and results, transcriptions, attempts,
and current root-route contribution. `--json` emits the same projection as JSON;
`--root STMT-…` selects a different root. `--all --json` emits the complete index
in one call for static explorer generation. Unknown statements or roots fail.

A single-statement dossier projects only that statement and skips corpus
validation (run `truth check`); `--all` still validates. Text output shows at
most `--limit` entries per section (default 8; the newest attempts) and shortens
long prose, saying how many entries `--json` adds. `--limit 0` gives the full
text. `--json` is always complete (#958).

The explorer links `/dossiers/<STMT-ID>/` from every statement page. CLI and
explorer consume the same Python projection and authoritative frontier rules.
Closure classification and *established* are separate: a conditional proof can
be classified as proved while depending on open premises. Dossiers do not
introduce another closure rule.

A route contribution is membership in the route's current
`open_premise_statement_ids`: the statement is either one counted open leaf or
it is not. The full route cost is shown alongside it. This is **not** a
counterfactual claim about how much the route would shrink if the premise were
proved; alternative proofs and shared leaves can change that calculation.

## Attempt records

The owner approved `corpus/attempts/*.json` in #413. These records describe work,
not propositions, source readings or inference steps. They do not participate in
the logical graph or establish/refute their targets. Backfilled records refer to
the original merged evidence and preserve its limitations.

```json
{
  "id": "ATTEMPT-EXAMPLE",
  "statement_ids": ["STMT-ACT-SIMPLY-PRIOR-TO-POTENCY"],
  "date": "2026-10-26",
  "kind": "source-search",
  "outcome": "blocked",
  "summary": "The available interpretation does not supply the required premise.",
  "evidence": [],
  "blocker": "Obtain and inspect the required pinned witness."
}
```

- `statement_ids` is nonempty and names existing independent statements; duplicates
  are rejected. One attempt may concern several precisely named targets.
- `date` is a calendar date in `YYYY-MM-DD` form.
- `kind` is `derivation`, `refutation`, `reading`, `countermodel`, or `source-search`.
- `outcome` is `succeeded`, `failed`, `blocked`, `superseded`, or `rejected`. It
  describes the attempt, never the truth status of its targets. `rejected` records
  a lead examined and dropped before a proof attempt (for example because the
  derivation would only relocate the premise or be a transcription); the summary
  gives each target's reason. `thickness --queue` marks its targets examined. A successful omission model, for
  example, can leave every philosophical premise open.
- `summary` records the finding, rejected interpretation or failed inference and
  its limits. `blocker` is required for blocked attempts, optional otherwise.
- `evidence` lists existing result or claim IDs, or `PR-<positive number>` for a
  truth-core pull request. It may be empty when no evidence reference exists yet;
  the dossier makes that absence visible. Local result/claim references resolve
  during `truth check`. PR references are syntax-checked and link to this
  repository; checking their remote existence is outside the offline validator.
  Neither a PR reference nor an attempt outcome is proof verification evidence.
  When the delivery number is known, add it to the attempt that records the
  finding. Keep earlier deliveries when a later PR extends the same attempt.
  Link the attempt's JSON file from the note section reporting its findings and
  use that section's anchor in the current assessment when one is recorded.

IDs are stable. Correct an inaccurate attempt record in place; preserve earlier
failed approaches as separate attempts when the approach genuinely differs.
A later successful proof does not rewrite the earlier failure into success.

## Explicit links, not semantic guesses

Countermodel attempts are linked by their target `statement_ids` and `kind`.
Their evidence links to the relevant existing result or PR. A result description
containing the word "countermodel" is not itself a structured model registration.
The dossier also lists existing results explicitly classified as instantiations
by the frontier report; these are not automatically instances of a future generic
schema. The mode-2 finite-model registry (#414) supplies explicit `model_evaluations`
with model ID, vocabulary, closed arguments and theorem certificate. CLI and
explorer show the same links without changing closure. See
[registered finite interpretations](finite-models.md) for the certificate gate,
co-failure candidates and the limits of finite interpretation tests. A separate
mode-5 schema registry (#412) now records explicit `instance_of_schema` relations
with checked theorem bindings; see [proved argument schemas](schemas.md). The
dossier does not yet project those registrations. No links are guessed from
similar words, theorem names or embeddings.

Configuration cases are linked by exact seed/application statement IDs through
`configuration_cases`. These links are registrations only; use the live
[`configurations` command](configurations.md) to certify their cores and witnesses.
No configuration input changes dossier closure or route contribution.

## Current assessment and publication disposition

An append-only `summary` is historical evidence, not a reliable current-state
excerpt. An attempt may carry one `current_assessment` object. It is the
explicitly selected assessment **of its named scope**, not a replacement for all
judgments mentioning the same statements. Multiple scoped assessments remain
side by side, including disagreements. The note retains the full argument and
historical findings; do not delete them when replacing this compact object.

Required fields are `date` (ISO calendar date), `statement_ids` (a nonempty
subset of this attempt's targets), `scope`, `assessment`, `next_test`, `note`
(the existing substantive note and anchor), `reviewed_revision` (full commit
hash of the assessed delivery), `review`, `publication`, `evidence`, and
`supersedes` (exact earlier wording/scope displaced, or explicitly none).
`review` is `unreviewed`, `accepted_qualified`, or `changes_requested`;
`publication` is `unpublished`, `published`, or `merged`. Evidence identifies
the review/publication record, its exact scope and qualifications. These are
recorded dispositions, never inferred from PR references, dates, CI or prose.
An unreviewed entry records the proposed delivery hash; that field alone does
not assert completed review. Keep an unresolved philosophical `outcome` and
`blocker` even when its bounded synthesis has been reviewed and merged.

`truth brief TARGET` and single-target `truth dossier TARGET` print these
assessments, exact revision, disposition and next test before historical
retrieval. Their JSON exposes `current_assessments`; batch
`brief --assessments-for ID,...` exposes the same entries. Question briefs
include them for the statements named in their matched evidence. Legacy attempts
remain unmarked; absence is unknown currentness, not unfinished integration.
Historical note sections use only their own heading dates. Note-wide dates and
later line position never certify currentness or supersession.

For example, `truth brief a7bbd2fd-242c-5097-a9a3-581d25835890` first reports
the qualified group #1730 synthesis at reviewed head
`f9bdbb32f6239430213eb42ec2f42768e5154c0d`, merged in PR #1742, and its
same-bearer/complete-exercise next test. The November 13 intrinsic attempt
remains `blocked` on philosophical adequacy. Its old pending-review handoff and
candidate-certification suggestion remain historical evidence; neither is the
current integration task. No premise is established by this disposition.

## Currentness view

`truth currentness [--frontier-root STATEMENT] [--limit N]` (#1751) lists each
open premise reaching the selected root (default `STMT-CATHOLICISM-TRUE`) with
its currentness state: `current` (named in some attempt's
`current_assessment.statement_ids`; the newest such entry's date, review and
publication disposition are shown), `legacy_only` (attempts exist, none with a
covering current assessment) or `none` (no attempt). It also counts pending
consumers from declared `revisions`. Items are grouped by the earliest case
stage they reach and ordered by route position (length of the recorded path to
the root), never by leaf count or a strength score; `--json` has stable keys.

Its flags are advisory heuristics that point at records to re-read, not
verdicts: support is transcription-only; a consuming argument is on the
sense-index allowlist; recorded alternatives or objections lack a covering
current assessment; the latest attempt predates the 2026-11-12 substantive
objection standard; a legacy blocker matches one of the old-policy phrasings
(rival exhaustion, route cost, owner approval) listed in
`truth::currentness::OLD_POLICY_PATTERNS` and echoed in the JSON.

This is a discovery view. It writes nothing and establishes, defeats or closes
nothing. Absence of a current assessment is unknown currentness, not failure or
unfinished work, and a flag is not evidence against a premise or an attempt.

## Declared revisions and downstream reassessment

When changing a meaning, premise warrant or influential judgment, declare the
change in the owning attempt's `revisions` array. Ordinary editorial edits and
publication bookkeeping do not require a declaration. Each declaration has a
stable `revision` identifier, `kind` (`meaning`, `premise_warrant`, `judgment`),
`statement_ids` within the current assessment's scope, `previous` (the exact
prior evidence locator/revision), and a substantive `reason`. Preserve the
prior assessment in the existing note before updating its current object.
A new revision gets its own acknowledgements; an old acknowledgement never
resolves a new change.

```json
{
  "revision": "same-bearer-warrant-v2",
  "kind": "premise_warrant",
  "statement_ids": ["<existing statement UUID>"],
  "previous": "docs/notes/existing-case.md#earlier-assessment",
  "reason": "New same-bearer evidence changes the application warrant.",
  "reassessments": [
    {
      "consumer": "arguments:<existing argument UUID>",
      "disposition": "retained",
      "reason": "The conditional argument retains its original interpretation; its application does not rely on the revised reading."
    },
    {
      "group": "path:docs/notes/existing-case.md",
      "disposition": "revised",
      "reason": "The note's sections now cite the revised assessment (docs/notes/existing-case.md#revised-assessment)."
    }
  ]
}
```

`brief` and single-target `dossier` expose `revision_impacts` for both the
changed targets and affected downstream endpoints. Producers of a reached
statement are alternative support, not consumers of the changed premise; they
still supply import-discovery sources. The declaring attempt,
target-registration fields and revision/review bookkeeping do not create
self-generated reassessment work. Each consumer records its `tier`, its reached
predecessor (`via`), the registering `field` and, for import discovery, its
`import_source` result. Consumers fall into four tiers, strongest first (#1757):

- **`premise_use`**: registered premise, commitment and inference-input fields,
  the result that verifies a reached argument, and argument/result conclusion
  propagation, followed to a fixed point. This is the declared formal channel.
- **`import`**: consumers reached once source-level Lean import discovery
  enters the chain (the existing context import parser), including registered
  premise use and conclusions downstream of an import. Imports expose potential
  uses, including uses omitted from a declared premise list; they are not
  proof-term use.
- **`reference`**: records whose structured fields cite the changed target or a
  `premise_use`/`import` consumer by id (one hop).
- **`prose`**: note sections and record prose that mention them (one hop).
  Other attempts' substantive summaries, evidence and selected judgment prose
  are reference or prose consumers.

Records reached only through a chain of two or more reference/prose mentions,
and the conclusions or imports beyond such a chain, are counted per record kind
in `transitive_mentions` but not listed: a mention of a mention is not a use of
the change. A previously acknowledged consumer from such a chain stays listed
as `transitive_mention`. Imports and mentions identify **potential uses**, not
proof-term use, semantic equivalence, a defeat, or an actual change in truth.
Nonregistered uses and implicit semantic dependencies remain outside this
analysis.

Every exposed consumer defaults to `pending`. Record `pending`, `retained`,
`revised`, or `not_applicable`, with a substantive reason, separately for each
revision, addressed in one of two ways:

- `"consumer": "<kind>:<id>"` for one consumer. This is the only way to resolve
  a `premise_use` consumer. An inference shares the disposition on which all of
  its reached containing arguments agree, and a result shares its argument's
  disposition, unless they have their own (`disposition_by` names the source).
- `"group": "tier:import"`, `"tier:reference"` or `"tier:prose"`, or
  `"group": "path:<repository path>"` (for example one note file), for every
  consumer of the groupable tiers in that tier or file. A path group takes
  precedence over a tier group; an individual disposition over both. A group
  never covers a `premise_use` consumer, and a group that covers nothing is
  rejected.

A consumer individually reassessed as `retained` or `not_applicable` in the
`premise_use` or `import` tier is reached but not expanded. Consumers downstream
**only** through such consumers stay listed with disposition `screened` and
`screened_by`; they need no disposition of their own for that revision. A
consumer still reachable another way stays live and is reported by its live
route, so a chain that now reaches it only through import discovery moves it
into the `import` tier. A `revised` consumer screens nothing: its conclusion
and its own consumers keep needing dispositions. Group dispositions never
screen. The text view summarizes each tier as consumers/pending/screened and
lists `premise_use` consumers and individual dispositions; `--json` lists every
consumer.

For the trial `judgment` revision on universal perfection transfer `b26c10a0`
(measured on main at 65b79aed5 and then withdrawn), the former flat
propagation listed 14,118 pending consumers. Tiered, it lists 4,478: 1,124
`premise_use`, 1,785 `import`, 743 `reference` and 826 `prose`, with 9,640
transitive mentions counted but not listed. Retaining the 37 arguments that
register `b26c10a0` as a premise, plus one group per groupable tier, leaves no
consumer pending; the remaining formal consumers stay live through import
discovery from the producers of `b26c10a0` and are reported in the `import`
tier.

Retain consequential revised findings in that consumer's existing record/note
and cite them in the reason. This is a review work item, not automatic
acceptance; disposition does not establish a claim. Reassessment records do not
change theorem status, proof validity, closure, premise cost or source/binding
rules. An unrelated proof remains unaffected. Newly discovered consumers remain
pending without editing another registry.

`truth check` validates declarations and rejects duplicate or unaffected
consumer or group acknowledgements against the current graph, and rejects a
group addressed to `premise_use` or an entry naming both a consumer and a group. Pending reassessment stays
visible without failing proof validation. Declarations are deliberate: this
mechanism does not attempt to infer a philosophical reversal from every prose
diff, and it cannot detect an undeclared reversal. Inspect `--json` for the full
consumer list and its reference/import boundary before recording dispositions.
