# Formal Logos agent contract

Advance meaningful philosophical arguments through verified, reusable steps. Keep complexity in the philosophy, not in repository machinery.

## Read before work

Follow the current owner request, repository-local instructions, then applicable installed conventions (specific before broad). Read the relevant local agent instructions. Resolve installed conventions against their current shared source; do not vendor or pin policy text. If no convention selection is installed, do not invent one.

Use these binding references for the work they govern:

| Work | Read |
| --- | --- |
| Research selection, warrant, challenge, integration, PRs | [Systematic research loop](docs/systematic-corpus-loop.md) |
| Source, proof, identity, validation, review and lane rules | [Agent operations and verification](docs/agent-operations.md) |
| Corpus entities, senses, definitions and closure | [Corpus model](docs/corpus-model.md) |
| Research entry and reuse | [Research skill](.agents/skills/truth-core-research/SKILL.md), [reuse skill](.agents/skills/proposition-reuse/SKILL.md) |
| Tool commands and issue brief | [Truth CLI](truth/README.md) |
| Source attribution and evidence | [Source evidence](docs/source-evidence.md) |
| Configuration comparison | [Configuration elimination loop](docs/configuration-elimination-loop.md) |
| Verification and permitted axioms | [Axiom policy](docs/axiom-policy.md) |

The systematic loop owns research methodology. The operations reference owns detailed repository mechanics. Do not duplicate either in progress notes or worker briefs. The policies below remain binding; neither a skill nor a tool output overrides them.

## Current research focus

Prioritize the existence of God and explicit bridges to divine attributes. Defer historical and specifically Christian/Catholic identification research until selected by the owner. The Catholicism root and existing closure rules remain unchanged; use its God-existence-stage nodes to locate work. See [the case](docs/catholic-case.md).

Name the root-route target before adding vocabulary, frameworks or results. Connect them to the case, or record the exact missing bridge, target and blocker. Inspect disconnected verified work with `truth orphans` when choosing research. A disconnected library is not case progress merely because it is verified.

## Research and warrant

- Follow the canonical [systematic loop](docs/systematic-corpus-loop.md): investigate a live uncertainty, compose existing results, compare the strongest relevant accounts at matching scope, and reconnect the findings to the parent question. Do not presuppose a preferred conclusion.
- Keep the proposition's meaning, witnesses, domain, frame, assumptions and dependencies fixed, or explicitly bridge changes. A dilemma needs coverage only when the inference requires it; exclusivity is a separate obligation. A contradictory bundle excludes the combination, not a preferred member.
- Investigate both direct and conditional warrant. Prima facie judgments, experience, successful inquiry, rational preconditions, arguments, network coherence and comparative explanatory adequacy can contribute cumulative warrant. Do not require an independent proof tree for every primitive or treat shared dependencies as a penalty. A circular implication alone adds no warrant.
- Record reasoned overall provisional judgments, serious objections, shared dependencies and revision conditions. Provisional premises may guide further reasoning only with those qualifications intact. Personal assent does not establish a premise; do not create new `owner_approval` floor markings.
- Distinguish formal consequence, source/semantic fidelity, premise warrant, computed closure and work completion. Strict self-refutation, epistemic self-undermining, lack of reasons for adoption and violation of inquiry preconditions are distinct outcomes. A surviving rival is not thereby true; failed proof search is not a refutation.
- Preserve defensible direct-assumption options when adding derivations. A new verified non-transcription derivation is conditional support-option progress even with additional open inputs. Report meaningful breadth, connections, evidence and exact changes, not aggregate bare/open-premise counts, deltas, ratios, leaf counts or route costs as progress. Use those diagnostics only for an explicit diagnostic question.
- Do not ask the owner to select a metaphysical winner to continue research. Retain defensible senses, rival standards and framework alternatives. Ask only when an actual exclusive action, authorization or scope decision is necessary.
- Use the independent [semantic challenge](docs/systematic-corpus-loop.md#independent-semantic-challenge) for consequential findings and complete the [bounded outcome review and repair](docs/systematic-corpus-loop.md#final-outcome-review-and-repair) before publishing reviewed conclusions. A formal or automated PR review is not this challenge.

## Substantive Objection Standard (owner direction, 2026-11-12)

Apply the same standard to arguments and objections regardless of worldview. Identify the exact target, the failure/support mechanism, positive non-question-begging reasons for it, and its relevance. Distinguish established counterexamples from hypothetical possibilities. A claimed failure to generalize must identify a relevant difference and why it matters. Positive justification need not be isolated from the rest of the graph. Do not invent contrived objections or unsupported alternatives for balance; if none is substantive, say so. An unspecified possibility of error is not evidence of error.

A checked finite model witnesses its stated formal interpretation, not its metaphysical applicability or the falsity of an omitted premise. Record such limits explicitly. Review an objection presented as evidence without the required support as P1. These standards do not relax proof, source, binding or closure requirements.

## Research continuation and stopping (owner direction, 2026-11-10)

A bounded assignment specifies the question and ownership, not a default token, time, depth, batch or PR budget. Explicit owner limits and runtime constraints apply. Continue across checkpoints while useful authorized work remains. Investigate a surviving rival's further commitments and subarguments; when a route stalls, seek another discriminating test, a horizontal bridge or a more consequential node.

Workers report resolved/stalled branches with evidence, exact blockers and reopening conditions; they continue other useful work within scope. The coordinator reassesses, reallocates or integrates rather than stopping at a worker's dead end. Stop only when the requested scope is resolved, all remaining branches have concrete blockers, or the owner stops the work. A runtime interruption requires a resumable handoff, not a completion claim.

## Worker brief and handoff

Use the [worker ownership and integration contract](docs/systematic-corpus-loop.md#worker-ownership-and-integration) and [parallel lanes](docs/systematic-corpus-loop.md#parallel-lanes). Delegate each issue or bounded investigation to a fresh worker; preserve the originating worker's ownership through repairs. With resources available, maintain two distinct proposition investigations and reserved challenge capacity. Do not overlap file or argument ownership; the coordinator owns synthesis, allocation and integration.

Give each worker:

1. Root-route target (or named missing bridge), parent question and why the slice is distinct from concurrent work.
2. Baseline revision, exact prior finding/attempt and assumptions; for formal reuse, statement IDs, senses, definitions and Lean declaration.
3. Live discriminating question and what could change the current judgment.
4. Expected useful change, including premise effects if relevant.
5. Explicit file/argument ownership and reassessment conditions.

For an issue, start with the [issue brief](truth/README.md#starting-from-a-github-issue) on current main; inspect linked PRs and reviewed work before reopening a delivered finding. Apply the [research issue](docs/systematic-corpus-loop.md#github-research-issue-contract) and [PR completion](docs/systematic-corpus-loop.md#pr-completion-contract) contracts. Do not prescribe a philosophical outcome or proof quota. Close only a delivered issue scope.

Persist substantive evidence, failed attempts, rejected readings with reasons, open gaps, strongest surviving rivals and next tests in existing records/notes. Maintain one current coordinator handoff with exact head, verified/unverified scope, findings and next step. Workers return a compact delta with links; do not create competing trackers. Progress updates report changes, not repeated plans or routine check histories.

## Premise dossiers and attempts

Follow the [reuse skill](.agents/skills/proposition-reuse/SKILL.md) and [dossier rules](docs/premise-dossiers.md). Before new investigation or vocabulary, use `truth related <STMT-ID>` (or `truth index search` without a seed). For an existing argument/result, start with `truth context <ID>`. Inspect `truth dossier <STMT-ID>` for each touched premise. Use `truth brief` and `truth novelty` before judging maturity or claiming novelty; use an offline issue/PR snapshot where available. Search results are advisory, never proof or evidence that missing hits mean no prior work exists.

Before proposing or reusing an argument, run `truth semantics <ID>` and its premise/conclusion preflight; resolve unbridged sense mixing. Record substantive successes, failed derivations, rejected readings and searches in `corpus/attempts/` with exact target IDs, findings, blocker and evidence. Attempts and generated dossiers do not change proof or closure status.

## Logic first; attribution deferred

For assigned logic tasks, including Carneades.org, use explicit analyst formulations and available summaries, transcripts and source leads. Source acquisition, passage pinning, PDF/transcript authentication and exegesis are not prerequisites for logical exploration. Do not create attribution records merely to permit formalization. Mark attribution deferred and preserve navigation leads without asserting unverified historical claims. Select source research when it answers a live research question; if attribution blocks a logic PR, defer the attribution, not the checked logic.

When publishing an attributed claim, read the actual cited passage and context; use precise source/edition/locator evidence and the [source workflow](docs/agent-operations.md#1-research-from-verified-source-evidence-attributed-work-only). Keep source integrity distinct from interpretive fidelity. A bibliographic witness requires reading the edition and is not byte-verified. Never invent a source claim. CI and routine local gates validate source records and bindings **offline**; no recurring source-host refetch or full-source verification. Use `source_evidence.py materialize` only for selected pinned source research. A green offline check does not certify bytes or fidelity.

## Formalization and corpus invariants

The full [permanent invariants](docs/agent-operations.md#permanent-invariants) and [atomic proof workflow](docs/agent-operations.md#one-atomic-work-item) apply.

- Statements have independent UUID identity; claims record source readings. Reuse only genuinely matching meanings. Never merge by name, translation or apparent similarity; register relationships explicitly. New IDs are UUIDs, legacy aliases are immutable, human labels carry sense tags.
- Use the weakest faithful statement and explicit inference/argument records. Keep stronger and weaker versions distinct and certify any `strengthens` relation; use the weakest sufficient version or justify retaining a stronger one. Defensible readings become sibling statements/claims, not ambiguous prose.
- Define load-bearing terms recursively; identify primitives, their meaning and open semantic obligations. Use numbered, append-only sense labels and distinct Lean declarations; one sense per term per argument, explicit `sense_bridges` for crossings. Preserve the shrinking legacy allowlist. Names/types alone do not establish meaning.
- Reuse shared frames and vocabulary (e.g. `CausalityFrame`) rather than recreating relation parameters. Tag parameter senses explicitly; untagged is unknown. Frame fields impose no hidden relation between them. Adapt older modules incrementally. For metaphysical relations, state ordinary meaning, examples/counterexamples or their absence, distinguishing and structural properties, and open bridges to reality; test serious rivals.
- Compose/import existing checked results. Prefer typed, falsifiable encodings; an opaque proposition or a premise already asserting the conclusion is a transcription, not a new derived argument. Label it as such; preserve the existing fixpoint closure rules for already-closed premises. Do not hide disputed commitments in definitions or axioms.
- Freeze the Challenge before solving; missing premises require a separately registered explicit candidate/configuration, not a weakened challenge or strengthened source reading. Every actual premise, including nonvacuity side conditions, must bind to the argument. Global semantic cycles are allowed, circular proof is not.
- Use explicit assumptions for conditional exploration; do not demand a source or independent defense merely to study consequence. Check models and omission counterexamples where useful; do not claim satisfiability, minimality or non-entailment without evidence. Compare actual interpretations and register selected comparisons in existing records/specs.
- Mathlib is approved for mathematical content; reuse it instead of bespoke equivalents. Non-Mathlib results remain zero-axiom; Mathlib results may permit only the documented three axioms. No other Lean dependency or new source kind without owner decision. Keep runtime and CI self-contained; no premature identity infrastructure.

Use `argument_batch.py` for coherent batches, exploration maps when useful, and `truth discover`, `prove-sweep` or `countermodel` as search helpers. Lean's kernel and the required verification boundaries, not tactics, solvers or LLM agreement, certify consequence. Register inference, argument, result and Comparator records as applicable; generate imports and records rather than hand-maintaining generated lists. Follow the [configuration loop](docs/configuration-elimination-loop.md) only when selected; exhaustive sense comparisons and model campaigns are not universal prerequisites.

## Local Lean preview service

Use the coordinator-supplied [local preview](docs/agent-service.md) with its workspace/session and lease; workers retain isolated canonical clones. The coordinator owns startup, refresh and shutdown. If unavailable, use the existing CLI; no external Lean service dependency. Interactive diagnostics are not final verification.

Follow [worker startup](docs/worker-startup.md): reuse warm clones or seed under the heavy-job lock; the coordinator preflights `worker_env.py --check` once per setup. Workers use its wrapper, preserving the pinned toolchain and explicit machine-local paths. A seeded build is readiness, not verification.

## Verification, review and integration

Follow the [detailed verification and review rules](docs/agent-operations.md#7-verify-the-three-boundaries). The Rust `truth` CLI is the sole corpus-command implementation; build once per clone with `cargo build --locked --release -p truth` and rebuild after changed Rust/Cargo inputs. Final applicable verification includes Lean build, corpus and bundle checks, binding, Comparator, independent NanoDa and CI. Reuse successful evidence for unchanged inputs; rerun affected checks on changes, failures or unresolved findings. Never claim mechanical verification without Comparator.

Before the first push of a formal/attribution batch, complete the claim/type and attribution self-sweep, the [recurring semantic defects checklist](docs/systematic-corpus-loop.md#recurring-semantic-defects-pre-push-checklist), and the applicable generated-record/import checks. Review exact quantifier scope, modality, witnesses, all premises, load-bearing definitions and disambiguations, and whether prose exceeds Lean or source. Apply the [review severity and reporting rules](docs/agent-operations.md#review-guidelines) in one pass; fix all P1s, route covered P2s appropriately. Open premises are allowed, not review defects.

For each PR, state intended premise effects and link/paste the actual computed `truth frontier-diff --base <merge-base>` (CI job summary); non-proof work has no intended premise change. Report exact relevant identities/status changes, not aggregate counts or reconstructed deltas. A new connection is not a discharge. Follow the existing PR template and review/merge authority; do not mark pending evidence passed. Recheck current main, dependent/overlapping work and applicable checks before integration.

Respect [A/B/C lane ownership](docs/agent-operations.md#lanes-and-shared-files) (lane C owns tooling and AGENTS.md), keep cross-lane edits minimal and list them in the PR. Merge current main before each push and regenerate shared imports/doc indexes; never hand-edit generated files. Existing proof, source, root-closure and merge gates are unchanged.

<!-- BEGIN:turborepo-agent-rules -->

# This is NOT the Turborepo you know

Turborepo configuration, task behavior, and CLI commands can vary between installed versions and may differ from your training data. Resolve the `turbo` package from this file's directory or relevant workspace; in monorepos, it may not be visible from the repository root. For example, run `node -p "require.resolve('turbo/package.json')"` from a workspace that depends on `turbo`.

Read `docs/README.md` inside that installed package first, then read the relevant pages from its `docs/` directory before changing Turborepo configuration or commands. Heed deprecation notices. These bundled docs match the installed package version and are available without network access.

This block is written and re-added by `turbo` before repository-scoped commands when an AI agent is detected. In the Turborepo source repository, its template is defined in `crates/turborepo-cli/src/cli/agent_guidance.rs`. Removing the managed block while updates are enabled means a later qualifying invocation will add it again. Set `"agentGuidance": false` in the root `turbo.json` or `turbo.jsonc` to opt out; this does not remove an existing block. Keep the block committed with your work to avoid an uncommitted change on the next agent invocation.
<!-- END:turborepo-agent-rules -->
