# AGENTS.md shortening map (#2183)

This note maps every section and rule of `AGENTS.md` as of `aabe61d38` (772 lines, 11,713 words) to its location after the shortening of #2183. Each rule either stays in `AGENTS.md`, condensed, or moves to [agent operations](../agent-operations.md) (which binds like `AGENTS.md`) or the systematic loop (followed as the canonical method); history and detail that already existed elsewhere stay in the decision records and the corpus model that `AGENTS.md` links. The earlier attempt, #2001, was used for ideas only. An independent completeness review of `e0b7e7721` found condensed wording that had narrowed or weakened some rules and one unsourced synthesis sentence; those were repaired, and the wording below is meant to drop or weaken no rule.

Short forms used below: **A** = `AGENTS.md`, **OPS** = [`docs/agent-operations.md`](../agent-operations.md) (the one new document), **LOOP** = [`docs/systematic-corpus-loop.md`](../systematic-corpus-loop.md), **CM** = [`docs/corpus-model.md`](../corpus-model.md).

Headings that other files link to by anchor are unchanged: `research-continuation-and-stopping-owner-direction-2026-11-10`, `worker-brief-and-handoff`, `premise-dossiers-and-attempts`, `substantive-objection-standard-owner-direction-2026-11-12`, `local-lean-preview-service` and `conditional-framework-exploration-owner-direction-2026-10-31`. Headings that code and records cite by name (`Lanes and shared files`, `Connect every library to the case`, `Proof-seeking stance`, `Review guidelines`, `Worker brief and handoff`, `Premise dossiers and attempts`) are unchanged, and the permanent invariants keep their numbers 1–19. "Encode first" is now the second half of the section `Lean first and encode first`.

## Section-by-section mapping

| Old section (old line) | Rules | New location |
| --- | --- | --- |
| `# Codex worker contract` (1) | Purpose; complexity in the philosophy | A, title and first paragraph (heading kept). A now opens with a table of the documents it cites: agent operations binds like A (its text moved from A), the loop is followed as the canonical method, the configuration loop when selected, the Catholic case is read first; the rest are references, as before. |
| Current research focus, 2026-11-17 (5) | God-existence priority; defer historical and Catholic identification; root unchanged | A, Current research focus, paragraph 1 |
| | End-to-end routes, strongest warrant, provisional assessment, matching-scope comparison, primitives kept, horizontal moves, no double-counting, visible dependencies, reviewed checkpoints, current-case view without leaf ranking | A, Current research focus, paragraph 2 |
| | Encode formal definitions, mathematical claims, countermodels and worked proof applications in compiled Lean; reuse declarations; link the theorem and register results; keep observations, attribution, judgments and applications traceable (b35a72189) | A, Lean first and encode first, "Lean first" paragraph |
| Source checks stay offline, 2026-11-11 (31) | No refetch in CI or routine gates; offline validation; local fixtures; materialize only for selected research; missing cache is no evidence; green check certifies no bytes | A, same heading (near verbatim) |
| Research policy and provisional judgments, 2026-11-10 (42) | Loop is canonical; overall provisional judgments and their limits; keep five assessments distinct; no assent-based warrant or new `owner_approval`; legacy statuses; semantic challenge; complete draft and bounded repair; scoped assignments; selected methods; supersession clause | A, same heading. Detail: LOOP, Provisional judgments and premise warrant; Independent semantic challenge; Final outcome review and repair |
| Argument breadth and cumulative warrant, 2026-11-12 (71) | Breadth is progress; direct and conditional options; no independent-argument demand; kinds of warrant; candidate primitives; no warrant from mutual implication; shared dependencies no penalty | A, same heading, bullets 1–3. Detail: LOOP, Cumulative warrant and support options |
| | Four kinds of comparative evidence; absence of objection is not proof; no manufactured objections | A, same heading, bullet 4 |
| | Progress reports lead with substance; diagnostics only for their questions; no aggregate counts (2026-11-24); inspectable assumptions; no schema or gate change | A, same heading, bullet 5 and closing line |
| Fresh subagents for issue work, 2026-11-08 (111) | Fresh subagent per issue or slice; ownership; contract; worker keeps slice through repairs; phase transition needs no new agent; parallel-lane policy; work continues during review/CI; compact delta to one handoff | A, same heading. Detail: LOOP, Worker ownership and integration; Parallel lanes |
| Research continuation and stopping, 2026-11-10 (127) | No default budget; continue while useful; owner limits apply | A, same heading, opening paragraph |
| | Walk the argument; report conditions; persist before reporting; master owns continuation; PRs are checkpoints; master's stopping conditions; resumable handoff | A, same heading, six bullets |
| Worker brief and handoff (169) | Five-part brief (target, starting result, judgment-changing question, expected value, ownership) | A, same heading, numbered list |
| | Context for a substantial frontier investigation; no complete tree required; lives in the one handoff | A, same heading, paragraph after the list |
| | Research issue contract; issue brief on current `main`; compare with reviewed records and PRs; carry through existing PR; record and close delivered scope; delivery and acceptance evidence; PR completion contract; templates and CLI/API; partial delivery | A, same heading, "Issues follow…" paragraph. Detail: LOOP, GitHub research issue contract; PR completion contract |
| | PR links the computed `frontier-diff`; connection is not discharge; non-transcription argument is conditional support-option progress; new obligations recorded; "none" for non-proof work | A, same heading (support-option rule) and Formalization, verification and review gates, "Premise reporting"; full text OPS, step 8, "Premise reporting" |
| | `worker_env.py --check` once; command mode; machine paths out of briefs; warm clones; `--seed-build-from`; Lake rebuilds changed modules; seeded build is readiness | A, same heading (one sentence); full text OPS, Worker environment |
| | Persist source findings, rejected interpretations and gaps; witness locators; temporary files not the only copy; no claims to log activity | A, same heading, last paragraph |
| Concise reporting and persistence (208) | Items 1–6 (report changes; timings; focused PRs; one handoff; preserve substance; trust completed work, 2026-10-28) | A, same heading, items 1–6 |
| Local Lean preview service (244) | Coordinator owns the service; isolated clones; lease; revision binding; pinned toolchain; CLI fallback; no new service by default; local only; diagnostics are not final checks | A, same heading |
| Premise dossiers and attempts (259) | `related`, `index search`, `context`, `brief`, `novelty`, `semantics` preflight, `dossier` and what each certifies | A, same heading, first paragraph (summary); full text OPS, Retrieval before research, whose attempts paragraph is replaced by a pointer back to A |
| | Update `corpus/attempts/`; reuse attempts; no claims to log activity; required fields; attempts change no closure; `workers` field (#2023, 2026-11-26) | A, same heading, second paragraph |
| Research hypotheses are not forced owner decisions, 2026-11-09 (308) | Classify alternatives; keep alternatives; ask only for an exclusive action; "investigate all options" is a decision; #1297 example | A, same heading |
| Substantive Objection Standard, 2026-11-12 (315) | Five requirements; independent justification; parity; non-generalization; no contrived balance; burden of proof; say so plainly; applies to every worldview | A, same heading, main paragraph |
| | Repository application: rival tables and countermodels; non-generalization claims; boundaries stay; review P1 | A, same heading, four bullets; the P1 also appears in Review guidelines, item 4 |
| Systematic sense and rival comparison (370) | Full procedure | OPS, Systematic sense and rival comparison (verbatim); A, Argument-first investigation and configuration comparison (summary) |
| Logic first; attribution deferred, 2026-11-05 (413) | All six bullets and the override paragraph | A, same heading (condensed; the override clause is kept) |
| Encode first, 2026-11-03 (452) | Encodings must fail; interpretation forks; strength forks (#1017); definitions not labels; sense labels (2026-11-07); shared frames (2026-11-19); prose evidence boundary | A, Lean first and encode first, "Encode first" bullets. Detail: CM, Strength order, Sense-indexed terms, Definition dependencies and formal meaning; [shared-frames decision](../decisions/2026-11-19-01-parameter-sense-tags-and-shared-frames.md) |
| Exploration and batch certification, 2026-11-07 (464) | Exploration maps; batch certification; no quota; nonvacuity witnesses; `thickness` as diagnostic; attempts for rejected leads; PRs on `main`; conflicts returned | A, same heading |
| Connect every library to the case, 2026-11-07 (470) | "What went wrong" history | A, same heading (one sentence); full history in the [decision record](../decisions/2026-11-07-02-connect-libraries-to-the-case.md) |
| | Rule and items 1–4, including the connectivity gate (#2097) and orphans gate (#2109) | A, same heading, items 1–4 (item 4 keeps its number; CM cites it) |
| | Placement is plumbing, not warrant (#2169): four standings and provenance keys; counts never progress | A, same heading, "Placement is plumbing" (complete) |
| Proof-seeking stance (497) | All bullets, including `truth discover` | A, same heading (one paragraph); Duper/Zipperposition detail in [discover](../discover.md) |
| Conditional framework exploration, 2026-10-31 (506) | Purpose; five bullets; boundaries | A, same heading |
| Semantic grounding of metaphysical relations (518) | Six requirements; conditional-consequence boundary; no causal reading by name | A, same heading. Detail: LOOP, Semantic grounding of metaphysical relations |
| Permanent invariants (533) | Invariants 1–19 | A, same heading, condensed under the same numbers; the full wording, which governs where the summary is shorter, is in OPS, Permanent invariants: full wording |
| | Pointer to the corpus model, source evidence and the Catholic case | A, same heading, closing paragraph |
| Configuration elimination and composition (557) | Configuration loop; labels relative; unresolved is not impossible; `truth countermodel`; `truth prove-sweep` | A, Argument-first investigation and configuration comparison, paragraph 2 |
| Argument-first investigation (563) | Whole argument in view; eligible targets; reconnect findings; coverage and exclusivity; contradictory bundles; constraints over counts; authorities preserved | A, Argument-first investigation and configuration comparison, paragraph 1 |
| Outer systematic loop (569) | Selecting work from the owner-scoped investigation; default choice on a #143 route; dependencies; no monopoly | A, Selecting work and source ingestion |
| | Source ingestion steps 1–4 (`truth next`, whole range, 5–10 claims, successor seeding, continuation conditions) | Merged into LOOP, 2. Candidate (steps 1–5) and Campaign handoff; A links it |
| Lanes and shared files (582) | Lanes A, B and C; cross-lane edits; merge before push | A, same heading (kept because tooling and tests cite it) |
| | Generators, conflict handling, pre-#416 rows | A, same heading (summary); full text OPS, Generated shared files |
| One atomic work item (598), steps 1–6 | Source evidence; reuse; formalizing a reading; fidelity critique; Challenge/Solution/module/aggregator/result/Comparator; missing premises | OPS, One atomic work item (verbatim); A, Formalization, verification and review gates (summary) |
| Step 7, Verify the three boundaries (665) | `truth` CLI; command list; `bundle_audit.py`; `bind-check` semantics; offline source checks; Comparator; NanoDa | OPS, step 7 (verbatim); A, Formalization, verification and review gates, "Verification coverage" |
| Step 8, Self-sweep before requesting review (704) | Review-guideline self-review; semantic defects checklist; automated review is not the challenge; draft PR rule; `scripts/preflight.sh` before pushing (#2038); attribution self-check before the first push (#989); definition links; claim vs type; computed premise reporting; route costs; establishment rules | OPS, step 8 (verbatim, plus the duplicate premise-reporting rule from Worker brief and handoff folded in); A, Formalization, verification and review gates, "Before pushing", "Before requesting `@codex review`", "Before the first push" and "Premise reporting"; the claim-vs-type gaps also in A, Review guidelines, item 4 |
| Review guidelines (724) | Items 1–5; P1 and P2 rules; `truth check` mechanical part | A, same heading (kept in A because `@codex review` reads it; condensed wording, the same P1 and P2 lists) |
| Naming (746) | Namespaces; UUID ids; labels; legacy aliases; label-cleanup list only shrinks; migration | OPS, Naming (verbatim); A, Naming (summary) |
| Turborepo block (762) | Generated guidance | A, end of file, byte-identical |

## Lean-first direction (#2183)

The two owner statements of 2026-11-25 quoted in #2183 are in A, Lean first and encode first, "Lean first". The section also covers:

- **Encode first.** The 2026-11-03 rules stay under the same heading. Encode first asked for prose on "provisional judgments … and what cannot yet be typed", while Lean first asks to encode "warrant criteria … defeaters". The two are reconciled explicitly: criteria, evidence and defeaters are encoded where practical, and the overall provisional judgment stays a prose assessment that cites them. It is never asserted as a Lean proposition. This matches Encode first's existing sentence "a provisional assessment is not an opaque proposition to assert in Lean".
- **Logic first** keeps its own section and scope (the Carneades.org campaign and other assigned logic tasks); no sentence merges it with Lean first or Encode first. [OPS, One atomic work item](../agent-operations.md#one-atomic-work-item) repeats, at the step where it applies, the existing Logic-first sentence that new formalizations need no new source, passage or claim records and are labelled analyst formulations with attribution deferred. Source-derived claims still follow invariants 1–3 and the fidelity critique of step 4.
- **The loop and assessment workflow,** as the owner's clarification asks. LOOP step 2 ("Investigate flexibly") and LOOP, Provisional judgments and premise warrant, each now carry a Lean-first sentence.

## Wording added for clarity (no new obligation)

- A, opening table: the standing of each cited document, as the old text gave it ("Follow the systematic research loop", "follow the configuration elimination loop", "read docs/catholic-case.md first", "See …" for the references).
- A, Review guidelines, item 4: the existing Substantive Objection Standard P1 is listed beside the other P1s, and the claim-vs-type gaps of old step 8 are named under the existing "claims more than its source or theorem supports" P1, so `@codex review` sees them. Old step 8 already called them "most review P1s".
- OPS: the analyst-formulation sentence before step 1 (from Logic first), the batch-generator pointer after step 5 (from Exploration and batch certification) and "(including the connectivity and placement gates)" in step 8 (true of `scripts/preflight.sh`).
- Pointers outside the moved text now name OPS: `.github/pull_request_template.md`, `docs/proof-exploration.md` (step 8) and the `scripts/convert_to_module.py check` hint (step 5).
- A, Permanent invariants: the condensed list states that the full wording in OPS governs.
- `scripts/agent_service.py` docstring: a stale pointer to a nonexistent AGENTS.md section, "Local server experiment for the next workloop", now names "Local Lean preview service".

## Flagged for the owner (kept, not deleted)

1. **#216 is closed.** The Review guidelines still route missing `definition_ids` links and coverage gaps to "the definition-coverage issue #216". That issue is now closed, so the routing points nowhere live. The text is kept unchanged; a replacement issue or "a follow-up issue" alone would settle it.
2. **The title "Codex worker contract".** The heading is kept as instructed, but the contract governs every agent and runtime, not only Codex workers. Renaming it is an owner choice.
3. **The duplicated premise-reporting rule.** The old file stated it three times: in Worker brief and handoff, Concise reporting item 3 and step 8. It now has one full statement (OPS step 8) and one summary (A, gates). This is not obsolete text, only deduplication; it is listed so the completeness review can check it.

No text was found to be genuinely contradictory once the Lean-first reconciliation above is applied.
