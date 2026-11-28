# Codex worker contract

This repository advances substantial arguments through small verified research steps. Keep the complexity in the philosophy, not in repository machinery. This contract binds every agent here, in every role. It states the rules; the documents below hold the procedures. A document named here as mandatory for a task is part of this contract for that task. If a linked document seems to conflict with this file, report the conflict instead of choosing silently.

| Task | Mandatory reading |
| --- | --- |
| Research selection, judgment, challenge, integration; worker ownership; lanes; issues and PRs | [Systematic corpus loop](docs/systematic-corpus-loop.md) (the canonical method) |
| Retrieval, worker environment, formalization steps, verification commands, self-sweep, sense/rival comparison, naming | [Agent operations](docs/agent-operations.md) |
| Records, definitions, senses, strength order, placement, frontier and closure | [Corpus model](docs/corpus-model.md) |
| Source witnesses and offline validation | [Source evidence](docs/source-evidence.md) |
| `truth` commands and the issue brief | [Truth CLI](truth/README.md) |
| Attempts and dossiers | [Premise dossiers](docs/premise-dossiers.md) |
| Worker clones; the Lean preview | [Worker startup](docs/worker-startup.md), [agent service](docs/agent-service.md) |
| Configuration comparison | [Configuration elimination loop](docs/configuration-elimination-loop.md) |
| The case and owner principles; axioms | [Catholic case](docs/catholic-case.md), [axiom policy](docs/axiom-policy.md) |

## Current research focus (owner direction, 2026-11-17)

Prioritize the existence of God and the explicit bridges to divine attributes. Defer evaluation of historical evidence and specifically Christian or Catholic identification until that phase is selected. The Catholicism root and closure rules stay unchanged; locate current work through its God-existence-stage nodes rather than silently changing the root.

Develop coherent end-to-end support routes with fixed meanings, witnesses and assumptions. State the strongest positive warrant and an overall provisional assessment of central premises, with substantive objections and revision conditions. Compare competing explanations of the same phenomenon at matching scope. Preserve defensible primitive commitments and direct assumption options; conditionality alone does not erase their warrant. When a vertical approach yields no further discriminating test, seek horizontal support from another argument family or move to another central node. Different presentations of one assumption are not additional evidence. Keep shared dependencies and exact missing bridges visible. Batch related findings into reviewed checkpoints before pushing, with a concise current conclusion linked to the evidence in existing records/notes. A generated current-case view reuses those records, distinguishes recorded warrant from formal status, and never ranks philosophical strength by leaf count.

## Lean first and encode first (owner directions, 2026-11-25 and 2026-11-03)

**Lean first (2026-11-25).** Substantive logical content belongs in Lean and the existing typed corpus: definitions and senses, propositions, distinctions, evidence, warrant criteria, rival commitments, defeaters, implications, incompatibilities, countermodels and exact open bridges. Encode them in reusable Lean declarations and typed records wherever practical, reusing existing declarations; compose and verify the consequences and expose the open premises. Formal definitions, mathematical claims, countermodels and worked proof applications go into compiled Lean wherever their meaning can be specified, linked from the research record and registered as results when they supply an argument in the graph. Then record the remaining reasoning concisely in prose that cites the formal results and canonical IDs instead of restating arguments: paraphrase, irreducible source fidelity and interpretation, premise warrant, empirical applicability, interpretive nuance, provisional judgments and exact blockers. Keep observations, historical attribution, interpretive judgments and open applications traceable to their evidence.

- This is a preference, not a rigid separation: agents may reason from both Lean and prose. Do not default to prose with Lean as an afterthought, or replace formalization with prose-only assessments, new note sections or opaque `Prop` flags. Equally, do not force opaque encodings, invent universal scoring rules or require proof quotas.
- When revisiting a note, migrate its formalizable content and trim redundancy without losing unique evidence (migration scope: #2002).
- A research PR whose scope is logical shows checked formal progress or names the precise formalization blocker; there is no proof quota and no duty to prove a disputed premise.
- The preference governs the [systematic loop](docs/systematic-corpus-loop.md) and its assessments as well as argument research. An overall provisional judgment stays prose citing the encoded criteria, results and open premises; it is never asserted as a Lean proposition.
- Semantic, proof, binding, review and closure gates stay intact.

**Encode first (2026-11-03).** Formalize what can be formalized and derive what can be derived, keeping the needed interpretation, warrant and review reasoning beside the formal evidence.

- **Encodings must be able to fail.** A transcription or opaque flag is documentation in Lean syntax (invariant 16).
- **Interpretation forks become sibling propositions** (invariant 5), linked by `interpretation_of` or a disambiguation, not "reading A / reading B" paragraphs.
- **Strength forks become strong and weak sibling versions (#1017)** ordered by a `strengthens` relation backed by a verified strong-to-weak result. Use the weakest version that suffices or record why in `strong_version_needed`; a source stating only the weak version is never attributed the strong one. Content-differing senses (eternity, sempiternity, #979) stay a disambiguation ([strength order](docs/corpus-model.md#premise-program-and-frontier)).
- **Disambiguate through definitions, not labels.** Each consequential sense has its own `DEF-…` record and faithful formal interpretation, with load-bearing terms defined inside it recursively and no arbitrary depth limit. A Lean primitive is declared as such, with meaning, distinguishing conditions and open obligations; a constraining theorem is not a definition. Never hide a contested bridge in definitional equality or unfold circularly ([definition dependencies](docs/corpus-model.md#definition-dependencies-and-formal-meaning)).
- **Terms carry sense labels (2026-11-07):** stable, append-only `TERM_n` labels with uuid identities, each sense a distinct Lean declaration so equivocation is a type error for `bind-check`; a label without one is not a finished sense. One sense per term per argument (`for_each_sense` for several); crossing senses needs a `sense_bridges` premise or derived bridge; mixing controls set `sense_mixing_control: true`; the legacy allowlist only shrinks (#1233) ([sense-indexed terms](docs/corpus-model.md#sense-indexed-terms)).
- **Shared frames for new work (owner decision, 2026-11-19, #1784).** New modules in a concept family take its shared frame (for causality `TruthCore.Causality.Frame.CausalityFrame`) instead of fresh parameters for its relations; senses stay distinct declarations. Each field is a stated primitive, sense-tagged where a sense matches, with no assumed relation between fields; bridges stay explicit premises. Older modules get adapters gradually. Tags are authored, never inferred from names; an untagged parameter is unknown.
- **Prose keeps its evidence boundary:** fidelity review, provisional judgments, rejected readings and reasons, and what cannot yet be typed, naming the vocabulary, sources or bridges that block formalization. Never disguise a defeasible judgment as a verified proposition.

Lean first, Encode first and Logic first state one priority: formalize and check the logic now; fidelity and attribution stay in prose and source records and are pursued when selected.

## Logic first; attribution deferred (owner direction, 2026-11-05)

For the **Carneades.org** campaign and other assigned logic tasks, formalization and consequence come first; source acquisition and exegesis must not displace them. The loop governs selection between logic, interpretation and warrant questions.

- Work from available summaries, transcripts, existing propositions and explicit reconstructions: formalize premises and conclusions, compose results, find incompatible bundles, build countermodels. Uncertain premises and readings are openly stipulated inputs, with variants as needed; neither attribution nor a defense of each premise is a prerequisite.
- **Keep PDF downloads, transcript authentication, passage pinning, extraction portability and exact authorial intention off the critical path,** and build no source infrastructure to unblock a logic task. Defer attribution unless selected for a live source or warrant question in scope.
- New formalizations need no source, passage or claim records: label them analyst formulations with attribution deferred, keep available titles/URLs/locators as navigation only, and preserve completed source findings without further certification effort.
- Source-integrity rules still govern deliberately published source claims; never bypass them or invent attribution. If a new attribution blocks a logic PR, defer it and its witness records and keep the checked logic.
- Lean, binding, Comparator/NanoDa, frozen Challenges, exact premise reporting and countermodel boundaries stay; a conditional consequence establishes neither its premises nor the root.
- Parallel workers own distinct argument clusters and files, preferably unrelated topics, in isolated clones, serializing shared heavy operations, without manufactured overlapping source tasks.

This overrides source-first and source-coverage priorities elsewhere here and in existing issue briefs for the logic-first phase. Attribution returns when selected and supportable; it never blocks unrelated logic work.

## Source checks stay offline (owner direction, 2026-11-11)

Full-source verification is not a repository standard. CI, scheduled/manual workflows and routine local gates never refetch historical witnesses or depend on source hosts staying available or byte-stable. Validate source records, claim bindings and attribution records offline; test extraction on local fixtures. Use `source_evidence.py materialize <PASSAGE-ID>` only for selected source research, and read the cited material before attributing a claim. Missing cached text is no evidence it was never read; a green offline check certifies neither bytes nor fidelity ([validation](docs/source-evidence.md#validation)).

## Research policy and provisional judgments (owner direction, 2026-11-10)

[The systematic loop](docs/systematic-corpus-loop.md) is the canonical research method. The coordinator issues reasoned **overall provisional judgments** of current support (cumulative evidence, shared dependencies, objections, revision conditions). They may guide priority, qualified conclusions and explicitly provisional downstream premises; they confer no formal verification, frontier establishment or rival defeat. Keep proof validity, interpretation fidelity, premise warrant, objections and work status distinct. Personal assent is not warrant: never ask the owner to pick a metaphysical winner or create new `owner_approval` floor markings (existing ones are legacy runtime behavior). Consequential definitions, bridges, claimed defeats and influential judgment changes need the [independent semantic challenge](docs/systematic-corpus-loop.md#independent-semantic-challenge) of the final findings; the coordinator drafts the complete outcome first and follows the [bounded review-and-repair procedure](docs/systematic-corpus-loop.md#final-outcome-review-and-repair) before publishing. Use scoped assignments, substantive reassessment and explicit reopening conditions; investigate support, rivals, consequences, preconditions and connections as the target warrants. Whole-case maps, exhaustive sense forks, models and source campaigns are selected methods, not prerequisites. This supersedes older route-cost, bare-premise-first and assent-only floor priorities and changes no proof, source, schema or closure rule.

## Research hypotheses are not forced owner decisions (owner direction, 2026-11-09)

Before offering A/B/C to the owner, classify the alternatives: exclusive *actions or bindings needed now*, or coexisting senses, standards, rivals or frameworks. A disputed thesis is no decision gate. Keep each defensible alternative with its strongest arguments, objections and replies, compare implications, countermodels and bridges without presuming exhaustiveness or exclusivity, and issue provisional judgments. Ask a focused question only when a concrete next action needs an exclusive commitment that cannot be carried as explicit alternatives. "Investigate all options" is a complete decision: persist it and proceed. Example: PR #1297's whole-series standards stay rival standards (attempt `a5958e25-0904-46cb-a9e8-62ca5f3f5286`).

## Argument breadth and cumulative warrant (owner direction, 2026-11-12)

- **Breadth is progress** when it adds meaningful coverage or genuine support options. Counts describe scale, not merit; do not keep presenting count growth or unchanged frontier totals as a weakness.
- **Direct and conditional options coexist.** A proposition may be held on its prima facie merits **and** supported by arguments. A derivation never removes the direct option and is not penalized for adding open premises, sharing dependencies or raising expanded-route cost.
- **Cumulative warrant.** Do **not** demand an independent argument for every premise or discount reasons that join the same web. Weigh prima facie plausibility, experience, successful inquiry, conceptual or practical preconditions, explicit arguments, coherence, explanatory performance and defeats of rivals together. Candidate primitives and preconditions of reasoning itself may be a stopping point once content, scope and defeaters are recorded. Ask whether support discriminates or begs the question; mutual implication or a closed proof cycle adds no warrant. Shared dependencies stay visible but are no penalty.
- **Comparative tests** (strict self-refutation, epistemic self-undermining, no internal reason to adopt, contradiction of inquiry preconditions) are distinct. Failing one costs standing; surviving one may gain *relative* standing, not truth. An undiscovered objection is no proof. Do not manufacture objections or demand arguments merely because a proposition is primitive.
- **Progress reports** lead with what was clarified, connected, supported, tested or compared. Establishment, independence and route cost answer only their diagnostic questions. Never report aggregate bare- or open-premise counts, deltas or ratios as progress or routine status (owner direction, 2026-11-24); keep individual assumptions, source depth and dependency changes inspectable.

Provisional warrant stays distinct from Lean consequence and computed closure; no schema or proof gate changes ([cumulative warrant](docs/systematic-corpus-loop.md#cumulative-warrant-and-support-options)).

## Substantive Objection Standard (owner direction, 2026-11-12)

Do not introduce speculative, nebulous or merely conceivable objections as if they carried evidential weight. An objection must (1) identify the specific premise, inference or assumption it challenges; (2) explain the concrete mechanism of failure; (3) give independent justification for that mechanism; (4) explain its relevance to the actual argument; (5) distinguish established counterexamples from hypothetical possibilities. Independent justification is positive support beyond asserting conceivable failure or restating the objection; it does **not** require isolation from the rest of the graph or an endlessly prior proof. The same non-question-begging test applies to supporting arguments. A non-generalization claim names the relevant difference and why it matters. Invent no contrived alternatives for balance. The burden lies with the objection's proponent; an unspecified possibility of error is not evidence of error. If no substantive objection exists, say so plainly rather than manufacture uncertainty. Apply this equally to arguments for and against theism, naturalism and every other worldview.

- A recorded rival or objection names its target, mechanism and the mechanism's justification; otherwise record "no substantive objection identified". A finite countermodel is a fact about one formal interpretation: it shows a premise is needed there, not that it is false, and is no evidence against it without that justification.
- "This case is special", "this may not extend" or "dropping assumptions may dissolve it" must name the difference and why it matters, or be removed or recorded as a weightless suggestion.
- The standard relaxes no proof, binding, source or closure rule: open premises stay open; a conditional theorem establishes only its conclusion under its premises.
- Reviewers apply it to objections exactly as to support; a failing objection presented as evidence is P1.

## Connect every library to the case (owner direction, 2026-11-07)

A verified library answering no question on a root route is not case progress: about 50 modal modules with 89 verified results never reached `STMT-CATHOLICISM-TRUE` ([decision record](docs/decisions/2026-11-07-02-connect-libraries-to-the-case.md)). No library, framework, vocabulary or result family is built or extended in isolation.

1. **Name the target before building.** Every brief and every PR adding vocabulary or results names the root-route node it serves: a premise discharged, argument connected or rival refuted (`truth frontier --routes`).
2. **Connect, or say why not.** The PR shows the connection in the computed `frontier-diff` or states a connection plan (target statement, missing bridge, blocker) that the handoff tracks; unconnected work is not case progress. CI gates: `truth connectivity --base <merge-base>` fails on a new, moved-out or previously planned statement that neither joins the root's typed component (arguments, inference steps, relations including `tests`; claims through relations, not attempts) nor records a valid `connection_plan`. Typed contact is not enough for results (owner decision, 2026-11-27): `truth orphans --base <merge-base> --gate` fails on a new, changed or previously placed verified result that neither reaches the root, nor is a placed diagnostic (`tests` a root-path node) or rival (typed rival relation), nor has a `connection_plan` on its conclusion targeting a root-path statement ([connection plans and placement](docs/corpus-model.md#premise-program-and-frontier)). Contrived edges and tautological bridges are unacceptable; passing a gate discharges no substantive obligation.
3. **Include idle work in prioritization:** inspect `truth orphans` when choosing a round. A bridge can be high-value but does not automatically outrank a live objection or missing warrant; judge research by the uncertainty it changes; route cost and thickness remain diagnostics.
4. **Investigate load-bearing senses and their relationships:** faithful definitions, consequential alternatives preserved, implication, equivalence or independence tested with the sense-index and bridge machinery; names or types alone establish no meaning; research rivals and premise warrant whenever informative. A [certified fork](docs/configuration-elimination-loop.md#certified-forks-for-selected-investigations) needs coverage only if its inference uses coverage, and exclusivity only if it uses exclusivity; overlapping or strength-ordered senses need not exclude each other, and no exhaustive enum or joint theorem is required first.

**Placement is plumbing, not warrant** (owner decision 2026-11-27, [decision record](docs/decisions/2026-11-27-02-curation-ends-mechanical-review-strict-main.md)). A result is placed or reaches the root when connected, not when supported. Progress reports keep four standings apart, mapping each reaching result's `truth orphans` provenance key:

1. **established**: the frontier's established statements (no key);
2. **conditionally supported by a substantive derivation**: `substantive`; `refutation_support` too, but only as support for that refutation of a recorded rival, not for a root route;
3. **connected only**: `transcription_closed` carries rule (d) closure but no independent warrant; `transcription_self` contributes at most rule (d) closure; `transcription_open`, `loop_back`, `registration_bare` and `unverified_route` carry no support;
4. **planned**: placement state `planned` (no key).

Counts are never progress (owner direction, 2026-11-24).

## Proof-seeking stance

Seek machine-checkable consequence, not prose approval; an LLM may propose readings, formalizations or proof steps, but its agreement is never evidence that a conclusion follows. Think Curry–Howard: propositions are types and proofs terms (implication a function type, conjunction a product, disjunction a sum, quantifiers dependent types). A claim `P1, ..., Pn ⊢ C` makes premises, definitions and rules explicit and reduces to a checkable artifact, in Lean by default. Keep interpretation, extraction, formalization, proof search and verification distinct: Lean's kernel is the authority; tactics, solvers, LLMs and `truth discover` are search helpers, and a discovery is a conditional support option for review, never a record ([discover](docs/discover.md)). Machine-checkable is not automatically discoverable: failed proof search is not a refutation, and verification establishes consequence only inside the encoded system, not premise truth, source fidelity, empirical truth or the logic's completeness.

## Conditional framework exploration (owner direction, 2026-10-31)

Truth Core investigates the case for Catholicism and the strongest competing worldviews. In the foundational phase, systematically explore combinations of low-level propositions, rules, framework commitments and semantic profiles, including routes to necessary concrete being and alternative conclusions, without an endless demand to justify each primitive first.

- **Assumptions are legitimate inputs:** agency, causal structure, a PSR variant, a modal rule or another contested commitment may be taken as given, declared with its interpretation, kept distinct from source-attributed claims, and explored without independent proof.
- **Explore the configuration space:** compose results, seek several routes, minimize sufficient bundles, derive incompatible cores, model surviving branches, and compare adding, removing or reversing commitments with logic and semantic profile fixed or the bridge marked.
- **Classify outcomes precisely:** conditional entailment, contradiction under stated assumptions, model-witnessed alternative, or unresolved search. Failed search refutes nothing; an inconsistent background supports no nonvacuous victory; a model witnesses only its formal interpretation.
- **Count conditional progress** (implications, weaker sufficient sets, incompatibilities, countermodels, distinguished alternatives) separately from root-frontier closure; a conditional theorem establishes no premise or root.
- **No recursive premise-defense by default.** Investigate an assumption's warrant, interpretation or applicability when selected, when it discriminates serious surviving alternatives, or when an unconditional truth claim is made; such warrant may be prima facie, practice-based, cumulative or inferential. Otherwise keep it open; do not spawn a source task for every primitive.

Challenge/Solution boundaries, source fidelity, exact premise reporting, no-smuggling and root-closure criteria remain; no framework's assumptions are thereby declared true.

## Semantic grounding of metaphysical relations

Every new or substantially reinterpreted relation of causation, dependence, grounding, contingency, necessity or explanation needs a clear, non-equivocal interpretation; its applicability to reality may stay open as an explicit framework assumption. For significant relations give: the ordinary-language meaning; concrete examples and counterexamples, or why none are available; distinctions from similar relations; explicit structural properties (transitivity, asymmetry, well-foundedness), defended or marked open where real-world applicability is claimed; each generalization from ordinary experience to metaphysics as an explicit bridge, investigating both accepting and rejecting it when consequential; and tests against serious competing accounts ([detailed questions](docs/systematic-corpus-loop.md#semantic-grounding-of-metaphysical-relations)). A verified theorem establishes a conditional consequence, not the truth or applicability of its interpretation; this bounds claims and is no prerequisite for exploration. No mathematical relation is causal or explanatory by its name.

## Exploration and batch certification (owner direction, 2026-11-07)

Use an exploration map (`explorations/<slug>.toml`, checked by `argument_batch.py map`) when it helps expose an argument DAG; none is required first. Reuse statement IDs and mark new nodes and bridges. Certify related derivations as one batch where useful (one vocabulary module, one Solution, a Challenge from `argument_batch.py challenge`, records from `argument_batch.py records SPEC --write --fix`), with no derivation quota and new bare premises and analyst bridges explicit and open. Seek nonvacuity witnesses and omission countermodels where informative; record unresolved satisfiability or necessity rather than demand a model for every result; satisfiability, non-entailment and minimality claims need their own evidence. `thickness` is a diagnostic, not a score or the sole queue. Record rejected leads as attempts. Base PRs on `main`; return conflicts to the owning worker and regenerate shared files.

## Argument-first investigation and configuration comparison

Keep the whole argument's purpose and strongest rivals in view while investigating one bounded uncertainty (implications, incompatibilities, warrant, preconditions, semantic bridges); decompose where useful and reconnect findings to the parent. Open premises do not block conditional work; a failed route does not justify inventing a stronger premise. An exhaustive dilemma needs checked coverage under explicit background assumptions; exclusivity is separate. A contradictory bundle forces rejecting some member, not a preferred one. Prefer meaningful constraints and better-supported judgments to issue/proposition counts. Preserve proof, source, dossier and frontier authorities; neither conditional elimination nor a provisional judgment establishes its background.

Selected configuration comparison follows the [configuration elimination loop](docs/configuration-elimination-loop.md): reuse certified results and models, seek verified contradictory sets and minimality where useful, compose proven implications, persist attempts and countermodels, and compare exact root-frontier premises before and after. Labels are relative to explicit formal semantics; a missing model or proof is unresolved, not impossible; closure rules are unchanged (#477). Use `truth countermodel` for omission countermodels ([countermodels](docs/countermodels.md)) and `truth prove-sweep` before hand-writing a Solution ([prove sweep](docs/prove-sweep.md)); both are advisory, and "unresolved" does not show a premise is needed. A selected sense/rival comparison follows [its procedure](docs/agent-operations.md#systematic-sense-and-rival-comparison): one meaning, witness, domain and frame; absent refutation is not compatibility, a finite countermodel not global incompatibility, and missing mappings stay untested.

## Fresh subagents for issue work (owner direction, 2026-11-08)

In a workloop the coordinator delegates each issue or bounded investigation to a fresh subagent, splitting broad issues into reviewable slices with explicit file and argument ownership, under the [worker ownership and integration contract](docs/systematic-corpus-loop.md#worker-ownership-and-integration) (scoped context, continuing repairs, review order, validation reuse, coordinator-owned integration). The originating worker keeps its slice through semantic and CI repairs; a phase transition alone needs no new agent. The [parallel-lane policy](docs/systematic-corpus-loop.md#parallel-lanes) governs two distinct propositions in different argument families, reserved review capacity and shared semantic baselines. Research continues while other work awaits review or CI; routine corrections stay in the loop. Workers persist findings in existing records and return a compact delta with evidence to the one current handoff.

## Research continuation and stopping (owner direction, 2026-11-10)

Research has no default token, time, depth, batch or PR budget; an assignment fixes question and ownership, not depth. Continue while a concrete relevant next step exists, within explicit owner limits and runtime constraints.

- **Walk the argument:** fix meanings, state the strongest rivals with their positive replacement accounts, derive their further commitments, and where a rival survives descend into its subarguments and reconnect to the parent. A surviving model or open premise is an intermediate finding, not a stop. A rival's price is not unreasonable for being unusual; name its conflict with an accepted floor item or its own commitments. Keep unresolved rivals visible.
- **Workers report a branch** when it is resolved under stated assumptions, needs unavailable evidence, capabilities or a genuine owner decision, repeatedly hits the same obstacle with no materially different test, or a more consequential question warrants a scope change; they continue other useful work in scope. A blocked approach is not an exhausted question.
- **Persist before reporting:** results, gaps, the strongest standing rival and its price, approaches tried and why they failed, next tests, in existing records, attempts and the linked note; return a compact delta with evidence and exact revision, and no tracker.
- **The master owns continuation:** it assesses each report against the whole argument, reuses unchanged evidence, and continues the branch, supplies a dependency, assigns another approach or redirects, respecting ownership and using fresh workers for unrelated slices. A worker's dead end does not end the master investigation.
- **PRs are checkpoints:** publication, green CI or review does not end the investigation; continue in scope without asking again. Proof gates and merge authority are unchanged.
- **The master stops** when the scope is substantively resolved, every remaining branch has a concrete blocker, or the owner stops it, and says so in the one handoff. A runtime interruption leaves a resumable handoff, not a completion claim.

## Worker brief and handoff

The master gives each worker a compact brief:

1. **Target:** proposition, parent question/argument family and root obligation advanced: a root-route node, or a named bridge, connection plan and blocker; and why it is independent of the other active target. An unbuilt bridge is not an existing route; a target serving no root route is rejected.
2. **Starting result:** baseline revision and the exact theorem, reviewed finding or attempt to build on, with scope and assumptions; for formal reuse, statement IDs, selected definitions and senses, and the Lean declaration. Without one, the closest evidence and what the search left open.
3. **Question that could change the judgment** and the finding that would change it; at a shared bottleneck, the [negated-premise test](docs/systematic-corpus-loop.md#when-several-arguments-stop-at-the-same-premise).
4. **Expected value:** the useful change sought, with expected premise effects; a finding may clarify without discharging.
5. **Ownership and reassessment:** file/argument ownership and the conditions for reporting a resolved or stalled branch. No work cap; an honest no-result report names approaches, obstacle and next test or reopening condition.

A substantial frontier brief states thesis, selected meaning, downstream purpose, serious rivals and evidence; the worker may refine it, and no complete tree or rival list is required. It lives in the one handoff or issue.

Issues follow the [research issue contract](docs/systematic-corpus-loop.md#github-research-issue-contract) (an answerable question, graph destination, existing dependencies and live discriminating uncertainty, not a prescribed conclusion or proof count) and state requested delivery and acceptance evidence. An issue assignment or returned handoff starts from the [issue brief](truth/README.md#starting-from-a-github-issue) on current `main`, compares the requested deliverable with the reviewed record and the linked open or merged PRs, reuses delivered findings and assigns the first unmet item. A covered issue is carried through its existing PR. After integration, record delivered evidence and remaining work in the existing issue/handoff and close a completed scope without treating the larger question as settled. PRs follow the [PR completion contract](docs/systematic-corpus-loop.md#pr-completion-contract); the templates prompt for its evidence, and issues and PRs made by CLI or API follow the same contracts. A partial delivery does not close an unfinished scope. A new verified non-transcription argument is **conditional support-option** progress even if it replaces one leaf with several open premises; record the new obligations separately; neither it nor a lower route cost establishes its conclusion.

Workers use the coordinator's checked environment and a warm clone ([worker environment](docs/agent-operations.md#worker-environment)); a seeded build is readiness, not verification. Before handoff or retirement, persist verified source findings, rejected interpretations with reasons and gaps in existing passage, claim, definition, disambiguation or candidate records or linked notes, with precise witness locators and sourced readings kept distinct from open commitments. Temporary files are never the only copy; no claim is created merely to record activity.

## Concise reporting and persistence

1. **Report changes** (a finding, decision, failure, merge or blocker), not unchanged plans, status or check inventories; one short verified-wait update during a long wait.
2. **Timings only when relevant** (requested performance work, an unexpectedly slow run); omit routine startup/build histories and unavailable-metric disclaimers, which stay in CI or command logs.
3. **Focused PRs:** problem, change, premise effects, essential validation, remaining gaps, with the claim/type self-sweep and computed `frontier-diff`; link check evidence instead of narrating runs, adding a reproduction command if needed.
4. **One current handoff,** kept by the coordinator: exact head/branch, open work, verified and unverified scope, next step. Workers return a delta and references; the handoff links rather than copies.
5. **Preserve research substance** (sources and locators, interpretations, rejected approaches and reasons, counterexamples, proof boundaries, gaps) in existing records or linked notes; shorter reporting must not remove it or leave it only in chat or temporary logs.
6. **Trust completed work** (owner instruction, 2026-10-28): reuse reports and check evidence for unchanged inputs and dependencies; focused diagnostics in development, final CI for the delivered revision; no repeated full builds, binding, Comparator, NanoDa, test suites or review rounds at each handoff. Rerun affected checks for relevant changes, concrete failures or unresolved findings. Self-sweep a batch before its first push; combine related findings into one PR where practical.

## Premise dossiers and attempts

Retrieve before inventing with the [retrieval commands](docs/agent-operations.md#retrieval-before-research): `truth related` (or `index search`) before new vocabulary, `context` for an existing argument or result, `brief` and `novelty` before judging maturity or novelty, `semantics` and its preflight before a derivation, and `dossier` for every premise touched. They are discovery aids: no ranking proves equivalence, implication or incompatibility, and a missing hit is no evidence that no prior work exists.

Before handoff, update `corpus/attempts/` for failed derivations, rejected readings, source searches and other substantive attempts, including successes; correct an existing attempt rather than duplicate it, and create no philosophical claim merely to log activity. Record exact target statement IDs, outcome, findings, blocker and result/claim/PR evidence. Attempts and computed dossiers change no proof or closure status. Each attempt a worker creates or updates appends itself to `workers` (role, provider, model, effort, date, PR) (owner direction, 2026-11-26). Format: [premise dossiers](docs/premise-dossiers.md).

## Local Lean preview service

When the coordinator supplies a [local preview](docs/agent-service.md), it owns startup, health checks, dependency refresh and shutdown and gives workers endpoint, workspace and session. Workers keep isolated canonical clones, use the shared session under its lease, and treat each response as bound to its exact revision and inputs. Reuse the pinned toolchain and dependencies; without a preview, use the CLI. A new service experiment is a selected tooling task; the service stays local and authorizes no external Lean dependency. Interactive diagnostics replace none of the final build, binding, axiom, Comparator and NanoDa checks.

## Permanent invariants

The numbers are cited across code and records; the [full wording](docs/agent-operations.md#permanent-invariants-full-wording) governs where this summary is shorter.

1. **Research before formalization.** A source-derived claim points to a stable source record and precise locator (for a copyrighted work without a pinnable witness, a `bibliographic_span` by edition and page; #378).
2. **Materialize, do not remember.** Before formalizing a source-derived claim, materialize its `corpus/passages/` witness and read it in context; memory, snippets and plausible citations are never evidence. A `bibliographic_span` is claimed from only after reading the edition, and its claims carry `witness: "bibliographic"`.
3. **Source integrity is not source fidelity.** Pins fix which text was consulted, not that a reading is right.
4. **Statements have independent identity,** never dependent on provenance; a claim says a source supports a statement under an interpretation.
5. **One defensible reading per claim;** two reasonable interpretations make two claims.
6. **Do not merge by similarity.** Textual, translational, formal, logical, philosophical and historical identity are different relations; never silently merge statement IDs.
7. **Reuse before invention,** but only on genuinely coinciding meaning; a false identification is worse than a duplicate.
8. **Weakest faithful formalization.** Never strengthen a source passage to ease later arguments.
9. **No premise smuggling.** Never silently add an axiom, assumption, definition or stronger reading to an existing argument or frozen Challenge because a proof needs it; register a stronger assumption as a separate labeled configuration or candidate, which closes no root premise.
10. **Inference is explicit:** inference-application records, never overloaded statement-to-statement edges.
11. **Global cycles are allowed; circular proof is not.** Each advertised argument is grounded in its premises and checked by Lean/Comparator.
12. **Challenge is frozen before solution work;** never edit it to make the Solution pass.
13. **Formal verification is not source verification,** nor proof that a premise is true.
14. **Mathlib for mathematics; no other dependency without an owner decision** (#337). Mathlib-using results may permit exactly `propext`, `Classical.choice` and `Quot.sound`; others stay zero-axiom ([axiom policy](docs/axiom-policy.md)); Mathlib never dresses up opaque propositions.
15. **No early identity infrastructure** (graph database, RDF ontology, embedding merger, equivalence resolver) until a concrete need.
16. **A transcription is not a proof.** A result whose proof only applies a premise whose consequent is the conclusion (`exact hBridge ⟨…⟩`), or whose atoms are unconstrained opaque `Prop`s, must be labelled a transcription; it is not case progress and closes its conclusion only when **every** premise is already closed (a fixpoint; owner decision on #143, 2026-10-24). Formalize internal structure with typed vocabulary so the conclusion is derived and could have failed; a hand-rolled substitute for a Mathlib notion needs a stated reason.
17. **Compose, do not restate.** Import earlier results instead of restating proved conclusions as premises; a new per-file `…Reading` vocabulary for an existing concept needs a stated reason.
18. **Source kinds are frozen** after `media_span`, `web_snapshot` and `bibliographic_span` (the last resort). Sourcing must not block reasoning, and reasoning must not fake sourcing: an unsourceable claim stays a candidate and its statement an explicit open premise.
19. **truth-core is self-sufficient:** no runtime or CI dependency on another repository except for a concrete blocked node, pinned like a source.

For the case for Catholicism (epic #143), its binding owner principles and working method, read [the Catholic case](docs/catholic-case.md) first; entity and verification boundaries are in the [corpus model](docs/corpus-model.md) and [source evidence](docs/source-evidence.md).

## Formalization, verification and review gates

Each source reading or argument follows the [atomic work item](docs/agent-operations.md#one-atomic-work-item): source evidence for attributed work, reuse check, smallest faithful formalization with linked definitions and disambiguations, fidelity critique, and, only where there is an argument, statement, inference, argument and result records, a frozen `Challenge.lean`, a separate `Solution.lean` Lean module, regenerated aggregators and a Comparator config. An unprovable Solution leaves the Challenge alone: test for a countermodel and register any stronger commitment separately.

- **Verification coverage:** `lake build`, `truth check`, `bundle_audit.py`, `truth bind-check`, `scripts/verify-result.sh <RESULT-ID>` and CI's independent NanoDa no-`sorry` check. An argument is mechanically verified only if its result passes Comparator. This is coverage, not duplicate runs: reuse evidence for unchanged inputs; final CI covers the delivered revision ([commands](docs/agent-operations.md#7-verify-the-three-boundaries)).
- **Before the first push:** self-review against the [Review guidelines](#review-guidelines) in one pass, work through the [recurring semantic defects checklist](docs/systematic-corpus-loop.md#recurring-semantic-defects-pre-push-checklist) for research PRs, run `truth attribution-check --base <merge-base>` and `scripts/preflight.sh` (including the connectivity and placement gates), and put the claim-vs-type comparison in the PR body ([self-sweep](docs/agent-operations.md#8-self-sweep-before-requesting-review)). An automated review is not the independent semantic challenge; a research thread leaves no draft PR without that challenge or a handoff naming it as pending.
- **Premise reporting:** each PR reports intended and actual root-path premise changes, including "no change", from the computed `truth frontier-diff --base <merge-base>` in CI's "Report the premise frontier" job summary, never a hand-built list. Report identities and status changes, not aggregate counts; a new connection is not a discharge, and route cost diagnoses an expanded proof, not progress. Non-proof work says "none" or "no premise change".

## Lanes and shared files

Work runs in parallel lanes (#416); each owns directories and their corpus records:

- **Lane A — Fourth Way and attributes:** `TruthCore/Latin/`, `TruthCore/Case/` (stages 1–2), `TruthCore/Results/Aquinas/`, `TruthCore/Results/Case/` (stages 1–2).
- **Lane B — stage 3:** `TruthCore/History/`, `TruthCore/Greek/NewTestament/`, `TruthCore/Case/Catholicism/StageThree/`, `TruthCore/Results/Case/Catholicism/StageThree/`, `TruthCore/Results/Comparison/Resurrection/`, the module `TruthCore/Comparison/Resurrection.lean` (in lane C's `Comparison` area, so a new sibling module there is a cross-lane edit), New Testament and Church sources.
- **Lane C — everything else, and the single writer of tooling:** CI, `AGENTS.md`, `scripts/`, the explorer and all other `TruthCore/` areas.

Edit outside your lane only where needed (e.g. a shared definition or `DISAMB-MOTION`), minimally, listing every cross-lane file in the PR. Merge `origin/main` right before every push, then rerun the generators and the checks the merge invalidates. Shared tables and import lists are generated, never hand-edited ([generators](docs/agent-operations.md#generated-shared-files)); CI rejects stale output.

## Selecting work and source ingestion

Select work from the owner-scoped investigation and its current handoff/issue under the loop's priority, exploration and synthesis rules; frontier reports and source candidates inform it. Without a named slice, choose a consequential unresolved question on a current #143 root route or a named bridge to one. Respect real dependencies; neither a favored conclusion nor cheap formal work may monopolize the queue. A useful finding alone does not end available research. Source ingestion for a frontier obligation follows the [candidate procedure](docs/systematic-corpus-loop.md#2-candidate-the-next-contiguous-source-range); keep the issue/handoff on the end-to-end argument and the source and failed-attempt evidence in corpus records.

## Review guidelines

Every code review (including `@codex review`) also tries to **understand and accept** each proof the change presents; the repository, not the reviewer's background knowledge, must make it convincing. Apply this to every result, argument or statement added or modified on a path to a root (`truth frontier --reaching-root`; `STMT-CATHOLICISM-TRUE` is the default root):

1. **Restate it:** what it concludes, from which premises, through which steps, and which Lean theorem binds it (`corpus/results/*.json` → `theorem`; the Challenge freezes its type). Say whether you accept that the conclusion follows on the repository's evidence (Lean statement, premise statements and claims, definitions). Lean checks consequence; you check that the Lean statement says what the prose and source claim say.
2. **Find the definition of every load-bearing term** (e.g. *being*, *act*, *potency*, *cause*, *per se*, *maxime ens*, *God*, *true*): a `corpus/definitions/*.json` record linked through `definition_ids`, either sourced (`claim_ids` to claims whose pinned passages give it) or stipulative (a `note` saying why and what would source it). Check it matches its Lean declaration and the statement's use.
3. **Find the disambiguation of every ambiguity** (several senses, a reading choice, premises that could use a word differently): a `corpus/disambiguations/*.json` record linked through `disambiguation_ids` or reached via a linked sense definition. Check that its `resolution` says which sense each use takes and why the argument does not pass between senses.
4. **Report gaps by severity,** each naming exactly what is missing (term, statement or argument ID, what the record would have to say). P1:
   - a load-bearing term with no definition, or one that changes what is proved (mismatching the Lean declaration or the use);
   - an ambiguity, equivocation risk or reading choice with no disambiguation covering this use;
   - an unstated reading step: prose or claim says more or less than the Lean statement and no record says which reading is formalized;
   - a gap between the Lean statement and its paraphrase or source claim (quantifier scope, modality, time, identity, causation, or a parameter treated as defined);
   - any proof, prose or record claiming more than its source or theorem supports;
   - an objection presented as evidence that fails the Substantive Objection Standard.

   A missing `definition_ids` link is P2 when the term already has a correct definition, or when covered by the definition-coverage issue #216; report all such links in one finding per review. Writing "this depends on what is meant by …" means a definition or disambiguation is missing: report P1 instead of guessing. An open or doubtful premise is not a P1: open premises are the frontier. Report only what stops you from understanding and accepting the step.
5. **Report everything in one pass,** not stopping at the first finding, grouped by kind (overstated or unstated readings, missing definitions, missing disambiguations, Lean/prose gaps, other bugs), re-checking every attributed claim and every `definition_ids` and `disambiguation_ids` link in the diff. P1s that overstate a proof are fixed in the PR; P2s and coverage gaps go to #216 or a follow-up issue.

`truth check` enforces the mechanical part (links resolve; sourced definitions have known claims and stipulative ones a note; disambiguations have two known senses; every definition is used; an argument using two senses of a term links its disambiguation; cited `STMT-`, `DEF-` and `DISAMB-` ids exist). Whether a term *should* be linked is this review's judgment. The explorer lists terms per page and at `/definitions`.

## Naming

Lean namespaces follow the source hierarchy (`TruthCore.Greek.Plato.Timaeus`). Corpus ids are opaque UUIDs (owner decision 2026-11-07): never mint a readable id; every record has a unique human `label` carrying the sense tags of its terms; legacy ids are permanent aliases ([naming](docs/agent-operations.md#naming)).

<!-- BEGIN:turborepo-agent-rules -->

# This is NOT the Turborepo you know

Turborepo configuration, task behavior, and CLI commands can vary between installed versions and may differ from your training data. Resolve the `turbo` package from this file's directory or relevant workspace; in monorepos, it may not be visible from the repository root. For example, run `node -p "require.resolve('turbo/package.json')"` from a workspace that depends on `turbo`.

Read `docs/README.md` inside that installed package first, then read the relevant pages from its `docs/` directory before changing Turborepo configuration or commands. Heed deprecation notices. These bundled docs match the installed package version and are available without network access.

This block is written and re-added by `turbo` before repository-scoped commands when an AI agent is detected. In the Turborepo source repository, its template is defined in `crates/turborepo-cli/src/cli/agent_guidance.rs`. Removing the managed block while updates are enabled means a later qualifying invocation will add it again. Set `"agentGuidance": false` in the root `turbo.json` or `turbo.jsonc` to opt out; this does not remove an existing block. Keep the block committed with your work to avoid an uncommitted change on the next agent invocation.
<!-- END:turborepo-agent-rules -->
