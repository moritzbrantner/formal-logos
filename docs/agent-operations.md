# Agent operations

This is the mandatory procedural reference named by [`AGENTS.md`](../AGENTS.md). Its rules bind like the contract itself for the tasks it covers: retrieval before research, the worker environment, formalizing a source reading or an argument, verifying and self-sweeping a change before review, generated shared files, a selected sense/rival comparison, naming records, and the full wording of the permanent invariants. It was moved out of `AGENTS.md` (#2183) with its wording unchanged apart from link formatting, two merges (the duplicate premise-reporting rule folded into step 8; the retrieval section's attempts paragraph replaced by a pointer to `AGENTS.md`) and the three pointers listed in the [shortening map](notes/agents-md-shortening-map.md#wording-added-for-clarity-no-new-obligation); the research method itself is in the [systematic corpus loop](systematic-corpus-loop.md), and source ingestion of candidate ranges is in its [candidate section](systematic-corpus-loop.md#2-candidate-the-next-contiguous-source-range).

## Retrieval before research

Before opening a new proposition investigation or introducing vocabulary, run `target/release/truth related <STMT-ID>` for the load-bearing seed. It ranks the loaded corpus in memory (no cache) and surfaces related propositions, complete argument bundles and previous attempts. Without a seed ID, start with `target/release/truth index search 'topic words'` (a disposable SQLite/FTS5 projection under `.cache/` of the corpus records and the `docs/notes/` sections (#952), rebuilt when either changed; never an authority). Inspect promising matches before reinventing them. Rankings and shared vocabulary are discovery aids, not proofs of equivalence, implication or incompatibility. The repository-local `proposition-reuse` skill in `.agents/skills/proposition-reuse/SKILL.md` describes this entry point.

When the target is an existing argument or result, start with `target/release/truth context <ARGUMENT-OR-RESULT-ID>`: one bounded pack with the frozen Lean statement, Lean-import reuse, premise status and other routes, countermodels, attempts and open work, derived on demand ([argument context](notes/argument-context.md)).

Before judging how mature a premise's research is, or calling a theorem, connection or research issue new, run `target/release/truth brief <STMT-ID>` (or `brief --question "..."`) and `target/release/truth novelty "<claim>"`, with `--issues-from` an offline `gh issue list`/`gh pr list --state all` snapshot where available. They retrieve prior notes, attempts, rivals, conditional results, recorded judgments and issues with their references; they are advisory and certify nothing, and a missing hit or snapshot is not evidence that no prior work exists ([`brief` and `novelty`](../truth/README.md#brief-and-novelty)).

Before proposing a derivation or reusing a proposition in a new argument, run `target/release/truth semantics <ID>` (definitions, senses, and the sense verdicts of connected arguments) and the preflight `truth semantics --premise … --conclusion …`. Split an unbridged mixing per sense, or bridge it by an explicit `sense_bridges` premise, before formalization; `argument_batch.py records`, `truth check` and `bind-check` then preserve and enforce it ([`semantics`](../truth/README.md#semantics)).

For every premise touched, inspect `target/release/truth dossier <STMT-ID>` (the explorer links the same generated dossier from the statement page). The dossier is computed from corpus records, not edited separately. Record attempts as [`AGENTS.md`](../AGENTS.md#premise-dossiers-and-attempts) requires, in the [attempt format](premise-dossiers.md).

## Worker environment

The coordinator runs `python3 scripts/worker_env.py --check` once for the selected toolchain/cache setup and supplies that setup to workers. Workers use `python3 scripts/worker_env.py -- <command> <args...>` without repeating the preflight unless the setup changes. Keep machine-specific verifier paths in repository-local Git configuration or the explicit environment, not in briefs that workers must reconstruct or in committed source.

Workers reuse a warm clone rather than compiling TruthCore cold: retain a quiescent prepared clone, or prepare a new one with `scripts/prepare-worker.py --seed-build-from <WARM-CLONE>` under the heavy-job lock ([worker startup](worker-startup.md)). Lake then rebuilds only modules whose inputs changed. A seeded build output is readiness, not verification: build, binding, axiom, Comparator and NanoDa gates still run on the final inputs.

## Generated shared files

Shared tables and import lists are generated, never hand-edited (#416). Lean imports: `scripts/root-imports.sh --write` (each area has its own aggregator under `TruthCore/Imports/`; `scripts/root_imports.py` lists the areas finer than one top-level directory). Docs tables and lists: add one entry file (for example `docs/decisions/<date>-<NN>-<slug>.md`) and run `python3 scripts/docs_index.py --write`. CI rejects stale output of both. Merge `origin/main` into your branch right before every push, then rerun these generators and only checks whose evidence the merge invalidates; reuse evidence for unchanged inputs, and final CI covers the delivered revision. After a merge conflict in a generated file, take either side and rerun the generator. A row or list item that a branch from before #416 added by hand must first move into an entry file: the generator keeps only entries.

## Systematic sense and rival comparison

Use this workflow when a sense/rival comparison is the selected question; it is not a prerequisite for every investigation in the systematic loop.

Before research, inspect `/progress` in the corpus explorer and the target's `/dossiers/<statement-uuid>#research-comparison`; use `target/release/truth context <ARGUMENT-OR-RESULT-ID>`, `target/release/truth dossier <STMT-ID>` for every touched premise, `target/release/truth brief <STMT-ID>` for prior rivals and judgments, and `target/release/truth related <STMT-ID>` before introducing vocabulary. These views reuse canonical corpus evidence; they are not a separate status registry.

- Pick a bounded root-route target and a named rival/sense question. Use a finite, explicitly scoped set of relevant senses. Do not presume coverage or exclusivity; make either an explicit obligation when an inference uses it. Absent mappings remain unknown or untested.
- Compare within the same meaning, witness, domain and frame. Each cell records a checked exclusion under listed premises, model-witnessed compatibility of the selected bundle, an unresolved exact gap, or untested. An absent refutation is not compatibility; a finite countermodel is not global incompatibility.
- Keep every assumption visible. A newly verified non-transcription argument is positive conditional support-option progress even with more explicit open inputs; it establishes its conclusion only under the existing closure rules. No independent defense of primitives is required merely to explore consequence.
- Before handoff persist evidence, exact gaps and the next concrete research step in existing corpus records, batch specs and `corpus/attempts/`, not another research/status registry. Attempts do not confer proof status. Use existing explicit configuration semantics and certificates for assumption comparisons; registration alone remains `verification required`. Generate batch records with `python3 scripts/argument_batch.py records SPEC --write --fix` and inspect the resulting dossier. The static progress view derives closure/support from `frontier --json`, gaps from dossiers/attempts, senses from disambiguations, and scoped comparisons from existing configuration reports. Record explicit sense/rival certificate annotations as `[[argument.research_comparisons]]` in the owning batch spec (fields and commands in [Recording a checked sense/rival comparison](github-pages.md#recording-a-checked-senserival-comparison)); the generator writes them to the existing result record. Missing mappings stay untested, never inferred from names or imports. These annotations do not bypass theorem verification or alter closure.
- The coordinator selects the next unanswered discriminating cells and assigns workers disjoint argument clusters. Reuse unchanged checked evidence. Report conditional support progress separately from establishment and root closure.

## One atomic work item

Perform this loop for each philosophically substantive reading or argument encountered inside the current candidate range. For an assigned logic task under [Logic first](../AGENTS.md#logic-first-attribution-deferred-owner-direction-2026-11-05), new formalizations need no new source, passage or claim records; label them as analyst formulations with attribution deferred.

### 1. Research from verified source evidence

- Resolve the passage to a `corpus/passages/` record. Its source snapshot must name the exact edition URN, repository, immutable revision, file path, Git blob SHA, source URL, language and license. Where no such witness exists, a `web_snapshot` pins a web page by hash instead; claims on a translation carry `basis: translation`. Only for a copyrighted work with neither, a `bibliographic_span` cites the edition by page, and its claims carry `witness: "bibliographic"` (see [source evidence](source-evidence.md)).
- If no passage witness covers the range, add one from a stable primary-source edition before creating any claim.
- Run `python3 scripts/source_evidence.py materialize <PASSAGE-ID>` and read the materialized text plus enough immediate context to avoid quotation-mining.
- Preserve the conventional classical locator and CTS identity. The conventional locator remains the human citation; the pinned witness makes the consulted bytes reproducible.
- Record a concise paraphrase rather than copying long translations into the repository.
- Identify one atomic source reading or argument.

A worker may use catalogs, translations, commentaries or search for orientation, but those do not substitute for reading the materialized primary-source witness used by the claim.

### 2. Check reuse

Search `corpus/statements/` and `TruthCore/` for existing propositions and concepts that may express the same thing. Reuse a statement ID only after checking meaning, not merely similar names. When uncertain, preserve separate statement identities; equivalence can be related later.

### 3. Formalize a source reading

- Add the smallest Lean declaration that captures the proposition when a Lean declaration is appropriate.
- Put source locator and interpretation notes in the Lean doc comment.
- Add/update an independent `corpus/statements/*.json` record for the proposition.
- Add/update the corresponding `corpus/claims/*.json` record linking the source reading to that statement.
- Ensure the claim's `source_id` and `locator` resolve to exactly one pinned passage. `target/release/truth check` rejects missing or ambiguous passage evidence.
- Link the senses of load-bearing terms through `definition_ids` and `disambiguation_ids`. When a term or reading choice has no record yet, add a `corpus/definitions/` or `corpus/disambiguations/` record (see [Review guidelines](../AGENTS.md#review-guidelines) and [corpus model](corpus-model.md)).
- If another reading is also defensible, create a sibling claim with the same source locator and an `interpretation_of` link. Do not use that link to imply statement equivalence.

### 4. Critique fidelity

Before proving anything, explicitly ask:

- Is the formal statement stronger than the source?
- Is it weaker in a way that removes philosophically relevant content?
- Did a natural-language relation get replaced by a modern notion with different semantics?
- Did quantifier scope, modality, time, identity or causation change?
- Does the cited locator genuinely support this reading when inspected in the pinned passage and its context?

If the answer is materially uncertain, preserve alternatives rather than silently selecting one. A green source-evidence check cannot answer these interpretive questions.

### 5. Create an argument only when there is an argument

A source claim need not have a proof: it may simply be a commitment attributed to a text. When statements are meant to support a conclusion:

- ensure every premise and conclusion has its own statement record;
- add one or more `corpus/inferences/*.json` records for the logical steps;
- add a `corpus/arguments/*.json` record composing those steps;
- add `Challenge.lean` containing the exact advertised theorem with `sorry`; it stays an ordinary (non-module) file;
- add a separate `Solution.lean` containing the same theorem and a real proof;
- write the new `Solution.lean` and every new vocabulary file as a Lean module: a `module` first line, `public import` for each import and `@[expose] public section` after the imports and module docstring (`python3 scripts/convert_to_module.py convert <FILE>` converts an ordinary draft). Every library file is a module, so this always applies; CI (`python3 scripts/convert_to_module.py check`) rejects an ordinary library file other than a Challenge or an aggregator (owner decision on #986);
- run `scripts/root-imports.sh --write` so the generated aggregator of the module's area (`TruthCore/Imports/<Area>.lean`) imports every new module (except `Challenge.lean`) in sorted order; `TruthCore.lean` imports only the aggregators and changes only when an area appears. Aggregators and the root are generated as Lean modules (`public import`) while every file they import is a module (#986); never hand-edit them;
- add a `corpus/results/*.json` verification record that points to the argument;
- add a Comparator JSON config naming the theorem and permitted axioms.

Scoped assumptions and discharged assumptions belong to inference records. They are not ordinary established corpus premises. For a batch of related derivations, `python3 scripts/argument_batch.py challenge` and `records SPEC --write --fix` generate the Challenge and records ([exploration and batch certification](../AGENTS.md#exploration-and-batch-certification-owner-direction-2026-11-07)).

### 6. Handle missing premises correctly

If a Solution cannot be proved from the advertised premises:

- do not change the frozen Challenge, silently add an axiom, strengthen a definition or broaden an existing source claim;
- test for a countermodel or a useful alternative configuration and record the unresolved inference;
- when a stronger commitment is worth exploring, register a separate candidate/configuration with that assumption explicit and compare its consequences; source research is required for attributed claims, not for every stipulated framework branch.

### 7. Verify the three boundaries

The following commands describe required verification coverage, not duplicate local runs for every worker and coordinator. Reuse completed evidence; final CI provides the integration checks. Run a check locally when development needs it or a relevant change or failure invalidates its earlier evidence.

`truth` is the repository's Rust CLI ([truth/README.md](../truth/README.md)): build it once per clone with `cargo build --locked --release -p truth` (rerun after Rust source or Cargo input changes) and run it from the repository root. It is the only implementation of the corpus commands (`check`, `frontier`, `frontier-diff`, `thickness`, `next`, `related`, `dossier`, `context` including `--proof-use`, `bind-check`, `unused-premises`, `lean-reuse`, `attribution-check`, `configurations`, `configuration-report`, `models`, `strength-comparisons`, `strength-report`, `structure`, `structure-report`, `issues`, `senses`, `index`, …); `scripts/corpus.py` was retired (#954 R2/R3). A statement root is `--frontier-root`. Rust `--root PATH` selects the input repository; `--json` selects machine-readable output, including frontier reports usable by `dossier` and `context` via `--frontier-json FILE` on the same inputs. `frontier-diff`, `thickness --base` and `orphans --base` judge the base revision's committed corpus and Lean sources by the running binary's rules (owner decision 2026-11-16, "head rules on base data"), so a PR that changes the frontier rules shows that change in its delta.

```bash
lake build
target/release/truth check
python3 scripts/bundle_audit.py
target/release/truth bind-check
scripts/verify-result.sh <RESULT-ID>
```

`bundle_audit.py` runs offline. Run it whenever you edit an argument bundle or a definition its audit pins by hash: CI runs it right after `truth check`.

`truth bind-check` (after `lake build`) reads each result theorem's type and checks that its `Prop` hypotheses are exactly the argument's premise statements and its result type is the conclusion statement, matched by `lean_declaration` head constant; type and vocabulary parameters are not premises. A hypothesis whose head is a theory definition (`TruthCore.Comparison.*`) is a theory bundle: it is unfolded one step and split on `∧`, and each conjunct must bind to a listed premise, covering them exactly. A conclusion that is a theory definition is a consistency claim: its argument must list `commitment_statement_ids` (and may then have no premises), and these must match the conclusion's conjuncts in the same way. Keep non-theory conclusion propositions outside `TruthCore.Comparison`. During development, `truth bind-check --result <ID>` (repeatable) or `--affected --base <BASE>` binds only the named or affected results and needs only their Solution modules built; the full `bind-check` (CI) also checks stale pins and registered models.

`truth check` includes the offline manifest and claim-binding validation of `source_evidence.py check` (rule for rule, `truth/src/check.rs`), so the separate command is no longer a required gate. Selected passage materialization checks acquired bytes against their pins; it is not a recurring repository gate. Source fidelity remains a research/review judgment. Lean/Comparator verifies only the formal consequence.

Do not call an argument mechanically verified unless its result passes Comparator. CI also runs an independent no-`sorry` NanoDa check: over the whole built library on `main` pushes, nightly and manual runs, and on a PR over the modules its diff can affect (changed modules and their reverse dependents; [axiom policy](axiom-policy.md)), so a failure a PR's scope missed still turns the next `main` run red.

### 8. Self-sweep before requesting review

Before requesting `@codex review`, apply the [Review guidelines](../AGENTS.md#review-guidelines) to your own diff in one pass and fix what you find. For research PRs, also go through the [recurring semantic defects checklist](systematic-corpus-loop.md#recurring-semantic-defects-pre-push-checklist). An automated review does not replace the independent semantic challenge. A research thread does not leave a draft PR without either that challenge or a handoff naming it as pending. Before pushing, run `scripts/preflight.sh`; it bundles the offline checks CI runs (including the connectivity and placement gates) plus a lint for artifacts, future dates and over-long labels ([worker startup](worker-startup.md)).

- Every "read as" or attributed claim states no more than its cited sentence; any strengthening is stated as an explicit, unattributed open premise.
- **Attribution self-check (#989), before the first push** (CI runs the same check on every PR): run `target/release/truth attribution-check --base <merge-base>`. This offline check prints each new or changed stating claim (or claim whose statement text changed) beside its locator and any usable cached passage text; absent or stale text is reported as not checked, and it fails until the claim records `"attribution": "The passage states X, which is the premise."` Check quantifier scope, species/genus restriction (one kind of cause or being read as all), and temporal and modal scope. If the sentence would be false, because the passage only bears on the premise or states something narrower, do not keep the claim as stating. Replace it by a `supports` relation with a gap note (#987), or state the narrower reading as its own statement.
- Every load-bearing term on a root path links a definition through `definition_ids`.
- Every ambiguous term links a disambiguation through `disambiguation_ids`.

**Claim vs type.** Most review P1s are prose saying more than the bound Lean type certifies. For every statement, argument or result the diff adds or changes, write in the PR body the prose next to the Lean type (statement paraphrase, claim interpretation, inference/argument `meaning`, result `description`, Lean doc comments, docs) and check:

- quantifiers and scope: "no", "not every", "some", "for all", "exists" (`¬ ∀` is not `∀ ¬`);
- modality and time;
- existence of a witness versus properties of the particular witness (a theorem about some model does not give the model's incidental properties);
- every hypothesis of the theorem is listed as a premise (including nonemptiness or satisfiability side conditions, so that no result is vacuous);
- conditions in the source (same-sense cause, restricted domain, "in any respect") survived into the Lean type;
- any condition added is not attributed to a source that does not state it; it is an explicit, unattributed open premise.

**Premise reporting.** Each PR also reports its intended and actual change in root-path open premises, including "no change". The actual change is computed, not hand-written: link or paste the output of `target/release/truth frontier-diff --base <merge-base>` (conditional support bundles added or removed when comparable and reaching-root premises added, removed, or moved between bare, supported, stated and closed), which CI prints to the job summary of the "Report the premise frontier" step for every PR. Report the identities and status changes of relevant premises, not their aggregate counts. Route costs follow the [per-route open-premise cost rule](corpus-model.md#premise-program-and-frontier) (`frontier --routes`): they diagnose an expanded proof, **not research progress**. A premise is established when it is self-evident with a met floor basis, defended (every recorded rival refuted by a verified refutation whose premises are all established, recursively and without circularity, #999), or derived from established premises; a stated or supported premise stays one leaf until it is established, so adding a derivation under it never raises a route's cost, while a derivation under a bare premise, or a new intermediate step, may raise it.

## Naming

Lean namespaces follow the source hierarchy, e.g.:

```text
TruthCore.Greek.Plato.Timaeus
TruthCore.Greek.Aristotle.Physics
```

Corpus ids are opaque UUIDs (owner decision 2026-11-07): "we just cannot afford any ambiguity anymore". A readable id puts words, and therefore senses, into identity.

- **Never mint a readable id.** A new record gets a uuid4 (`python3 scripts/new_id.py`); `argument_batch.py` mints them for spec records.
- **Use labels for humans.** Every record has a `label`, unique within its kind, at most 100 characters, with no id-like text, naming the thing plainly (a statement by its proposition, an argument or result by its conclusion and route). A term with a linked disambiguated sense carries its sense tag: "Act is PRIOR_1 to potency".
- **Legacy readable ids are aliases.** Migrated records keep the old id as `legacy_id` (for example `STMT-CATHOLICISM-TRUE`, `PLATO-TIM-28A-CAUSE-A`); tools and prose may use it, and it resolves to exactly one uuid per kind. Tools accept a uuid, legacy id or label and print `label [uuid8]`.
- **IDs are permanent UUIDs; legacy aliases never change.** Labels may be improved at any time; [label cleanup](notes/label-cleanup.md) lists the mechanical labels to fix, and that list may only shrink (#1233).
- An in-flight branch with readable-id records converts by merging `origin/main` and running `python3 scripts/migrate_uuid.py --write` ([uuid migration](notes/uuid-migration.md)).

## Permanent invariants: full wording

[`AGENTS.md`](../AGENTS.md#permanent-invariants) states the nineteen permanent invariants in condensed form under the same numbers, which code and records cite ("AGENTS.md invariant 16"). This is their full wording as of #2183; where the condensed form is shorter, this wording governs.

1. **Research before formalization.** Every source-derived claim must point to a stable source record and a precise locator. For a copyrighted work with no pinnable witness, that locator may be a `bibliographic_span`: edition, ISBN or DOI, and exact pages or section, without pinned bytes (owner decision 1c on #378; see [source evidence](source-evidence.md)).
2. **Materialize, do not remember.** Before formalizing a source-derived claim, resolve or create its `corpus/passages/` witness and run `python3 scripts/source_evidence.py materialize <PASSAGE-ID>`. Read that verified text and enough context to interpret it. Model memory, a search snippet, or a plausible citation is never source evidence. A `bibliographic_span` has no bytes to materialize (`materialize` refuses it): claim from it only after reading the cited pages in the edition itself, never from memory, and its claims carry `witness: "bibliographic"`, so they are shown as not byte-verified.
3. **Source integrity is not source fidelity.** A pinned revision, Git blob hash, CTS path, and successful materialization establish which source text was consulted. They do not establish that an interpretation is correct. Preserve that scholarly judgment separately.
4. **Statements have independent identity.** A statement is a proposition used by logic. A claim says that a source supports a statement under an interpretation. Never make statement identity depend on source provenance.
5. **One defensible reading per claim.** If two materially different interpretations are both reasonable, create two claims. They may point to distinct statements even when later work could relate those statements.
6. **Do not merge by similarity.** Textual identity, translation equivalence, formal equality, logical equivalence, philosophical equivalence, and historical identity are different possible relations. Add relations later; do not silently merge statement IDs.
7. **Reuse before invention.** Search existing statements and Lean declarations before adding vocabulary. Reuse only when the meanings genuinely coincide; a false identification is worse than a duplicate statement.
8. **Weakest faithful formalization.** Do not strengthen a source passage to make later arguments easier.
9. **No premise smuggling.** A proof worker may not silently add an axiom, assumption, definition, or stronger reading to an existing argument or frozen Challenge solely because its proof needs it. Register a consequential stronger assumption as a separate, explicitly labeled framework configuration or candidate and compare its consequences. Source it when attributing it to a text; an openly stipulated framework commitment need not be independently proved to be explored. It does not close a root premise.
10. **Inference is explicit.** Arguments connect statement IDs through inference-application records. Never encode a logical step as an overloaded bare statement-to-statement edge.
11. **Global cycles are allowed; circular proof is not.** Semantic relations and mutually supporting statements may form cycles. Each advertised argument must still be grounded in its premises and mechanically checked by Lean/Comparator.
12. **Challenge is frozen before solution work.** Never weaken or otherwise edit a Challenge merely to make the Solution pass. If source review changes the statement, treat that as a new/revised claim first.
13. **Formal verification is not source verification.** A result verifies an argument's formal consequence. It does not establish that a source really meant a statement or that a premise is philosophically true.
14. **Mathlib for mathematics; no other dependency without an owner decision.** Mathlib is an approved dependency for mathematical content: analysis, order, set theory, ordinals and cardinals, combinatorics. Prefer an existing Mathlib notion over a hand-rolled one. Do not use Mathlib to dress up opaque propositions: importing it adds no philosophical content. A result whose proof uses Mathlib may permit exactly `propext`, `Classical.choice` and `Quot.sound`; a result that does not import Mathlib stays zero-axiom ([axiom policy](axiom-policy.md)). `lean-toolchain` pins the exact Lean version the pinned Mathlib release requires. Any other external Lean dependency still needs an owner decision (#337).
15. **Do not build identity infrastructure early.** No graph database, RDF ontology, embedding-based merger, or canonical-equivalence resolver until the corpus creates a concrete need. The typed JSON records are sufficient for now.
16. **A transcription is not a proof.** A result whose proof only applies a premise whose consequent already is the advertised conclusion (`exact hBridge ⟨…⟩`), or whose atoms are opaque `Prop`s that nothing constrains, certifies only that "therefore" was transcribed. Such a result may still be recorded as a faithful map of a source argument, but the PR and the result record's description must call it a transcription. It does not count as progress on the case and closes no frontier node by itself (see the [systematic loop](systematic-corpus-loop.md)). The one exception is closure carried through it: a transcription closes its conclusion exactly when **every** premise of its argument is already closed—self-evident, alternatives all refuted, the conclusion of a non-transcription result, or itself closed by this same rule (computed as a fixpoint; owner decision on #143, 2026-10-24). A transcription with any open premise, such as an open `A ∧ B → C` bridge, leaves its conclusion open. Where the philosophy has internal structure, formalize that structure with typed vocabulary (beings, respects, causes, sentences, …) so the conclusion is *derived* and the result could have failed. Likewise, a hand-rolled substitute for a notion Mathlib already provides (for example "eventually constant" in place of convergence, or a bespoke ω+1 in place of an ordinal or order embedding) needs a stated reason in its doc comment.
17. **Compose, do not restate.** Build on earlier results by importing their Lean modules and using their theorems. Do not restate a proved conclusion as a fresh premise. Reuse shared typed vocabulary where meanings coincide (invariant 7); a new per-file `…Reading` vocabulary for a concept the corpus already has needs a stated reason.
18. **Source kinds are frozen.** After `media_span` (#152), `web_snapshot` (#154) and `bibliographic_span` (#378), add no new source kind without an owner decision. A `bibliographic_span` is the last resort: allowed only for a copyrighted work when no pinnable witness (git text, public-domain edition, `web_snapshot` of a legitimately hosted copy) exists, with a `why_bibliographic` note; upgrade it to a pinned witness when one becomes available. When not even a bibliographic citation can be read and given, keep the claim as a candidate marked as waiting for a witness, and continue the reasoning with its statement as an explicit open premise. Sourcing must not block reasoning, and reasoning must not fake sourcing.
19. **truth-core is self-sufficient.** Do not add runtime or CI dependencies on other repositories (historical-source-atlas, worldview-lab, solver services, …). Use one only for a concrete node that is blocked without it, and pin it like a source.
