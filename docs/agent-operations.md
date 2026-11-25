# Agent operations and verification

This is the detailed operational reference required by the [root agent contract](../AGENTS.md). The [systematic research loop](systematic-corpus-loop.md) is authoritative for research selection, provisional judgments, semantic challenge, worker integration and PR completion. Commands and code paths in this document are relative to the repository root. This document preserves repository-specific source, proof, identity, verification and review rules; it is not another research loop.

## Permanent invariants

1. **Read before attributing.** Every source-derived claim must point to a stable source record and a precise locator. For a copyrighted work with no pinnable witness, that locator may be a `bibliographic_span`: edition, ISBN or DOI, and exact pages or section, without pinned bytes (owner decision 1c on #378; see `docs/source-evidence.md`).
2. **Materialize, do not remember.** Before publishing a source-derived claim, resolve or create its `corpus/passages/` witness and run `python3 scripts/source_evidence.py materialize <PASSAGE-ID>`. Read that verified text and enough context to interpret it. Model memory, a search snippet, or a plausible citation is never source evidence. A `bibliographic_span` has no bytes to materialize (`materialize` refuses it): claim from it only after reading the cited pages in the edition itself, never from memory, and its claims carry `witness: "bibliographic"`, so they are shown as not byte-verified.
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
14. **Mathlib for mathematics; no other dependency without an owner decision.** Mathlib is an approved dependency for mathematical content: analysis, order, set theory, ordinals and cardinals, combinatorics. Prefer an existing Mathlib notion over a hand-rolled one. Do not use Mathlib to dress up opaque propositions: importing it adds no philosophical content. A result whose proof uses Mathlib may permit exactly `propext`, `Classical.choice` and `Quot.sound`; a result that does not import Mathlib stays zero-axiom (`docs/axiom-policy.md`). `lean-toolchain` pins the exact Lean version the pinned Mathlib release requires. Any other external Lean dependency still needs an owner decision (#337).
15. **Do not build identity infrastructure early.** No graph database, RDF ontology, embedding-based merger, or canonical-equivalence resolver until the corpus creates a concrete need. The typed JSON records are sufficient for now.
16. **A transcription is not a proof.** A result whose proof only applies a premise whose consequent already is the advertised conclusion (`exact hBridge ⟨…⟩`), or whose atoms are opaque `Prop`s that nothing constrains, certifies only that "therefore" was transcribed. Such a result may still be recorded as a faithful map of a source argument, but the PR and the result record's description must call it a transcription. It does not count as progress on the case and closes no frontier node by itself (see `docs/systematic-corpus-loop.md`). The one exception is closure carried through it: a transcription closes its conclusion exactly when **every** premise of its argument is already closed—self-evident, alternatives all refuted, the conclusion of a non-transcription result, or itself closed by this same rule (computed as a fixpoint; owner decision on #143, 2026-10-24). A transcription with any open premise, such as an open `A ∧ B → C` bridge, leaves its conclusion open. Where the philosophy has internal structure, formalize that structure with typed vocabulary (beings, respects, causes, sentences, …) so the conclusion is *derived* and the result could have failed. Likewise, a hand-rolled substitute for a notion Mathlib already provides (for example "eventually constant" in place of convergence, or a bespoke ω+1 in place of an ordinal or order embedding) needs a stated reason in its doc comment.
17. **Compose, do not restate.** Build on earlier results by importing their Lean modules and using their theorems. Do not restate a proved conclusion as a fresh premise. Reuse shared typed vocabulary where meanings coincide (invariant 7); a new per-file `…Reading` vocabulary for a concept the corpus already has needs a stated reason.
18. **Source kinds are frozen.** After `media_span` (#152), `web_snapshot` (#154) and `bibliographic_span` (#378), add no new source kind without an owner decision. A `bibliographic_span` is the last resort: allowed only for a copyrighted work when no pinnable witness (git text, public-domain edition, `web_snapshot` of a legitimately hosted copy) exists, with a `why_bibliographic` note; upgrade it to a pinned witness when one becomes available. When not even a bibliographic citation can be read and given, keep the claim as a candidate marked as waiting for a witness, and continue the reasoning with its statement as an explicit open premise. Sourcing must not block reasoning, and reasoning must not fake sourcing.
19. **Formal Logos is self-sufficient.** Do not add runtime or CI dependencies on other repositories (historical-source-atlas, worldview-lab, solver services, …). Use one only for a concrete node that is blocked without it, and pin it like a source.

See `docs/corpus-model.md` and `docs/source-evidence.md` for the entity and verification boundaries. For the campaign to formalize the case for Catholicism (epic #143), including the owner's binding principles and the working method, read `docs/catholic-case.md` first.

## Lanes and shared files

Work runs in parallel lanes (#416). Each lane owns directories and the corpus records about them:

- **Lane A — Fourth Way and attributes:** `TruthCore/Latin/`, `TruthCore/Case/` (stages 1–2), `TruthCore/Results/Aquinas/`, `TruthCore/Results/Case/` (stages 1–2), and their corpus records.
- **Lane B — stage 3:** `TruthCore/History/`, `TruthCore/Greek/NewTestament/`, `TruthCore/Case/Catholicism/StageThree/`, `TruthCore/Results/Case/Catholicism/StageThree/`, `TruthCore/Results/Comparison/Resurrection/`, the module `TruthCore/Comparison/Resurrection.lean` (in lane C's `Comparison` area, so a new sibling module there is a cross-lane edit), New Testament and Church sources, and their corpus records.
- **Lane C — everything else, and the single writer of tooling:** CI, `AGENTS.md`, `scripts/`, the explorer, and all other `TruthCore/` areas.

Rules:

- Edit outside your lane only where the work needs it (for example a shared definition or disambiguation such as `DISAMB-MOTION`), keep that edit minimal, and list every cross-lane file in the PR description.
- Merge `origin/main` into your branch right before every push, then rerun the generators below and only checks whose evidence the merge invalidates. Reuse evidence for unchanged inputs; final CI covers the delivered revision.
- Shared tables and import lists are generated, never hand-edited. Lean imports: `scripts/root-imports.sh --write` (each area has its own aggregator under `TruthCore/Imports/`; `scripts/root_imports.py` lists the areas finer than one top-level directory). Docs tables and lists: add one entry file (for example `docs/decisions/<date>-<NN>-<slug>.md`) and run `python3 scripts/docs_index.py --write`. CI rejects stale output of both. After a merge conflict in a generated file, take either side and rerun the generator. A row or list item that a branch from before #416 added by hand must first move into an entry file: the generator keeps only entries.

See `docs/systematic-corpus-loop.md`, "Parallel lanes".

## One atomic work item

For each substantive reading or argument, apply the relevant steps below. Steps 1, 3's attribution requirements and 4 apply when publishing a source-derived claim. For an analyst formulation, start with reuse and a faithful explicit reconstruction; do not make source acquisition a prerequisite. All applicable formal certification and review gates still apply.

### 1. Research from verified source evidence (attributed work only)

- Resolve the passage to a `corpus/passages/` record. Its source snapshot must name the exact edition URN, repository, immutable revision, file path, Git blob SHA, source URL, language, and license. Where no such witness exists, a `web_snapshot` pins a web page by hash instead; claims on a translation carry `basis: translation`. Only for a copyrighted work with neither, a `bibliographic_span` cites the edition by page, and its claims carry `witness: "bibliographic"` (see `docs/source-evidence.md`).
- If no passage witness covers the range, add one from a stable primary-source edition before creating any claim.
- For a pinned witness, run `python3 scripts/source_evidence.py materialize <PASSAGE-ID>` and read the materialized text plus enough context. For a `bibliographic_span`, read the cited pages in the specified edition instead; it has no materializable bytes.
- Preserve the conventional classical locator and CTS identity. The conventional locator remains the human citation; the pinned witness makes the consulted bytes reproducible.
- Record a concise paraphrase rather than copying long translations into the repository.
- Identify one atomic source reading or argument.

A worker may use catalogs, translations, commentaries, or search for orientation, but those do not substitute for reading the materialized primary-source witness used by the claim.

### 2. Check reuse

Search `corpus/statements/` and `TruthCore/` for existing propositions and concepts that may express the same thing. Reuse a statement ID only after checking meaning, not merely similar names. When uncertain, preserve separate statement identities; equivalence can be related later.

### 3. Register the proposition and, where applicable, its source reading

- Add the smallest Lean declaration that captures the proposition when a Lean declaration is appropriate.
- Put interpretation notes in the Lean doc comment; include a source locator only for an attributed reading.
- Add/update an independent `corpus/statements/*.json` record for the proposition.
- For an attributed reading, add/update the corresponding `corpus/claims/*.json` record linking the source reading to that statement. For an analyst formulation, record its interpretation and explicit assumptions without inventing a claim or passage.
- For an attributed claim, ensure its `source_id` and `locator` resolve to exactly one pinned passage. `target/release/truth check` rejects missing or ambiguous passage evidence.
- Link the senses of load-bearing terms through `definition_ids` and `disambiguation_ids`. When a term or reading choice has no record yet, add a `corpus/definitions/` or `corpus/disambiguations/` record (see Review guidelines and `docs/corpus-model.md`).
- If another reading is also defensible, create a sibling claim with the same source locator and an `interpretation_of` link. Do not use that link to imply statement equivalence.

### 4. Critique fidelity (attributed work only)

Before proving anything, explicitly ask:

- Is the formal statement stronger than the source?
- Is it weaker in a way that removes philosophically relevant content?
- Did a natural-language relation get replaced by a modern notion with different semantics?
- Did quantifier scope, modality, time, identity, or causation change?
- Does the cited locator genuinely support this reading when inspected in the pinned passage and its context?

If the answer is materially uncertain, preserve alternatives rather than silently selecting one. A green source-evidence check cannot answer these interpretive questions for you.

### 5. Create an argument only when there is an argument

A source claim need not have a proof: it may simply be a commitment attributed to a text.

When statements are meant to support a conclusion:

- ensure every premise and conclusion has its own statement record;
- add one or more `corpus/inferences/*.json` records for the logical steps;
- add a `corpus/arguments/*.json` record composing those steps;
- add `Challenge.lean` containing the exact advertised theorem with `sorry`; it stays an ordinary (non-module) file;
- add a separate `Solution.lean` containing the same theorem and a real proof;
- write the new `Solution.lean` and every new vocabulary file as a Lean module: a `module` first line, `public import` for each import and `@[expose] public section` after the imports and module docstring (`python3 scripts/convert_to_module.py convert <FILE>` converts an ordinary draft). Every library file is a module, so this always applies; CI (`python3 scripts/convert_to_module.py check`) rejects an ordinary library file other than a Challenge or an aggregator (owner decision on #986);
- run `scripts/root-imports.sh --write` so the generated aggregator of the module's area (`TruthCore/Imports/<Area>.lean`) imports every new module (except `Challenge.lean`) in sorted order; `TruthCore.lean` imports only the aggregators and changes only when an area appears. Aggregators and the root are generated as Lean modules (`public import`) while every file they import is a module (#986); never hand-edit them;
- add a `corpus/results/*.json` verification record that points to the argument;
- add a Comparator JSON config naming the theorem and permitted axioms.

Scoped assumptions and discharged assumptions belong to inference records. They are not ordinary established corpus premises.

### 6. Handle missing premises correctly

If a Solution cannot be proved from the advertised premises:

- do not change the frozen Challenge, silently add an axiom, strengthen a definition, or broaden an existing source claim;
- test for a countermodel or a useful alternative configuration and record the unresolved inference;
- when a stronger commitment is worth exploring, register a separate candidate/configuration with that assumption explicit and compare its consequences; source research is required for attributed claims, not for every stipulated framework branch.

### 7. Verify the three boundaries

Run the applicable gates for the delivered change. The following commands describe formal/corpus verification coverage, not duplicate
local runs for every worker and coordinator. Reuse completed evidence; final CI
provides the integration checks. Run a check locally when development needs it
or a relevant change or failure invalidates its earlier evidence:

`truth` is the repository's Rust CLI (`truth/README.md`): build it once per
clone with `cargo build --locked --release -p truth` (rerun after Rust source
or Cargo input changes) and run it from the
repository root. It is the only implementation of the corpus commands
(`check`, `frontier`, `frontier-diff`, `thickness`, `next`, `related`,
`dossier`, `context` including `--proof-use`, `bind-check`,
`unused-premises`, `lean-reuse`, `attribution-check`, `configurations`,
`configuration-report`, `models`, `strength-comparisons`, `strength-report`,
`structure`, `structure-report`, `issues`, `senses`, `index`, …);
`scripts/corpus.py` was retired (#954 R2/R3). A statement root is
`--frontier-root`. Rust `--root PATH` selects the input repository;
`--json` selects machine-readable output, including frontier reports usable by
`dossier` and `context` via `--frontier-json FILE` on the same inputs.
`frontier-diff`, `thickness --base` and `orphans --base` judge the base
revision's committed corpus and Lean sources by the running binary's rules
(owner decision 2026-11-16, "head rules on base data"), so a PR that changes
the frontier rules shows that change in its delta.

```bash
lake build
target/release/truth check
python3 scripts/bundle_audit.py
target/release/truth bind-check
scripts/verify-result.sh <RESULT-ID>
```

`bundle_audit.py` runs offline. Run it whenever you edit an argument bundle or a definition its audit pins by hash: CI runs it right after `truth check`.

`truth bind-check` (after `lake build`) reads each result theorem's type and checks that its `Prop` hypotheses are exactly the argument's premise statements and its result type is the conclusion statement, matched by `lean_declaration` head constant; type and vocabulary parameters are not premises. A hypothesis whose head is a theory definition (`TruthCore.Comparison.*`) is a theory bundle: it is unfolded one step and split on `∧`, and each conjunct must bind to a listed premise, covering them exactly. A conclusion that is a theory definition is a consistency claim: its argument must list `commitment_statement_ids` (and may then have no premises), and these must match the conclusion's conjuncts in the same way. Keep non-theory conclusion propositions outside `TruthCore.Comparison`. During development, `truth bind-check --result <ID>` (repeatable) or `--affected --base <BASE>` binds only the named or affected results and needs only their Solution modules built; the full `bind-check` (CI) also checks stale pins and registered models. `truth check` includes the offline manifest and claim-binding validation of `source_evidence.py check` (rule for rule, `truth/src/check.rs`), so the separate command is no longer a required gate. Selected passage materialization checks acquired bytes against their pins; it is not a recurring repository gate. Source fidelity remains a research/review judgment. Lean/Comparator verifies only the formal consequence.

Do not call an argument mechanically verified unless its result passes Comparator. CI also runs an independent no-`sorry` NanoDa check: over the whole built library on `main` pushes, nightly and manual runs, and on a PR over the modules its diff can affect (changed modules and their reverse dependents; `docs/axiom-policy.md`), so a failure a PR's scope missed still turns the next `main` run red.

### 8. Self-sweep before requesting review

Before requesting `@codex review`, apply the Review guidelines below to your own diff in one pass and fix what you find. For research PRs, also go through the [recurring semantic defects checklist](systematic-corpus-loop.md#recurring-semantic-defects-pre-push-checklist). An automated review does not replace the independent semantic challenge. A research thread does not leave a draft PR without either that challenge or a handoff naming it as pending.

- every "read as" or attributed claim states no more than its cited sentence; any strengthening is stated as an explicit, unattributed open premise;
- **attribution self-check (#989), before the first push** (CI runs the same check on every PR): run `target/release/truth attribution-check --base <merge-base>`. This offline check prints each new or changed stating claim (or claim whose statement text changed) beside its locator and any usable cached passage text; absent or stale text is reported as not checked, and it fails until the claim records `"attribution": "The passage states X, which is the premise."` Check quantifier scope, species/genus restriction (one kind of cause or being read as all), and temporal and modal scope. If the sentence would be false, because the passage only bears on the premise or states something narrower, do not keep the claim as stating. Replace it by a `supports` relation with a gap note (#987), or state the narrower reading as its own statement;
- every load-bearing term on a root path links a definition through `definition_ids`;
- every ambiguous term links a disambiguation through `disambiguation_ids`.

**Claim vs type.** Most review P1s are prose saying more than the bound Lean type certifies. For every statement, argument or result the diff adds or changes, write in the PR body the prose next to the Lean type (statement paraphrase, claim interpretation, inference/argument `meaning`, result `description`, Lean doc comments, docs) and check:

- quantifiers and scope: "no", "not every", "some", "for all", "exists" (`¬ ∀` is not `∀ ¬`);
- modality and time;
- existence of a witness versus properties of the particular witness (a theorem about some model does not give the model's incidental properties);
- every hypothesis of the theorem is listed as a premise (including nonemptiness or satisfiability side conditions, so that no result is vacuous);
- conditions in the source (same-sense cause, restricted domain, "in any respect") survived into the Lean type;
- any condition added is not attributed to a source that does not state it; it is an explicit, unattributed open premise.

Each PR also reports its intended and actual change in root-path open premises, including "no change". The actual change is computed, not hand-written: link or paste the output of `target/release/truth frontier-diff --base <merge-base>` (conditional support bundles added or removed when comparable and reaching-root premises added, removed, or moved between bare, supported, stated and closed), which CI prints to the job summary for every PR. Report the identities and status changes of relevant premises, not their aggregate counts. Route costs follow the [per-route open-premise cost rule](corpus-model.md#premise-program-and-frontier) (`frontier --routes`): they diagnose an expanded proof, **not research progress**. A premise is established when it is self-evident with a met floor basis, defended (every recorded rival refuted by a verified refutation whose premises are all established, recursively and without circularity, #999), or derived from established premises; a stated or supported premise stays one leaf until it is established, so adding a derivation under it never raises a route's cost, while a derivation under a bare premise, or a new intermediate step, may raise it.

## Review guidelines

Every code review (including `@codex review`) has one more job besides finding bugs: the reviewer must try to **understand and accept** each proof the change presents. The repository, not the reviewer's background knowledge, has to make the proof convincing. Apply this to every result, argument or statement that the change adds or modifies and that lies on a path to a root (`target/release/truth frontier --reaching-root` lists the root paths; `STMT-CATHOLICISM-TRUE` is the default root). For each one:

1. **Restate it.** In a few sentences, say what the argument concludes, from which premises, through which steps, and which Lean theorem binds it (`corpus/results/*.json` → `theorem`; the Challenge module freezes its type). Then say whether you accept that the conclusion follows, on the evidence in the repository: the Lean statement, the premise statements and their claims, and the definitions below. Lean checks consequence; you check that the Lean statement says what the prose and the source claim say.
2. **Find the definition of every load-bearing term.** List each term whose meaning the conclusion depends on (for example *being*, *act*, *potency*, *cause*, *per se*, *maxime ens*, *God*, *true*). Locate its definition: a `corpus/definitions/*.json` record (`DEF-…`) linked from the statement, claim or argument through `definition_ids`. A definition is either sourced (its `claim_ids` point to the claims whose pinned passages give it) or stipulative (its `note` says why, and what would source it). Check that the definition matches the Lean declaration it names and the way the statement uses the term.
3. **Find the disambiguation of every ambiguity.** Where a term has more than one sense, a reading choice is made, or two premises could use a word differently, locate the `corpus/disambiguations/*.json` record (`DISAMB-…`), linked through `disambiguation_ids` or reached because a linked definition is one of its `sense_definition_ids`. Check that its `resolution` says which sense each use takes and why the argument does not pass from one sense to another.
4. **Report gaps by severity.** Each finding must say exactly what is missing (the term, the statement or argument ID, and what a definition or disambiguation would have to say). Each of the following is a P1 finding:
   - a load-bearing term with no definition record at all, or with a definition that is wrong in a way that changes what is proved (it does not match the Lean declaration or the statement's use);
   - an ambiguity, equivocation risk or reading choice with no disambiguation, or whose disambiguation does not cover this use;
   - a reading step that is not stated: the prose or claim says more or less than the Lean statement, and no record says which reading is formalized;
   - a gap between the Lean statement and its prose paraphrase or its source claim (quantifier scope, modality, time, identity, causation, or a parameter the prose treats as defined);
   - any proof, prose or record that claims more than its source or its Lean theorem supports.

   A missing `definition_ids` link is P2, not P1, when the term already has a correct definition record, or when the gap is covered by the definition-coverage issue #216. Report all such missing links in one finding per review, not one per cycle.

   If you would write "this depends on what is meant by …", the repository is missing a definition or a disambiguation: report that as P1 instead of guessing the intended sense. Do not report as P1 that a premise is open or that you doubt its truth; open premises are the frontier and are allowed. Report only what stops you from understanding and accepting the step as presented.

5. **Report everything in one pass.** Report every finding you can identify in a single review, grouped by kind (overstated or unstated readings, missing definitions, missing disambiguations, Lean/prose gaps, other bugs). Do not stop at the first finding. Before finishing, re-check every attributed claim and every `definition_ids` and `disambiguation_ids` link in the diff. Handling is unchanged: P1s that overstate a proof are fixed in the PR; P2s and coverage gaps go to #216 or a follow-up issue.

`target/release/truth check` enforces the mechanical part: every `definition_ids` and `disambiguation_ids` entry must resolve, a sourced definition needs known claims, a stipulative one needs a note, a disambiguation needs at least two known senses, every definition must be used, an argument whose conclusion, premises or commitments use two senses of one disambiguated term must link that disambiguation, and every `STMT-`, `DEF-` or `DISAMB-` id cited in their prose must exist. It cannot tell whether a term *should* have been linked; that judgment is this review's job. The explorer shows the terms on each statement, claim and result page and lists them all at `/definitions`.

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
- **IDs are permanent UUIDs; legacy aliases never change.** Labels may be improved at any time; docs/notes/label-cleanup.md lists the mechanical labels to fix, and that list may only shrink (#1233).
- An in-flight branch with readable-id records converts by merging `origin/main` and running `python3 scripts/migrate_uuid.py --write` (docs/notes/uuid-migration.md).
