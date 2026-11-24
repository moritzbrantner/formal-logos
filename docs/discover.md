# Discovery engine

`truth discover` searches for new logical relationships between corpus
propositions (#1784). For each target statement it retrieves candidate
premises, asks Duper whether they prove the target over the statements' own
Lean declarations (the tactic portfolio of `truth prove-sweep` first, then
Duper), minimizes and filters what it finds, and re-checks every
surviving proof from its text. It also reports, for goals it cannot prove, the
exact missing bridges between vocabularies that would close them. It is a
search helper: the Lean kernel is the authority, and a discovery is a
conditional support option for review, never a corpus record by itself.

```bash
flock /tmp/moenarch/truth-core-heavy.lock \
  target/release/truth discover --targets open-root --module TruthCore.Causality --limit 40
target/release/truth discover --target STATEMENT --premise-pool all --candidates 10
target/release/truth discover --target STATEMENT --premise PREMISE_1 --premise PREMISE_2
target/release/truth --json discover --targets next-tests --zipperposition ~/.cache/agent-work/bin/zipperposition
target/release/truth discover --target STATEMENT --write-spec specs/discover-causality.toml
```

## Pipeline

1. **Targets.** `--target STATEMENT` (repeatable), `--targets open-root` (the
   open premises that reach the root) or `--targets next-tests` (the leaves
   of the frontier's next steps). `--module PREFIX` keeps the targets and
   candidates whose `lean_declaration` starts with the prefix; `--limit N`
   caps the targets.
2. **Premise pool.** `--premise-pool closed` (default: closed or established
   in the frontier), `proved` (also conclusions of verified non-transcription
   results) or `all` (every statement with a Lean declaration: the discoveries
   are then conditional on open premises). Premises are always existing
   corpus statements: nothing else enters a goal as a hypothesis.

   **Exact bundles.** Repeated `--premise STATEMENT` selects the complete
   input bundle for every selected target, including open premises. IDs,
   legacy aliases and labels resolve to canonical IDs; duplicates are removed
   in first-supplied order. This mode bypasses the pool, retrieval ranking and
   candidate cap. It never adds a registered bridge automatically: name a
   bridge with another `--premise` when it is part of the intended bundle.
   `--module` still filters targets, but does not remove an explicit premise.
   `--premise-pool` and `--candidates` are rejected in this mode, as are empty,
   unknown or undeclared premises and a target included as its own premise.
   A declared premise missing from the built library is an error, not a
   skipped goal. The same binding, search, minimization, weakening, filters,
   certification and spec generation below apply; minimization may remove a
   redundant premise, and weakening produces separately labelled trials.
3. **Retrieval.** `scripts/StatementConstants.lean` exports every
   declaration's parameter names and the project constants it mentions,
   closed transitively. A candidate must share project vocabulary, a
   definition or an authored sense (below) with the target, and have a
   parameter that can join one of the target's: the same name, a projection
   (below) or the same whole-binder sense tag. A shared parameter name alone
   never admits a candidate. It is ranked by the share of its parameters the
   target also has (type fit), the share of its vocabulary the target uses
   and of the target's vocabulary it uses, shared `definition_ids`, the same
   module and a `strengthens` relation with the target. The vocabulary is
   the project constants together with the senses the whole binders are
   tagged with (parameter-level sense tags, below): a relation binder such as
   `MoreIn : B → B → R → Prop` mentions no constant, and its authored sense
   says which concept it expresses, as a constant would (#1845). Tags are
   read, never inferred: an untagged binder contributes nothing, and a
   partial-application tag (`CausesIn _ _ esse`) neither admits nor fits.
   A candidate parameter that shares no name with the target's but is
   a structure with a field of a target parameter's type (`m : Profile W B`,
   whose `m.ontic : Ontic W B`, against `o : Ontic W B`) counts toward the type
   fit, adds the same bonus as a strength order (the structure's other fields
   otherwise dilute its constant overlap) and admits the candidate, since the goal builder may bind through that
   projection (step 4); the export lists each parameter's type head and, for a
   structure, its fields' type heads. A projecting parameter that the
   candidate uses *only* through fields of the target parameter's type
   (`OnticFrameKT (m : Profile W B) := FrameSatisfies .KT m.ontic.frame`
   uses `m` only through `ontic`) makes the candidate a statement about that
   field's value: the structure's other fields are no part of it, so their
   vocabulary, which still dilutes the overlap, says nothing against it, and
   it gets the same bonus once more (`binder_uses` in the export, #1845).
   The best `--candidates N` (default 8) form the goal. When the target
   and a candidate carry different senses of one term (parameter-level sense
   tags, below), the registered bridge statements for those senses join the
   goal as optional premises, reported as such.
4. **Goal.** `scripts/Discover.lean` builds
   `∀ params, P₁ → … → Pₙ → T` from the declarations themselves. Each
   premise parameter is identified with an outer one of definitionally equal
   type when it is an instance (by type or synthesis), or when it has the same
   name *and is declared in the same module*, or is tagged with the *same
   sense*. Nothing is identified by name across modules: a carrier
   (`B : Type`) may range over beings in one module and sentences in another.
   One reported fallback: a carrier or structure bundle (`h : History W B T`)
   of the same name and type in another module is identified and listed in
   `domain_identified_by_name`, because no cross-module goal could otherwise be
   stated until carriers are tagged. Such a goal is filtered
   (`domain_by_name`), kept out of `--write-spec` drafts and listed as needing a
   sense tag or a bridge; its missing bridges carry the same flag. The flag is
   recomputed among the retained declarations (the minimal premises and the
   target, or a bridge's used premises, the target and the declarations of
   its assumed elements): two retained declarations of different modules that
   share a binder only through a dropped declaration still share it by name.
   The text report prints these qualifications, and a bridge's assumed
   elements, under each ranked bridge. Every other
   parameter becomes a new outer binder, so the theorem stays universally
   quantified, as a result theorem's binders are. A universe-polymorphic
   statement is taken at the lowest universe that keeps each carrier a type
   (a specialization, so the theorem stays valid).

   **Projection binding.** When the goal fails, a target binder may be the
   field of a premise's structure binder: `OnticTSchemaValid (o : Ontic W B)`
   against `OnticFrameKT (m : Profile W B)`, where the intended theorem is
   `∀ m, OnticFrameKT m → OnticTSchemaValid m.ontic` (#1819; proved by hand in
   #1827). Each target binder that is a value (an element or a structure) is
   paired with each non-instance premise structure binder that has a field of
   definitionally equal type, and the goal is searched again with the target
   binder replaced by that projection (at most four choices; each failed choice
   costs one more full search, so a goal with four choices may take up to five
   times as long). Instances, carriers, predicates and functions are never
   projected, also behind a definitional alias (`def Pred B := B → Prop`,
   Mathlib's `Set B`): binding `R := b.Q` would equate two relations by type
   alone. The binding is explicit and never silent. The choice that closes
   the goal is reported as `projection` and as `bound_to` on the binder, a spec
   draft states it in the argument's `meaning`, and an unresolved goal lists
   the choices it tried (`projections_tried`). A goal closed under a projection
   is a *specialization* of the target statement to that projection, not the
   statement over an arbitrary binder. Three outcomes are distinguished:
   a unique choice is flagged `projection_binding` (informational); a target
   binder with more than one candidate projection (two fields or two
   structures of its type) among the premises minimization keeps is rejected
   as `projection_ambiguous`, since picking the first that closes the goal is
   identification by type alone (an alternative that only a dropped premise
   introduced is no part of the theorem: it is listed as
   `dropped_alternatives`, #1845); and a
   choice whose structure premise minimization drops (the target then follows
   from other premises about the projected field alone) is rejected as
   `projection_unused`, reported only when no other choice succeeds. Rejected
   goals stay out of `--write-spec` drafts.

   **Term binding.** A target binder may instead stand for a structure that a
   premise *builds* from outer binders with a project definition: the frame
   adapter `groundProfile F concrete G`, which `ActualRootsWithholdEachGrounded
   F concrete G w` applies to its own binders, against the target
   `NecessaryActualConcretaAreRoots (m : Profile W B) w` (#1926). After the
   projections, each closed application of a project definition (not a
   projection) in a delta-expanded premise whose type is the target binder's
   is tried as the same kind of explicit choice, for a target binder of
   structure type only: reported as `projection` with
   `term` and `bound_to`, a specialization of the target to that term, under
   the same `ambiguous`, `dropped_alternatives` and `projection_unused` rules
   (a term is "used" when a minimal premise still builds it; the four-choice
   cap counts both kinds). Nothing else is unified: an element binder such as
   `w : W` is never bound to a term (binding it to `pick W f v`, which a premise
   `P (pick W f v)` builds, would relabel the premise's instance as the
   target), and binders of different modules still need a sense tag (step 4).

   Same-module identification compares the binder names the declarations
   *declare*: an outer binder renamed on entry (`w_3`, because the target
   already has a `w`) is still joined by a premise of its own module whose
   binder is `w` (before #1926 the renamed binder matched nothing and the
   premise got a separate `w_4`).
5. **Search.** The hypotheses and the conclusion are delta-expanded through
   every project definition whose type ends in `Prop` (not projections or
   instances). The tactic portfolio of `truth prove-sweep`
   (`PORTFOLIO` in `truth/src/prove_sweep.rs`: `decide`, `omega`, `tauto`,
   `simp_all`, `aesop`, `grind`, `unfold+grind`, `unfold+aesop`, with its
   `prove_sweep_unfold` step) runs first, each tactic under prove-sweep's
   budget (raw `maxHeartbeats` 20000; the configuration carries the list and
   budget, read from that one source, not restated). Then `duper [*]` runs
   under `--heartbeats` (thousands, default 100000, shared by Duper's
   portfolio). A portfolio proof is an ordinary kernel-checked proof term and
   goes through everything below exactly as Duper's: minimization (each
   deletion tries the portfolio, then Duper), the incompatibility core,
   probe, witnesses and certification; the prover is reported as
   `portfolio:<label>`. Unlike `duper [*]`, which sees only the goal's
   hypotheses, a portfolio tactic can reach the imported library: `@[simp]`
   and `@[grind]` lemmas, `aesop` rules, instances. Whatever the route, the
   proof term names what it used, and the check is on the term: a closed
   attempt that rests on a project (`TruthCore.`) constant whose type is a
   proposition (a theorem, a Prop-typed definition such as `abbrev alias :=
   @lemma`, an opaque or an axiom) and that is no part of the statement's own
   vocabulary (its constants closed through definition values) is discarded
   and listed under `outside_bundle_rejected` with the constants it used.
   Auxiliary lemmas the tactic created (`_proof_N`, `_auxLemma`, `_simp_N`,
   also private) are read through; an auxiliary of the library itself is
   reported. Exempt are only generated lemmas of the right kind: equation
   lemmas (`eq_N`, `eq_def`, `eq_unfold`) of a definition and `inj`, `injEq`,
   `sizeOf_spec` of a constructor; a hand-written `@[simp] theorem f.inj` and
   every `ext` lemma are premises. Bridge checks stay Duper-only. When that fails and the goal
   reaches a definition of a value (its type ends in a value type such as
   `Formula Unit`, not in `Prop` or a `Sort`: `convergenceFormula`,
   `Formula.iterBox`), Duper is tried once more after rewriting those
   definitions by their defining equations (`simp only [...] at *`, prover
   `duper+equations`): delta-expansion leaves a closed computed term such as
   `convergenceFormula 1 0 1 1`, built by recursion, unevaluated, and no
   prover reads it; its equations evaluate it to constructor form, and fire
   on a recursive definition only where its argument is a constructor
   (#1845). The plain attempt comes first, so a proof that treats such a
   definition as an opaque symbol is kept; the fallback costs at most one
   more search per attempt, and a definition by well-founded recursion whose
   equations keep rewriting only exhausts that attempt's heartbeats. The
   outcome lists the delta-expanded definitions as `unfold` and, when the
   closing proof needed them, the rewritten ones as `equations`. With `--zipperposition PATH` (or
   `TRUTH_ZIPPERPOSITION`) lean-auto is tried next, with Zipperposition as
   premise selector and Duper as its native prover; Duper then re-proves the
   goal on the selected core, so the Solution never needs the external prover.
   Every closed attempt is added as a kernel-checked theorem and its axioms are
   collected. `--batch N` targets share one Lean process (default 6), `--jobs N`
   processes run at once (default 2). Run it under the heavy-job lock.
6. **Minimization.** The premises the proof term uses are kept; then each is
   deleted in turn and the goal searched again. A deletion that fails leaves
   the premise as needed *within the budget*: that is not a proof that it is
   needed. A one-point omission model (below) certifies that a premise is
   needed when one exists.
7. **Weakening.** For each premise of a discovery with a weaker strength
   sibling (`strengthens`), the goal is searched again with the weaker version.
   Originals and weakenings are both certified (step 8). Only a weaker
   discovery that passes certification and the axiom check supersedes the
   stronger bundle, which is then reported as filtered (`weakened`); when the
   weaker one fails, the original stays a discovery, flagged with the reason
   (`weakening_rejected`).
8. **Certification.** Each discovery is rendered as plain theorem text
   (binders with full names, hypotheses, conclusion, `delta …; duper [*]`;
   when the fallback closed the goal, `delta …`, `try simp only […] at *`,
   `all_goals duper [*]`; for a portfolio proof, `delta …` and the
   portfolio tactic with its `prove_sweep_unfold` step stated as the explicit
   `delta` of the definitions that step unfolds (`sweep_unfold` in the
   outcome; the step is dropped when there are none); the statement itself
   unchanged) and elaborated in a separate Lean run with `#print axioms`. The
   Solution draft states the same text, so neither declares tactic syntax
   that could clash with prove-sweep's scratch tactics where the module is
   imported; a replay that differs from the search fails closed. The file also
   defines the search's `#discover_external` command (in a `section`, so its
   `open`s do not reach the theorems), which runs after each theorem. A discovery whose text fails, whose proof uses an
   axiom other than `propext`, `Classical.choice` and `Quot.sound`, or whose
   re-elaborated proof rests on a project theorem outside its bundle is
   filtered (`certification`, `axioms`, `outside_bundle`).

## Filters

| Filter | Rejects when | Kind |
| --- | --- | --- |
| `known` | the target follows by composing verified arguments from the minimal premises (forward-chaining closure; covers supersets of an existing argument's premises). A proof that uses `Classical.choice` has excluded middle without a premise stating it: an argument that lists excluded middle (`ee4ab504`, the one recorded logical-background statement, `CLASSICAL_BACKGROUND`) as an explicit premise matches when its other premises are among the found ones (#1845) | reject |
| `implicit_excluded_middle` | the `known` match above needed excluded middle, which the classical proof supplied implicitly; the report says so | flag |
| `transcription` | one premise application closes the folded goal (the `truth prove-sweep` probe, invariant 16) | reject |
| vacuity | `False` follows from the minimal premises over their own binders only (no element or instance borrowed from the target or a dropped premise): reported as an **incompatibility** (the inconsistent core, minimized), never as support; filtered (`axioms`) when a contradiction proof uses an axiom outside the three allowed | separate kind |
| `literal_negation` | the inconsistent core is a premise and its literal negation: one member's declaration unfolds definitionally (delta, default transparency) to `¬` the other's, as `ActNotPriorInTime F := ¬ ActPriorInTime F` does, recorded rivals included. Such a core is inconsistent by construction, neither an incompatibility nor support, and its goal is not counted as proved. A contradictory pair that takes logic to recognize (`∀ y, S y` against `∃ y, ¬ S y`) is not literal and stays an incompatibility | reject |
| `known` (incompatibility), `duplicate` | the inconsistent core contains recorded rivals (`alternative_to`, `attacks`); or an earlier goal already found the same core | reject |
| `senses` | the argument uses two senses of one term (`argument_term_senses`, the check `truth check` applies) and neither a premise nor the conclusion is a registered bridge between them. Whatever role a bridge was registered with, it bridges as a premise when it is one, and as the conclusion when the argument concludes it (it then derives the bridge, `role: "conclusion"`), as `truth check` accepts (#1845) | reject |
| `domain_by_name` | a carrier or structure bundle was identified with one of another module by name only | reject (listed as needing a tag or bridge) |
| `sense_bridge` | a premise is the registered bridge between the senses it mixes | flag |
| `projection_binding` | the goal closed only with a target binder bound to a premise structure's field (step 4) | flag |
| `projection_ambiguous`, `projection_unused` | the projected target binder had another candidate projection (identification by type alone); or minimization dropped the premise that introduced the projected structure (step 4) | reject |
| `witness` | no one-point joint model was found; Duper found no contradiction, so consistency is unresolved | flag |
| `vacuous_target` | the premises refute the target's own antecedents (`∀ x, A x → B x` holds because nothing is `A`): valid, but true vacuously | flag |
| `axioms`, `certification`, `reconstruction` | an axiom outside the three; the theorem text fails; Duper did not reprove an ATP-found goal | reject |
| `outside_bundle` | the certified proof rests on a project proposition outside the statement's vocabulary (a library lemma, rule, instance or Prop-typed alias a portfolio tactic used; step 5) | reject |

The joint witness interprets every carrier as `Unit`, every predicate (and
predicate-valued structure field) as a constant `True` or `False`, structure
binders by their constructor and other values by `default`, and closes the
instantiated premises and conclusion by `simp`/`decide`, kernel-checked; a
model whose proof uses an axiom other than the three allowed (say, through an
imported `sorry`-dependent simp lemma) is not reported. It
tries all-`False`, all-`True` and each single flip. Such a model may be
trivial (every antecedent empty); it shows only that the formal premises are
jointly satisfiable. The engine keeps this one-point search; `truth
countermodel` now also reads structure parameters such as the shared frame
(field tables and the anonymous constructor, [countermodels](countermodels.md#structure-parameters)),
so a finite omission model of a recorded result over a frame can be searched
there; the engine does not call it.

Bindings are part of the result. The JSON lists every outer binder with the
declaration and parameter it came from, so a reviewer can see which
parameters were identified.

## Missing bridges

When a goal fails, the engine looks for the exact missing link between the
vocabulary the premises use and the vocabulary the conclusion uses, after
delta-expansion. For a relation `p` used by a premise (a parameter, or a
Prop-valued field of a structure parameter such as `G.GivesAt`) and a relation
`q` used by the conclusion, in both directions, it forms

```text
∀ a₁ … aₘ, p a₁ … aₘ → ∃ (unmatched bⱼ), q b₁ … bₙ
```

matching each argument of `q` to an unused argument of `p` of the same type.
The `fixed` variant, tried first because it is weaker, fixes an argument
whose type has exactly one element parameter occurring together with that
relation (in one hypothesis, or in the conclusion)
(`∀ c x, CausesIn c x esse → CausesIn_2 c x esse_2`).

When the conclusion's antecedent is a conjunction of at least two relations
(`∀ g, Simple g → Perfect g → … → HasWill g → Q g`, or one hypothesis
`A g ∧ B g`), bridges that make one conjunct sufficient
(`∀ g, Eternal g → IsGod σ g`) are formally candidates but philosophically
uninformative. The conjunctive bridge `∀ g, Simple g → … → HasWill g →
IsGod σ g` is tried first instead, once per premise relation outside the
antecedent (at most eight, with their own cap and the full heartbeat budget,
since the long antecedent makes the search heavier), and reported with
`conjunctive: true` and the conjuncts it stands for
(`replaces_single_conjuncts`) (#1819). When one passes, the single-conjunct
bridges are dropped: over the same element each is stronger than it. The
builder matches each argument of the consequent to the first unused
antecedent element of its type, so with several elements of one type it need
not unlock every target a single bridge does. When no conjunctive bridge
passes, the single-conjunct bridges are therefore tried after all others and
reported as `single_conjunct`, ranked last.

A bridge is reported when
the premises with it prove the target, do not prove `False`, and the bridge
alone does not prove the target (it would merely restate it). The proof is
rechecked over the binders the used premises, the bridge and the target
mention only, so it never borrows an element that an unused candidate
introduced (which would hide a nonemptiness assumption); an element that only
the bridge mentions (a fixed argument) is listed as `assumed_binders`. The report
ranks bridges by the number of targets they unlock, then goals, and lists the
premises the unlocked proofs used. Pairs where each relation is used on one
side only come first; at most 48 bridge candidates are tried per goal. A bridge is a **candidate proposition**: a
research question to state, interpret and warrant, never a premise of any
record until it is. A bridge between two parameters of the same name and
type in different modules often asks whether the two declarations use one
sense: tagging both parameters with that sense (below) answers it formally.

## Parameter-level sense tags

A disambiguation sense may list `lean_parameters`:
`[{"declaration": "…", "parameter": "<binder>", "arguments": ["_", "_", "esse"]}]`,
meaning that the binder of that declaration, applied to the positional fixed
arguments if given (`_` leaves a place open), expresses the sense. The engine
uses the corpus reader `truth::parameter_tags` (#1794); an untagged parameter is
unknown. Two binders tagged with the same sense id are identified across
modules; different senses of one term bring in the registered bridge
statements (`sense_bridges` of existing arguments) as optional premises. A tag
with fixed arguments names a partial application (`CausesIn _ _ esse`): it
describes only that application, not the binder at every argument, so it never
identifies two binders. Such binders stay separate outer binders (unless the
same-module name convention identifies them); relating their tagged slices
needs an explicit bridge premise, never a silent identification of the full
relations. Retrieval (step 3) reads the same whole-binder tags: a shared
authored sense admits a candidate and counts as shared vocabulary.

## Output

Text, or `--json`: the options, a summary (targets, goals, proved, minimized,
discoveries, incompatibilities, vocabulary theorems, filtered by filter,
unresolved, errors, missing bridges, seconds), the ranked missing bridges and
one finding per goal with its candidates, minimal premises, filters,
certification verdict and the raw Lean outcome (binders and their origins,
a projection binding choice, deletions, witness, omission models,
`literal_negation`, signature, unfolded definitions). `proved` counts the
goals closed, except those closed only by a literal P/¬P core. A
*vocabulary theorem* is a target that follows from no premise: its
definitions alone prove it.

The options report `premise_selection` as `ranked` or `exact`. For an exact
bundle, `premises` lists the ordered canonical input IDs, while `premise_pool`
and `candidates` are null because no retrieval occurred. The finding's
`candidates` retains that exact input; its `premises` reports what the proof
kept. Adaptive repair does not diagnose a retrieval-cap failure from an exact
bundle's size.

`--write-spec PATH` writes an `argument_batch.py` spec draft with one argument
per discovery (premises, conclusion, the three axioms, `sense_bridges` where a
premise bridges senses, or `role = "conclusion"` where the conclusion does)
and a Solution draft `PATH` with the extension
`.Solution.lean`, in the results module named after the spec
(`specs/discover-causality.toml` → `TruthCore.Results.Discover.DiscoverCausality`).
Move the Solution into place, generate the Challenge and records with the
commands at the top of the spec, and route the batch through the semantic
challenge of consequential bridges and a normal PR. The command never writes
corpus records.

## Capability audit and measured discovery loop (2026-11-24)

This bounded evaluation follows #1784, #1833, #1834 and #1644. It separates
**retrieval** of a complete premise bundle, **binding** of its carriers and
senses, **solver recovery** of the typed implication, and **philosophical
warrant** for its assumptions. A change at one layer does not settle another.

### Capabilities and remaining boundaries

| Surface | What it supplies; what remains outside its result |
| --- | --- |
| `discover`, Duper and lean-auto | Target-relative vocabulary/definition/sense ranking, typed binding, Duper search, equation fallback, optional ATP selection with Duper reconstruction, and separate certification. This evaluation used Duper only; it makes no ATP comparison. The separate [bounded second-hop follow-up (#1929)](https://github.com/moritzbrantner/formal-logos/pull/1929) fills unused slots; full-list premise selection and reliable timeout-versus-saturation reporting remain open. |
| Exact bundles and adaptive repair | `--premise` now reaches the existing engine rather than being silently ignored. Raw `repair/retry` candidates can receive the engine's filters, certification and weakening. A supplied bundle is external premise selection; an oracle identification remains conditional until reviewed. Repeating unchanged inputs supplies no new diagnosis. |
| Minimization, weakening and incompatibility | Failed deletion is not necessity; a certified weaker sibling may supersede a stronger bundle. A nontrivial certified inconsistent core supplies an incompatibility; literal-negation pairs are filtered and neither supplies affirmative support. Independent deletions cannot be combined without checking the retained conjunction; the separate #1925 repair is discussed below. |
| `countermodel` and `prove-sweep` | Checked finite models establish a precise formal non-implication; bounded failure does not establish entailment. The separate [unary-function follow-up (#1930)](https://github.com/moritzbrantner/formal-logos/pull/1930) supports explicit-input, nondependent unary carrier functions; richer function fragments and structure vocabulary still limit extraction. Prove-sweep probes frozen Challenges and possible transcriptions; its closure still needs a real Solution and the normal gates. |
| Target-free pilot | Explicit binder maps and full AND bundles permit checked cross-family conjectures, models and OPEN bridges. Graph-known filtering requires a registered conclusion ID; arbitrary Lean text still needs prior-work comparison. A sufficient bridge is not shown necessary or weakest. An intended root connection remains OPEN until linked; naming a consumer does not connect it. |
| `brief`, `related`, `novelty`, `semantics` | Retrieve prior arguments, assessments, sources, senses and issue history, then expose identification obligations. Relevance is not equivalence, `no-match-found` is not novelty, and a missing snapshot means unknown history. The later independent #1644 tier, not its superseded lexical verdicts, supplies the controls below. |
| Frontier and support | `frontier` identifies consequential obligations; `support-graph` preserves alternative rules, full conjunctions, commitments and cycles. Neither replaces Lean composition or premise warrant. A lower-level derivation can add leaves while improving conditional support options; fewer leaves is not itself a better argument. |

### Frozen comparison and provenance

The [fixed fixture](../scripts/testdata/discovery-benchmark.json) was frozen
before execution, SHA-256
`ffbdb95ca2166b85440c6dfc382f79aa6ebfb0679ccfe91ca9c95b69c45fda56`.
It contains three positive reference cases (A, B, D), negative C, and two
countermodel boundaries that were unsupported at baseline. The frozen fixture
is unchanged; the unary-function follow-up below supersedes one of those
refusals. B is held out from the curation case.
All positive relationships were registered or previously reported; no cited
Solution theorem was passed as a premise or hint. Novel relationships are
therefore **0**, independently of whether a run labels a result `discovery`.

Source snapshots for reproduction are:

- Baseline: `ad4ffa2e5fbd245434f3d4b468f42f2b3f9ffaf2`.
- Exact engine before tags: `2546e8b46c574144be9266ccbb4efbf09082627c`.
- Curated corpus before new support registration:
  `090cb4d2f9cd88788b80a55496f90412e474bc17`.

The last two are content-identical source snapshots of the local captures
`76f23a354a47ae4eea417662e114faedcec34774` and
`4b04b035297321a881edfe1e79921ae5b82b1391`, respectively; they are not the
checkout hashes printed in the original logs. Raw reports, commands, source
and binary identities are retained in the external `discovery-evidence/`
run artifacts. Reproduce on the pre-registration snapshots: after registration,
the new argument can correctly change A's `known` classification.

The frozen budget was CLI `--heartbeats 10000` (the CLI's thousands unit),
`--batch 1 --jobs 1`, no Zipperposition; ranked runs used `--premise-pool all
--candidates 8`. Seconds below are engine `summary.seconds`, including
vocabulary export, search and certification after the library build. Wrapper
elapsed time also includes lock waits and preparation. An initial export
interrupted under runtime memory pressure reached no goal and is unavailable
evidence, not an unresolved proof. The unchanged exporter completed after
the toolchain was moved out of tmpfs; no exporter optimization was adopted.

| Case and input | Reference coverage | Name-only identifications | Outcome at 10000 | Seconds |
| --- | --- | ---: | --- | ---: |
| A: maximality, baseline ranked | 3/3, among 8 candidates | 8 | unresolved | 106 |
| A: exact before tags | 3/3 | 2 | unresolved | 33 |
| A: tagged ranked | 3/3, among 8 candidates | 6 | unresolved | 109 |
| A: tagged exact | 3/3 | 0 | unresolved | 36 |
| B: assertion meaning, baseline ranked | 1/2; assertion witness absent | 0 | unresolved | 99 |
| B: exact | 2/2 | 0 | proved, filtered `known` | 22 |
| C: assertion without meaning bridge, exact | only the occurrence premise | 0 | unresolved; one OPEN bridge | 23 |
| D: well-founded ascent, baseline ranked | 3/5; well-foundedness and EM absent | 0 | unresolved | 105 |
| D: exact | 5/5 | 0 | unresolved; manual reference route exists | 28 |

Positive proof recovery is **0/3 ranked → 1/3 supplied exact**, with no new
discovery at this budget. This measures recovery with externally selected
premises, not autonomous ranking gain. A already retrieved all three reference
premises: its failure is not a retrieval omission. Its two reviewed carrier
tags remove the exact bundle's name-only obligations but do not close it at
10000. B demonstrates a selection gap and correct known-route suppression.
D removes selection uncertainty yet remains a solver limitation on an existing
manual proof, not evidence for another philosophical premise. The reference
coverage counts do not establish that every listed premise is necessary.
The curation adds existing whole-binder Being/Respect tags only to
`SomeBeingMaximalInBeing`; it does not merge maximal, greatest-degree or
strictly-greatest readings or change proposition bodies and source readings.

### Supplemental proof, registration and omission models

After A's frozen-budget failure, a separately labelled pair used
`--heartbeats 100000`, reproducing the historical #1850 budget. Before tags it
proved the implication in 49 seconds and was filtered only by `domain_by_name`;
after tags it was a certified discovery in 48 seconds, retaining all three
premises, no filters and no name-only identifications. Its axioms were
`propext`, `Classical.choice`, `Quot.sound`. These runs do not change the
frozen recovery denominator or establish a runtime improvement.

The bundle for target `4c79298d` is `18561596` (a maximum excludes a distinct
cause of its being), `fad8af3e` (some being is maximal) and `86d02b69` (every
GOD_4 causes every other's being). Given a maximal witness `m`, any GOD_4
`g ≠ m` would cause `m`, contradicting the exclusion; hence `g = m`.
Already reported in #1850/#1860 and the
[adaptive attempt](../corpus/attempts/discover-adaptive-repair-fourth-way-20261122.json),
this route is now registered as
[argument 14cbab05](../corpus/arguments/14cbab05-1f5f-4bbd-8fe7-f3c2b7ac19a5.json)
and [result d377c7c7](../corpus/results/d377c7c7-4d89-45a5-bdf1-d56620b49101.json),
theorem `TruthCore.Results.Discover.GodMaximalFromCauseExclusion.godMaximalFromCauseExclusion`.
Build, bind-check and Comparator with NanoDa passed. The conclusion remains
universal over `IsGod`; it does not assert that God exists. The direct premises
remain open, and deriving `18561596` from `d5a94eb1` retains that shared
dependence. Registration is neither global weakening nor independent corroboration.

An actual `countermodel --all --size 2` run on that theorem Lean-checked:

| Check | Being size | Respect size | What it certifies |
| --- | ---: | ---: | --- |
| Omit `h0` / `18561596` | 2 | 1 | Other premises true, conclusion false |
| Omit `h1` / `fad8af3e` | 1 | 1 | Other premises true, conclusion false |
| Omit `h2` / `86d02b69` | 2 | 1 | Other premises true, conclusion false |
| Joint witness | 1 | 1 | All premises and conclusion true; `IsGod` is false everywhere |

Together with the proof, these omission models establish inclusion-minimality
of **this fixed encoded bundle**, not philosophical necessity or a globally
weakest sufficient bundle. The joint witness establishes formal consistency;
its empty `IsGod` predicate supplies neither God-existence nor metaphysical
coherence. Existing Challenges and the target's 56 result-backed consumers
are preserved, including [simplicity `c473ec4b`](../corpus/arguments/CATHOLICISM-STAGE2-GOD-IS-SIMPLE.json)
and [immutability `38244f91`](../corpus/arguments/CATHOLICISM-STAGE2-GOD-IS-IMMUTABLE.json);
their other premises remain obligations.

**Formal frontier delta:** `truth frontier-diff --base origin/main`, against
`6ecc2d87c3576906cb32ea8dbbca22e7557cce6b`, computes 602 → 603 distinct
verified support alternatives, with one added for `4c79298d`. Open premises
reaching the root remain 581 (430 bare, 92 supported, 59 stated); the lowest
expanded-route cost remains 16, and no bare premise is added. This is one
additional conditional support option, with no premise establishment.
Independent semantic review accepted the complete outcome at
`b396ef0d004daf2bdc5a2f118b8bee3aea5c1506` on 2026-11-24, with no blocking
semantic, mathematical, source-boundary or measurement finding. A redundant
completed task in the handoff was removed; the formal and philosophical
limits above remain part of that acceptance.

### Negative controls, model boundaries and incompatibility

C supplies only `AssertionMade`, without local bridge `42114721`. The engine
proposes `∀ a c, Asserts a c → Meaningful c`, which stays OPEN and is broader
than the existing bridge for the selected claim. It is not shown necessary
or weakest. An actual `meaningFromAssertion --omit hMeaning` countermodel
was Lean-checked with one agent and one content, `Asserts = True` and
`Meaningful = False`. It concerns the formal assertion marker, not an example
of genuinely cognitive assertion without meaning. Prove-sweep closed the full
frozen theorem with `unfold+grind` in 2 engine seconds, with no transcription flag.

Thus actual assertion plus its local meaning requirement excludes
`NoMeaningfulContent`. A rival retaining that denial must contest a premise
or the marker's cognitive interpretation; this yields no truth, knowledge or
God inference. The model distinguishes the missing assumption; proof-search
failure by itself did not do so.

| Countermodel request, bound 2 | Historical baseline finding | Follow-up scope |
| --- | --- | --- |
| `existenceFromOccurrence --omit hRepresents` | Unsupported `represent : Episode → Being`, exit 2 | Superseded in #1930 for this explicit unary function: the omission is Lean-checked |
| `actualGiverImpliesB2 --omit hGiver` | Unsupported `F : CausalityFrame W B T R`, exit 2 | Still unsupported; no shared-frame model result |

Neither baseline refusal was an exhaustive failed model search. The separate
[unary-function extension (#1930)](https://github.com/moritzbrantner/formal-logos/pull/1930)
returns exactly three `lean-checked` reports for
the module-qualified `existenceFromOccurrence --all --size 2` run: omit
`hOccurs`, omit `hRepresents`, and the joint witness, all with singleton
`Episode` and `Being` carriers. The [measured countermodel outcome](https://github.com/moritzbrantner/formal-logos/blob/7b7747917203127d6bb6005f0a798544619ae0f8/docs/countermodels.md#unary-function-coverage-checked-on-2026-11-24)
records the command, complete predicate assignments, existing control and
the separately Lean-checked nonconstant swap probe. Occurrence alone does not
entail `SomeExistent ExistsIn` under the encoded vocabulary; the witness for
both premises establishes formal satisfiability only. This is known-control
coverage with no novel philosophical consequence, premise-warrant change or
metaphysical-coherence claim. It does not generalize to the remaining
structure case or to higher-order, dependent or implicit-input functions.

In the separate #1925 classifier regression, `{P, ¬P, Q, ¬Q}` exposed independent
single deletions being combined into an empty core and a false reported
incompatibility. The same unedited Lean output was fed to both classifiers:
all four deletions proved contradiction; the repair retained all four premises,
flagged the core as not minimized and rejected literal negation. Single-success
and no-success deletion controls retained the certified pair and rejected it
in both versions. Together with 28 passing offline tests, this is Lean-backed
synthetic protocol evidence, not a new corpus incompatibility. Sequential
certified core minimization remains a further experiment; failed deletion
still does not prove necessity.

### Research retrieval check and practical continuation

The existing [independent #1644 correctness tier](notes/retrieval-benchmark-1644.md#independent-offline-correctness-tier-2026-11-17)
was rerun unchanged. Both binaries gave semantic recall 6/6, precision 6/12,
novelty correctness 6/6, and historical reference recall 5/5 with 4/4 correct
historical verdicts. The four historical JSON outputs total about 54.94 MB
for either binary; their single-sample totals were 28.31 seconds baseline and
26.94 candidate. No retrieval improvement, general performance advantage,
agent-effort reduction, token saving or monetary saving was established.
The direction, negation, quantifier and sense distinctions remain required;
large navigation output remains a practical limitation.

Reproduce with the fixture's IDs and the existing runner, for example A:

```bash
bash scripts/run-discovery.sh --target 4c79298d-ee09-5e99-9ced-1be92c19b4cc \
  --premise-pool all --candidates 8 --heartbeats 10000 --batch 1 --jobs 1
bash scripts/run-discovery.sh --target 4c79298d-ee09-5e99-9ced-1be92c19b4cc \
  --premise 18561596-1269-53ff-8505-c56e4348e335 \
  --premise fad8af3e-3e4e-582a-a592-0164bdd62527 \
  --premise 86d02b69-87eb-5594-9958-ccaa5fe6b685 \
  --heartbeats 10000 --batch 1 --jobs 1
python3 scripts/retrieval_correctness_benchmark.py \
  --baseline /path/to/baseline/truth --truth target/release/truth \
  --json /tmp/retrieval-correctness.json
```

The bounded second hop is submitted in [#1929](https://github.com/moritzbrantner/formal-logos/pull/1929):
development B gains its missing reference premise and a known-filtered proof,
while fresh held-out coverage remains 8/11 complete primary bundles and 18/23
reference occurrences. The next retrieval priority is selection among competing
full-list premise bundles, tested on those frozen misses. Other priorities are a
checked `WellFounded.has_min` specialization for D, derived from its supplied
well-foundedness rather than a stronger axiom, and finite models for the remaining
shared-frame boundary. The explicit unary-function boundary has the scoped checked
coverage in separate [#1930](https://github.com/moritzbrantner/formal-logos/pull/1930).
Both follow-ups are submitted independently; this audit preserves its original
baseline and does not imply that their implementations are included here. Follow
with sequential certified core minimization, registration of the already
checked [modal alternative/strength bundles](../corpus/attempts/modal-discover-findings-20261120.json)
(registration, not novelty), and reliable timeout/saturation diagnostics.

For agents, first use `brief`/`related`/`novelty` and `semantics` to recover the
question's prior work, meanings, serious rivals and downstream purpose. When
a complete candidate bundle is available, an exact run can isolate selection
from binding and search before new manual derivation. Let the evidence choose
a changed bundle, faithful tag review, proved lemma, bounded model or OPEN
premise investigation; this is not a mandatory tool sequence. Return raw
repair candidates to the engine's certification path. Keep stronger direct
assumptions alongside their lower-level derivations, preserve all AND
premises, and use the existing attempt, spec, Challenge/Solution and review
workflow. No new runner, truth authority or evidence registry is needed.

## Agent-guided blueprint recipe

A work-loop recipe for targets that a plain run leaves unresolved (#1832). It
reuses the engine and its filters; nothing below writes a corpus record, and an
agent's proposal stays untrusted until Lean checks it.

1. **Baseline.** Run `scripts/run-discovery.sh` on the targets with the budget
   you will reuse (`--premise-pool`, `--candidates`, `--heartbeats`), and keep
   the report and its revision.
2. **Diagnose.** Export the binders of the statement declarations and read the
   report against the corpus:

   ```bash
   lake env lean --run scripts/DiscoverBinders.lean TruthCore DECLS.txt > binders.jsonl
   python3 scripts/discover_blueprint.py diagnose REPORT.json --binders binders.jsonl --target ID
   ```

   For each target it lists the verified arguments that already conclude it,
   the premises the run did not retrieve, and the binders the run could not
   identify (a premise binder whose name an earlier binder of another module
   has, or a second carrier). The verdict separates a *retrieval* gap, an
   *identification* gap (the exact sense or bridge obligations), a *search* gap
   (retrieved, identifiable, not composed) and *no-known* derivation.

   When this exposes a complete known bundle that retrieval missed, try it
   with repeated `--premise` before developing a new manual derivation. This
   isolates retrieval from binding and proof search while keeping the normal
   filters; an expected `known` result confirms recovery, not a new argument.
   Repeating unchanged inputs adds no evidence. Let the diagnosis select a
   changed bundle, a justified budget test, a reviewed identification or
   manual lemma work; exact search is useful for this case, not a prerequisite
   for every investigation.
3. **Oracle (optional).** To ask whether an identification is the only
   obstacle, run the engine once with a temporary overlay of whole-binder tags
   (`python3 scripts/discover_blueprint.py oracle OVERLAY.json -- <run-discovery
   arguments>`). The overlay is written only into a disposable detached `git
   worktree` at HEAD (under `--scratch`, default the repository's parent
   directory), which carries the uncommitted files, shares the built `.lake`
   by symlink (unchanged sources, so Lake only replays) and is removed
   afterwards; the repository's own corpus is never edited. The overlay is
   saved beside the report. Every finding of such a run is conditional on the
   overlay: an identification becomes admissible only through a reviewed sense
   tag or an explicit bridge premise, never through the overlay. To check an
   identification by hand instead, state the target and the known premises
   over one signature, as in
   `scripts/testdata/discover-blueprint/IdentificationOracle.lean`.
4. **Blueprint.** For a target without an admissible route, write a small
   AND/OR graph of candidate intermediate lemmas over existing statement IDs,
   marking each node as a verified theorem, a candidate lemma or OPEN. Check
   candidates in Lean with their original binders, quantifiers and senses;
   run `truth semantics --premise … --conclusion …` on each composition; reject
   a step whose only premise restates its conclusion, a lemma whose proof uses
   its own consequence (a support cycle), and a premise core that is
   inconsistent. An AI-proposed proposition that no existing statement proves
   stays OPEN: register it, if at all, as an explicit open premise.
5. **Record.** Register a surviving composition through `argument_batch.py`
   with controls, and persist every candidate, rejected or not, with its reason
   in one attempt record.

## Adaptive repair

For a goal a run left unresolved or filtered, `discover_blueprint.py repair`
reads the report and the corpus and lists the alternative diagnoses (#1833),
each `supported`, `possible`, `excluded` for the exact bundle tested, or `not
indicated`, with the signals behind it. A failed search proves none of them.

| Diagnosis | Signals |
| --- | --- |
| (a) tactic, selection or budget | no proof (the engine does not record whether the heartbeat budget expired or Duper saturated, so this stays possible); the candidate list at its cap; a known derivation retrieved and identifiable but not composed (identifiable only when a binder export is given); a known bundle with no same-named binder left separate that does not close; a Lean process timeout. *Excluded* for a bundle only by a one-point countermodel under the plain binding when no projection binding applies; with an untested projection binding it stays possible |
| (b) malformed goal or missing lemma | a Lean error stating the goal; known-derivation premises not retrieved; a verified lemma that follows from the bundle but is not in it |
| (c) carrier or sense misidentification | `domain_identified_by_name`, the `domain_by_name` and `senses` filters, known-derivation binders no tag identifies, a missing bridge between same-named relations of different declarations |
| (d) inconsistent or vacuous bundle | `vacuous`, `literal_negation`, `antecedent_refuted`, the `witness` flag. A one-point model of the premises shows they are not an inconsistent core; it does not exclude a vacuous target, so it excludes neither half of (d) as a whole |
| (e) missing substantive premise | at most *possible*: an engine bridge (a candidate proposition, OPEN), or a countermodel, which shows that the bundle as bound lacks *something* (premise, lemma, identification or bridge), never which, nor that it is substantive |
| (f) unknown | nothing supports another diagnosis |

```bash
python3 scripts/discover_blueprint.py repair REPORT.json --binders binders.jsonl [--target ID]
python3 scripts/discover_blueprint.py retry REPORT.json --binders binders.jsonl --target ID --auto 4
python3 scripts/discover_blueprint.py retry REPORT.json --action 4c79298d-countermodel-1a2b3c
```

The retry actions, in priority order: **reuse-lemma** (add the conclusion of a
verified argument whose premises the goal already has and that bears on the
target: a premise of a known derivation, or a shared definition; Duper does
not compose through other theorems); **known-bundle** (the premises of a
verified argument concluding the target that retrieval missed; expected to be
filtered as known, which confirms a retrieval gap); **countermodel**
(`scripts/DiscoverRepair.lean`, below); **split** (when exactly one known
premise is missing: search it from the bundle, and the target from the bundle
with it); **budget** (once, at four times the heartbeats, only after a
countermodel search completed without finding one); **strict-domains** (a goal closed through a by-name
carrier: the same bundle without that fallback); and the reports
**open-bridge**, **blocker**, **reject** and **record-incompatibility**, which
run no solver. Every premise is an existing corpus statement: an action never
weakens or strengthens a statement, writes a sense tag or identifies two
binders, and an engine bridge is never added to a goal. Guards refuse a
support cycle (a premise every verified derivation of which uses the target),
a solver input already in the trace, a second action of a kind whose diagnosis
an earlier run settled, any action whose goals would take the goal past eight
solver runs (a split counts two), and an input whose run failed twice for
infrastructure reasons. The run cap counts per goal label *and* solver-input
revision: after the corpus, library, Discover scripts or Lean pins change,
the same goal gets eight fresh runs (`--trace` with a new file also starts
afresh). An action's id is derived from its content (kind, solver keys and,
for a known bundle or split, the verified argument it comes from), so it does
not change when another action is inserted. `repair`
only plans and leaves the trace file unchanged.

`retry` runs the exact goal through the same binding as `truth discover`: a
scratch file of `scripts/Discover.lean` and `scripts/DiscoverRepair.lean`, one
`#discover` or `#discover_countermodel` command per goal, under the heavy-job
lock (the time limit bounds Lean only), in the `--root` repository (or this
tool's own when `--root` is no Lake project with those scripts), whose
Discover scripts and prove-sweep probe it reads, with the corpus's sense tags in the engine's order (`senseOf` takes a
binder's first tag, so a binder with both a whole-binder and a
partial-application tag is identified or not by that order; the repair flags
such binders). Retrieval is bypassed, not changed. Each
run appends an entry to the attempt trace (`repair-trace.json` beside the
report, or `--trace`): the solver key (a hash of the command, the solver-input
revision, the declarations, budget, domain policy, tags and the prove-sweep
probe), the exact goal and premise ids,
the declarations, the diagnoses when it was chosen, why it was chosen, the
change against the engine's goal and the outcome. The engine's own goal is the
trace's first entry, so an identical retry is refused, and a rerun of `retry
--auto` on a finished trace runs nothing. The solver-input revision hashes the
Git objects of `corpus/`, `TruthCore/`, the two Discover scripts,
`lake-manifest.json` and `lean-toolchain`, and their uncommitted changes by
content; the repair tool itself is not an input. A run that produced no
outcome (no output, Lean timed out or killed: exit 137 is reported as out of
memory or the kill after a timeout) is recorded unkeyed as `failed`, not as a
solver result, so it can be rerun.

A closed goal is assessed offline with what the raw result carries, reading
the minimized proof's axioms as the engine does: a proof on an axiom other
than `propext`, `Classical.choice` and `Quot.sound` is rejected (`axioms`); a literal
P/¬P core is rejected and never support; an inconsistent core is an
incompatibility; a by-name carrier or the transcription probe rejects it;
the engine's projection filters reject `projection_unused` and an ambiguous
projection, and a unique projection is noted as a specialization;
composition from verified arguments makes it `closed-known` (`modulo_logic`
when only with excluded middle, granted, as by the engine's `known` filter,
only to a proof whose axioms include `Classical.choice`); the
`truth semantics` preflight checks its senses, for known closures too. What survives is a raw
`closed-candidate`: submit the same ordered bundle and heartbeat budget to
`truth discover --target ID --premise P1 --premise P2 --heartbeats N` for the
engine's filters and certification, and record it only through the spec path
and the semantic challenge. This uses the corpus's reviewed tags; the retry's
raw result or an oracle overlay is not a certificate. Per premise, a deletion that fails
is "kept within budget; necessity unresolved" unless an omission model shows
it needed. A goal with no proof is `unresolved`, never refuted.

The countermodel probe binds the target and premises as `#discover` binds the
plain goal and searches the one-point models of `Discover.witness`, of the
premises alone and of the premises with the negated target. It does not try
the projection bindings `#discover` tries next (a target binder bound to a
premise structure's field); it lists them as `projections_untested`, and while
one exists a countermodel leaves (a) possible: a countermodel to
`∀ o m, H m → T o` does not refute `∀ m, H m → T m.ontic`. A countermodel is
reported with every outer binder (name, originating declaration and binder,
sense tag, type), the slot pattern and the map from slots to binders, and the
by-name identifications it is conditional on. The repair tool adds its bounds:
it shows only that this formal implication, over these declarations under the
plain binding, fails at one instantiation of its binders. It refutes no
premise, no stronger or differently bound formulation, no sense identification
and no larger bundle.

Engine changes this layer does not make: a reported distinction between a
heartbeat timeout and a saturated search; countermodels for unresolved goals
in the engine itself; a binding
rule that does not depend on tag order when a binder carries both a
whole-binder and a partial-application tag; and one shared
universe-specialization helper (`scripts/DiscoverRepair.lean` copies the block
of `Discover.trial`). Two earlier follow-ups are in the engine since #1850:
the `known` filter grants excluded middle to a classical proof, and retrieval
admits and ranks premises by whole-binder sense tags.

## Boundaries

- Proof validity is not premise warrant. A discovery from open premises is a
  conditional support option and closes nothing beyond the existing closure
  rules. Unresolved targets and kept premises are not refutations.
- A binding is an interpretation choice. Identification by name within a
  module follows that module's convention; across modules only sense tags
  identify parameters. The reviewer still checks that the composed statement
  means what the prose says (AGENTS.md, Review guidelines).
- Duper's proofs, and those of `tauto`, `grind` and `aesop`, are classical (`Classical.choice`): a discovery must not count
  as evidence where excluded middle is in question (docs/axiom-policy.md). For
  the same reason a known route that lists excluded middle as a premise counts
  as the same route (`known`, flagged `implicit_excluded_middle`); a
  constructive proof does not match it and stays a discovery.
- The run is local and recurring by choice; CI runs only one fixed known
  derivation as a smoke test, and `scripts/DuperAxiomAudit.lean`.
- `TRUTH_DISCOVER_KEEP=1` keeps the scratch files for debugging.

## Target-free conjecture pilot

`truth discover` starts from a target statement. The pilot of #1834 starts from
two argument families instead and asks which *new* conclusions or
relationships between them hold, without a preselected target.
`scripts/discover_conjecture.py` certifies a fixed list of candidates written
in a configuration (`explorations/conjectures/*.toml`); the list may come from
an agent, the checks do not.

```bash
python3 scripts/discover_conjecture.py run explorations/conjectures/actualization-grades-1834.toml \
  --out-dir .cache/conjectures/run    # under the heavy-job lock
python3 scripts/discover_conjecture.py classify CONFIG --binders B.jsonl --lean-output OUT.txt --map FILE.lean.map.json
```

Each candidate states its outer binders with their types, its premises
(existing statements, every declaration parameter mapped to an outer binder:
nothing is identified by unification), its conclusion (an existing statement
or a new proposition over the outer binders), and optionally models (checked
by `decide` or `simp`), a witness model with an optional antecedent instance,
and an explicit OPEN bridge. The rendered Lean file checks, each as its own
declaration under `#print axioms`, the goal (`duper` after delta-unfolding the
project definitions, as `truth prove-sweep` does), the premises against
`False`, every single-premise deletion, the conclusion from no premise, the
prove-sweep transcription probe, literal negation between premises, the
models, and the bridge with and without the premises. Every check counts as
proved only within `propext`, `Classical.choice` and `Quot.sound`.

`classify` gives each candidate one outcome: `verified_conditional_implication`
(support only with a certified joint witness; otherwise consistency is
unresolved), `incompatibility` (an inconsistent bundle; never support),
`certified_non_implication` (only in the stated model), `open_bridge` (valid only
with an explicit bridge, or only under an identification that no module or tag
licenses: filter `name_only_identification`, or `senses` for an inconsistent
bundle joining two senses), `rejected` (with the filter: `known` by a registered
argument or by forward-chaining closure, `transcription`, `tautology`,
`literal_negation`, `senses`, `single_family`, `axioms`) or `unresolved`.
Identification follows the engine's rule: two parameters share a binder only when
they have the same name in one Lean module or carry one whole-binder sense tag (by
sense id); a carrier is shared also when such an identification of a relation over
it forces it; two parameters of one declaration mapped to one binder are an
obligation. Single deletions are independent checks: when more than one
succeeds the full bundle is kept and flagged. In particular, `vacdrop_i` checks
each delete one premise from the original bundle. One certified deletion may
reduce `inconsistent_core`; with several successes the classifier retains the
full certified bundle and flags it as not minimized, because joint deletion
was not tested. Literal-negation controls run on that retained or reduced
bundle. Failed or uncertified deletion searches retain premises and do not
prove necessity or minimality; a premise counts as needed only with a certified
omission model. A bridge is reported as one sufficient bridge,
not as the weakest one. When a candidate's conclusion uses binders that no premise
mentions (pilot C05b, C11), its non-implication is immediate: the model names the
missing link, it does not show substantive independence. The tests
(`scripts/test_discover_conjecture.py`) cover the acceptance fixtures of #1834
offline. The pilot's candidates, outcomes and comparison with `truth discover`
and `truth bridge-experiments` are recorded in the attempt it cites.

## Bounded second-hop retrieval benchmark (2026-11-24)

Second-hop backfill keeps the direct candidates in order and fills unused slots
through their eligible neighbors, using the same rules and premise pool. Additions
never become anchors. Empty and full direct lists stay unchanged; the target and
aliases of selected declarations are excluded from additions. `Candidate.via`
records the admitting anchor, not a proof dependency. An added candidate's score
is relative to that anchor, not directly comparable to target scores.

The cap applies to the **ranked list**. The existing goal builder can then append
registered sense bridges as optional, explicit hypotheses, so a trial can exceed
the ranking cap. Coverage below is measured before that insertion, separately
from the retained proof; retrieval itself identifies no senses.

### Frozen workload and measurement

The [fixture](../scripts/testdata/discovery-multihop-benchmark.json) has twelve
fresh targets: eleven known-consequence cases and one negative neighborhood.
There are thirteen reference AND bundles because C2 has three separate routes.
Assertion/meaning B is development data; maximality A and causal ascent D are reused
full-list controls. Keep these groups separate: related cases are not independent
philosophical corroboration, and no favorable subset was selected after outcomes.

An independent semantic audit selected the target cohort and candidate reference
routes before production-ranker outcomes and engine edits. Reference annotations
were completed after baseline candidate counts were reported, before implementation
and proof outcomes; all initially inspected C2 pairs were retained. The fixture
is published unchanged as `ac6415f504215acba366462a99a322dfa97dfbcd`, with SHA-256
`cb1e6d8daf68dfd12238951fa8c46d9a8e2836b272c4d54df914929b4e2d98b7`.

Both engines use corpus `00d3e61cfb7e8f32e89a8444499b065ad370116f`, the same complete
dependency-closed vocabulary of 12,716 declarations, pool `all` and candidate cap
eight. Coverage means literal canonical IDs in each frozen bundle: every AND
member must occur, including explicit excluded middle where listed. Neither proof
minimization nor implicit classical background changes the reference oracle.
The reference bundles are not a complete relevance oracle for every possible route.

Proof diagnostics use 10,000 heartbeats in the CLI's thousands unit, batch one,
one job and no external prover. The rule selects every underfilled baseline case:
three fresh cases and development B. Nine fresh cases and A/D have full lists;
unchanged ranked inputs permit reuse of unchanged proof evidence. Exact reference
bundles and the literal-pair negative diagnostic use the separate explicit-premise
path on the #1928 integration and do not count as ranked retrieval improvements.
No referenced Solution theorem or custom proof hint is supplied to search.

### Reference coverage

| Fresh target | Direct candidates | Primary bundle before | Primary bundle after |
|---|---:|---:|---:|
| `6280fbf0` eligible uptake yields warranted belief | 3 | 2/2 | 2/2 |
| `8c6a14f8` goal-relative authority exclusion | 8 | 0/2 | 0/2 |
| `b391c809` goal-relative actual-force concession | 8 | 0/2 | 0/2 |
| `c830e937` within-history tracking mismatch | 8 | 2/2 | 2/2 |
| `475beacf` history-fixed accuracy | 8 | 3/3 | 3/3 |
| `fe53f4ab` cross-history tracking mismatch | 8 | 2/2 | 2/2 |
| `7989856a` moral truth-aptness and error | 8 | 2/2 | 2/2 |
| `6508c239` contingent reception/prior cause, C2 | 8 | 1/2 | 1/2 |
| `bf4167dc` strong supplementation | 8 | 2/2 | 2/2 |
| `53716090` reject affection-report-only content | 8 | 2/2 | 2/2 |
| `f976f890` generic unique existence | 2 | 2/2 | 2/2 |
| `38eb1610` eligible-uptake negative neighborhood | 3 | Not scored | Not scored |

Baseline primary coverage is 8/11 complete bundles and 18/23 reference occurrences.
Each additional C2 bundle retrieves one of its two members, giving 8/13 complete
bundles and 20/27 occurrences across all frozen positive routes. All these figures
are unchanged after backfill: every fresh target has the same ordered IDs and scores.
The primary-reference membership precision proxy is also unchanged: 18 matches
among 77 candidates across the eleven positive cases, or 18/77, with recall 18/23.
Off-reference does not mean irrelevant: the frozen bundles are not a complete
semantic-relevance oracle. Coverage does not discharge moral-error's cross-module
Agent/Sentence identifications or predict proof success.

Only development B changes: two to seven candidates and reference coverage one of
two to two of two. All five additions have `via: 42114721`; the missing assertion
`b45ca9db` is the first addition. B's membership proxy is 1/2 before and 2/7 after;
its reference recall rises from 1/2 to 2/2. This is no held-out gain. A retains
three of three reference premises; D retains three of five. Both eight-entry lists
keep identical IDs, order and scores. A full list is not a complete reference bundle.

### Proof and negative-control outcomes

| Case | Before | After | Interpretation |
|---|---|---|---|
| Fresh eligible-uptake warrant | Known-filtered proof | Same | Reference bundle already complete before |
| Fresh generic unique existence | Known-filtered proof | Same | Reference bundle already complete before |
| Fresh negative uptake neighborhood | Literal-negation filtered | Same | Contradictory pair supplies no support |
| Development assertion/meaning B | Unresolved | Known-filtered proof | Development recovery, excluded from held-out gains |

The negative neighborhood includes `6280fbf0` (some warranted actual belief) and
`cbe1661b` (its literal negation), initially at ranks two and three. A reconstructed
proof from that pair is filtered as `literal_negation` in both ranked runs and the
separate exact diagnostic. The latter preserves precisely those two requested IDs,
with null ranking cap and pool. An all-pool run is not a non-entailment test: other
premises may legitimately support its target. The observed filter is evidence of
rejection of this literal pair, not of general target non-entailment.

Known-filtered proofs are recoveries, not emitted certified discoveries: their
`certified` fields are null. B retains `42114721` and `b45ca9db`, with no name-only
binding, and matches registered argument `8a3dcfc2`. The four-goal runs change from
two to three known proofs and one to zero unresolved goals; both reject the literal
pair. New discoveries, incompatibilities, vocabulary theorems and errors are zero.
Open-premise warrant and actual applicability remain separate obligations.

Total engine times were 716 seconds before, 1,482 after and 525 for exact negative.
They are not comparable performance measurements: the after run stalled in the
unchanged vocabulary export under resource pressure, with disposable debug-build
cache removed during the run. A separate warmed, serialized comparison interleaved
three samples per engine under the heavy-job lock: baseline 0.494, 0.515, 0.362
seconds; after 0.367, 0.336, 0.352. Each covers process start, corpus load, cached
vocabulary read and ranking all fifteen targets, excluding extraction and proof
search. All were below 0.52 seconds; this small workload does not establish a speedup.

### Remaining gaps and reproduction

The frozen missing bundles are in full lists. Epistemic authority targets
`8c6a14f8` and `b391c809` omit both reference members. C2 retrieves B2 but omits
B3 `ee74c678`; its reception alternative retrieves R1 but omits `7fcfcee8`, and its
weak-form alternative again omits B3. D additionally misses `5cda1946` and
`ee4ab504`. Backfilling unused slots cannot fix these full-list omissions; they
remain a distinct ranking problem. The existing well-founded proof-search gap is
also separate. No new philosophical assumption follows from either limitation.

Published source snapshots are tests-only `b179899fb7020932f35b3fb50af85444e465d8e1`
and engine `263a6653bd00d0ff6014343bcc70e48605f2d667`, independently based on main
`6ecc2d87c3576906cb32ea8dbbca22e7557cce6b`. To reproduce the controlled after source,
apply those two commits to curated baseline `00d3e61c`, then add the frozen fixture
commit above. This reconstructs the measured code in integration `e49c8a753`;
it does not make the production change depend on #1928.
For ranking-only reproduction, load the same corpus with `Corpus::load`, obtain
`discover::statements`, and export and close the vocabulary with production
`discover::export_vocabulary` and `discover::close_vocabulary`. Reuse that exact
export for both engines. Build `SenseTags` and `weaker_siblings` from the same
corpus and call `discover::rank` with the all-statement pool and limit eight for
each fixture target. Compare ordered IDs and second-hop `via`; do not reproduce
the scoring formula in another implementation. The closed-export SHA-256 is
`2fe7b436115a0f0554188c06edb20359a2726aee0421a88047b1f6dbb4ce3b95`.

For the four proof diagnostics, build the selected engine and use the same corpus
root and the corresponding fixture target, under the existing heavy-job lock:

```bash
flock /tmp/moenarch/truth-core-heavy.lock \
  ENGINE/target/release/truth --root CORPUS --json discover \
  --target TARGET --premise-pool all --candidates 8 \
  --heartbeats 10000 --batch 1 --jobs 1
```

Record engine/corpus/fixture/vocabulary identities with raw reports. The tests-only
snapshot produced five failures and two passes in its seven focused cases; the
engine passed 54 discovery unit tests, four exact-CLI integration tests, formatting,
Clippy, release build, corpus/generator checks and attribution. The independent
main-based production change leaves its frontier unchanged: 602 support alternatives,
581 open premises and cost 16. This is separate from the curated measurement corpus.
Shared-runner timings are informational; no universal speed or precision claim follows.

## Frame goals: portfolio, term binding and the NAR exact bundle (#1926, 2026-11-24)

On `03b9c7e15`, the exact NAR bundle (target `43651417`
`NecessaryActualConcretaAreRoots`; premises `0c27f65a`
`IntellectualGodCommonRootAt`, `eeccc832` (b2), `fbd0a6d3` (a)) gave "0 proved,
1 unresolved" in 201 s, while `truth prove-sweep` closes the matching
Challenge `narFromRootWithholding` by `unfold+grind`. Three causes were
separated:

| Cause | Evidence | Change |
| --- | --- | --- |
| Proof search | On the Challenge's own statement, `delta`/`prove_sweep_unfold; duper [*]` hits 100000 heartbeats; `unfold+grind` closes it | the prove-sweep portfolio runs before Duper (step 5) |
| Renamed binder | the two NarDerivation premises got two worlds (`w_3`, `w_4`): the same-module rule compared the renamed outer name | same-module identification compares declared names (step 4) |
| Adapter term | the Challenge binds the target's `m : Profile W B` to `groundProfile F concrete G`, which the premises build; no projection reaches it | term binding (step 4) |
| Cross-module identification | the target, `IntellectualGodCommonRootAt` and the NarDerivation premises are three modules; their `w`, and the two `m`, carry no authored sense tag | none: an identification is a reviewed tag or an explicit bridge, never a tooling default |

Same bundle, default budget (Duper 100000, portfolio 20000), `--batch 1`
implied, under the heavy-job lock; seconds are the engine's `summary.seconds`:

| Run | Outcome | Seconds |
| --- | --- | ---: |
| `03b9c7e15`, Duper only | unresolved | 201 |
| portfolio only, binding unchanged | unresolved (the goal as bound is false: four worlds, `m` unbound) | 197 |
| this change, plain exact run | unresolved: the NarDerivation premises share one world; the term binding `m := groundProfile F concrete G` is tried; three worlds of three modules stay separate | 313 |
| this change, `discover_blueprint.py oracle` with temporary whole-binder tags on the four `w` and the two `m` | proved by `portfolio:unfold+grind` under the term binding; minimization keeps all three premises (each deletion fails within budget; a one-point omission model shows `0c27f65a` needed); filtered `known` (registered argument `abc27f55`), `domain_by_name` (carriers `W`, `B`) and the informational `projection_binding` | 163 |

Its rendered theorem text, re-elaborated as the certification file states it,
was accepted with axioms `propext`, `Classical.choice`, `Quot.sound` and no
project theorem outside the bundle (`discover-external: []`). The CI smoke
target (`c7de7537`) is now proved by `portfolio:grind` and filtered `known`,
as before.

The oracle run is conditional on its disposable tags: it shows that the four
`w` binders and the two `m` binders are the only identification obstacle
left, and it licenses neither tag. Authoring them is a semantic decision
(sense records with `lean_parameters`), outside this tooling change. The
proof is a rediscovery: `known` names the registered argument it recovers,
and `domain_by_name` the existing name fallback for the carriers `W` and `B`,
which the same tags would discharge. No premise, statement or warrant changes.
