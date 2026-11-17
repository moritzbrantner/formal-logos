# Dependence shapes: cycles, regresses and mereological priority

This is the #336 integration for the #310 grounding and #320 uniqueness
questions, at baseline `956c8280973ea7d9ed085de07c6b2b50c4c9cf06`.
It compares mathematical dependency shapes without identifying borrowed power,
explanation, existence-grounding and parthood. Those interpretations require
separate bridges. All new formulations are analyst formulations; attribution
is deferred. None of the controls establishes actual gunk, actual causal
well-foundedness, uniqueness of an ultimate ground or a root premise.

Issue navigation: [#336](https://github.com/moritzbrantner/formal-logos/issues/336)
connects [#299](https://github.com/moritzbrantner/formal-logos/issues/299),
[#310](https://github.com/moritzbrantner/formal-logos/issues/310),
[#311](https://github.com/moritzbrantner/formal-logos/issues/311),
[#317](https://github.com/moritzbrantner/formal-logos/issues/317),
[#318](https://github.com/moritzbrantner/formal-logos/issues/318),
[#319](https://github.com/moritzbrantner/formal-logos/issues/319) and
[#320](https://github.com/moritzbrantner/formal-logos/issues/320) to
[#325](https://github.com/moritzbrantner/formal-logos/issues/325),
[#326](https://github.com/moritzbrantner/formal-logos/issues/326),
[#327](https://github.com/moritzbrantner/formal-logos/issues/327),
[#328](https://github.com/moritzbrantner/formal-logos/issues/328),
[#329](https://github.com/moritzbrantner/formal-logos/issues/329),
[#330](https://github.com/moritzbrantner/formal-logos/issues/330) and
[#331](https://github.com/moritzbrantner/formal-logos/issues/331).
Reuse/reference issues are
[#339](https://github.com/moritzbrantner/formal-logos/issues/339),
[#346](https://github.com/moritzbrantner/formal-logos/issues/346) and
[Mathlib adoption #358](https://github.com/moritzbrantner/formal-logos/pull/358).
The historical [#337](https://github.com/moritzbrantner/formal-logos/issues/337)
blocker is superseded by that adoption.

## Reconciliation and delivered controls

The Mathlib prerequisite #358 is complete. The following work was already
available and is reused, rather than reimplemented:

- #339's `EssentialPower` and `FiniteGroundingHasSource` distinguish local
  transmission from inductive finite-source grounding. `Logic.Regress` supplies
  the monotone operator, least-fixed-point identification, conditional
  least/greatest agreement and well-founded graph controls. `RegressSchema`
  already has the self-loop/distinct-chain and reverse-Nat order boundaries.
- `Mereology.AtomlessFusionProfile` supplies a complete Boolean algebra of
  Mathlib regular open real regions with bottom removed, full nonempty-family
  fusion/remainder structure and a positive proper part below every region.
  Its atomic contrast is the existing `UniversalFusionBoundary.Body` of
  nonempty subsets of Bool. No replacement finite gunk model is introduced.
- `SupplementationFusion` and `SumOneComplementation` compare supplementation
  and different fusion profiles. `ActualFusionProfile` distinguishes a greatest
  actual object in each world from one necessary object across worlds.
- #346's issue points to these models, but its pinned AFP reference and
  system-by-system M/MM/EM/CEM/GEM correspondence remain separate obligations.
  The neighboring Lean results are not evidence that this reference comparison
  has been completed.

The new frozen Challenge and Solution are
[`DependenceShapes`](../TruthCore/Results/Mereology/DependenceShapes/Solution.lean),
with statements/inferences/arguments/results generated from
[`specs/dependence-shapes.toml`](../specs/dependence-shapes.toml).
Their vocabulary is
[`Mereology.DependenceShapes`](../TruthCore/Mereology/DependenceShapes.lean).

| Control | Existing evidence reused | Added distinction |
| --- | --- | --- |
| DS-1 `shapeControl` | Graph controls and monotone transmission | A joint self-loop certificate: no injective Nat sequence, non-WF, finite grounding when all nodes are intrinsic, and empty source-free lfp versus universal gfp. Strict reverse Nat has an infinite successor chain despite irreflexivity and transitivity. |
| DS-2 `priorityControl` | The same regular-open full-fusion gunk model | An injective descending chain anchored at every region; **both** full strict-order directions are non-WF; the reverse rejects the same oriented downward chain. A designated-whole star on the same carrier is WF but omits intermediate whole-to-part edges. Mathlib `IsAtom`, `IsAtomic`, `IsAtomistic` state the atomless/atomic contrast. |
| DS-3 `extensionalityControl` | The same full-fusion two-atom Body and exact remainders | Unrestricted proper-parts extensionality collapses all minimal objects; strong supplementation proves composite-restricted extensionality; Body satisfies the restricted principle and has two distinct simples with equal empty strict lower cones. |

These are premise-free mathematical controls whose universally quantified
subclauses retain their hypotheses. They are not unqualified claims about the
actual world. Standard permitted Lean/Mathlib axioms are `propext`,
`Classical.choice`, `Quot.sound`; no additional axiom is introduced.

## 1. Cycles, distinct chains and fixed points (#311, #310, #339)

Write `R y x` for an upstream dependency of x on y. A finite directed cycle
can be traversed repeatedly to produce an infinite **periodic** backward walk.
It need not contain infinitely many distinct nodes. Thus a prohibition of
injective infinite chains leaves finite cycles available: DS-1 uses a Unit
self-loop, not an alleged infinite collection of Unit objects. Conversely,
strict reverse Nat order is transitive and irreflexive, while `f n = n` is
an injective backward chain. Transitivity and irreflexivity exclude cycles,
but do not exclude that regress. Well-foundedness excludes both shapes.
It does not require a common finite bound on the lengths of finite paths.

There are two further distinctions in the original issue's shorthand:

1. `FinitelyGroundedPower R intrinsic x` is an **existential finite derivation**
   ending at an intrinsic node. `FiniteGroundingHasSource` uses no WF
   hypothesis. It does not exclude other infinite or cyclic dependencies of x.
   DS-1's intrinsically grounded self-loop is a simple control; the stronger
   existing `GroundingWithoutUniqueCauseAllowsRegress` has unlinked intrinsic
   sources and source paths alongside a genuine infinite chain.
   `GroundingWithUniqueCauseYieldsRegressReading` needs its additional
   no-incoming-source and unique-immediate-cause hypotheses.
2. For the particular monotone operator
   `T S = {x | intrinsic x ∨ ∃ y, R y x ∧ y ∈ S}`,
   `Graph.grounded_eq_lfp` identifies finite grounding with the least fixed
   point. WF makes lfp and gfp equal; the converse is false (the existing
   all-intrinsic self-loop has equality). A source-free cycle or successor
   chain can belong to this operator's gfp and not its lfp. This is not a
   theorem about every inductive/coinductive semantics or every dependency
   operator. For example, the existential predecessor clause is not an
   all-premise requirement for jointly necessary contributors.

`EssentialPowerUnderdetermined` uses the successor relation, not a literal
one-node cycle. Uniform on/off solutions are constant activity assignments;
equal truth values at successive nodes do not identify those nodes or turn
that graph into a self-loop. The cycle analogy concerns the missing boundary
condition, not equality of the dependency structures.

**Connection to the case:** #310 ACT-GROUND must defend the application of a
particular grounded-power semantics to actual power. #311 must specify which
same-respect links its bootstrap case has and why those links are forbidden.
Their structural tests overlap, but neither conclusion transfers merely from
the words “dependence” or “least fixed point”.

## 2. Gunk, whole priority and junk (#325–#331, #310)

In the existing positive regular-open Boolean model every represented object
has a positive strict part. Accessibility induction therefore fails at every
node. Mathlib's descending-chain theorem gives a chain from each selected
region, and strict decrease makes it injective. This is genuine atomlessness,
not merely an infinite domain or failure of atomicity somewhere in a mixed
world. The Boolean algebra has no `IsAtom`; its set-algebra contrast is both
`IsAtomic` and `IsAtomistic`. Zero is excluded from the object domain, so it
cannot masquerade as a physical atom or a universal common part.

The inference to an infinite **grounding** chain is conditional on:

- the represented positive regions being actual objects in the relevant world;
- every selected proper-part pair giving an upstream ground edge **in the
  same grounding relation**; and
- the modal/actual domain preserving those parts and edges.

Only the second is needed for the abstract structural transfer: an
edge-preserving map from the strict-part graph to a WF ground graph would
make the strict-part graph WF (`Graph.Map.wellFounded`), contradicting DS-2.
This is an explicit missing application bridge, not a definition of actual
grounding by `<`. A source-free mathematical partial order supplies no reason
by itself to accept that application.

**Whole priority needs precision.** If `f (n+1) < f n`, the same sequence
cannot also satisfy `f n < f (n+1)`. But full reversal of `<` on positive
regular opens is **also non-WF**. On the nonzero, non-top regions, Boolean
complementation reverses strict order. Every such region still has a smaller
positive region. A hypothetical WF upward order pulls back along
complementation to a WF downward order on that inhabited subdomain, a
contradiction. The existence of a greatest whole therefore does not make all
upward chains terminate.

DS-2's alternative is a genuine different relation on the **same** carrier:
`wholeStar u` has `edge y x ↔ y = u ∧ x ≠ u`, with u the greatest region.
It is WF and has u as its only relative source. It does not assert that every
intermediate whole grounds each of its proper parts; DS-2 explicitly refutes
that inclusion. This witnesses structural compatibility of atomless parthood
with a whole-first star account, not adequacy of that account as metaphysical
explanation. If whole priority is instead required to include every reverse
strict-part edge, this regular-open interpretation cannot meet WF.

Accordingly, “no regress forces atoms **or** whole priority” is not an
exhaustive theorem. WF strict parthood supplies a minimal part below each
object; gunk with the all-proper-parts-to-ground bridge cannot meet WF ground.
One may instead reject actual gunk, the bridge, universal grounding WF, or the
assumed domain/comprehension policy. A whole-first star is one constructive
replacement account. No reason supplied here defeats it, and no reason supplied
here independently warrants its applicability.

**Junk is a different condition:** every object has a strictly larger whole,
with no maximal object. In a nonempty such domain, including every larger-whole
edge as ground again contradicts WF, by the same minimal-element argument in
the dual order. But unrestricted fusion of **every nonempty Lean Set**, applied
to the entire carrier, gives a greatest object (`UniversalFusionBoundary.checks`),
so this global junk condition cannot hold in that profile. Regular-open gunk
already has a top and is not junk, even though the full reversed order is
non-WF. Infinite ascending chains and absence of any maximal object must not
be conflated. Nothing here asserts symmetric metaphysical admissibility of
gunk and junk, a single uniform priority direction across all possible worlds,
or a theorem about a first-order fusion schema's set-theoretic completeness.

The selected #331 application has now been checked against Schaffer 2010
§1.4 p.44: his monist definition explicitly leaves derivative ordering open.
It requires each proper part to depend on the basic cosmos, **not** priority of
every intermediate whole over every proper part. Equal-secondary and
hierarchical derivative orderings are source-permitted alternatives, rather
than an actual star selected by the source. The full-converse/WF conflict above
therefore rejects a stronger completion on this carrier, not priority monism
itself. See [the complete source/application comparison](notes/priority-monism-framework.md#ds-2-application-intermediate-whole-to-part-edges-336--331)
for the exact relation direction, the owner-prescribed Schaffer/Raven/power
separation, #1096/#1097 scope and the remaining actual-power/being/uniqueness
bridges. No new mathematical model or root premise is established by that reading.

A subsequent [one-candidate test](notes/priority-monism-framework.md#one-candidate-intermediate-edge-functional-organ-integration-21)
selects Schaffer §2.1's functional organ/organism rationale. If its proposed
same-domain edge `D organ organism` is warranted, it distinguishes an exact
star and composes transitively with dependence on the cosmos; it does not
license all intermediate edges or establish global WF, immediate/full grounding
or productive power. The source gives this common-sense case only weak/default
weight. The remaining function-to-entity-priority application and the recommended
#319 actual-uniting-cause interface are recorded there, without a new model.

## 3. Unity and counting subdivisions (#318, #329, #330, #328)

[`Supertasks`](../TruthCore/Causality/Supertasks.lean) distinguishes unit-cost
partial sums, stable endpoints, oscillation and finite-prefix versus uniform
possibility. “There are infinitely many described subintervals” does not yet
supply infinitely many discrete acts, each costing at least a fixed positive
unit. Conversely, numerical convergence of a duration schedule does not
supply the causal resources for its operations. See [the supertask note](supertasks.md).

A continuous process, an actual object-part, an operation and an independently
costed act are different kinds of item. A substantial-unity account contributes
to SU-REAL only after it explains **which** subdivisions are potential rather
than independently actual operations, and why that matters to the cost rule.
Unity alone does not eliminate all actual proper parts. The relevant typed
application must assign candidate stages to actual operations and justify the
cost/operation condition for that assignment. No such assignment is produced
by the mathematical fusion profile.

Unrestricted fusion says that every admitted nonempty family has a fusion.
It does not itself populate a continuum with infinitely many actual physical
parts. DS-2's **particular** region model has infinitely many represented
parts; the same profile has the finite atomic Body model. Composition as
identity, unrestricted fusion, and actual infinite divisibility are therefore
not interchangeable premises. An actual-continuum interpretation with all its
subregions actual would inherit a real infinite part-domain, but neither a
unit act cost nor infinite total time follows without the operation bridge.

The #329/#330 vitalism gap remains visible. In `Vitalism.Scenario` the candidate
bridges have exact types
`∀ p, s.Alive p → s.SubstantialUnity p` and
`∀ p, s.SubstantialUnity p → s.SoulAsForm p`.
On the existing `scenario False False` the first fails; on
`scenario True False` the second fails; `scenario True True` meets both.
These evaluations only test freely supplied predicates. They are not a
substantive definition of unity or soul, nor evidence against either bridge.
This slice adds no new such flags. To obtain a discriminating physical model,
the predicates must be connected to an independently described organization,
continuity and explanatory task; the existing turnover and
[life-restricted composition](notes/life-restricted-composition-327.md) work
is the reuse point. Neither DS-2 nor those freely set flags supplies SU-REAL.

## 4. Material and formal dependence cycles (#311, #329)

**Research lead; historical attribution deferred:** Aristotle, *Physics* II.3,
“causes of each other” in different modes. No passage is attributed here.

The proposed organism pattern has `materiallyDepends whole part` and
`formallyDepends part whole`. It is a two-edge cycle only after taking the
union of two differently interpreted relations. Separate acyclicity/WF of
each relation does not imply WF of their union: opposing edges furnish a
specific failure mechanism. Nor does a cycle in that union establish a cycle
in either original relation. Even on one carrier the tags matter.

This distinction is relevant to the bootstrap comparison only if both plans
require their own production in the **same** respect. If a bootstrap proposal
instead distinguishes possession, exercise, enabling conditions or existence,
its actual bridge must be inspected; a verbal loop does not settle the matter.
Reuse the existing `power-capacity-exercise` and `existence-esse-support`
disambiguations and the separately typed domain adapters in `RegressDomains`.
Their edges are not an already-built organism/formal-cause bridge. We have no
source-based argument here that every mixed-mode cycle is benign or that every
same-respect cycle is vicious. The exact relation, respect and independent
reason for its relevant structural law remain obligations.

## 5. Extra-serial completion (#317, #318, #319)

`SupertaskMoment.limit` is distinct from every finite stage; every finite
stage precedes it and no finite stage is last. A constant Boolean output can
satisfy `StableAtLimit`. Neither the added endpoint nor the stability criterion
is a productive cause. The alternating output fails that particular criterion,
without thereby proving a physical impossibility. This is an order/output
completion, not proof that an uncaused being exists.

For the causal question, an intrinsic supplier must do the work specified by
its transmission/explanation conditions, not simply receive an “outside” name.
A graph-relative source might be a member of the graph carrier and the endpoint
of a finite upstream path; “outside the derivative series” does not mean
“outside every entity-domain”. Likewise a cause numerically different from a
composite can be one of its parts: `UniversalFusionBoundary` distinguishes
`DistinctCause` from `OutsideCause`. Its greatest material whole has no
outside **material** part-domain cause, without excluding a nonmaterial cause
in a wider domain. These controls prevent importing an extraserial endpoint
into SU-GROUND or BR-POWER-TO-BEING without causal/existential evidence.

The positive common question is precise: what additional supplied structure
changes a local description into a completed explanation? A limit output rule,
intrinsic power, an existence-support bridge and a unifying form are different
answers, each with its own application conditions. Their shared shape alone
provides none of those conditions.

## 6. Extensionality and uniqueness (#320)

`SameProperParts x y` means `∀ p, p < x ↔ p < y`.
For Mathlib `IsMin x` and `IsMin y`, both strict lower cones are empty.
Unrestricted proper-parts extensionality therefore identifies x and y.
DS-3 proves this universally, not just by enumerating two objects.

Under **strong supplementation**, if two composites have the same proper
parts and one is not contained in the other, a disjoint separating part
contradicts their common proper-part profile. If that separating part is the
whole itself, an existing strict part of the composite supplies the overlap
contradiction. Thus both containments hold and antisymmetry gives identity.
This is the composite-restricted principle, with the supplementation hypothesis
explicit. It is not a consequence of `PartialOrder` alone: the existing
`SupplementationFusion.Rival` has distinct duplicate composites with the
same proper parts and fails SS.

The existing full-fusion Body, nonempty subsets of Bool, satisfies strong
supplementation and composite extensionality but has distinct atoms `{false}`
and `{true}`. Both are minimal and share the empty strict lower cone. Hence
unrestricted extensionality fails in the **same** interpretation. This also
explains why equality of proper-part profiles is not the same principle as
overlap-profile extensionality: each of the two atoms overlaps itself and does
not overlap the other. DS-3 is explicitly a sense-mixing control, not an
argument substituting one identity principle for another.

The inference to “at most one simple ultimate ground” consequently needs
additional content specifying what differentiates ultimate candidates and why
that difference is impossible. Reuse [the q11 connection](q11-uniqueness-connection.md)
and `NecessarySimplePlurality` rather than creating another two-root model.
The latter already jointly studies two represented simple necessary roots,
with explicit limits on its respects, component predicate and PSR assignments.
DS-3 establishes only **mereological** minimality; it does not establish the
Case vocabulary's richer `IsSimple`, necessity, actuality or intrinsic
explanation. The q11 individuation/common-nature bridge and its existing
omission controls remain independent of this mereological identity test.

## 7. The regress of unifiers (#325, #310)

**Research lead; historical attribution deferred:** Aristotle, *Metaphysics*
VII.17, the syllable/letters discussion. No newly read witness is claimed.
See also [the existing H.6 unity investigation](notes/aristotelian-unity-h6.md);
its different chapter/claim scope must not silently authenticate VII.17.

The live argument is conditional: suppose a whole's unity is explained by
adding a further detachable object u, and suppose the resulting collection
requires a **new** unifier under the same explanatory rule. Repeating that
rule yields a regress only if its domain is closed under those additions and
no earlier unifier suffices. The need for an additional unifier is a substantive
premise about explanatory adequacy, not a theorem of set union or fusion.
Without a strict novelty condition, repetition could instead be a cycle.
WF would exclude either graph, but the applicability of WF remains separate.

A formal/organizational account offers a positive replacement: unity is the
organization of these constituents rather than a further constituent demanding
the same kind of organization. A material-process account offers productive
interactions and maintained coordination. Neither is refuted by merely asking
for another unifier: the proponent of the regress must show which explanatory
requirement remains unsatisfied and independently justify its recurrence.
Conversely a fusion's existence or an unexplained organization assignment does
not by itself satisfy the unification task. No substantive objection to either
complete account is identified by these graph controls alone. The open work
is to specify and compare their explanatory conditions on one actual example,
not to add a `Unified` Boolean or to rerun a generic infinite-chain proof.

## Application bridges, assessment and next tests

The useful progress is an integrated map and three inspectable controls,
including a concrete counterexample to the unrestricted “reverse the order to
remove regress” inference. The strongest formally demonstrated alternative to
parts-first WF in this gunk carrier is the WF designated-whole star. Its
specific commitment is to whole-rooted dependence without every intermediate
whole-to-part edge. Whether its explanatory content is adequate remains OPEN;
the model alone neither warrants it nor supplies an objection to it.

The seven connections leave the following exact application tasks:

| Destination | Bridge still required | Next discriminating task |
| --- | --- | --- |
| #310 actual power/ground | Same actual beings and respect, actual endpoints, and a defended power/being grounding rule; existential finite-source grounding is not all-edge WF. | Apply the existing grounded-power alternatives to the selected actual-power meaning, including joint contributors if necessary. |
| #331 whole priority | Actual region/object interpretation and an explanatory account of whole-to-part dependence; choose star versus all-strict-superparts by their meanings, not names. | Schaffer §1.4 p.44 does not require all intermediate-whole edges; identify and justify any actual derivative D-edges before selecting a completion. DS-2 excludes universal inclusion on this carrier with WF. |
| #318 SU-REAL/SU-GROUND | Actual operation/stage mapping and cost/resource conditions; potential subdivision and substantial unity need content. | Reuse the operational organization/turnover vocabulary before proposing a unity-to-act-count bridge. |
| #311 organism/bootstrap | Material/formal and capacity/exercise/existence edges and an independently justified same-respect anti-cycle rule. | Specify the actual purported loop, then inspect each typed edge. Historical Physics attribution remains a separate selected source task. |
| #319 BR-POWER-TO-BEING | Original productive power to underived existence on the same witness; relative source versus outside-domain cause. | Consume existing power/existence scope controls, not the order endpoint. |
| #320 uniqueness | Non-mereological individuation or an existing universal-causal/perfection route on the same candidate. | Reuse q11/OneFirstMover omission evidence and NecessarySimplePlurality; DS-3 supplies no identity bridge. |
| #325 unifier | A recurrent explanatory rule, domain closure and justified novelty/nontermination, or a specified organization/process replacement. | Compare their explanatory task on the same structured whole; VII.17 attribution remains a research lead. |

Rejected approaches: duplicate finite atomless models; taking uniform activity
values as identity of nodes; equating a finite source path with all-chain WF;
claiming that a top element eliminates all infinite ascending chains;
identifying minimal atoms with full metaphysical simplicity; treating universal
fusion as actual infinite divisibility; and using free unity/soul flags as
independent warrant. Each fails for the specific structural or semantic reason
above, not merely because an unspecified alternative is conceivable.

This is the complete proposed outcome for the coordinator's independent
semantic challenge. Its provisional assessment concerns these mathematical
comparisons and identified bridges; it is not an overall verdict on theism,
naturalism or the root. Shared imports, documentation indexes, publication and
final integrated CI belong to the coordinator.

## Claim/type self-sweep and verification

The resolved live convention `sourceRevision` is
`15f348b072188255da837578eaafc8a98f12fdf0`.
The three targets were frozen before proof work; their unchanged Challenge
SHA256 is `e719170b4de802f25110b0ba984438b80669d55a57172fb612bb99240ce8a6db`.

The self-sweep compared each statement paraphrase, inference/argument meaning,
result description, definition and Lean comment with these bound types:

- `shapeControl : ShapeControl`: the universal WF implication retains its
  graph parameter/hypothesis; the cycle is an existential Unit graph. The
  all-intrinsic finite-grounding clause and source-free lfp/gfp clauses use
  different explicit intrinsic predicates on that same graph. Nat claims are
  about the displayed strict reverse order, not arbitrary infinite graphs.
- `priorityControl : PriorityControl`: GunkCertificate and every added chain,
  no-WF and atom clause use the existing fixed region carrier/algebra. The
  reverse-chain rejection is universal over downward chains; the reverse-order
  non-WF clause is a separate claim. The existential greatest star uses the
  same carrier and certifies a unique **relative** source, while explicitly
  refuting inclusion of every converse part edge. The set-algebra atomicity
  contrast is not a physical-atom or termination claim.
- `extensionalityControl : ExtensionalityControl`: the first universal
  conditional assumes unrestricted extensionality; the second assumes strong
  supplementation. Neither assumes those policies of the actual world. The
  nonvacuous two-atom comparison uses the same fixed Body and checks both
  minimalities, distinctness, equal proper-part profiles and the failed
  unrestricted principle jointly. Its `sense_mixing_control` annotation is
  justified by this checked failure of substituting the restricted principle
  for the unrestricted one. It establishes no full metaphysical simplicity.

Focused Solution build passed with no `sorry` or new warning. The three result
bindings passed (`3 bound, 0 pinned, 0 mismatch`). Each result's Comparator and
NanoDa verification passed, with only the expected frozen Challenge `sorry`
warnings. Reproduce using `python3 scripts/worker_env.py --` before the ordinary
commands (and the heavy-job lock for builds/verification):

```text
lake build TruthCore.Results.Mereology.DependenceShapes.Solution
target/release/truth bind-check --result fbd52670-af3c-4076-bc3a-7aa7f93203d2 --result 879fff06-016b-4a5e-9b0b-3ba5b7e99633 --result 21cd4ed5-3ced-46c8-8a61-4bf427845614
bash scripts/verify-result.sh fbd52670-af3c-4076-bc3a-7aa7f93203d2
bash scripts/verify-result.sh 879fff06-016b-4a5e-9b0b-3ba5b7e99633
bash scripts/verify-result.sh 21cd4ed5-3ced-46c8-8a61-4bf427845614
```

The offline corpus check, bundle audit, spec regeneration check and Lean-module
format check passed. Attribution check found no new or changed stating claims.
No source acquisition was performed. The corpus check retains warning-only
lexicon/backfill advisories and reports seven new definition cache entries as
not computed; no shared status cache or allowlist was changed. Shared generated
imports/indexes were not edited; the coordinator owns their regeneration and final integrated CI.
The independent semantic challenge has **not** been performed by this worker.

Intended premise effect: none. The exact computed output of
`target/release/truth frontier-diff --base 956c8280973ea7d9ed085de07c6b2b50c4c9cf06`
on this delta is:

```text
premise delta for Catholicism is true: the Catholic Church is a teaching authority founded by GOD_4, and every… [53964cbe]: 956c8280973ea7d9ed085de07c6b2b50c4c9cf06 -> working tree
open premises reaching the root: 494 (353 bare, 90 supported, 51 stated) -> 494 (353 bare, 90 supported, 51 stated)
expanded-route diagnostic (lowest cost): Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16) -> Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16)
distinct verified support alternatives: 494 -> 494
verified support alternatives added: 0
no change
```

These totals describe the unchanged root graph; they are not a judgment of the
value of the controls or the comparative warrant of any metaphysical account.

## Strength-fork repair after independent review

The independent review of `cf9b2522cd73335493fbd68d6b7d021324fd3136`
accepted the full proposed outcome's semantic and quantifier boundaries, with
one required P2 repair: register the two extensionality principles as a strength
fork. This addition addresses that repair only; it does not start the subsequent
#331 investigation. The original DS-1–DS-3 definitions, proofs, sense identities,
DS-3 `sense_mixing_control` and frozen Challenge are unchanged.

The sibling principle statements are:

- `52337b28-dc07-4675-977d-c3be4b63b291`, **PROPER_PART_EXTENSIONALITY_1**:
  `ProperExtensionality B` for a supplied `B : Type` and `PartialOrder B`.
- `799b9e92-e95e-40c7-a01f-30c1b70b317f`, **PROPER_PART_EXTENSIONALITY_2**:
  `CompositeExtensionality B` for that exact same B and partial order.

Neither statement quantifies over a different domain/order, asserts population,
or assumes actual-world applicability. The new theorem
`restrictedOfUnrestricted (B : Type) [PartialOrder B]
(h : ProperExtensionality B) : CompositeExtensionality B`
restricts the two object quantifiers to composites. Its **sole Prop premise**
is the strong statement; the two composite conditions are antecedents inside
the weak conclusion, not additional corpus premises. It uses no axioms.
The argument is explicitly marked as weakening/instantiation, rather than a
new non-transcription root-support option.

Relation `33c67df1-3147-4a46-840b-18626d7276e8` registers
strong → weak using verified result `636955de-a12b-40a4-b4c6-f2062b3a70ee`.
Its `strictness_result_id` reuses the unchanged verified DS-3 result
`21cd4ed5-3ced-46c8-8a61-4bf427845614`: that certificate jointly gives
`CompositeExtensionality Body ∧ ¬ ProperExtensionality Body` along with the
two distinct minimal atoms. Thus the weak principle does not entail the strong
one over arbitrary supplied orders. This does not refute the strong principle
in every interpretation or identify minimality with full metaphysical simplicity.
No second Body model or second verification of unchanged DS-3 is introduced.

The exact added content is also certified under the existing strength schema:

```text
∀ (B : Type) [PartialOrder B],
  ProperExtensionality B ↔
    CompositeExtensionality B ∧ AtMostOneMinimal B
```

Here `AtMostOneMinimal B` means `∀ x y : B, IsMin x → IsMin y → x = y`;
it does **not** require a minimal object to exist. This difference statement is
`1eb4b406-31d1-4f40-9398-f5d53e97363e`, and exact-factorization statement
`80bb67f2-29df-4748-9c2d-add1e0e5ff6f` is verified by result
`bb3b3505-2876-4a11-acc0-0d9786d30b64`. For the reverse direction of the
factorization, equal strict-part profiles either both have a strict part, when
the restricted principle applies, or both have none, when minimal uniqueness
applies. There is no independently assumed supplementation or existence premise.
The delta states concrete uniqueness content, rather than restating STRONG or
WEAK → STRONG.

Relation `ac865453-fdde-4724-aa96-b2f2f71809c7` registers the certified
difference, using `DependenceShapesStrength.comparison`, no background and
parameter indices `[0, 1]` for all three predicates (B and its same order).
The new definitions are in
[`DependenceShapesStrength`](../TruthCore/Mereology/DependenceShapesStrength.lean),
the two new targets in its separate
[Solution](../TruthCore/Results/Mereology/DependenceShapesStrength/Solution.lean),
and all generated registrations in
[`dependence-shapes-strength.toml`](../specs/dependence-shapes-strength.toml).
The separate new Challenge was frozen before proof work, SHA256
`be52b55a1296adba4f75a79a2aa66054b2c43b90a61489a3dbfd484dd437b252`.

**Repair self-sweep:** the implication's parameter order, sole premise and
conclusion match the two sibling declarations. The exact-factorization result
quantifies over the same domain/order on both sides and asserts only a comparison.
The delta asserts uniqueness without existence. The original Body evidence
witnesses failure of converse entailment, not impossibility or falsity of the
strong principle in general. The existing sense declarations and labels remain
stable; explicit conclusion bridges record the proved restriction/factorization.
No original DS-3 assumption, conclusion or sense-mixing annotation is changed.

Focused build passed without Solution warnings. The selected live strength
check passed, including both affected result bindings, full certificate-type and
parameter binding, the nondegenerate-delta guard, Comparator and NanoDa for the
two new results. It reported `verified: true`, `proved implication`,
`exact factorization proved` and `delta_degenerate: false`. The selected
comparison has no separately registered exact-type `Separation` role; its
`converse_status: unresolved` field does not describe the separate, already
verified DS-3 strictness evidence linked by `strengthens.strictness_result_id`.
Reproduce the affected proof and strength checks with the prepared worker setup:

```text
python3 scripts/worker_env.py -- flock /tmp/moenarch/truth-core-heavy.lock lake build TruthCore.Results.Mereology.DependenceShapesStrength.Solution
python3 scripts/worker_env.py -- flock /tmp/moenarch/truth-core-heavy.lock target/release/truth strength-comparisons ac865453-fdde-4724-aa96-b2f2f71809c7 --json
```

Offline corpus validation, both specs' unchanged regeneration, bundle audit and
module-format checks passed. Original proof/Comparator evidence is reused for
unchanged inputs. No shared imports, status caches or allowlists were edited;
coordinator integration and final CI remain pending. The live convention
sourceRevision remains `15f348b072188255da837578eaafc8a98f12fdf0`.

The exact computed repair-only frontier delta is:

```text
premise delta for Catholicism is true: the Catholic Church is a teaching authority founded by GOD_4, and every… [53964cbe]: cf9b2522cd73335493fbd68d6b7d021324fd3136 -> working tree
open premises reaching the root: 494 (353 bare, 90 supported, 51 stated) -> 494 (353 bare, 90 supported, 51 stated)
expanded-route diagnostic (lowest cost): Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16) -> Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16)
distinct verified support alternatives: 494 -> 494
verified support alternatives added: 0
no change
```

The repair registers a logical order and its exact difference; it changes no
root-reaching premise and resolves none of the existing actual-power/being,
unity or uniqueness application gaps. The next coordinator reassessment remains
#331's intermediate-whole edges, outside this repair.

Exact repair paths relative to `cf9b2522` (original reviewed files outside
this list are unchanged):

```text
TruthCore/Mereology/DependenceShapesStrength.lean
TruthCore/Results/Mereology/DependenceShapesStrength/Challenge.lean
TruthCore/Results/Mereology/DependenceShapesStrength/Solution.lean
corpus/arguments/87e6caf0-3d9c-42cc-8280-7162cd42743e.json
corpus/arguments/e891585c-2077-42eb-b272-60bfce948957.json
corpus/attempts/90acb324-1d17-4ddf-9d2a-51616732e5c6.json
corpus/definitions/105f1631-62c6-4f24-aec8-1fd12a760f10.json
corpus/definitions/39de6e29-e2e8-4f4f-8463-66a075f59d99.json
corpus/disambiguations/91d5918a-a193-491d-806f-d32441ee41c5.json
corpus/inferences/9dfaa487-2f58-4402-8e8b-d87c53ee88ef.json
corpus/inferences/c476ff6e-0be5-4812-a544-d750a7fc0421.json
corpus/relations/33c67df1-3147-4a46-840b-18626d7276e8.json
corpus/relations/ac865453-fdde-4724-aa96-b2f2f71809c7.json
corpus/results/636955de-a12b-40a4-b4c6-f2062b3a70ee.json
corpus/results/bb3b3505-2876-4a11-acc0-0d9786d30b64.json
corpus/statements/1eb4b406-31d1-4f40-9398-f5d53e97363e.json
corpus/statements/52337b28-dc07-4675-977d-c3be4b63b291.json
corpus/statements/799b9e92-e95e-40c7-a01f-30c1b70b317f.json
corpus/statements/80bb67f2-29df-4748-9c2d-add1e0e5ff6f.json
docs/dependence-shapes.md
results/636955de-a12b-40a4-b4c6-f2062b3a70ee/comparator.json
results/bb3b3505-2876-4a11-acc0-0d9786d30b64/comparator.json
specs/dependence-shapes-strength.toml
```
