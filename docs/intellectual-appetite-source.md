# The intellect–will source gap

`STMT-WILL-FOLLOWS-INTELLECT` remains an open input to the classical-attributes
stage. `StageTwo.GodHasWill.godHasWill` already imports
`StageTwo.GodHasIntellect.godHasIntellect`, then uses the universal source reading
`WillFollowsIntellectReading`. There is no missing composition call. This change
preserves source distinctions needed before replacing that input with a
structural derivation; it adds no result or root route and closes no premise. [Original PR #305](https://github.com/moritzbrantner/formal-logos/pull/305)

## Verified readings

The complete articles I q.19 a.1–2 were read from the existing SCTA Leonine 1888
snapshot. The q.19 a.1 witness is reused; a.2 is a new selector in the same
unchanged Git blob. The complete question I q.80 a.1–2, including its prologue,
objections and replies, was materialized from a separately hash-pinned Latin
Corpus Thomisticum page. The page identifies the Leonine text of Rome 1889,
Busa's electronic transcription and Alarcón's revision, and claims rights for
its electronic edition. Its metadata and hashes are committed, not its text.
The selected SCTA revision has only empty placeholders for this part; the web
witness is not represented as an SCTA transcription or a translation.

Q.19 a.1 distinguishes seeking absent good from loving and delighting in good
already possessed. The latter is essential to its divine application; willing
is not inherently a deficiency. Its corpus and ad 3 also identify divine willing
with divine being and qualify its description as motion. Q.19 a.2 adds that
possession of good can issue in communicating it, insofar as possible. It does
not conclude that every possible good must be produced.

Q.80 a.1 distinguishes natural inclination following a thing's own form from a
soul's appetite following apprehension. It speaks of a power by which the animal
*can* appetitively relate to apprehended things. Its ad 2 distinguishes the
formal aspect of an object from the numerical identity of that object: one
thing can be apprehended as sensible/intelligible and appetible as suitable/good.
Q.80 a.2 distinguishes intellectual and sensitive appetite through the
apprehended object and its proportion to a passive power. Intellectual appetite
can concern singular things under a universal account, as well as immaterial
goods; it is not restricted to external objects that are universals.

## What must not be identified

- Natural appetite is not intellectual appetite. Noncognitive directedness in
  the Fifth-Way `TendsTo` API supplies no intellectual-appetite theorem.
- Having intellect or will is not an assertion of a particular current exercise.
  A capacity-to-exercise step must be stated rather than inferred from an opaque
  predicate label. This distinction does not attribute dormant cognition to God.
- Love/rest in possessed good is not deficient seeking. A model requiring an
  absent object would exclude the source's own divine case.
- Q.80's soul-power account describes appetite as passive. That feature must not
  be carried into the universal q.19 conclusion or divine willing, which q.19
  reads as divine being. The analogy of cognition-relative inclination does not
  identify God with a subject acquiring a distinct passive faculty.

These choices are linked from the existing bridge through
`DISAMB-APPETITE-POWER-AND-EXERCISE` and
`DISAMB-CREATURE-PASSIVE-APPETITE-AND-DIVINE-WILL`; natural/cognitive appetite is
separately distinguished by `DISAMB-NATURAL-AND-COGNITIVE-APPETITE`.

## Remaining A–C obligations

The candidate `AQUINAS-INTELLECTUAL-APPETITE-TO-WILL` keeps these obligations open:

A. Represent the form-relative orientation of intellectual nature toward
apprehended good, using q.19's analogy without importing creaturely passivity.

B. Explain an appetitive capacity at the level of nature/power, with seeking or
love/rest appropriately distinguished by possession. Q.80 gives useful
creaturely power structure, but that structure is not yet a universal model of
divine and created willing.

C. State how the resulting intellectual-appetite account is recognized by the
existing primitive `HasWill` predicate. Its intended sourced content is already
recorded by `DEF-HAS-WILL`; the Lean predicate has not been redefined as a
conjunction of newly introduced fields.

A–C are neither proved premises nor a claim of assumptions weaker than the old
bridge. A chain of opaque predicates with these names would only transcribe the
conclusion. A God-specific model would also need a typed account of divine
self-knowledge and known goodness, not merely the old `HasIntellect` label.
No appetite ontology or extra root wrapper is introduced here.

## Omission and discrimination controls

The following are model requirements/research controls, not newly verified Lean
results or refutations of Aquinas:

1. A subject loves its possessed good and never seeks an absent good: an
   absent-good-only definition of will fails the q.19 divine application.
2. A represented intellectual capacity has no represented current exercise:
   this blocks an unargued power-to-current-seeking inference.
3. A noncognitive thing has natural inclination without intellectual appetite:
   this blocks substituting Fifth-Way directedness for will.
4. One object has different cognitive and appetitive formal aspects: numerical
   object identity does not collapse the powers in q.80 a.1 ad 2.
5. A soul's passive appetite is proportioned to an apprehended object; divine
   willing is not thereby made externally moved or passive.
6. A proposed local appetite structure is held fixed while the independent old
   `HasWill` predicate is false: until C is justified, the old bridge does not
   follow from that structure alone. This is an API gap, not a counterexample to
   the full root theory or to the source's intended theology.

The source-only preservation changes no `Challenge`, `Solution`, existing
statement identity, root-route selection, or meanings of `HasIntellect` and
`HasWill`. All six new readings are source claims, not verified derivations.


## Boundary audit for #355 (2026-11-09)

This section preserves the audit snapshot from #1284 before the structured
capacity work below. Its unencoded-target and no-new-result statements describe
that audit; the following section supplies the finite conditional encoding while
retaining the representation-to-appetite and `HasWill` recognition gaps.

The current bounded inventory was inspected against main at `52d8cb761`.
This is an audit and rejected-lead record, not a new derivation or a claim that
all intellectual-appetite distinctions have been encoded.

* `Results.Causality.IntellectualInclination.willFromIntellectualInclination`
  takes `IntellectHasIntelligibleForm`, `EveryFormHasInclination`, and
  `IntelligibleInclinationIsWill` jointly. Its proof extracts an intelligible
  form, applies the universal inclination premise, then applies recognition.
  The conclusion is the old universal `WillFollowsIntellectReading`; no exercise,
  chosen object or output follows. The companion `controls` already supplies
  the populated one-being/two-form omission interpretations, including cognition
  without inclination and inclination without the independent `HasWill` flag.
  Do not recreate these as an IntellectWillBoundary result. Important evidence
  limit: `results/WILL-FROM-INTELLECTUAL-INCLINATION/comparator.json` lists only
  `willFromIntellectualInclination`, not `controls`; the controls have source
  proofs but are not separately compared under that configuration.
* `Results.Causality.Round5Worklist.willFromIntellectualAppetite` factors
  recognition through `IntelligibleInclinationIsIntellectualAppetite` and
  `IntellectualAppetiteIsWill`. Both are OPEN. The first produces a principle
  bearing `AppetitivePowerOf` and `FollowsIntellect`; these predicates do not
  encode a response to a represented object's goodness or possession. Adding
  another existential intermediary would only relocate recognition.
* Round5's `everyFormInclinedFromFinality` already factors inclination through
  an operation, an end and `EndDirectedOperationIsInclination`. Its
  `DirectedTo o e` does not assert that the subject cognitively represents e as
  good. Identifying these relations would hide the very bridge at issue.
* `Modal.SimplicityCollapse.optionalAct` already has no performance/output at
  world `true`; `inefficaciousAct` has performance there without output. Both
  retain the concrete `noCreation` ontology and its necessary source. Their
  clauses occur in `Results.Modal.SimplicityCollapse.core`, selected by
  `results/SIMPLICITY-COLLAPSE-CORE/comparator.json`. These are output/efficacy
  controls, not models of an intellectual subject without appetitive capacity.
* `Results.Modal.OptimalCreationChoice.checks` already contains the distinct
  tied-optimum candidates, local determinism, failed cross-world stability,
  and the strict-improvement/no-optimum consequence. `OptimalOutputs` separately
  assumes positive-output totality; `uniqueOptimalStable` separately assumes
  uniqueness of the optimal candidate, not just equality of greatest values.
  Reusing these controls does not turn rational appetite into maximizing choice,
  libertarian alternatives or temporal deliberation.

### Actual missing bridge

The unresolved inference is from **representing an end under an apprehended-good
aspect** to **an appetitive capacity responsive to that aspect**, even when the
represented good is already possessed. Neither `Intelligible f` nor
`DirectedTo o e` contains that representation/possession structure. The smallest
next investigation should hold the represented object and its goodness fixed,
vary possession, and distinguish capacity to seek absent good from capacity to
rest in possessed good. It must also admit a cognitive-only subject with the
same representations and no appetitive responses. Then test an explicit local
response-capacity constraint, restricted to the represented goods actually used,
rather than `EveryFormHasInclination` for every natural and intelligible form.
This is a proposed encoding target, not a proved weaker replacement premise.

Recognition by the old primitive `HasWill` remains a separate open bridge; a
response table cannot establish it by renaming its fields. No transfer from
capacity to present exercise or production is licensed. A God-specific use still
needs self-knowledge/known-goodness structure and must allow possessed-good rest
without creaturely passivity. This audit does not reopen the parked immateriality,
life or concrete-scope investigation (#1282).

No new vocabulary, exploration map, Challenge, Solution, source claim or result
was minted: the duplicate distinctions above were rejected, while the proposed
possession-sensitive bridge remains unencoded. The claim/type self-sweep found
no new theorem claim. All three original premises and both appetite-recognition
premises remain open; no will premise is established. Root-premise delta: none.
The unavailable `corpus.py orphans` subcommand was not treated as an idle-library
audit. Shared convention sourceRevision for this audit:
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.

## Possession-sensitive finite capacity (2026-11-09)

The follow-up to #1284 (head `1cb91ff342d673ac2c838c87e939011bf535b660`,
merged in `79b2e599e`)
inspected its exact diff, the #355 context, related propositions and the will
recognition dossiers. Its flag-level audit remains useful; the next step is
now encoded in `TruthCore/Causality/PossessionSensitiveAppetite.lean` and the
matching generated batch. This is an analyst pragmatic interpretation with
attribution deferred, not a universal definition of intellectual appetite.

One end is held fixed and is represented as good in both absent and possessed
states. `Action.acquire` makes it possessed; `Action.retain` preserves its
possession; `Action.ignore` leaves it alone. `serves` excludes acquisition of an
already possessed end, retention of an absent end, and indifference in either
state. Thus its action/end relation distinguishes seeking from resting rather
than hiding them in an appetite flag. These are hypothetical response states,
not a claim that God changes over time. An actual multi-end intellectual or
divine application remains an additional semantic obligation.

`Profile.rank` is a primitive comparative appetitive attraction input, distinct
from representation, ability and objective value. The **OPEN calibration** only
compares the appropriate response against ignoring, only where that end is
represented as good. For example, acquiring absent water or retaining possessed
water may outrank indifference. Mere cognition with zero attraction, aversion,
and unavailable response are serious alternatives, not logical errors. The
rank is not derived from representation or justified as normatively correct.
No comparison against every action, maximizing rule, unique optimum, global
form-inclination principle or actual selection is assumed. This is the weakest
comparison used by this proof; no claim of minimality across all appetite
semantics is made.

The `capacity` theorem retains two explicit inputs: local calibration and local
availability. It constructs a feasible, comparatively oriented action witness,
then checks its appropriateness and possession result by cases. Neither premise
already states this existential conclusion. `controls` fixes populated
representations in both states: the responsive profile satisfies both inputs;
the cognitive-only profile has all abilities but zero attraction and fails
capacity; the unavailable profile retains calibration but fails capacity.
Both carrying-premise omissions and nonvacuity are in the frozen Challenge and
their respective Comparator configurations. No existing choice/tie/output
controls were recreated. These finite models witness the stated pragmatic
interpretation only, not real-world applicability or metaphysical possibility.

Connection plan: the root-route target remains STMT-WILL-FOLLOWS-INTELLECT,
and hence STMT-GOD-HAS-WILL. The next unencoded inference must supply this
representation/response profile from intellect and recognize its structured
capacity by the unchanged `HasWill` predicate. The old recognition premise is
not discharged, replaced or silently identified with `Capacity`. A divine
application additionally requires known goodness/self-knowledge with possessed
good rest. No will, objective normative truth or root premise is established.
The two new results are currently disconnected support for that named bridge;
they must not be counted as completed root progress. The existing #355
`controls` Comparator coverage limitation recorded in #1284 remains unchanged.

Exact reuse boundary: the inspected existing declarations were
`Results.Causality.IntellectualInclination.willFromIntellectualInclination`
and its `controls`, `Results.Causality.Round5Worklist.willFromIntellectualAppetite`
and `everyFormInclinedFromFinality`, `Results.Modal.SimplicityCollapse.core`
(with the optional/inefficacious act interpretations), and
`Results.Modal.OptimalCreationChoice.checks`. Prefix each with `TruthCore.`.
They are reused as established scope boundaries rather than imported as
premises of the new finite proof. The original inclination Comparator config
lists the derivation only, not its controls. In contrast both new theorem names
have their own zero-axiom Comparator configurations. No broad idle-library
claim is made: `corpus.py orphans` is unavailable in this checkout; the existing
`orphan_summary.py --base origin/main` reports the two new disconnected results,
whose single missing connection plan is stated above.

## Declaration completion: capacity and exercise (2026-11-09)

The existing exercise sense `9931b112-52ba-466c-945a-c5cd7f73a8f3`
is bound to `AppetitePowerExercise.Exercise`. Its subject, object and occasion
are dependent indices, with separate seeking, love, delight and communication
constructors. Actual act relations are explicit primitives, not inferred from
names, represented goodness or ability. Seeking requires absence; the other
modes require possession. Communication carries a recipient, possibility and
actual communication independently. No transition between occasions is assumed.
The supplied interpretations separate possessed-good love from deficient
seeking and possible communication from actual communication. Their semantic
applicability remains open; they are not models of divine being.

The owner selected a relational interface for capacity sense
`183bff99-a67d-46f9-ae43-a68cba27119c`. Its full-body declaration is now
`AppetitePowerExercise.Capacity.Possessed`, parameterized by the
`AppetitePowerExercise.Capacity` content interface. Universal responsiveness
remains OPEN.
`possible o t r` is primitive appetitive ability, constrained to follow suitable
OR good apprehension; mode-specific laws distinguish absence, possession and
possible sharing. Actual act relations are independent. The structure specifies
relational content. Its separate `Capacity.Possessed` admission condition
requires a soul and a nonempty possible-response relation at some occasion;
it is not an assertion that any being actually possesses that capacity.
An empty relation can be specified but fails that admission condition. The
`idleCapacity` and `cognitiveOnly` controls hold appraisal fixed: the former
admits a possible love response without actual exercise; the latter has no
appetitive response and fails possession. Neither cognition nor the response
tag alone establishes appetitive ability. Applying the primitive possibility
relation to real souls remains an explicit semantic obligation.

This relational interface does not impose response to every apprehended good,
require current exercise, rank ends, or identify the finite one-end model with
the source power. The `selective` control has two equally apprehended possessed goods, a possible love response to one and no response to the other. It witnesses that nonempty capacity does not imply universal responsiveness.
Recognition by `HasWill` and any divine application remain open bridges.

Consumer audit: `IntellectualInclination.EveryFormHasInclination` uses
`InclinedTo : B → F → Prop`; `IntelligibleInclinationIsWill` independently
recognizes it by `HasWill`. Neither contains a soul, an object apprehended as
suitable/good, possible responses or an actual episode. Round5's
`AppetitivePowerOf` and `FollowsIntellect` factor recognition but do not supply
those fields. Completing the exercise type therefore changes no frozen theorem
or recognition premise. Root connection plan remains STMT-WILL-FOLLOWS-INTELLECT
then STMT-GOD-HAS-WILL: supply an appropriate intellect-to-capacity bridge and
justify recognition by unchanged HasWill. Capacity-to-current-act is not part
of that plan. No new argument batch or premise discharge is claimed.

### Original cognitive-appetite declaration audit (2026-11-09)

At `b043e7299d38897b864e892d8bd02dbc2f649a67`, the remaining original sense
`564e875a-6317-4c7d-a5b2-8f84b4e2f35b` and the already anchored sense
`183bff99-a67d-46f9-ae43-a68cba27119c` refer to the same definition
`44a0654e-6b36-52d6-91c2-0a5c6a13dc5c`. Cross-disambiguation identity does
not by itself resolve a body-to-type gap. The unchanged full body says
**a soul's power**; `Capacity m s` neither requires `m.isSoul s` nor a nonempty
response relation. The existing `cognitiveOnly` control already supplies an
empty specification. Copying the existing `Capacity` anchor would therefore
anchor only its content specification.

The existing body-bearing predicate `Capacity.Possessed`, parameterized by
supplied `Capacity` content, instead adds exactly soulhood and nonempty
appetitive ability at some occasion. Its supplied content already constrains
apprehension (suitable OR good) and the mode-specific possession conditions.
It requires no actual current act, absent good or universal responsiveness.
It thus interprets the full possession-bearing body without changing its words,
adding a wrapper or silently strengthening capacity to exercise. The shared
definition and both of its sense anchors now consistently use that predicate;
only the original missing-declaration allowance is removed. The declaration
completion is conditional on the explicitly primitive meaning of appetitive
ability. Concrete recognition of that relation as appetitive rather than fixed
only by natural form, soul-power applicability, and HasWill recognition remain
open semantic burdens. This registration does not assert that any real subject
satisfies the predicate.

The old root consumer has a separate migration debt. Neither
`Round5Worklist.AppetitivePowerOf` nor `FollowsIntellect` consumes this content
or its possession condition. The path remains recognition premise
`b7b10ad2-fafe-552e-8bf4-205d49f2f070`, argument
`22a7366c-57ed-5f39-8421-89e6664fa4e0`, conclusion
`090be689-b77f-51a1-9d5d-caf339169e4b`, and root argument
`1deb1d29-d514-591d-9b2d-26eb4401d371`. Completing a declaration alone would
not migrate this consumer, defend its recognition input or establish will.

A local Lean signature probe isolated a previously unanswered appraisal cell:
retain the actual `possessedLove` assignment, including its soul, possession
and actual love, but set `apprehendsGood` false. A nonempty possible-love
capacity follows suitable apprehension. Every `Exercise` constructor still
requires good appraisal, so no exercise inhabitant exists. The signature boundary is axiom-free. It is **not** a registered result,
Comparator/NanoDa certificate, model-compatible research-comparison cell,
real psychology or source-compatible interpretation. No proof-status change
is inferred. Its exclusion is a direct constructor-admission consequence.

If actual love in the intended interpretation requires good appraisal, the
explicit calibration `∀ s o t, loves s o t → apprehendsGood s o t` rules out
this signature assignment. It must then be treated as a signature stress test,
not a philosophical counterexample. Conversely, adding good appraisal to its
already fixed actual love and possession directly instantiates
`Exercise.loving`; that direction is transcription, not a new argument.
Existing idle controls isolate missing acts and need no duplication.

[Compiled appraisal control and its interpretation](../TruthCore/Causality/AppetiteAppraisal.lean#L24).

Next step: retain specification, possession, recognition and divine applicability
as separate obligations. The remaining consumer bridge must supply the content
and its possession admission from intellect, then justify recognition by the
unchanged HasWill. Before publishing the appraisal cell as a philosophical
comparison, state and test the intended love-to-good-appraisal calibration and
give any non-transcription result its owning batch/spec and final verification.
Original declaration completion count: one. New certified conditional support:
zero. Root premise and closure change: none. Attribution remains deferred.

## Research attempts citing this note

- [#355: typed the q.19 a.1 argument with forms and inclinations so that will follows intellect is…](../corpus/attempts/will-from-intellectual-inclination.json)

## Intellectual appetite, willing and self-operation (2026-11-26)

### Provisional judgment

The best current intellect-based support for GOD_4 possessing will concerns
its own apprehended good. It combines an account of an intellectual act in
which the bearer knows its own form, an account of how that good is presented
under an evaluative aspect, and a substantive principle that this evaluative
apprehension grounds an orientation of the bearer to the good. The proof
leaves that last principle open. Pure contemplation is the strongest local
challenge. The exercise of will toward a possessed intrinsic good is a
further step. Practical direction toward distinct effects has its own
evidential route through #2019–#2021.

#### From intellectual form to capacity

The general conditional is already proved by
[willFromIntellectualInclination](../TruthCore/Results/Causality/IntellectualInclination/Solution.lean).
Its three premises are intelligible-form coverage for intellect, inclination
following every form, and recognition of intelligible-form inclination as
will. Round 5 decomposes those premises separately through operation and
finality, actual understanding, and an appetitive principle. The old
inclination and recognition predicates leave the evaluative aspect implicit.

The new [same-bearer application](../TruthCore/Results/Causality/IntellectualAppetite/Solution.lean)
fixes the aspect explicitly. Given `GodHasIntellect`, it uses:

1. `GodIntellectApprehendsGood` (`700215cd`). Each qualifying bearer is in act
   through some intelligible form and apprehends a good under that same form.
   The form index tracks the intelligible presentation. The predicate adds
   appraisal to actual understanding in rows 173–174. There is no
   general premise that every possible intellect is exercising cognition.
2. `AppraisedFormInclines` (`69bbed47`). On a GOD_4 bearer and a form satisfying
   those guards, an inclination follows that form. The application uses the
   same relation `InclinedTo` as the older proof. The narrower law is sufficient
   here without requiring comparable inclinations for other forms and bearers.
3. `AppraisedInclinationIsWill` (`6f3f1c14`). The inclination is recognized as
   HAS_WILL_1 on the same bearer. The premise carries the claim that the
   orientation answers to the good under the apprehended aspect. Form-correlated
   activity could otherwise have another explanatory ground. The classification
   uses neither creaturely passive power nor a present episode as an antecedent.

`godHasWillFromAppraisedForm` binds all four premises to the existing
`GodHasWill` statement `66aecdd7`. Its exact type is universal over bearers
that satisfy GOD_4. Existence remains a separate root obligation. The finite
controls give omission assignments for each of the four inputs and a
populated positive application. In `Control.contemplator` the single bearer
has the specified intelligible appraisal and no form-relative inclination
at all. Recognition holds on that assignment, the inclination law fails,
and the bearer has no will. The model is a structural test of the inference.

`restrictFormInclination` and `restrictRecognition` prove the respective
scope reductions on the same Lean assignments. `Control.scopeIsStrict`
has an appraised case satisfying the local inclination law and a distinct
form outside the guards falsifying `EveryFormHasInclination`. The strength
order is checked here at the type level. A corpus `strengthens` edge needs
prior review of the old bindings. On new-argument preflight,
`STMT-EVERY-FORM-HAS-INCLINATION` imports both appetite senses through its
definition links, and `STMT-INTELLIGIBLE-INCLINATION-IS-WILL` imports both
HAVING_WILL_OR_APPETITE_VERSUS_EXERCISING_1 and _2. The Lean sources of the
projections quantify over a primitive orientation. They supply no conversion
from `Capacity.Possessed`, which requires soulhood. Registering either
projection with those links as a new sense bridge would overstate it.
The earlier applications and the direct assumption options remain available.

#### From capacity to exercise, life and direction

| Claim | Encoded boundary on the same bearer |
| --- | --- |
| Possession of will | `GodHasWill` uses HAS_WILL_1 and WILL_CAPACITY_VERSUS_WILLED_GIVING_1. Appetite's `Capacity.Possessed` is a separate soul-relative sense. |
| Act of will concerning a good | `Nonempty (AppetitePowerExercise.Exercise m g o t)` is a concrete episode claim in the supplied interpretation. `t` is an occasion and may represent an intrinsic act without a temporal transition. |
| Self-operation and life | `OperatingFromItselfIsLiving Operates Lives` applies at a supplied time of actual self-operation. The worked application uses pure act and `PureActLifeAtSomeTimeIsLiving` to reach the separate timeless `D.Lives g`. The existing immanent-operation route can use understanding even while will is unsettled. |
| Rational exercise and direction | WILL_CAPACITY_VERSUS_WILLED_GIVING_3 is `RationallyGivesAt F A w g x`, actual giving by an owned rational power. The worked #2020 application derives `∃ e, Directs g x e` for the same distinct actual effect using operative-plan coverage, end-omission rejection and end-recognition. WILL_CAPACITY_VERSUS_WILLED_GIVING_2 adds a same-set-up withholding witness, which those direction inputs do not supply. |

`exerciseAtPossessedGood` uses the calibration that at this possessed
apprehended good a bearer with will is either exercising it there or is
in potency in a supplied intrinsic respect. Pure act rules out the latter
on the same bearer. This calibration carries a substantive match of
respect, good and occasion. In the adopted POTENCY_1 reading,
`exerciseAtMatchedRespect` exposes its components: `CanBe g r` must
include this intrinsic exercise at the selected respect, and `InAct g r`
must deliver an actual episode in the interpretation. Pure act alone
supplies neither. Widening `r` to the ability to produce each external
effect would require a distinct warrant and can force every represented
ability into actual production. Neither theorem yields that application.

`Control.capacityAndExercise` checks populated apprehension of a possessed
good with possible love and no act, and an actual-love assignment with the
same good and occasion. `Control.pureActWithoutCalibration` checks an
independent assignment of pure act, HAS_WILL_1, appraisal and possession
with no represented exercise. Soulhood is false in that assignment. This
identifies the missing respect calibration even if the pure-act predicate
holds. The proofs do not certify a patientless metaphysical realization.

#### Scope of the prior evidence and standing rivals

The prior [source-support batch](https://github.com/moritzbrantner/formal-logos/pull/2024)
supports narrower readings of ST I q.76 a.1 and q.80 a.1–2, the possessed-good
case of q.19 a.1, and the immanent-operation reading of q.18 a.2–3.
Sourced support for agential finality in ST I–II q.1 a.2 bears on row 170.
To use rows 170/171/178 together, an operation needs its intrinsic form
and attributable end in a common respect. A ball can roll toward a drain
because it was put on a gradient. Identifying its path or endpoint alone
does not identify an intrinsic end that follows from the ball's own form.
The finality decomposition adds explanatory structure when it supplies
that intrinsic link. Otherwise the direct form–inclination premise is a
credible candidate primitive in a theory where forms specify characteristic
operations. The strongest everyday warrant is the stability of species-
characteristic activity across ordinary changes of opportunity or
interference. This warrants form-relative orientation better than it
warrants the universal quantifier over immaterial and intelligible form.
The negative test is whether good-directedness is constitutive of the
intellectual form at issue, or the good is already a sufficient terminus
of contemplation with no additional appetite. Rows 177/180 require
recognizing that same orientation as an appetitive principle and then
as possession of will. The existing `HAS_WILL_3` label in row 180 must
be read against its actual `HasWill` parameter and DEF-HAS-WILL link.
It supplies neither form-indexed actual exercise nor rational giving.

- **Pure contemplation.** In *Metaphysics* Λ.9, intellect's supreme
  actuality is explained by the excellence and identity of its
  sole primary object, itself. Dependence on another object or a switch
  of object would undermine the explanatory account of its invariant
  excellence. Λ.7 explains motion through an object of desire and
  identifies the first actuality's own life with thought. This motivates
  a pure-contemplator reconstruction that grants actual apprehension
  and rejects `AppraisedFormInclines` if form-relative appetite is an
  additional determinant of that activity. The rival explains intrinsic
  life and final attracting without an account of efficient giving in
  esse. The historical reading is narrower than the finite control:
  Λ.7 calls contemplation supremely pleasant, so Λ.9 cannot by itself
  establish absence of intrinsic rest or delight. If the pleasure is
  genuine affirmation of the apprehended good, the Thomist recognition
  may apply even on a model with no outward willing. The discriminating
  question is whether self-thinking accounts for that pleasure in full
  or is also an immanent appetitive act toward its object.
  [Aristotle, *Metaphysics* XII.7 and XII.9, Ross translation](https://classics.mit.edu/Aristotle/metaphysics.12.xii.html)
- **Procession from perfection.** *Enneads* V.4 distinguishes a perfection
  internal to the source and a consequent outgoing activity. Fire's
  outward warmth illustrates production which has its explanation in
  a source remaining what it is. Plotinus accordingly gives a positive
  replacement for effect-selection by a governing plan, and his distinction
  between the One and derivative Intellect makes the antecedent of
  `GodIntellectApprehendsGood` itself disputed for the first source.
  Taking necessary procession as the complete explanation rejects
  the inference from production to `RationallyGivesAt`, or rejects
  effect-specific operative-plan coverage (row 217) if a thin rationality
  assignment is allowed. His distinction between the One's qualified
  self-presence and ordinary intellectual multiplicity also challenges
  whether the first bearer is intellectual in the selected sense.
  In VI.8.13 Plotinus treats the One's will toward itself and its
  essential being as identical, with an explicit qualification about
  applying the language to the One. This gives independent historical
  motivation for allowing intrinsic willing alongside an account of
  procession that dispenses with practical selection of effects.
  The strongest relevant check is whether stable inward perfection can
  discriminate actual effects while satisfying the same contingency
  constraints as the theistic route. For the same giver with invariant
  set-up and factive giving, the checked fixedness law in
  [will versus chance](notes/will-versus-chance.md#2-part-a-a-necessitating-source-is-excluded-already)
  requires necessity of effects if giving is set-up necessitated. A
  rival that accepts only necessary effects can retain the mechanism
  by rejecting the shared contingency premise. The restriction applies
  to necessitating rational giving as well.
  [Plotinus, *Enneads* V.4.1–2, MacKenna translation](https://en.wikisource.org/wiki/Plotinus_(MacKenna)/Volume_4/Ennead_5.4)
  [Plotinus, *Enneads* VI.8, MacKenna translation](https://en.wikisource.org/wiki/Plotinus_(MacKenna)/Volume_5/Ennead_6.8)
- **Anthropomorphic transfer.** The objection with a mechanism targets
  recognition via a univocal passive soul-power, or the interpretation
  of every actual will as seeking an absent good. Such an exercise
  depends on a mover or a deficiency that explains a new actualization.
  Perfect contemplation or a non-receptive source suffices in the
  replacement account, so that mechanism would conflict with the
  alleged pure act. The q.19 possessed-good reading avoids that transfer.
  Its positive content is rest or affirmation in a good already
  possessed. No substantive objection to that reading follows from
  the creaturely passivity mechanism by itself. Actual exercise still
  needs the same intrinsic respect and an appraisal that meets the
  episode type.

#### Remaining discrimination

For rows 173–174 the closest positive support is the prior
[`ImmanentSelfPresence` route](notes/causal-perfection-transfer.md) and
`SelfKnownGoodIsRepresented`. Actual self-understanding supplies a form
and its primary object under its existing calibrations. Recognition of
that object's goodness under **that very intelligible form** is the
remaining input. The possession-sensitive response profile has a
retain/absence distinction but does not carry this form index into
`Appraises`. The next test is to interpret the same selected primary
species in both the self-apprehension and evaluative roles, then compare
the case of acknowledged value without any conative relation against
intrinsic affirmation of possessed good. Another description of bare
self-knowledge would leave the gap intact.

For row 181 the relevant upgrade is the positive identification of the
self-operation with an actual immanent understanding at a supplied
duration index. The downstream time-to-timeless bridge is separate.
For row 197 the fact that practical judgments can direct owned operations
supports a rational-power reading of the pertinent will, but a generic
inclination supplies no agency-frame `PowerOf` or `Rational` witness.
The matched objection is a source that possesses an intrinsic self-good
orientation while its productive power is classified independently.
The exact question is whether one power realizes both on the same giver.

Rows 217 and 235 remain applications to already exercised rational giving.
Check that a plan governs this act rather than merely describing its
foreseen output, and independently recognize an end-placement requirement
as actual direction. Row 245 already has a general type-level
specialization, `directionOfPracticalSpecification`, from the broader
effect-wise result. It has no additional evidential independence from
coverage, rejection and recognition. The governing end may differ by
effect, and the benefit and authority conclusions have separate bridges.
