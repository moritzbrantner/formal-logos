# One dependence order (#1926 phase 3)

Status: verified conditional derivations and controls on branch
`research/1926-one-dependence-order`; independent semantic challenge pending.
Spec `specs/one-dependence-order.toml`, module
`TruthCore/Causality/OneDependenceOrder.lean`, results
`TruthCore/Results/Causality/OneDependenceOrder/`. Attempt record
`corpus/attempts/` "One dependence order" (this delivery).

## Question

Several stage-one premises on the God-existence routes are separate
well-foundedness assumptions over different relations:

| Statement | Relation | Family |
| --- | --- | --- |
| `fd12ad3d`, `NoInfiniteActualEsseCauseRegress` (with its per se sibling `ea251340`) | actual causes of being, `CausesIn … esse` (CAUSE_2) | De ente |
| `d85de8e1`, `SimplePriorityWellFounded` | simple priority (PRIOR_1) | prima via |
| `97f5850f`, `NoInfinitePerSeEfficientCauseSeriesReading` | per se ordered efficient causes, `CausesAsCaused` | secunda via |
| `7dfa068a`, `NoInfiniteAscentInBeing` | the comparative `MoreIn esse` (MORE_1) | quarta via |
| `82cfaf26`, `ActualGroundingWF` (AGWF) | the profile's selected grounding relation among actual concreta | modal / root fork |

Can they be derived from one well-foundedness principle over one relation,
through explicit and open inclusion bridges, without identifying cause, ground,
priority and comparison by definition (#1626; #1926 rigor contract 5)? Which
inclusions have real warrant, which fail, and is "one premise instead of
several" a real shared dependency or the same assumption presented several
times?

## The formal mechanism

Well-foundedness transfers *downward* along an inclusion: if every `R`-step is
a `G`-step (among the relevant beings) and `G` is well-founded there, then `R`
is well-founded. It never transfers upward. So a single principle can serve
several targets only if each target relation is included in the principle's
relation. The kernel `wellFounded_of_predecessorInclusion` needs only the
*predecessor* of each step to be an actual concretum, so a regress among
actual causes of being or simple priority on the whole carrier follows from
well-foundedness among actual concreta. Core Lean, no axiom.

## Results (all constructive, no axiom, controls attached)

| Result | Premises | Conclusion | Inclusion used |
| --- | --- | --- | --- |
| `esseRegressOfActualGroundingWF` | AGWF `82cfaf26`, esse cause is actual concrete ground `cb1cdea9`, in act of esse exists at w `546975ef`, esse in re is concrete `2d9807a5` | `fd12ad3d` | actual esse causing ⊆ grounding among actual concreta |
| `actualGroundingWFOfEsseRegress` | `fd12ad3d`, actual ground is distinct esse cause `98efaa9e`, existing is in act `0436de86` | AGWF | grounding among actual concreta ⊆ actual esse causing |
| `simplePriorityWFOfActualGroundingWF` | AGWF, simply prior is actual concrete ground `86efed1a`, nothing prior to itself `32d77f18` | `d85de8e1` | simple priority ⊆ grounding (predecessor actual) |
| `perSeEfficientSeriesOfPerSeEsseRegress` | per se esse regress `ea251340`, **new** per se links are PER_SE_5 actual esse causes `e8664ab8` | `97f5850f` | per se efficient causing ⊆ per se actual esse causing |

Controls (Comparator-checked theorems, facts about the stated interpretations
only): `esseRegressControls`, `converseControls`, `priorityControls` and
`secundaControls` drop each input in turn in a one-world `Bool`
interpretation in which the others hold and the conclusion fails, and give a
nonvacuous interpretation. The last conjunct of `converseControls` is the
strictness control. `ascentLimit` is the limit result below.

`ea251340` (the per se esse regress) follows from `fd12ad3d` through the
existing strength order `80f81d44`; no separate argument is added. The secunda
via step consumes the weaker `ea251340`, the weakest regress version that
suffices; its bridge is correspondingly stronger (it also asserts the PER_SE_5
link `AsCaused`).

### Verification of the earlier read-only survey

* "`controls_of_wellFounded` applies to `ActualGroundingWF` once a
  `Source ↔ ActualRoot` lemma is stated": **true, with an axiom cost**. Checked
  in a scratch file (not committed): with the graph on the actual-concreta
  subtype, `Source a ↔ ActualRoot m w a.1` holds with no axiom, and
  `controls_of_wellFounded` then applies; but that lemma uses `classical`, so
  the consequence depends on `propext`, `Classical.choice` and `Quot.sound`.
  For zero-axiom consumers `NecessaryRootFork.actualRootExists`, with excluded
  middle as an explicit hypothesis, stays the right tool (rigor contract 2).
* "One more inclusion bridge (efficient causation of esse counts as actual
  concrete grounding) derives `NoInfiniteActualEsseCauseRegress`": **partly
  wrong.** That bridge already exists (`cb1cdea9`, with `86efed1a` and the
  necessity-cause bridge as its two siblings). It does not suffice: it fires
  only when the effect is an actual concretum, and the q.3 a.4 profile's
  `InAct` is world-free. The derivation also needs the two actuality
  calibrations `546975ef` and `2d9807a5`; `esseRegressControls` drops each and
  the regress fails. No new premise was needed for this step.
* "… and the secunda via's first cause": **not by that bridge.** The secunda
  via's relation is `CausesAsCaused`, not `CausesIn … esse`. It needs a
  further inclusion, the new `e8664ab8`, whose warrant is assessed below.

## Which inclusions are warranted

Each assessment applies the Substantive Objection Standard. "Kept" means a
recorded objection with a named target, mechanism and independent
justification.

1. **Actual esse causing ⊆ grounding (`cb1cdea9` with `546975ef`,
   `2d9807a5`). Provisional assessment: well supported on the selected
   meanings.** Positive warrant: `cb1cdea9` is already derived on the root
   route from esse dependence (`2068f91c`, ST I q.44 a.1 ad 2 read for causes
   of esse) and actual dependence-to-grounding (`57f22435`); the selected
   relation `grounds w` is world-local sustaining of being, so a distinct cause
   of a thing's esse is the paradigm instance. `2d9807a5` is one direction of
   the owner-adopted CONCRETE_6 calibration (#1113, `EsseIntendedProfile`).
   `546975ef` reads the world-free `InAct x esse` at the reading world, the
   convention the stage-one vocabulary already uses
   (`NecessaryConcreteRouteBridge`: "the case's vocabulary is read at w").
   Rivals: the recorded alternative `2d08898d` (a non-concrete esse cause) is
   kept as an alternative to `cb1cdea9`; grounding read as non-causal
   determination among facts (Fine, Rosen) is **a different relation, not an
   objection**: the selected `grounds` relates concreta and is glossed as
   sustaining of being, which is Schaffer's metaphysical-causation reading;
   under a Fine/Rosen relation the bridge would have no target on its selected
   sense. Existential inertia (rival 3 of the causal-dependence assessment)
   bears on whether there are present sustaining causes at all, which
   `cb1cdea9` does not assert.

2. **Grounding ⊆ actual esse causing (`98efaa9e` with `0436de86`).
   Provisional assessment: plausible on the principal-sustaining reading, with
   a kept scope condition.** Positive warrant: on the selected reading a ground
   of a thing's being is what gives it being. Kept scope condition (rival 15 of
   the causal-dependence assessment): instrumental or compositional grounds
   satisfy the bridge only if the selected relation is principal sustaining of
   being. `0436de86` is the selected-world contract adopted for the intended
   esse profile (#1113).

3. **Simple priority ⊆ grounding (`86efed1a` with `32d77f18`). Provisional
   assessment: supported on priority in being, not on priority in a respect.**
   Positive warrant: on priority in being (In V Metaph. lect. 13 nn. 15–18;
   `47aff057`, already deriving `86efed1a` through `2adcc5ff`), what is prior
   to x is what x depends on for its being, hence its sustaining ground.
   Irreflexivity is source-stated (q.2 a.3, "prius seipso, quod est
   impossibile"). Kept counterexample on the other sense: the hand is prior to
   the stick in act in the respect of moving, and the stick does not depend on
   the hand for its being (causal-dependence-support-investigation.md,
   section (e), row 1). So `simplePriorityWFOfActualGroundingWF` transfers
   well-foundedness to priority in being. It does not reach the secunda via
   through the existing chain `d85de8e1 → e229bb2c → 42890b45 → 97f5850f`,
   which also needs all-respects `e078f07b`; that joint use is lane B's kept
   counterexample (row 21).

4. **Per se efficient causing ⊆ per se actual esse causing (new `e8664ab8`).
   Provisional assessment: contested; defensible only on the existential
   reading of the second way.** Positive warrant: on the reading of the
   secunda via as an order of causes of being here and now (the reading on
   which an essentially ordered series of *existence-giving* causes cannot be
   infinite), every per se link is a cause of the effect's being. Kept
   objection on a respect-free reading of `CausesAsCaused`. *Target:* the
   bridge's quantifier over every per se link. *Mechanism:* a per se ordered
   cause of motion is not a cause of being. *Independent justification:* ST I
   q.46 a.2 ad 7 itself gives the per se series stone–stick–hand, and the
   stick continues to be when the hand lets go. *Relevance:* the bridge is
   stated for all `CausesAsCaused` links. This is the same mechanism as row 1.
   The secunda via therefore joins the one order only where its per se links
   are causes of being. That is the exact missing condition.

5. **More in being ⊆ grounding (needed for ascent). Fails; not formalized as
   a premise.** Well-foundedness of `MoreIn esse` would follow from AGWF only
   if every comparison between actual concreta were a grounding step. Kept
   counterexample. *Target:* that inclusion. *Mechanism:* the grade compares
   beings that stand in no dependence relation; a living oak is more a being
   than a pebble and neither sustains the other. *Independent justification:*
   ordinary cases; the quarta via itself assigns a causal role only to the
   maximum (`MaximumInGenusCausesAllInGenusReading`), not to intermediate
   grades. *Relevance:* it is the only inclusion that would carry AGWF to the
   ascent premise. **`ascentLimit`** (Comparator-checked) gives a `Nat`
   interpretation in which AGWF, the esse regress, well-founded priority, the four
   recorded inclusions among esse causing, priority, grounding and the grade
   (`cb1cdea9`, `98efaa9e`, `86efed1a`, `d96105fb` ground ⊆ more), the genus
   principle `d9fad785` (vacuously), the three actuality calibrations and
   `GradesFoundInBeing` all hold, with grounding, causing and priority the single
   edge `1 → 0`, while there is an infinite ascent in being, even among actual
   concreta. The genus principle cannot help: an infinite ascent has no
   maximum, so it is vacuous there. The recorded inclusion runs the other way:
   ground ⊆ more (`d96105fb`, causa nobilior effectu) gives AGWF *from* the
   restricted no-ascent premise `c18faab2` (existing `f9c69ee8`). The quarta via
   premise therefore sits *above* grounding in this order, as its strongest
   member, not below it.

## Shared dependency or presentation?

* **Forward direction only (bridges 1, 3): a real reduction.** AGWF is not
  entailed by what it yields together with the forward bridges. The strictness
  conjunct of
  `converseControls` is an interpretation in which the forward bridges, the
  esse regress, irreflexive priority, its bridge and well-founded priority all
  hold while grounding among actual concreta is a two-cycle. So deriving
  `fd12ad3d` and `d85de8e1` from AGWF replaces two well-foundedness premises by
  one stronger premise plus bridges. It is a support option, not new evidence
  for AGWF.
* **Both directions (bridges 1 and 2): one assumption, two presentations.**
  Under `cb1cdea9`, `546975ef`, `2d9807a5`, `98efaa9e` and `0436de86`, AGWF and
  `fd12ad3d` are interderivable. On that package, warrant for one is warrant
  for the other and is not additional evidence; the two derivations close a
  support cycle, which adds no warrant by itself.
* **The strongest standing rival is unchanged by the move.** The source-free
  global-structure reply (rival 4 of the causal-dependence assessment: a
  beginningless, lawfully organized network of instruments as the whole
  explanation) targets well-foundedness as such. It bears on AGWF exactly as on
  `d85de8e1` and `fd12ad3d`. Its price is a beginningless series whose every
  member's being is derived, with no member that has its being of itself; the
  De ente other-cause step and the per se readings deny that such a series
  explains the being of any member. Concentrating the load on one premise makes
  that dependency visible; it does not answer the rival.

## Overall provisional judgment

The God-existence stage-one well-foundedness premises over *being* relations
form one order. Actual causes of being, simple priority in being and
grounding among actual concreta are included in one another through recorded,
positively supported bridges, with AGWF (or, above it, the restricted
no-ascent premise `c18faab2` with ground ⊆ more) as the single load-bearing
well-foundedness assumption. Under the two-way esse bridges, AGWF and the De
ente regress are the same assumption. Relations of causing *in a respect*
(motion, the secunda via's per se series read respect-free, priority in act)
are not included. Their only inclusions face the established hand-and-stick
counterexample. The grade relation `MoreIn esse` is not included either; it
lies above grounding, so the quarta via's premise is stronger, not derived.
Outcome label (rigor contract 6): **a new bridge** (verified conditional
derivations AGWF → `fd12ad3d`, AGWF → `d85de8e1`, `ea251340` → `97f5850f`,
and `fd12ad3d` → AGWF), with **presentational duplicates identified**
(AGWF/`fd12ad3d` under the two-way package), not consolidated by a relation.

Revision conditions: a defended non-causal reading of the selected `grounds`
relation (Fine/Rosen) on the route would cut bridge 1; a positive case that the
secunda via's per se series is existential would upgrade bridge 4; an
interpretation of `CausesAsCaused` restricted to causes of being would make
bridge 4 nearly a meaning postulate; a defended "more in being is grounding"
for actual concreta would bring the ascent premise into the order (none is
known); a defence of the source-free global structure against the
other-cause step would weaken every member at once.

## Next tests

* Register `logically_equivalent_to` between AGWF and `fd12ad3d` only as a
  conditional relation if the schema supports conditional equivalence; it does
  not today, so the interderivability stays in this note and the two results.
* A restricted bridge for the existential reading only, with a sense split of `CausesAsCaused` (in esse / in a
  respect), would separate the defensible from the contested part of bridge 4.
* Phase 2 of #1926: an `instance_of_schema` registration of the esse,
  priority and grounding regress premises as instances of the inclusion
  kernel.
