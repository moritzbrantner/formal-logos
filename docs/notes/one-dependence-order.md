# One dependence order (#1926 phase 3)

Status: verified conditional derivations and controls on branch
`research/1926-one-dependence-order`. The independent semantic challenge
accepted the derivations and controls subject to one P1 fix (the re-rating of
`e8664ab8`) and P2 repairs, all applied here. Spec
`specs/one-dependence-order.toml`, module
`TruthCore/Causality/OneDependenceOrder.lean`, results
`TruthCore/Results/Causality/OneDependenceOrder/`. Attempt record
`b2cf0e2e`.

## Question

Several stage-one premises on the God-existence routes are separate
well-foundedness assumptions over different relations:

| Statement | Relation | Family |
| --- | --- | --- |
| `fd12ad3d`, `NoInfiniteActualEsseCauseRegress` (with its per se sibling `ea251340`) | actual causes of being, `CausesIn … esse` (CAUSE_2) | De ente |
| `d85de8e1`, `SimplePriorityWellFounded` | simple priority (PRIOR_1) | prima via |
| `97f5850f`, `NoInfinitePerSeEfficientCauseSeriesReading` | per se ordered efficient causes, `CausesAsCaused` (CAUSES_AS_CAUSED_3) | secunda via |
| `7dfa068a`, `NoInfiniteAscentInBeing` | the comparative `MoreIn esse` (MORE_1) | quarta via |
| `82cfaf26`, `ActualGroundingWF` (AGWF) | the profile's selected grounding relation among actual concreta | modal / root fork |

Can they be derived from one well-foundedness principle over one relation,
through explicit and open inclusion bridges, without identifying cause, ground,
priority and comparison by definition (#1626; #1926 rigor contract 5)? Which
inclusions have real warrant, which fail, and is "one premise instead of
several" a real shared dependency or the same assumption presented several
times?

## The formal mechanism

Well-foundedness pulls back along any edge-preserving map
(`Logic.Regress.Graph.Map.wellFounded`): if every `R`-step is sent to a
`G`-step and `G` is well-founded, `R` is well-founded. It never transfers in
the other direction. An inclusion is the identity case of such a map, and it is
the case used here. So a single principle can serve several targets only if
each target relation maps into the principle's relation. The kernel
`wellFounded_of_predecessorInclusion` (core Lean, no axiom) needs only the
*predecessor* of each step to be an actual concretum, so a regress among
actual causes of being, or simple priority on the whole carrier, follows from
well-foundedness among actual concreta.

## Results (all constructive, no axiom, controls attached)

| Result | Premises | Conclusion | Inclusion used |
| --- | --- | --- | --- |
| `esseRegressOfActualGroundingWF` | AGWF `82cfaf26`, esse cause is actual concrete ground `cb1cdea9`, in act of esse exists at w `546975ef`, esse in re is concrete `2d9807a5` | `fd12ad3d` | actual esse causing ⊆ grounding among actual concreta |
| `esseRegressOfActualGroundingWFWeak` | AGWF, **new** weak bridge `ActualEsseCauseIsActualGround`, `546975ef`, `2d9807a5` | `fd12ad3d` | the same, through the weaker bridge |
| `actualEsseCauseIsActualGroundOfEsseCause` | `cb1cdea9` | the weak bridge | strength step; registered `strengthens` |
| `actualGroundingWFOfEsseRegress` | `fd12ad3d`, actual ground is distinct esse cause `98efaa9e`, existing is in act `0436de86` | AGWF | grounding among actual concreta ⊆ actual esse causing |
| `simplePriorityWFOfActualGroundingWF` | AGWF, simply prior is actual concrete ground `86efed1a`, nothing prior to itself `32d77f18` | `d85de8e1` | simple priority ⊆ grounding (predecessor actual) |
| `perSeEfficientSeriesOfPerSeEsseRegress` | per se esse regress `ea251340`, **new** premise `e8664ab8` | `97f5850f` | per se efficient causing ⊆ per se actual esse causing |

Controls (Comparator-checked theorems, facts about the stated interpretations
only): `esseRegressControls`, `weakEsseRegressControls`, `converseControls`,
`priorityControls` and `secundaControls` drop each input in turn in a
one-world `Bool` interpretation in which the others hold and the conclusion
fails, and give a nonvacuous interpretation. The last conjunct of
`converseControls` is the strictness control; in it causes of being and simple
priority are the empty relation, so the forward bridges, the regress,
irreflexivity, the priority bridge and well-founded priority hold vacuously.
`ascentLimit` is the limit result below. The law
`actualEsseCause_iff_actualGround` (lake-checked, not registered, no axiom)
states the coextension under the two-way package.

`ea251340` (the per se esse regress) follows from `fd12ad3d` through the
existing strength relation `ed411e36` (its argument `80f81d44`); no separate
argument is added. The secunda via step consumes the weaker `ea251340`, the
weakest regress version that suffices; its premise is correspondingly stronger
(it also asserts the PER_SE_5 link `AsCaused`).

### Verification of the earlier read-only survey

* "`controls_of_wellFounded` applies to `ActualGroundingWF` once a
  `Source ↔ ActualRoot` lemma is stated": **true, with an axiom cost**. Checked
  in scratch files (not committed, and independently by the reviewer): with
  the graph on the actual-concreta subtype, `Source a ↔ ActualRoot m w a.1`
  holds with no axiom, and `controls_of_wellFounded` then applies. But
  `controls_of_wellFounded` itself uses `classical`, so the consequence
  depends on `propext`, `Classical.choice` and `Quot.sound`. For zero-axiom
  consumers `NecessaryRootFork.actualRootExists`, with excluded middle as an
  explicit hypothesis, stays the right tool (rigor contract 2).
* "One more inclusion bridge (efficient causation of esse counts as actual
  concrete grounding) derives `NoInfiniteActualEsseCauseRegress`": **partly
  wrong.** That bridge already exists (`cb1cdea9`, with `86efed1a` and the
  necessity-cause bridge as its two siblings). It does not suffice: it fires
  only when the effect is an actual concretum, and the q.3 a.4 profile's
  `InAct` is world-free. The derivation also needs the two actuality
  calibrations `546975ef` and `2d9807a5`; the controls drop each and the
  regress fails.
* "… and the secunda via's first cause": **not by that bridge.** The secunda
  via's relation is `CausesAsCaused`, not `CausesIn … esse`. It needs a
  further inclusion, the new `e8664ab8`, which fails on its bound sense
  (item 4).

## Which inclusions are warranted

Each assessment applies the Substantive Objection Standard. "Kept" means a
recorded objection with a named target, mechanism and independent
justification.

**Shared dependency of bridges 1 and 2.** DEF `58fee8ed` (AGWF) gives no
gloss of the selected relation `grounds`, and DEF `c57e2682` calls it only a
stipulated world-local existential-grounding relation. The gloss "sustaining of being" belongs to DEF
`32606882`, linked from bridge `98efaa9e`. Both bridges depend on reading the
stipulated relation as existential grounding of concreta; that reading is a
shared, open interpretive commitment, not a fixed meaning.

1. **Actual esse causing ⊆ grounding (`cb1cdea9` with `546975ef`,
   `2d9807a5`). Provisional assessment: supported on the selected meanings,
   with a kept scope condition; the weak bridge removes it.** Positive warrant:
   `cb1cdea9` is already derived on the root route from esse dependence
   (`2068f91c`, ST I q.44 a.1 ad 2 read for causes of esse) and actual
   dependence-to-grounding (`57f22435`); read as existential grounding, a
   distinct cause of a thing's esse is its paradigm instance. `2d9807a5` is one
   direction of the owner-adopted CONCRETE_6 calibration (#1113,
   `EsseIntendedProfile`). `546975ef` reads the world-free `InAct x esse` at
   the reading world, the convention the stage-one vocabulary already uses
   (`NecessaryConcreteRouteBridge`: "the case's vocabulary is read at w").
   *Kept scope condition.* `CausesIn` is world-free and tenseless (DEF
   `211a6432`), and `cb1cdea9` does not restrict `c` yet concludes that `c`
   exists at w. An originating cause, or a cause of coming to be, that is
   absent at w falsifies it, unless `CausesIn … esse` is read as concurrent
   causa essendi (row 14 of causal-dependence-support-investigation.md (e);
   #1626; q.104 a.1 claims `40aefb2e`, `da9c82ed`). The weak bridge
   `ActualEsseCauseIsActualGround` (actual concretum `c`, actual concretum `x`,
   `c ≠ x`, `CausesIn c x esse` ⇒ `grounds w c x`) suffices, because the
   derivation can use the `InAct c` clause of `ActualEsseCause` with the two
   calibrations. It is registered as the weak version of `cb1cdea9`
   (`strengthens`), and the scope condition does not touch it.
   Rivals: statement `4c9908ba` (some actual concretum has a distinct existing
   non-concrete esse cause; relation `2d08898d`) is kept as an alternative to
   `cb1cdea9`. Grounding read as non-causal determination among facts (Fine,
   Rosen) is **a different relation, not an objection**, because the bound
   type relates beings, here concreta, not facts. Existential inertia (rival 3
   of the causal-dependence assessment) bears on whether there are present
   sustaining causes at all, which neither bridge asserts.

2. **Grounding ⊆ actual esse causing (`98efaa9e` with `0436de86`).
   Provisional assessment: plausible on the principal-sustaining reading, with
   a kept scope condition.** Positive warrant: on that reading (DEF
   `32606882`) a ground of a thing's being is what gives it being. Kept scope
   condition (rival 15 of the causal-dependence assessment): instrumental or
   compositional grounds satisfy the bridge only if the selected relation is
   principal sustaining of being. `0436de86` is the selected-world contract
   adopted for the intended esse profile (#1113).

3. **Simple priority ⊆ grounding (`86efed1a` with `32d77f18`). Provisional
   assessment: supported on only one of the two readings that the bound type
   does not distinguish.** The type is the unsplit PRIOR_1 (`F.PriorSimply`).
   On priority in being (In V Metaph. lect. 13 nn. 15–18; `47aff057`, already
   deriving `86efed1a` through `2adcc5ff`) what is prior to x is what x
   depends on for its being, hence its ground. Irreflexivity is source-stated
   (q.2 a.3, "prius seipso, quod est impossibile"). On priority in act in a
   respect, `86efed1a` meets the hand-and-stick counterexample: the hand is
   prior to the stick in act in the respect of moving, and the stick does not
   depend on the hand for its being (causal-dependence-support-investigation.md,
   section (e), row 1). `86efed1a`'s own paraphrase records a second
   falsifier: a non-concrete or absent simply prior thing. So the closure of
   `d85de8e1` through `simplePriorityWFOfActualGroundingWF` rests on
   `86efed1a` read in the unsplit PRIOR_1 type; the cluster assessment
   (d85de8e1 dossier) already asks for a split of simple priority, and the
   PRIOR_1 split is a next test. The derivation does not reach the secunda
   via through the existing chain (`d85de8e1` → `e229bb2c` → `42890b45`,
   then `438866fa` with `f10d5632` → `97f5850f`), which also needs all-respects
   `e078f07b`; that joint use is lane A's reciprocity case (row 21), and the
   hand-and-stick counterexample to `e078f07b` is kept.

4. **Per se efficient causing ⊆ per se actual esse causing (new `e8664ab8`).
   Provisional assessment: fails on the bound sense CAUSES_AS_CAUSED_3, which
   `c2880fe0` (sourced to ad 7) extends to per se mover links; defensible only
   under a not-yet-existing existential sense of `CausesAsCaused`; the sense
   split is the next test.** DEF `4a101a4c` names
   STMT-PER-SE-MOVER-LINK-IS-PER-SE-CAUSE-LINK as the premise extending
   `CausesAsCaused` to per se mover links: statement `c2880fe0`
   (`PerSeMoverLinkIsPerSeCauseLinkReading : ∀ y x, MovesAsMoved y x →
   CausesAsCaused y x`), proved, with stating claim `712924b7` on ad 7. So the
   respect-free reading is the bound one, and `c2880fe0` with `e8664ab8`
   entails that every per se mover is a per se actual cause of the moved
   thing's esse. *Target:* `e8664ab8`'s quantifier over every
   `CausesAsCaused` link. *Mechanism:* a per se ordered cause of motion or of
   coming to be is not thereby a cause of the effect's being. *Independent
   justification:* ST I q.46 a.2 ad 7 (passage `a34be6a3`, read) gives two per
   se series: the stone moved by the stick, moved by the hand ("sicut si lapis
   moveretur a baculo, et baculus a manu"), and the generation of this man
   depending "ab hoc homine, et a corpore elementari, et a sole", a per se
   series of causes of coming to be. The text says these are causes "quae per
   se requiruntur ad aliquem effectum"; it does not say they are causes of the
   effect's being. That the stick continues to be when the hand lets go is an
   analyst observation, not ad 7's. *Relevance:* the premise is stated for all
   `CausesAsCaused` links, on the bound sense. `e8664ab8` is kept as an open
   framework premise; the support option for `97f5850f` through it currently
   rests on a premise with a kept counterexample.

5. **More in being ⊆ grounding (needed for ascent). Fails; not formalized as
   a premise.** Well-foundedness of `MoreIn esse` would follow from AGWF only
   if every comparison between actual concreta were a grounding step. Kept
   counterexample. *Target:* that inclusion. *Mechanism:* the grade compares
   beings that stand in no dependence relation; a living oak is more a being
   than a pebble and neither grounds the other. *Independent justification:*
   ordinary cases; the quarta via itself assigns a causal role only to the
   maximum (`MaximumInGenusCausesAllInGenusReading`), not to intermediate
   grades. *Relevance:* it is the only inclusion that would carry AGWF to the
   ascent premise, and any map-based transfer faces the same counterexample.
   **`ascentLimit`** (Comparator-checked) gives a `Nat` interpretation in
   which AGWF, the esse regress, well-founded priority, the four listed
   inclusions (`cb1cdea9`, `98efaa9e`, `86efed1a`, and `d96105fb`
   ground ⊆ more), the genus principle `d9fad785` (vacuously), the three
   actuality calibrations and `GradesFoundInBeing` all hold, with grounding,
   causing and priority the single edge `1 → 0`, while there is an infinite
   ascent in being, even among actual concreta. The genus principle cannot
   help: an infinite ascent has no maximum, so it is vacuous there. The
   recorded inclusion runs the other way: ground ⊆ more (`d96105fb`, causa
   nobilior effectu) gives AGWF *from* the restricted no-ascent premise
   `c18faab2` (existing `f9c69ee8`, theorem `actualGroundingWFOfAscent` in
   `TruthCore.Results.Causality.GradedSupportFoundation`). The quarta via
   premise therefore sits *above* grounding in this order, as its strongest
   member, not below it.

## Shared dependency or presentation?

* **Forward direction only (bridges 1, 3): a real reduction.** AGWF is not
  entailed by what it yields together with the forward bridges. The strictness
  conjunct of `converseControls` is an interpretation in which those all hold,
  vacuously, while grounding among actual concreta is a two-cycle. So deriving
  `fd12ad3d` and `d85de8e1` from AGWF replaces two well-foundedness premises by
  one stronger premise plus bridges. It is a support option, not new evidence
  for AGWF.
* **Both directions (bridges 1 and 2): one assumption, two presentations.**
  Under `cb1cdea9`, `546975ef`, `2d9807a5`, `98efaa9e` and `0436de86`,
  `ActualEsseCause p c x ↔ ActualConcrete m w c ∧ ActualConcrete m w x ∧
  m.grounds w c x` (`actualEsseCause_iff_actualGround`), so AGWF and
  `fd12ad3d` are interderivable. The package's warrant is warrant for an
  extensional identification of the two relations made through explicit open
  premises. On that package warrant for one is warrant for the other and is
  not additional evidence; the two derivations close a support cycle, which
  adds no warrant by itself.
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

The stage-one well-foundedness premises over *being* relations form one order.
Simple priority (read as priority in being) is included in grounding, and
grounding (read as existential grounding of concreta) in actual esse causing;
actual esse causing is included in grounding through the esse-cause bridge or
its weak version. These are recorded, positively supported bridges, with AGWF
(or, above it, the restricted no-ascent premise `c18faab2` with ground ⊆ more)
as the single load-bearing well-foundedness assumption. Under the two-way esse
bridges, AGWF and the De ente regress are the same assumption. Relations of
causing *in a respect* (motion, the secunda via's per se series on its bound
sense, priority in act) are not included: their only inclusions face the
hand-and-stick case, and for the secunda via ad 7's own per se examples. The
grade relation `MoreIn esse` is not included either; it lies above grounding,
so the quarta via's premise is stronger, not derived.

Outcome label (rigor contract 6): **a new bridge** (verified conditional
derivations AGWF → `fd12ad3d` with the strong or the weak esse bridge,
AGWF → `d85de8e1`, `ea251340` → `97f5850f`, and `fd12ad3d` → AGWF), with
**presentational duplicates identified** (AGWF/`fd12ad3d` under the two-way
package), not consolidated by a relation. The `ea251340` → `97f5850f` option
rests on `e8664ab8`, which fails on its bound sense.

Revision conditions: a defended non-causal, fact-relating reading of the
selected `grounds` relation on the route would cut bridges 1 and 2; an
existential sense of `CausesAsCaused`, split from CAUSES_AS_CAUSED_3 and
positively supported as the secunda via's sense, would let a restricted
version of bridge 4 stand; a PRIOR_1 split would decide which reading the
priority derivation binds; a defended "more in being is grounding" for actual
concreta would bring the ascent premise into the order (none is known); a
defence of the source-free global structure against the other-cause step
would weaken every member at once.

## Next tests

* Sense split of `CausesAsCaused` into an existential sense (in esse) and the
  bound CAUSES_AS_CAUSED_3, with `e8664ab8` restated on the existential sense
  and its relation to `c2880fe0` checked.
* PRIOR_1 split into priority in being and priority in act in a respect,
  re-binding `86efed1a` and `simplePriorityWFOfActualGroundingWF`.
* Register `logically_equivalent_to` between AGWF and `fd12ad3d` only as a
  conditional relation if the schema supports conditional equivalence; it does
  not today, so the interderivability stays in this note, the two results and
  the law.
* Phase 2 of #1926: an `instance_of_schema` registration of the esse,
  priority and grounding regress premises as instances of the inclusion
  kernel.
