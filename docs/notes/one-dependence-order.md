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
| `97f5850f`, `NoInfinitePerSeEfficientCauseSeriesReading` | per se ordered efficient causes, `CausesAsCaused` (SERIES_OF_CAUSES_3) | secunda via |
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
| `esseRegressOfActualGroundingWFWeak` | AGWF `82cfaf26`, **new** weak bridge `b17a8954` (`ActualEsseCauseIsActualGround`), in act of esse exists at w `546975ef`, esse in re is concrete `2d9807a5` | `fd12ad3d` | actual esse causing ⊆ grounding among actual concreta |
| `actualEsseCauseIsActualGroundOfEsseCause` | `cb1cdea9` | the weak bridge | strength step; registered `strengthens` |
| `actualGroundingWFOfEsseRegress` | `fd12ad3d`, actual ground is distinct esse cause `98efaa9e`, existing is in act `0436de86` | AGWF | grounding among actual concreta ⊆ actual esse causing |
| `simplePriorityWFOfActualGroundingWF` | AGWF, simply prior is actual concrete ground `86efed1a`, nothing prior to itself `32d77f18` | `d85de8e1` | simple priority ⊆ grounding (predecessor actual) |
| `perSeEfficientSeriesOfPerSeEsseRegress` | per se esse regress `ea251340`, **new** premise `e8664ab8` | `97f5850f` | per se efficient causing ⊆ per se actual esse causing |

Controls (Comparator-checked theorems, facts about the stated interpretations
only): `weakEsseRegressControls`, `converseControls`,
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
  calibrations `546975ef` and `2d9807a5`; `weakEsseRegressControls` drops
  each (with the weak bridge in place of `cb1cdea9`) and the regress fails.
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
   (`strengthens`), and the scope condition does not touch it. Under the
   weakest-version rule the batch derives `fd12ad3d` only through the weak
   bridge; an earlier sibling from `cb1cdea9` itself was dropped before merge.
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
   does not distinguish.** *Superseded by "Sense splits" below: PRIOR_1 is
   defined (DEF `1d9aa4d9`) as priority in act in a respect, not as an unsplit
   relation with two readings, and priority in being has been the separate
   sense PRIOR_4 since #1751.* The type is the unsplit PRIOR_1 (`F.PriorSimply`).
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
   Provisional assessment: fails on the bound sense SERIES_OF_CAUSES_3, which
   `c2880fe0` (sourced to ad 7) extends to per se mover links; defensible only
   under an existential sense of `CausesAsCaused` (now SERIES_OF_CAUSES_4, see
   "Sense splits"); the sense
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
   ascent premise. It is the only inclusion. A map-based transfer would need a
   further premise supplying the map, and `ascentLimit` shows that the listed
   premises supply none.
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
derivations AGWF → `fd12ad3d` through the weak esse bridge (itself derived
from `cb1cdea9`),
AGWF → `d85de8e1`, `ea251340` → `97f5850f`, and `fd12ad3d` → AGWF), with
**presentational duplicates identified** (AGWF/`fd12ad3d` under the two-way
package), not consolidated by a relation. The `ea251340` → `97f5850f` option
rests on `e8664ab8`, which fails on its bound sense.

Revision conditions: a defended non-causal, fact-relating reading of the
selected `grounds` relation on the route would cut bridges 1 and 2; an
existential sense of `CausesAsCaused`, split from SERIES_OF_CAUSES_3 and
positively supported as the secunda via's sense, would let a restricted
version of bridge 4 stand; a PRIOR_1 split would decide which reading the
priority derivation binds; a defended "more in being is grounding" for actual
concreta would bring the ascent premise into the order (none is known); a
defence of the source-free global structure against the other-cause step
would weaken every member at once.

## Next tests

* Sense split of `CausesAsCaused` into an existential sense (in esse) and the
  bound SERIES_OF_CAUSES_3, with `e8664ab8` restated on the existential sense
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

## Sense splits (#1926, continued, 2026-11-24)

Status: verified conditional derivations and controls on branch
`research/1926-sense-splits`. The independent semantic challenge accepted it
subject to P1 fixes, which are applied here together with its P2 repairs.
Spec `specs/dependence-order-senses.toml`, module
`TruthCore/Causality/DependenceOrderSenses.lean`, results
`TruthCore/Results/Causality/DependenceOrderSenses/`, attempt `b204e708`.
It takes up the first two next tests above.

### (i) The existential sense of the per se link

**The sense.** SERIES_OF_CAUSES_4 (definition `57348ddc`) is appended to the
"Series of causes" disambiguation `81c233d4`. There `CausesAsCaused` is
SERIES_OF_CAUSES_3, formerly labelled `CAUSES_AS_CAUSED_3` in DEF 4a101a4c
and the #1942 records.

Lean: `CausesBeingAsCaused EfficientlyCausesIn esse AsCaused c x :=
EfficientlyCausesIn c x esse ∧ AsCaused c x`. Here and now `c` efficiently causes
the being of `x` (DEF-EFFICIENT-CAUSING at the respect of being), and does so per
se, as caused. `AsCaused` is the PER_SE_5 primitive, whose definition already
glosses it as "c causes the esse of x only insofar as c's own esse is caused".

The sense is an analyst existential narrowing of the secunda via's per se link.
It is defined from two existing primitives. It is not defined from
`CausesAsCaused`, `CausesIn`, grounding or priority.

**Results** (all constructive, no axiom, Comparator and NanoDa checked):

| Result | Premises | Conclusion |
| --- | --- | --- |
| `perSeEsseSeriesOfPerSeEsseRegress` (`0d89840b`) | PER_SE_5 regress `ea251340`, restated bridge `bb7e4426` | existential no-regress `87aa978c` |
| `perSeEsseLinksOfPresentEsseCause` (`c4b9b829`) | no self-causation `8b2561cd`, present-cause bridge `622dbf36` | restated bridge `bb7e4426` |
| `perSeEsseSeriesOfPerSeEfficientSeries` (`c6a1167b`) | `97f5850f`, sense inclusion `e81ec2fe` | `87aa978c` |
| `perSeEsseLinksOfPerSeEfficientLinks` (`15f2decb`) | `e8664ab8`, sense inclusion `e81ec2fe` | `bb7e4426` |
| `perSeEsseLinkIsPerSeCauseLinkOfOrdering` (`e082dd15`) | per se ordering `8a22ae75`, `8b2561cd`, existential cause efficiently caused (new) | sense inclusion `e81ec2fe` |

**The restated bridge.** `bb7e4426` is e8664ab8 restated on SERIES_OF_CAUSES_4.
The per se conjunct is the same primitive on both sides, so its only content is
the passage from present efficient causing of being to a distinct actual cause of
being. `622dbf36` states exactly that, without the per se link. `8b2561cd` (ST I
q.2 a.3, "nec est possibile quod aliquid sit causa efficiens sui ipsius")
supplies distinctness. The uniting-cause (`57f80020`) and cause (`00e0d443`)
disambiguations now name `622dbf36` as the explicit EFFICIENT_CAUSING → CAUSE_2
passage at esse.

**Relation between the senses.** Neither inclusion is definitional
(`CausesAsCaused` is a primitive).

* With the open sense bridge `e81ec2fe` (SERIES_OF_CAUSES_4 ⊆ SERIES_OF_CAUSES_3),
  the existential relation is the narrower one. So its no-regress premise is the
  *weaker* (`c6a1167b`), and the restated bridge is weaker than e8664ab8
  (`15f2decb`).
* Without the sense bridge, the two no-regress premises are independent (second
  conjunct of `senseInclusionControls`).
* The existential premise does not entail 97f5850f (`secundaSplitLimit`).
* No `strengthens` relation is registered: each order needs the open sense
  bridge, so no single-premise strength result exists.
* The converse inclusion fails on the hand-and-stick case: the hand is a
  SERIES_OF_CAUSES_3 link through c2880fe0 and causes no being.

**Warrant for the sense bridge `e81ec2fe`.** It has a support option. It follows
from three premises:

* the secunda via's per se ordering premise `8a22ae75` (strong reading A);
* `8b2561cd`;
* the new premise that an existential link's cause is itself efficiently caused
  here and now in some respect (`e082dd15`).

That new premise closes a **kept mode gap**. `AsCaused` says only that c's esse is
caused, in an unspecified mode. DEF 4a101a4c requires a middle cause to be
efficiently caused here and now. So a cause of being whose own being was caused
non-efficiently, or not now, would be a SERIES_OF_CAUSES_4 link and no
SERIES_OF_CAUSES_3 link. No case of that kind is on file. Reading A of
`8a22ae75` is itself strong: any efficient cause caused in any respect counts as
a middle cause.

**Does the secunda via's premise join the one order?**

* On SERIES_OF_CAUSES_4, yes: AGWF `82cfaf26` → `fd12ad3d` (#1942, weak
  esse-ground bridge) → `ea251340` (`ed411e36`) → `87aa978c` (through
  `bb7e4426`).
* On the bound SERIES_OF_CAUSES_3, no. `secundaSplitLimit` (attached to
  `15f2decb`) is a `Nat` interpretation with two respects, being and motion.
  * What holds: the whole existential part of the order, non-vacuously. That is
    AGWF, the weak esse-ground bridge, both calibrations, `fd12ad3d`, `ea251340`,
    `bb7e4426`, `e81ec2fe` and `87aa978c`, with the existential link `1 → 0`.
  * Efficient causing in the motion respect is the upward successor. The
    secunda via's per se ordering premise `8a22ae75` holds, and so does
    `c2880fe0`.
  * Yet `97f5850f`, the per se mover regress and e8664ab8 all fail.
  * So under the encoded predicates, the existential order does not entail
    `97f5850f`, the mover regress or e8664ab8. That is a fact about this
    interpretation, not a claim about real series of movers or of causes of
    becoming.

**Root connection.** None changed (`frontier-diff`: no change). The root routes
consume `97f5850f` on SERIES_OF_CAUSES_3 in two ways:

* The efficient-regress Catholicism routes derive the prima via's mover regress
  from it through `c2880fe0` (`226c38f6`). That use cannot run on
  SERIES_OF_CAUSES_4, because mover links are not existential links.
* The secunda via argument `fc96d5e9` concludes `6105565d` (a first efficient
  cause, in any respect). Its SERIES_OF_CAUSES_4 counterpart would be a
  different conclusion, a first efficient cause *of being*. It would need its own
  instances of the order and priority premises at the respect of being.

**Connection plan for `87aa978c`.** The target is the De ente node `3d01134d`
(every actual distinct esse descends, via actual causes of being, from one whose
esse is its essence). It is on the GOD_4 routes.

* Missing bridges: an existential instance of the secunda via (a first efficient
  cause of being at the respect of being), and the passage from "uncaused in
  being" to "esse is essence" (the q.3 a.4 dichotomy).
* Blocker: none technical. But `3d01134d` already descends from `fd12ad3d`, which
  is stronger than `87aa978c` given `bb7e4426`. So the plan would add only a
  weaker-premise alternative.

**Source fidelity.** I materialized and read passages `aba37900` (q.2 a.3),
`a34be6a3` (q.46 a.2) and `f74e1b94` (q.104 a.1, in English).

* **The secunda via (q.2 a.3).** It speaks of an "ordo causarum efficientium"
  found in sensible things. In "invenimus ... esse ordinem", "esse" is the
  existential infinitive of an accusative-and-infinitive construction ("that
  there is an order"), not the act of being of the effects. The text does not
  restrict the series to causes of the effect's being. The removal clause
  ("remota autem causa, removetur effectus ... non erit nec effectus ultimus")
  is the hook existential readers cite. It does not by itself say that what is
  removed is the effect's being rather than its becoming or motion.
* **Ad 7 (q.46 a.2).** Its per se series are the stone, stick and hand (motion)
  and "generatio huius hominis", which depends on this man, the elementary body
  and the sun.
* **Q.104 a.1.** A same-species generator is a cause of becoming only, while a
  heavenly body is a cause of being as well. So ad 7's second series mixes the
  two and is a series of causes of the generation. Q.104 a.1 shows that Aquinas
  has the notion of a per se cause of being (preservation per se: "when what is
  preserved depends on the preserver in such a way that it cannot exist without
  it").
* **De ente cap. 3** (repository numbering, passage `7070ccdd`; Leonine c.4)
  runs a regress over causes of esse, as recorded for `fd12ad3d`. But no read
  passage restricts the secunda via's per se series to causes of being.

**Finding:** the existential reading is an analyst narrowing of the secunda via,
attribution deferred. It narrows the series' relation, which gives a weaker
no-regress premise and a different conclusion (a first efficient cause of
being). It is not a reading the read text states. Whether any commentator's
existential reading matches it is not checked here.

**Warrant.**

* `622dbf36` is positively supported by the meanings: efficient causing is one
  mode of the mode-unspecified `CausesIn`; a present agent acts only as in act; a
  present effect of being has being. No substantive objection identified beyond
  one shared reading: the q.3 a.4 profile's world-free `InAct` is read as being
  in act at the reading world (#1942).
* `e81ec2fe` is discussed above: it is supported, and its mode gap is kept.
* `87aa978c` inherits AGWF's standing. The source-free global-structure rival (a
  beginningless network in which every member's being is derived) targets it
  exactly as it targets AGWF and `fd12ad3d`. The split does not answer it.

### (ii) PRIOR_1 and PRIOR_4

**PRIOR_4 already existed.** It is `f4365b55`, `PriorityInBeing.PriorInBeing`
(In V Metaph. lect. 13 n. 15, being-without), so no new sense was needed.

PRIOR_1's definition (`1d9aa4d9`) is priority in act in a respect. On that bound
sense 86efed1a is falsified by the hand-and-stick case, given two readings: the
selected `grounds` read existentially, and the hand counted as PRIOR_1 to the
stick in the respect of moving. The verdict bears on 86efed1a's derivations
`2adcc5ff` and `931319ea` (from `47aff057`) and `8cbf4314` (from `70e98bb5`).
The positive warrant #1942 cited for 86efed1a (lect. 13 nn. 15-18, `47aff057`)
is warrant for the PRIOR_4 reading.

**Results:**

| Result | Premises | Conclusion |
| --- | --- | --- |
| `priorityInBeingWFOfActualGroundingWF` (`1dbd7440`) | AGWF `82cfaf26`, PRIOR_4 bridge `bd305511` | PRIOR_4 well-founded among actual concreta `522506d1` |
| `priorInBeingGroundOfDependence` (`67b278a7`) | `c4bb0481` (PRIOR_4 ⇒ nonmutual dependence for being), `a8298fbd` (a distinct actual dependee grounds) | `bd305511` |

The first result needs no irreflexivity premise, because PRIOR_4 is asymmetric by
definition.

`bd305511` assumes that both relata are actual concreta. So two falsifiers miss
it:

* An absent or non-concrete prior thing (86efed1a's second falsifier). On the
  real-possibility reading of CanBeWithout, every necessary abstract object is
  PRIOR_4 to every contingent being it can be without; this is the Fine-style
  overgeneration of modal dependence.
* The hand-and-stick case: the stick can be without the hand.

It is derived from `c4bb0481` and `a8298fbd`, so it shares their dependencies
(000e1f65, 8ab3d114 and excluded middle behind `c4bb0481`). It is not
independent warrant beside them. ST I q.104 a.1 runs the converse direction
(dependence to cannot-be-without), so it is not warrant for `bd305511`.

*Kept scope condition on `bd305511`:*

* Target: its grounding conclusion.
* Mechanism: a necessary condition that is no ground. A flame cannot be without
  oxygen, and oxygen can be without the flame, so oxygen is PRIOR_4 to the flame
  among actual concreta.
* Justification: the distinction between a cause and a condition.
* Relevance: the bridge then needs the selected `grounds` to count such
  conditions as grounds. The principal-sustaining reading that the converse
  bridge `98efaa9e` needs excludes them. So `bd305511` and `98efaa9e` pull the
  reading of `grounds` in opposite directions (broad and principal); no argument
  uses both.
* DEF-CAN-BE-WITHOUT fixes real possibility. Whether that means natural
  possibility or possibility by divine power, by which the flame could be
  without oxygen, is open. It decides whether such cases are PRIOR_4 at all.

**Relation PRIOR_1 / PRIOR_4.** No inclusion either way is asserted or
definitional. `priorityConsumerLimit` uses one interpretation with a PRIOR_1 pair
that is not PRIOR_4, and a second with a PRIOR_4 pair that is not PRIOR_1. That
is formal independence of the two primitives under the encoding. The substantive
cases are the ones already on file:

* reciprocal cross-respect moving excludes PRIOR_1 ⊆ PRIOR_4
  (`moverPriorityAsPriorityInBeingExcludesReciprocity`);
* PRIOR_4 ⊆ PRIOR_1 has no positive warrant beyond n. 18's "aliquo modo".

**Consumers.** The only consumer of `d85de8e1` is `e229bb2c` (→ `42890b45` →
`438866fa` → `97f5850f`). It needs PRIOR_1. Its other premise, e078f07b, makes
every efficient cause, in any respect, prior to its effect. The PRIOR_4 reading of
that shape fails by the hand-and-stick argument: the stick can be without the
hand.

`priorityConsumerLimit` shows something different: the PRIOR_4 member does not
entail `d85de8e1`, `42890b45` or the PRIOR_4 reading of e078f07b. The PRIOR_4
member is AGWF, `bd305511`, `522506d1`, and even well-founded PRIOR_4 on the
whole carrier, all holding non-vacuously with the pair `true → false`. In that
interpretation the inputs of `e229bb2c` (`57552dce`, e078f07b) and `32d77f18`
hold while `d85de8e1`, `42890b45` and 86efed1a fail.

So the weakest version that suffices for the one order on priority is
`522506d1`, and no current root-route consumer uses it. The many other arguments
that take 86efed1a as a premise (the GOD_4 existence and classical-attributes
routes) were not re-bound here.

**Connection plan for `522506d1`.**

* Target: `c51a07a1` (every first mover moved by none is first in being,
  PRIOR_4; `specs/priority-in-being.toml`). It feeds the pure-act route
  `fb8fba1e` and is on the GOD_4 routes. Today it is derived through the quarta
  via.
* Missing bridges:
  * from no infinite PRIOR_4 descent among actual concreta to "some actual
    concretum is first in being". This needs a classical minimal element and
    that what is PRIOR_4 to an actual concretum is itself an actual concretum;
  * from "the first in being" to "the first unmoved mover is first in being".
* Blocker: that second identification is the same-bearer obstacle (#1926
  findings: 89 attempts). Well-foundedness gives *some* first in being, not that
  the first mover is it.

### Updated overall provisional judgment

The one dependence order is an order of *being*. Four members share it through
recorded, positively supported bridges:

* AGWF;
* the De ente esse regress and its per se version;
* PRIOR_4 among actual concreta;
* the existential per se series.

Their known counterexamples (hand and stick; an absent or abstract prior thing)
are excluded by the bridges' scope. Two scope conditions are kept and stay open:

* `bd305511`'s condition is not a ground (oxygen and flame);
* `e81ec2fe` has its mode gap.

The stage-one regress premises the current routes consume on the prima and
secunda via are `d85de8e1` (PRIOR_1, priority in act in a respect) and
`97f5850f` (SERIES_OF_CAUSES_3, the respect-free per se link of efficient
causes, which through c2880fe0 includes mover links). They are not presentations
of AGWF. On current evidence their support comes from their own warrants:

* the per se mover series;
* the instrument argument;
* for `97f5850f`, the finite-ancestry route `b58472dd` (`e529c42f`, `37e9e7a0`,
  `f10d5632`).

None of these runs through the order. The inclusions on file face the
hand-and-stick case, and the two limit interpretations show that the order does
not entail them under the encoded predicates.

Revision conditions:

* a defended reading of the prima or secunda via on which every per se link
  causes being (no read text supports one);
* a defended PRIOR_4 → PRIOR_1 bridge for first beings (on file only as the
  first-in-being bridge, equivalent to 74eb9113);
* a root route rebuilt on the existential secunda via;
* a defence of the source-free global structure, which would weaken every
  member of the order at once.

Outcome label (rigor contract 6): **a new bridge**. The verified conditional
derivations join the existential secunda via premise and PRIOR_4 to the one
order, with per-sense restated bridges and strength comparisons conditional on
an open sense bridge. No presentational duplicates factored, no proof-body
consolidation.

### Next tests

* An existential instance of the secunda via, wired to `3d01134d`, if the
  existential series is to carry weight on a route (plan above).
* A same-bearer bridge for `522506d1` → `c51a07a1` (plan above).
* PRIOR_4 siblings of the 86efed1a consumers on the GOD_4 routes, one argument
  at a time, checking whether each downstream step needs PRIOR_1.
* Natural possibility versus possibility by divine power under
  DEF-CAN-BE-WITHOUT's real possibility. This decides the oxygen case for
  `bd305511`.
* Tooling (lane C). Lean's `Expr` equality ignores binder info, so lean4export
  hash-conses two whole definition values into one node:
  * `PerSeMoverLinkIsPerSeCauseLinkReading`'s value
    `fun {Being} (M C : Being → Being → Prop) => ∀ y x, M y x → C y x`;
  * `Subrelation`'s value `fun {α} (q r : α → α → Prop) => ∀ {a b}, q a b → r a b`.

  Those values are equal up to binder info. When a Solution's export also
  contains `Subrelation`, the exported value of the first carries implicit
  binders, and Comparator reports a value mismatch (attempt `b204e708`).
  `secundaSplitLimit` is therefore attached to `15f2decb`, whose export has no
  `Subrelation`.
