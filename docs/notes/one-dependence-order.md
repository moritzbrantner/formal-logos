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

## Sense splits (#1926, continued, 2026-11-24)

Status: verified conditional derivations and controls on branch
`research/1926-sense-splits`, pending the independent semantic challenge.
Spec `specs/dependence-order-senses.toml`, module
`TruthCore/Causality/DependenceOrderSenses.lean`, results
`TruthCore/Results/Causality/DependenceOrderSenses/`, attempt `b204e708`.
It takes up the first two next tests above.

### (i) The existential sense of the per se link

**The sense.** SERIES_OF_CAUSES_4 (definition `57348ddc`, appended to the
"Series of causes" disambiguation `81c233d4`, where `CausesAsCaused` is
SERIES_OF_CAUSES_3; the `CAUSES_AS_CAUSED_3` of the records above is that
sense). Lean: `CausesBeingAsCaused EfficientlyCausesIn esse AsCaused c x :=
EfficientlyCausesIn c x esse ∧ AsCaused c x`. Here and now `c` efficiently causes
the being of `x` (DEF-EFFICIENT-CAUSING at the respect of being), and does so per
se, as caused: `AsCaused` is the PER_SE_5 primitive, whose definition already
glosses it as "c causes the esse of x only insofar as c's own esse is caused".
The sense is defined from two existing primitives; it is not defined from
`CausesAsCaused`, `CausesIn`, grounding or priority.

**Results** (all constructive, no axiom, Comparator and NanoDa checked):

| Result | Premises | Conclusion |
| --- | --- | --- |
| `perSeEsseSeriesOfPerSeEsseRegress` (`0d89840b`) | PER_SE_5 regress `ea251340`, restated bridge `bb7e4426` | existential no-regress `87aa978c` |
| `perSeEsseLinksOfPresentEsseCause` (`c4b9b829`) | no self-causation `8b2561cd`, present-cause bridge `622dbf36` | restated bridge `bb7e4426` |
| `perSeEsseSeriesOfPerSeEfficientSeries` (`c6a1167b`) | `97f5850f`, sense inclusion `e81ec2fe` | `87aa978c` |
| `perSeEsseLinksOfPerSeEfficientLinks` (`15f2decb`) | `e8664ab8`, sense inclusion `e81ec2fe` | `bb7e4426` |

`bb7e4426` is e8664ab8 restated on SERIES_OF_CAUSES_4. Since the per se conjunct
is the same primitive on both sides, its only content is the passage from present
efficient causing of being to a distinct actual cause of being; `622dbf36` states
exactly that, without the per se link, and `8b2561cd` (ST I q.2 a.3, "nec est
possibile quod aliquid sit causa efficiens sui ipsius") supplies distinctness.

**Relation between the senses.** Neither inclusion is definitional
(`CausesAsCaused` is a primitive). With the open sense bridge `e81ec2fe`
(SERIES_OF_CAUSES_4 ⊆ SERIES_OF_CAUSES_3) the existential relation is the narrower
one, so its no-regress premise is the *weaker* (`c6a1167b`) and the restated bridge
is weaker than e8664ab8 (`15f2decb`). Without the sense bridge the two no-regress
premises are independent (second conjunct of `senseInclusionControls`), and the
existential premise never gives 97f5850f (`secundaSplitLimit`). No `strengthens`
relation is registered: each order needs the open sense bridge, so no
single-premise strength result exists. The converse inclusion fails on the
hand-and-stick case: the hand is a SERIES_OF_CAUSES_3 link through c2880fe0 and
causes no being.

**Does the secunda via's premise join the one order?** On SERIES_OF_CAUSES_4,
yes: AGWF `82cfaf26` → `fd12ad3d` (#1942, weak esse-ground bridge) → `ea251340`
(`ed411e36`) → `87aa978c` (through `bb7e4426`). On the bound SERIES_OF_CAUSES_3,
no: `secundaSplitLimit` is a `Nat` interpretation in which the whole existential
part of the order holds nonvacuously (AGWF, the weak esse-ground bridge, both
calibrations, `fd12ad3d`, `ea251340`, `bb7e4426`, `e81ec2fe`, `87aa978c`, with
the existential link `1 → 0`), while `97f5850f` and the per se mover regress fail
(an infinite upward successor series, mover links read as equal to
`CausesAsCaused`) and e8664ab8 fails. A fact about that interpretation: the
existential order puts no constraint on per se series of movers or of causes of
becoming.

**Root connection.** None changed (`frontier-diff`: no change). The root routes
consume `97f5850f` on SERIES_OF_CAUSES_3: the efficient-regress Catholicism routes
use it to derive the prima via's mover regress through c2880fe0 (`226c38f6`), and
the secunda via conclusion `6105565d` (`fc96d5e9`) uses it. Neither can run on
SERIES_OF_CAUSES_4, because mover links are not existential links. Connection plan
for `87aa978c`: a SERIES_OF_CAUSES_4 instance of the secunda via (a first
efficient cause of being), feeding the De ente root interface. No technical
blocker; its value is low while the De ente route already consumes `fd12ad3d`,
which is stronger than `87aa978c` given `bb7e4426`.

**Source fidelity** (passages materialized and read: `aba37900` q.2 a.3,
`a34be6a3` q.46 a.2, `f74e1b94` q.104 a.1 in English). The secunda via speaks of
an "ordo causarum efficientium" found in sensible things and of the removal of
the effect with the cause; it does not restrict the series to causes of the
effect's being ("esse ordinem" there is the copula, not the act of being). Ad 7
gives as per se series the stone, stick and hand (motion) and "generatio huius
hominis" depending on this man, the elementary body and the sun. By q.104 a.1 a
same-species generator is a cause of becoming only, while a heavenly body is a
cause of being as well: ad 7's second series mixes the two, and is a series of
causes of the generation. Q.104 a.1 shows that Aquinas has the notion of a per se
cause of being (preservation per se, "when what is preserved depends on the
preserver in such a way that it cannot exist without it") and De ente c.4 runs a
regress over causes of esse, but no read passage restricts the secunda via's per
se series to causes of being. **Finding:** the existential reading is an analyst
reading of the secunda via, attribution deferred; it is a narrowing of the
series' relation (so a weaker no-regress premise, and a different conclusion: a
first efficient cause of being), not a reading the read text states. Whether a
commentator's existential reading matches it is not checked here.

**Warrant.** `622dbf36`: positively supported by the meanings (efficient causing
is one mode of the mode-unspecified `CausesIn`; a present agent acts only as in
act; a present effect of being has being). No substantive objection identified,
beyond the shared reading of the q.3 a.4 profile's world-free `InAct` as being in
act at the reading world (#1942). `e81ec2fe`: supported if SERIES_OF_CAUSES_3 is
the respect-free per se link of all efficient causes, as its definition says; no
substantive objection identified. `87aa978c` inherits AGWF's standing: the
source-free global-structure rival (a beginningless network in which every
member's being is derived) targets it exactly as it targets AGWF and `fd12ad3d`;
the split does not answer it.

### (ii) PRIOR_1 and PRIOR_4

**PRIOR_4 already existed** (`f4365b55`, `PriorityInBeing.PriorInBeing`, In V
Metaph. lect. 13 n. 15, being-without). No new sense was needed. PRIOR_1's
definition (`1d9aa4d9`) is priority in act in a respect. So 86efed1a, bound to
PRIOR_1, is falsified on its bound sense by the hand-and-stick case, and the
positive warrant #1942 cited for it (lect. 13 nn. 15-18, `47aff057`) is warrant
for the PRIOR_4 reading.

**Result** `priorityInBeingWFOfActualGroundingWF` (`1dbd7440`): AGWF `82cfaf26`
and the bridge `bd305511` (between actual concreta at w, what is PRIOR_4 to the
other grounds it) give PRIOR_4 well-founded among the actual concreta at w
(`522506d1`). It needs no irreflexivity premise, because PRIOR_4 is asymmetric by
definition. The bridge assumes both relata are actual concreta, so neither the
absent or non-concrete prior thing (86efed1a's second falsifier; on the
real-possibility reading of CanBeWithout every necessary abstract object is
PRIOR_4 to every contingent being it can be without, the Fine-style
overgeneration of modal dependence) nor the hand-and-stick case (the stick can be
without the hand) touches it. *Kept scope condition* on `bd305511`. Target: its
grounding conclusion. Mechanism: a necessary condition that is no ground. A flame
cannot be without oxygen, and oxygen can be without the flame, so oxygen is
PRIOR_4 to the flame among actual concreta. Justification: the cause/condition
distinction. Relevance: the bridge then needs the selected `grounds` to count
such conditions as grounds, which the principal-sustaining reading that the
converse bridge `98efaa9e` needs excludes. Whether "possunt" is natural or
absolute possibility decides whether such cases are PRIOR_4 at all: under divine
power the flame could be without oxygen. That choice is open in DEF-CAN-BE-WITHOUT.
So `bd305511` and `98efaa9e` pull the reading of `grounds` in opposite directions
(broad and principal); no argument uses both.

**Relation PRIOR_1 / PRIOR_4.** No inclusion either way is asserted or
definitional. `priorityConsumerLimit` gives an interpretation with a PRIOR_1 pair
that is not PRIOR_4 and one with a PRIOR_4 pair that is not PRIOR_1 (formal
independence of the two primitives under the encoding). The substantive cases are
the ones already on file: reciprocal cross-respect moving excludes PRIOR_1 ⊆
PRIOR_4 (`moverPriorityAsPriorityInBeingExcludesReciprocity`), and PRIOR_4 ⊆
PRIOR_1 has no positive warrant beyond n. 18's "aliquo modo".

**Consumers.** The only consumer of `d85de8e1` is `e229bb2c` (→ `42890b45` →
`438866fa` → `97f5850f`). It needs PRIOR_1: its other premise e078f07b makes
every efficient cause, in any respect, prior to its effect, and the PRIOR_4
reading of that shape fails (the stick can be without the hand).
`priorityConsumerLimit` certifies this: there AGWF, `bd305511`, `522506d1` and
PRIOR_4 well-founded on the whole carrier hold, the inputs of `e229bb2c`
(`57552dce`, e078f07b) and `32d77f18` hold, while `d85de8e1` and `42890b45` fail
and 86efed1a fails. So the weakest version that suffices for the one order on
priority is `522506d1`, and no current root-route consumer uses it. The many
other arguments that take 86efed1a as a premise (the GOD_4 existence and
classical-attributes routes) were not re-bound here; each would need its own
PRIOR_4 sibling, and whether its downstream use needs PRIOR_1 is that argument's
question.

### Updated overall provisional judgment

The one dependence order is an order of *being*: AGWF, the De ente esse regress
(and its per se version), PRIOR_4 among actual concreta and the existential per
se series all share it through recorded, positively supported bridges whose
counterexamples have been scoped away. The stage-one premises the root routes
actually consume on the prima and secunda via (`d85de8e1` on PRIOR_1, `97f5850f`
on SERIES_OF_CAUSES_3) are about causing and priority *in a respect* (motion,
becoming). They do not share the order: their only inclusions face the
hand-and-stick case, and the two limit interpretations show the order is silent
about them. So on the current routes, the prima and secunda via regress premises
remain separate well-foundedness assumptions, not presentations of AGWF. Each
can be supported only by its own warrant: the per se mover series and the
instrument argument. Revision conditions: a defended reading of the prima or
secunda via on which every per se link causes being (no read text supports it);
a defended PRIOR_4 → PRIOR_1 bridge for first beings (on file only as the
first-in-being bridge, equivalent to 74eb9113); a root route rebuilt on the
existential secunda via.

Outcome label (rigor contract 6): **a new bridge** (verified conditional
derivations joining the existential secunda via premise and PRIOR_4 to the one
order, with per-sense restated bridges and strength comparisons conditional on an
open sense bridge). No presentational duplicates factored, no proof-body
consolidation.

### Next tests

* If the existential secunda via is to carry weight on a route: a
  SERIES_OF_CAUSES_4 instance of the secunda via conclusion, wired to the De ente
  root interface (connection plan above).
* PRIOR_4 siblings of the 86efed1a consumers on the GOD_4 routes, one argument at
  a time, checking whether each downstream step needs PRIOR_1.
* Natural versus absolute possibility in DEF-CAN-BE-WITHOUT, which decides the
  oxygen case for `bd305511`.
* Tooling (lane C): lean4export merges `∀ y x, R y x → S y x` with the
  implicit-binder body of `Subrelation`, so Comparator reports a value mismatch
  for a definition with that body when the Solution also uses `Subrelation`
  (attempt `b204e708`). `SecundaSplitLimit` omits its c2880fe0 conjunct for this
  reason.
