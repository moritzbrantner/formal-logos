module

public import TruthCore.Case.Catholicism.StageOneBridges
public import TruthCore.Alternatives.NightCosmogony

/-!
# Priority in being (PRIOR_4), split from priority in act in a respect (#1751)

The prima via route used one Lean relation `PriorSimply` (PRIOR_1,
DEF-SIMPLE-PRIORITY) in two senses (lane B, 2026-11-18, item (d) 4):

* priority in act in a respect, the gloss of DEF-SIMPLE-PRIORITY ("whatever is
  in potency in a respect presupposes some being in act in that respect"),
  carried by `ActSimplyPriorToPotencyReading` (a4d3261a), and
* priority in being (*In V Metaph.* lect. 13 nn. 15-18), used by the bridges
  47aff057, 97fa3a0b and, through 70e98bb5, 5dacb0db.

This module gives the second sense its own typed relation, `PriorInBeing`,
defined from the primitive `CanBeWithout` (DEF-CAN-BE-WITHOUT, "y can be while
x is not") exactly as lect. 13 n. 15 states the criterion: *priora dicuntur,
quae possunt esse sine aliis et illa non possunt esse sine eis*. The criterion
is the definition here, so the transport from it to PRIOR_1 (the open step of
97fa3a0b) does not arise for this sense. The relation between being-without and
dependence for being (n. 18) is not built in: it stays in the explicit open
bridges 000e1f65 and 8ab3d114.

Analyst formulations, attribution deferred, except where a statement record
cites a claim. No premise is established here.
-/

@[expose] public section

namespace TruthCore.Causality.PriorityInBeing

open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover)

universe u v

/-- PRIOR_4, priority in being (*In V Metaph.* lect. 13 n. 15): `y` is prior in
being to `x` when `y` can be without `x` and `x` cannot be without `y`.
`CanBeWithout` is the primitive of DEF-CAN-BE-WITHOUT. -/
def PriorInBeing {B : Sort u} (CanBeWithout : B → B → Prop) (y x : B) : Prop :=
  CanBeWithout y x ∧ ¬ CanBeWithout x y

/-- PRIOR_4 is asymmetric by its definition, whatever `CanBeWithout` is. -/
theorem priorInBeing_asymm {B : Sort u} (CanBeWithout : B → B → Prop) {y x : B}
    (h : PriorInBeing CanBeWithout y x) : ¬ PriorInBeing CanBeWithout x y :=
  fun h' => h.2 h'.1

/-- The n. 15 criterion, read for PRIOR_4: if `y` can be without `x` and `x`
cannot be without `y`, then `y` is prior in being to `x`. Definitional for this
sense (sibling of 97fa3a0b, which concludes PRIOR_1). -/
def BeingWithoutCriterionGivesPriorityInBeing {B : Sort u}
    (CanBeWithout : B → B → Prop) : Prop :=
  ∀ y x, CanBeWithout y x → ¬ CanBeWithout x y → PriorInBeing CanBeWithout y x

/-- If `y` is prior in being to `x`, then `x` depends for its being on `y` and
`y` does not so depend on `x` (sibling of 47aff057 for PRIOR_4). With PRIOR_4
defined by being-without, this is a bridge from being-without to dependence for
being, not a definitional truth. -/
def PriorityInBeingRequiresNonmutualDependence {B : Sort u}
    (CanBeWithout DependsForBeing : B → B → Prop) : Prop :=
  ∀ y x, PriorInBeing CanBeWithout y x → DependsForBeing x y ∧ ¬ DependsForBeing y x

/-- What is prior in being to a thing is a cause of its being (sibling of
70e98bb5 for PRIOR_4). -/
def PriorInBeingIsCauseOfBeing {B : Sort u} {R : Sort v}
    (CanBeWithout : B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ y x, PriorInBeing CanBeWithout y x → CausesIn y x esse

/-- Every first mover moved by none is first in being: nothing other than it is
prior in being to it (sibling of 74eb9113 for PRIOR_4). -/
def FirstUnmovedMoverIsFirstInBeing {B : Sort u} {R : Sort v}
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (CanBeWithout : B → B → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → IsFirstBeing (PriorInBeing CanBeWithout) f

/-- Sense bridge PRIOR_4 → PRIOR_1 at first unmoved movers: a first mover moved
by none that is first in being is also first in act-priority, so nothing other
than it is PRIOR_1 to it. The weakest bridge the pure-act derivation needs;
it is not a general inclusion of PRIOR_1 in PRIOR_4. -/
def FirstInBeingMoverIsFirstInActPriority {B : Sort u} {R : Sort v}
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (CanBeWithout PriorSimply : B → B → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f →
    IsFirstBeing (PriorInBeing CanBeWithout) f → IsFirstBeing PriorSimply f

/-- Sense-mixing control: read with PRIOR_4 in place of PRIOR_1, priority from
actual moving (the shape of 6ca87431) excludes every reciprocal cross-respect
moving case, for any `CanBeWithout`. A fact about the conflated reading only. -/
def MoverPriorityAsPriorityInBeingExcludesReciprocity : Prop :=
  ∀ (B R : Type) (InAct InPotency : B → R → Prop) (MovesIn : B → B → R → Prop)
    (CanBeWithout : B → B → Prop),
    TruthCore.Alternatives.NightCosmogony.ActualMoverIsSimplyPriorReading InAct InPotency MovesIn
      (PriorInBeing CanBeWithout) →
    ¬ ∃ y x r r', y ≠ x ∧ InAct y r ∧ InPotency x r ∧ MovesIn y x r ∧
      InAct x r' ∧ InPotency y r' ∧ MovesIn x y r'

end TruthCore.Causality.PriorityInBeing
