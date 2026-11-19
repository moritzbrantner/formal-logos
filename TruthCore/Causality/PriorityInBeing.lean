module

public import TruthCore.Case.Catholicism.StageOneBridges
public import TruthCore.Alternatives.NightCosmogony
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency

/-!
# Priority in being (PRIOR_4), split from priority in act in a respect (#1751)

The prima via route used one Lean relation `PriorSimply` (PRIOR_1,
DEF-SIMPLE-PRIORITY) in two senses (lane B, 2026-11-18, item (d) 4):

* priority in act in a respect, the gloss of DEF-SIMPLE-PRIORITY ("whatever is
  in potency in a respect presupposes some being in act in that respect"),
  carried by `ActSimplyPriorToPotencyReading` (a4d3261a), and
* priority in being (*In V Metaph.* lect. 13 nn. 15-18; here its first mode,
  by being-without, n. 15), used by the bridges
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

/-- PRIOR_4, priority in being in its first mode (*In V Metaph.* lect. 13 n. 15,
being-without; n. 15 says priority by nature and substance is said in three
ways, and n. 18 reduces the others to this one only *aliquo modo*): `y` is prior in
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
than it is PRIOR_1 to it. A sufficient bridge for the pure-act derivation; the
respect-matched weaker variant `RespectMatchedFirstInBeingBridge` also
suffices (`pureActOfRespectMatchedBridge`). It is not a general inclusion of
PRIOR_1 in PRIOR_4. Given `FirstUnmovedMoverIsFirstInBeing`, it is equivalent
to the content of 74eb9113 (`firstInActBridge_iff_firstBeing`), so it adds no
warrant for PRIOR_1-firstness beyond that statement. -/
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

/-! ## Checked controls on the bridge (#1751 review)

Facts about the bridge's logical strength, not registered arguments. -/

/-- Given that every first unmoved mover is first in being, the PRIOR_4 →
PRIOR_1 bridge is equivalent to the content of 74eb9113: every first unmoved
mover is first in PRIOR_1. -/
theorem firstInActBridge_iff_firstBeing {B : Sort u} {R : Sort v}
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (CanBeWithout PriorSimply : B → B → Prop)
    (hFirst : FirstUnmovedMoverIsFirstInBeing MovedIn MovesIn CanBeWithout) :
    FirstInBeingMoverIsFirstInActPriority MovedIn MovesIn CanBeWithout PriorSimply ↔
      ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → IsFirstBeing PriorSimply f :=
  ⟨fun hb f hf => hb f hf (hFirst f hf), fun h f hf _ => h f hf⟩

/-- With an empty `CanBeWithout`, first-in-being holds of every first unmoved
mover, so the bridge then is exactly the content of 74eb9113. -/
theorem firstInBeing_of_emptyCanBeWithout {B : Sort u} {R : Sort v}
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop) :
    FirstUnmovedMoverIsFirstInBeing MovedIn MovesIn (fun _ _ : B => False) :=
  fun _ _ _ h => h.1.elim

/-- A respect-matched bridge, weaker than `FirstInBeingMoverIsFirstInActPriority`:
for a first unmoved mover first in being, a being that is in act in a respect
in which the mover is in potency and is PRIOR_1 to it is the mover itself. -/
def RespectMatchedFirstInBeingBridge {B : Sort u} {R : Sort v}
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (CanBeWithout PriorSimply : B → B → Prop) (InAct InPotency : B → R → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → IsFirstBeing (PriorInBeing CanBeWithout) f →
    ∀ y r, InPotency f r → InAct y r → PriorSimply y f → y = f

/-- The registered bridge implies the respect-matched one. -/
theorem respectMatchedBridge_of_bridge {B : Sort u} {R : Sort v}
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (CanBeWithout PriorSimply : B → B → Prop) (InAct InPotency : B → R → Prop)
    (h : FirstInBeingMoverIsFirstInActPriority MovedIn MovesIn CanBeWithout PriorSimply) :
    RespectMatchedFirstInBeingBridge MovedIn MovesIn CanBeWithout PriorSimply InAct InPotency :=
  fun f hf hb y _ _ _ hP => h f hf hb y hP

/-- The respect-matched bridge suffices for pure act under adopted POTENCY_1,
with first-in-being and act's simple priority. -/
theorem pureActOfRespectMatchedBridge {B R : Type}
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (CanBeWithout PriorSimply : B → B → Prop) (InAct CanBe : B → R → Prop)
    (hFirst : FirstUnmovedMoverIsFirstInBeing MovedIn MovesIn CanBeWithout)
    (hBridge : RespectMatchedFirstInBeingBridge MovedIn MovesIn CanBeWithout PriorSimply
      InAct (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe))
    (hPrior : TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading InAct
      (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)
      PriorSimply) :
    TruthCore.Case.Catholicism.FirstUnmovedMoverIsPureAct MovedIn MovesIn
      (TruthCore.Latin.Aquinas.SummaTheologiae.PureAct
        (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)) := by
  intro f hf r hPot
  obtain ⟨y, hy, hP⟩ := hPrior f r hPot
  have hEq := hBridge f hf (hFirst f hf) y r hPot hy hP
  subst hEq
  exact hPot.2 hy

end TruthCore.Causality.PriorityInBeing
