import TruthCore.Causality.TotalHolding
import TruthCore.Results.Causality.HoldingMotion.Solution

namespace TruthCore.Results.Causality.TotalHolding

open TruthCore.Causality.HoldingMotion
open TruthCore.Causality.TotalHolding
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Unfold the control models and the predicates over them, then decide. -/
local macro "models" : tactic => `(tactic| ((simp only [
  TruthCore.Causality.TotalHolding.Control.cardsOnFloor,
  TruthCore.Causality.TotalHolding.Control.cardsOnFloorLinks,
  TruthCore.Causality.TotalHolding.Control.coHeld,
  TruthCore.Causality.TotalHolding.Control.giver,
  TruthCore.Causality.TotalHolding.Control.giverInAct,
  TruthCore.Causality.TotalHolding.Control.giverCanBe,
  TruthCore.Causality.TotalHolding.Control.heldCanBe,
  TruthCore.Causality.TotalHolding.Control.giverLack,
  TotallyHolds, TotallyHeld, heldMotion_iff, SomeTwoHoldEachOther, SomethingIsTotallyHeld,
  TotallyHeldTotalHolderIsPerSe, ActualizerIsInAct, LackableActsAreHeld,
  HeldMoverIsHeldInItsOperativeAct, HeldTotalHolderIsTotallyHeld, LackableBeingIsHeld,
  GivingBeingHoldsLackableActs, LackableActBringsLackableBeing, PotencyBringsLackableBeing,
  EveryUnheldHolderIsPureAct, PureAct, AdoptedPotency.InPotency]) <;> decide))

/-- The total-holding First Way to a relative first total holder. Take a thing
`x` totally held in `r` by `z`. If `z` is not totally held in `r`, it is the
holder sought; if it is, `z` is a per se link of `x`, and its total holder `w`
repeats the step one link up the well-founded total-holding series. -/
theorem totalHolderNotTotallyHeld {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (AsTotallyHeld : B → B → Prop)
    (hSomething : SomethingIsTotallyHeld InAct H)
    (hPerSe : TotallyHeldTotalHolderIsPerSe InAct H AsTotallyHeld)
    (hRegress : NoInfiniteTotalHoldingSeries AsTotallyHeld) :
    TotalHolderNotTotallyHeldCannotBeLacking InAct H := by
  sorry

/-- With the bridge that a held total holder is totally held, the relative first
total holder is unheld in the act by which it holds. -/
theorem unheldTotalHolder {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (hFirst : TotalHolderNotTotallyHeldCannotBeLacking InAct H)
    (hBridge : HeldTotalHolderIsTotallyHeld InAct H) :
    UnheldTotalHolderCannotBeLacking InAct H := by
  sorry

/-- Under the esse-side bundle, a total holder of a lackable act gives being.
The held thing could lack being, so some `g` other than it gives it being; `g`
holds it in every act it could lack, the held act included; the total holder
is the only holder of that act, so it is `g`. -/
theorem totalHolderGivesBeing {B R : Type} (InAct : B → R → Prop) (L : Lackability B R)
    (H : Holding B R) (esse : R)
    (hEsse : LackableBeingIsHeld InAct L H esse)
    (hAccidents : GivingBeingHoldsLackableActs InAct L H esse)
    (hBeing : LackableActBringsLackableBeing InAct L esse) :
    TotalHolderOfLackableActGivesBeing InAct L H esse := by
  sorry

/-- From the potency bridge and the esse instance of concurrent actualization:
what is in potency in some respect could lack being, hence is held as to being;
so what is not held as to being is in potency in no respect. -/
theorem pureActOfUnheldInBeing {B R : Type} (InAct CanBe : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) (esse : R)
    (hPotency : PotencyBringsLackableBeing InAct CanBe L esse)
    (hEsse : LackableBeingIsHeld InAct L H esse) :
    UnheldInBeingIsPureAct InAct CanBe H esse := by
  sorry

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The controls of `Control.Certificate`. The finite parts are decided after
unfolding; the larger decidability instances need a raised synthesis bound. -/
theorem controls : TruthCore.Causality.TotalHolding.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.TotalHolding
