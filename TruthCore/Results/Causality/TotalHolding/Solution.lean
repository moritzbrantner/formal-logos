module

public import TruthCore.Causality.TotalHolding
public import TruthCore.Results.Causality.HoldingMotion.Solution

@[expose] public section

namespace TruthCore.Results.Causality.TotalHolding

open TruthCore.Causality.HoldingMotion
open TruthCore.Causality.TotalHolding
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- MOTION_3 holding, unfolded to a decidable shape for the finite controls. -/
theorem heldMotion_iff {B R : Type} (InAct : B → R → Prop) (H : Holding B R) (x : B) (r : R) :
    HeldMotion InAct H x r ↔ InAct x r ∧ ∃ z, z ≠ x ∧ H.ActualizesNow z x r :=
  ⟨fun h => by cases h with | intro z hAct hzx hA => exact ⟨hAct, z, hzx, hA⟩,
    fun ⟨hAct, z, hzx, hA⟩ => ⟨z, hAct, hzx, hA⟩⟩

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
  intro hNone
  have key : ∀ x, Acc AsTotallyHeld x → ∀ z r, TotallyHolds H z x r → False := by
    intro x hAcc
    induction hAcc with
    | intro x _ ih =>
      intro z r hz
      exact hNone ⟨z, x, r, hz, fun hzHeld => by
        have hLink := hPerSe z x r hz hzHeld
        obtain ⟨_, w, hw⟩ := hzHeld
        exact ih z hLink w r hw⟩
  obtain ⟨x, r, _, z, hz⟩ := hSomething
  exact key x (hRegress x) z r hz

/-- With the bridge that a held total holder is totally held, the relative first
total holder is unheld in the act by which it holds. -/
theorem unheldTotalHolder {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (hFirst : TotalHolderNotTotallyHeldCannotBeLacking InAct H)
    (hBridge : HeldTotalHolderIsTotallyHeld InAct H) :
    UnheldTotalHolderCannotBeLacking InAct H := by
  intro hNone
  exact hFirst fun ⟨f, x, r, hf, hNot⟩ =>
    hNone ⟨f, x, r, hf, fun hHeld => hNot (hBridge f x r hf hHeld)⟩

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
  intro z x r hz hAct hLack
  obtain ⟨hActEsse, hLackEsse⟩ := hBeing x r hAct hLack
  cases hEsse x hActEsse hLackEsse with
  | intro g _ hgx hGives =>
    have hgz : g = z := hz.2.2.1 g (hAccidents g x r hgx hGives hAct hLack)
    subst hgz
    exact hGives

/-- From the potency bridge and the esse instance of concurrent actualization:
what is in potency in some respect could lack being, hence is held as to being;
so what is not held as to being is in potency in no respect. -/
theorem pureActOfUnheldInBeing {B R : Type} (InAct CanBe : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) (esse : R)
    (hPotency : PotencyBringsLackableBeing InAct CanBe L esse)
    (hEsse : LackableBeingIsHeld InAct L H esse) :
    UnheldInBeingIsPureAct InAct CanBe H esse := by
  intro f hUnheld r hPot
  obtain ⟨hAct, hLack⟩ := hPotency f r hPot
  exact hUnheld (hEsse f hAct hLack)

/-- `¬ ¬ P` fails exactly when `P` fails. -/
private theorem not_notNot {P : Prop} (h : ¬ P) : ¬ ¬ ¬ P := fun hn => hn h

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The controls of `Control.Certificate`. The finite parts are decided after
unfolding; the larger decidability instances need a raised synthesis bound. -/
theorem controls : TruthCore.Causality.TotalHolding.Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  -- (1) cards on a floor
  · models
  · models
  · models
  · intro x
    refine ⟨x, fun y hy => ?_⟩
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨2, fun z hz => by obtain ⟨_, h⟩ := hz; exact absurd h (by decide)⟩
  · models
  · intro AsHeld hPerSe hRegress
    exact TruthCore.Results.Causality.HoldingMotion.noMutualHolding _ _ AsHeld hPerSe hRegress
      (by models)
  -- (2) co-held holder
  · models
  · models
  · intro x; exact ⟨x, fun _ h => h.elim⟩
  · models
  · models
  · models
  · models
  · exact not_notNot (by models)
  · models
  · apply not_notNot
    rintro ⟨_, _, _, _, _, _, hNot⟩
    exact hNot trivial
  -- (3) giver and (4) held potency
  all_goals models

end TruthCore.Results.Causality.TotalHolding
