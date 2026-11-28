module

public import TruthCore.Causality.HoldingFirstMover

@[expose] public section

namespace TruthCore.Results.Causality.HoldingFirstMover

open TruthCore.Causality.HoldingMotion
open TruthCore.Causality.TotalHolding
open TruthCore.Causality.HoldingFirstMover
open TruthCore.Latin.Aquinas.SummaTheologiae (FirstUnmovedMoverCannotBeLackingReading)

/-- Passage (2'): the first holder, which could not lack the act by which it
holds, is held in no respect. If it were held in some respect it could lack that
act, hence could lack being, hence could lack its operative act. -/
theorem firstUnheldHolderOfUnlosable {B R : Type} (InAct : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) (esse : R)
    (hFirst : UnlosableOperativeHolderCannotBeLacking InAct L H)
    (hHeld : HeldActsAreLackable InAct L H)
    (hBeing : LackableActBringsLackableBeing InAct L esse)
    (hEvery : LackableBeingLacksEveryAct InAct L esse) :
    FirstUnheldHolderCannotBeLacking InAct H := by
  intro hNone
  apply hFirst
  rintro ⟨f, x, r, hfx, hAct, hIn, hNotLack⟩
  apply hNone
  refine ⟨f, ⟨x, r, hfx, hAct⟩, fun s hs => ?_⟩
  obtain ⟨hInS, _⟩ := heldMotion_iff.mp hs
  have hLackBeing := (hBeing f s hInS (hHeld f s hs)).2
  exact hNotLack (hEvery f r hLackBeing hIn)

/-- The MOTION_3 first holder is the First-Way reading with `MovedIn` read as
MOTION_3 holding and moving read as holding another. -/
theorem firstUnheldHolder_iff_reading {B R : Type} (InAct : B → R → Prop) (H : Holding B R) :
    FirstUnheldHolderCannotBeLacking InAct H ↔
      FirstUnmovedMoverCannotBeLackingReading (HeldMotion InAct H)
        (fun f x r => f ≠ x ∧ H.ActualizesNow f x r) :=
  Iff.rfl

/-- Bridge (3): with the two MOTION_3 → MOTION_1 sense bridges, the first holder
held in no respect gives the First-Way conclusion for `MovedIn` and `MovesIn`. -/
theorem firstMoverOfFirstUnheldHolder {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (hFirst : FirstUnheldHolderCannotBeLacking InAct H)
    (hMoving : HoldingAnotherIsMoving H MovesIn)
    (hMoved : MovedIsHeld InAct H MovedIn) :
    FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn := by
  intro hNone
  apply hFirst
  rintro ⟨f, ⟨x, r, hfx, hAct⟩, hUnheld⟩
  apply hNone
  obtain ⟨s, hs⟩ := hMoving f x r hfx hAct
  refine ⟨f, ⟨x, s, hs⟩, fun t ht => ?_⟩
  obtain ⟨u, hu⟩ := hMoved f t ht
  exact hUnheld u hu

/-- The total-holding repair feeds the relative first holder: a total holder
not MOTION_3 held in its operative respect is a holder of another unheld there. -/
theorem unheldOperativeOfUnheldTotal {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (h : UnheldTotalHolderCannotBeLacking InAct H) :
    UnheldOperativeHolderCannotBeLacking InAct H := by
  intro hNone
  apply h
  rintro ⟨f, x, r, ⟨hfx, hAct, _, _⟩, hUnheld⟩
  exact hNone ⟨f, x, r, hfx, hAct, hUnheld⟩

open TruthCore.Causality.HoldingFirstMover.Control

/-- Unfold the control models and the predicates over them, then decide. -/
local macro "models" : tactic => `(tactic| ((simp only [
  UnlosableOperativeHolderCannotBeLacking, HeldActsAreLackable,
  LackableActBringsLackableBeing, LackableBeingLacksEveryAct,
  FirstUnheldHolderCannotBeLacking, HoldingAnotherIsMoving, MovedIsHeld,
  FirstUnmovedMoverCannotBeLackingReading, heldMotion_iff, soleHolder, soleLack, heldBack,
  heldBackLack, esseLoop, esseLoopLack, allInAct]) <;> decide))

/-- Omission and nonvacuity controls (`Control.Certificate`). -/
theorem controls : Certificate :=
  ⟨⟨by models, by models, by models, by models, by models, by models, by models, by models⟩,
    ⟨by models, by models, by models, by models, by models⟩,
    ⟨by models, by models, by models, by models, by models⟩,
    ⟨by models, by models, by models⟩, ⟨by models, by models, by models⟩⟩

end TruthCore.Results.Causality.HoldingFirstMover
