module

public import TruthCore.Causality.CausedMoverCStar

@[expose] public section

namespace TruthCore.Results.Causality.CausedMoverCStar

open TruthCore.Causality.CausedMoverCStar
open TruthCore.Causality.MotionMapsBatch1
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The unified operation derivation of C\* for caused movers. A caused mover
`y` moving `x` in `r` is in potency to an operation respect `o`; acting
actualizes that potency as such, so `y` is being moved in `o` (Physics III.1);
and `o` is relevant to the moving. The hypothesis that `y` is moved in some
respect is not used. -/
theorem cstarOfOperation {B R : Type} (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (OperationOf : B → B → R → R → Prop)
    (InPotency ActualizedQuaPotential : B → R → Prop) (RelevantTo : B → B → R → R → Prop)
    (hPotency : CausedMoverInPotencyToItsOperation MovesIn CausesIn esse OperationOf InPotency)
    (hActing : ActingActualizesOperationPotency MovesIn OperationOf ActualizedQuaPotential)
    (hMotion : BeingMovedIsActualizationOfPotencyReading MovedIn InPotency
      ActualizedQuaPotential)
    (hRelevant : OperationRespectIsRelevant MovesIn OperationOf RelevantTo) :
    CausedMoverMovedInRelevantRespect MovedIn MovesIn CausesIn esse RelevantTo := by
  intro y x r hCaused _ hMoves _
  obtain ⟨o, hOp, hPot⟩ := hPotency y x r hCaused hMoves
  exact ⟨o, (hMotion y o).2 ⟨hPot, hActing y x r o hMoves hOp⟩, hRelevant y x r o hMoves hOp⟩

/-- The scope bridge `b3573a61` from C\* for caused movers and the premise that
whatever is moved has its being caused by another. -/
theorem relevantRespectOfCaused {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (RelevantTo : B → B → R → R → Prop)
    (hCaused : CausedMoverMovedInRelevantRespect MovedIn MovesIn CausesIn esse RelevantTo)
    (hMovedCaused : MovedIsCaused MovedIn CausesIn esse) :
    RelevantRespectCoversEveryMovedMover MovedIn MovesIn RelevantTo := by
  intro y x r hne hMoves hMoved
  obtain ⟨r', h⟩ := hMoved
  exact hCaused y x r (hMovedCaused y r' h) hne hMoves ⟨r', h⟩

/-- The strong per se premise (`1e47e6db`) and the per se regress (`226c38f6`)
exclude reciprocal moved movers: each would be a per se link of the other, a
two-cycle that well-foundedness excludes. -/
theorem strongPerSeExcludesReciprocity {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (MovesAsMoved : B → B → Prop)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    NoTwoMoveEachOtherWhileMoved MovedIn MovesIn := by
  rintro ⟨a, b, r, s, hab, h1, h2, ha, hb⟩
  have e1 : MovesAsMoved a b := hPerSe a b r hab h1 ⟨s, ha⟩
  have e2 : MovesAsMoved b a := hPerSe b a s (fun h => hab h.symm) h2 ⟨r, hb⟩
  have key : ∀ z, Acc MovesAsMoved z → z ≠ a ∧ z ≠ b := by
    intro z hz
    induction hz with
    | intro w _ ih =>
      constructor
      · intro hw; subst hw; exact (ih b e2).2 rfl
      · intro hw; subst hw; exact (ih a e1).1 rfl
  exact (key a (hRegress a)).1 rfl

end TruthCore.Results.Causality.CausedMoverCStar
