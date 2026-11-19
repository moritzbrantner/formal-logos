import TruthCore.Causality.CausedMoverCStar

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
  sorry

/-- The scope bridge `b3573a61` from C\* for caused movers and the premise that
whatever is moved has its being caused by another. -/
theorem relevantRespectOfCaused {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (RelevantTo : B → B → R → R → Prop)
    (hCaused : CausedMoverMovedInRelevantRespect MovedIn MovesIn CausesIn esse RelevantTo)
    (hMovedCaused : MovedIsCaused MovedIn CausesIn esse) :
    RelevantRespectCoversEveryMovedMover MovedIn MovesIn RelevantTo := by
  sorry

/-- The strong per se premise (`1e47e6db`) and the per se regress (`226c38f6`)
exclude reciprocal moved movers: each would be a per se link of the other, a
two-cycle that well-foundedness excludes. -/
theorem strongPerSeExcludesReciprocity {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (MovesAsMoved : B → B → Prop)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    NoTwoMoveEachOtherWhileMoved MovedIn MovesIn := by
  sorry

end TruthCore.Results.Causality.CausedMoverCStar
