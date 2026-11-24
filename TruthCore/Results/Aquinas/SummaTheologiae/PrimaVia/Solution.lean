module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Results.Causality.SameRespectActualization.Solution
public import TruthCore.Logic.RootDescent

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.RootDescent (acc_not_of_notNot_inherited)
theorem primaVia {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn := by
  -- Reuse the two separately checked first-way intermediate inferences.
  have hNoSelf := TruthCore.Results.Causality.SameRespectActualization.noSelfMotion
    MovedIn MovesIn InPotency InAct hPotency hAct hNotBoth
  have hAnother := TruthCore.Results.Causality.SameRespectActualization.movedByAnother
    MovedIn MovesIn hReduction hNoSelf
  -- INF-AQUINAS-ST-I-Q2-A3-FIRST-MOVER: reductio by well-founded induction
  intro hNoFirst
  -- Being moved passes up a well-founded per se series: nothing is moved.
  have hNoMotion : ∀ x, ¬ ∃ r, MovedIn x r := fun x =>
    acc_not_of_notNot_inherited (P := fun x => ∃ r, MovedIn x r)
      (fun x ⟨r, hMoved⟩ hNoUp => by
        obtain ⟨y, hDistinct, hMoves⟩ := hAnother x r hMoved
        -- If the mover y were moved in no respect, it would be a first mover;
        -- otherwise it is a second mover, one step up the series.
        exact hNoFirst ⟨y, ⟨x, r, hMoves⟩, fun r' h =>
          hNoUp ⟨y, hPerSe y x r hDistinct hMoves ⟨r', h⟩, r', h⟩⟩) (hRegress x)
  obtain ⟨x, r, hMoved⟩ := hSense
  exact hNoMotion x ⟨r, hMoved⟩
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
