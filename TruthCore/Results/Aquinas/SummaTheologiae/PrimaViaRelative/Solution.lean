module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Results.Causality.SameRespectActualization.Solution
public import TruthCore.Logic.RootDescent

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaRelative
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.RootDescent (acc_not_of_notNot_inherited)
theorem primaViaRelative {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveAsMovedInRelevantRespectReading
      MovedIn MovesIn MovesAsMoved RelevantTo)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    RelativelyUnmovedMoverCannotBeLackingReading MovedIn MovesIn RelevantTo := by
  -- Reuse the two separately checked first-way intermediate inferences.
  have hNoSelf := TruthCore.Results.Causality.SameRespectActualization.noSelfMotion
    MovedIn MovesIn InPotency InAct hPotency hAct hNotBoth
  have hAnother := TruthCore.Results.Causality.SameRespectActualization.movedByAnother
    MovedIn MovesIn hReduction hNoSelf
  -- INF-AQUINAS-ST-I-Q2-A3-RELATIVE-FIRST-MOVER
  intro hNoFirst
  -- Being moved passes up a well-founded per se series: nothing is moved.
  have hNoMotion : ∀ x, ¬ ∃ r, MovedIn x r := fun x =>
    acc_not_of_notNot_inherited (P := fun x => ∃ r, MovedIn x r)
      (fun x ⟨r, hMoved⟩ hNoUp => by
        obtain ⟨y, hDistinct, hMoves⟩ := hAnother x r hMoved
        -- If y were moved in no respect relevant to moving x, it would be a
        -- relatively first mover; otherwise it is one step up the series.
        exact hNoFirst ⟨y, x, r, hMoves, fun r' ⟨hMoved', hRelevant⟩ =>
          hNoUp ⟨y, hPerSe y x r r' hDistinct hMoves hMoved' hRelevant, r', hMoved'⟩⟩)
        (hRegress x)
  obtain ⟨x, r, hMoved⟩ := hSense
  exact hNoMotion x ⟨r, hMoved⟩
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaRelative
