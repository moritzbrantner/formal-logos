module

public import TruthCore.Science.HistoryObservationLaws
public import TruthCore.Results.Explanation.NoFoundationLawChaos.Solution
public import TruthCore.Results.Science.AdaptiveHistoryAccess.Solution

@[expose] public section

namespace TruthCore.Results.Science.HistoryObservationLaws

open MeasureTheory
open TruthCore.Science.AdaptiveHistoryAccess
open TruthCore.Science.HistoryObservationLaws
open scoped TruthCore.Science.HistoryObservationLaws
open TruthCore.Science.Identifiability
open TruthCore.Explanation.NoFoundationLawChaos (generated copySchedule toggleFrom)

private theorem law_eq_dirac {M O : Type} [MeasurableSpace O]
    (observe : M → O) (m : M) :
    (deterministic observe).law m = Measure.dirac (observe m) :=
  Measure.map_dirac' measurable_const false

private theorem identifies_law_iff {M O T : Type} [MeasurableSpace O]
    [MeasurableSingletonClass O] (observe : M → O) (target : M → T) :
    Identifies (deterministic observe).law target ↔ Identifies observe target := by
  constructor
  · intro h p q same
    apply h p q
    rw [law_eq_dirac, law_eq_dirac, same]
  · intro h p q same
    apply h p q
    rw [law_eq_dirac, law_eq_dirac] at same
    exact Measure.dirac_eq_dirac_iff.mp same

theorem historicalBoundary : HistoricalBoundary := by
  have controls := TruthCore.Results.Science.AdaptiveHistoryAccess.historyControls
  constructor
  · intro policy n identified
    exact controls.2.2.1 policy n
      ((proposition_criterion_iff _ _).mpr ((identifies_law_iff _ _).mp identified))
  · exact (identifies_law_iff _ _).mpr
      ((proposition_criterion_iff _ _).mp controls.2.2.2.2.2.2)

theorem scheduleBoundary : ScheduleBoundary := by
  intro n k hn
  dsimp only
  obtain ⟨switched, copy, _, _, _, switchedNext, copyNext⟩ :=
    TruthCore.Results.Explanation.NoFoundationLawChaos.lawSwitch.2.2 n k hn
  refine ⟨?_, ?_⟩
  · have same : prefix n (generated copySchedule) = prefix n (generated (toggleFrom k)) :=
      funext fun i => (copy.2 i.val i.isLt).trans ((switched.2 i.val i.isLt).symm)
    rw [law_eq_dirac, law_eq_dirac, same]
  · rw [law_eq_dirac, law_eq_dirac, switchedNext, copyNext]
    exact Measure.dirac_ne_dirac_iff.mpr Bool.noConfusion

end TruthCore.Results.Science.HistoryObservationLaws
