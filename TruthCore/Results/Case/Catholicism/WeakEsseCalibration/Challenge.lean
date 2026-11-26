import TruthCore.Case.Catholicism.CauseOfBeingHasBeing
import TruthCore.Causality.CausalConcreteRivalBoundary

namespace TruthCore.Results.Case.Catholicism.WeakEsseCalibration

open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness (OwnerCommitmentAt)
open TruthCore.Logic (ExcludedMiddle)

/-- The grounding field accompanies the same profile and is unused.
Only the direction from esse in re to concreteness is required. -/
theorem structuralCoverage (f : Frame)
    (grounds : f.World → f.Being → f.Being → Prop) (hEM : ExcludedMiddle)
    (hCal : EsseInReIsConcrete ⟨f.ontic, f.concrete, grounds⟩ f.InAct f.esse) :
    StructuralFork f := by
  sorry

/-- Eliminate the named countercases in the selected frame after using
the one-direction calibration in structural coverage. -/
theorem namedElimination (f : Frame)
    (grounds : f.World → f.Being → f.Being → Prop) (hEM : ExcludedMiddle)
    (hCal : EsseInReIsConcrete ⟨f.ontic, f.concrete, grounds⟩ f.InAct f.esse)
    (hCover : NamedCoverage f) (hFail : NamedCasesFail f) :
    OwnerCommitmentAt f.ontic f.concrete f.power f.selected := by
  sorry

end TruthCore.Results.Case.Catholicism.WeakEsseCalibration
