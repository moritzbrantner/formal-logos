module

public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing
public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section

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
  rcases hEM (SelectedCounter f) with hCounter | hNoCounter
  · exact Or.inr hCounter
  have concreteOfActivity (x : f.Being)
      (hActivity : f.power f.selected x ∨ ∃ y, f.ontic.Causes f.selected x y) :
      f.concrete x := by
    rcases hEM (Esse f x) with hEsse | hNoEsse
    · exact hCal x hEsse
    · exact (hNoCounter ⟨x, hNoEsse, hActivity⟩).elim
  exact Or.inl ⟨fun x hp => concreteOfActivity x (.inl hp),
    fun x y hc => concreteOfActivity x (.inr ⟨y, hc⟩)⟩

/-- Eliminate the named countercases in the selected frame after using
the one-direction calibration in structural coverage. -/
theorem namedElimination (f : Frame)
    (grounds : f.World → f.Being → f.Being → Prop) (hEM : ExcludedMiddle)
    (hCal : EsseInReIsConcrete ⟨f.ontic, f.concrete, grounds⟩ f.InAct f.esse)
    (hCover : NamedCoverage f) (hFail : NamedCasesFail f) :
    OwnerCommitmentAt f.ontic f.concrete f.power f.selected := by
  rcases structuralCoverage f grounds hEM hCal with hOwner | hCounter
  · exact hOwner
  rcases hCover hCounter with hSet | hForm | hMath
  · exact (hFail.1 hSet).elim
  · exact (hFail.2.1 hForm).elim
  · exact (hFail.2.2 hMath).elim

end TruthCore.Results.Case.Catholicism.WeakEsseCalibration
