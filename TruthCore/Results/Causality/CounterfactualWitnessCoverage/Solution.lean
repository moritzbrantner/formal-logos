module

public import TruthCore.Modal.CounterfactualSelectionControls

@[expose] public section

namespace TruthCore.Results.Causality.CounterfactualWitnessCoverage

open TruthCore.Causality.Frame
open TruthCore.Causality.CounterfactualDependence
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Modal.CounterfactualSelection
open TruthCore.Modal.CounterfactualSelectionControls
open Replacement

theorem full_coverage_preserves_witnesses {W B T R : Type}
    (f : CausalityFrame W B T R) (select : Selector W) (w : W)
    (cover : CoversAccessibleAbsence f select w) :
    PreservesAccessibleAbsenceWitnesses f select w := by
  rintro x y ⟨v, hAccess, hPresent, hAbsent⟩
  exact ⟨v, hAccess, hPresent, hAbsent, cover y v hAccess hAbsent⟩

theorem dependence_excludes_being_without_of_witnesses {W B T R : Type}
    (f : CausalityFrame W B T R) (select : Selector W) (w : W)
    (CanBeWithout : B → B → Prop)
    (track : DependenceTracksSelectedAbsence f select w)
    (preserve : PreservesAccessibleAbsenceWitnesses f select w)
    (realize : BeingWithoutHasAccessibleWitness f w CanBeWithout) :
    DependenceExcludesBeingWithout f.DependsForBeing CanBeWithout := by
  intro x y hDepend hWithout
  obtain ⟨v, _, hPresent, _, hSelected⟩ := preserve x y (realize x y hWithout)
  exact track x y hDepend hSelected hPresent

/-- Structural boundary (#2103): with the selector free, soundness and witness
preservation hold for some selector exactly when the conclusion holds with
being-without read as accessible contrast. Not a registered result. -/
theorem track_preserve_iff_strict {W B T R : Type} (f : CausalityFrame W B T R) (w : W) :
    (∃ select, DependenceTracksSelectedAbsence f select w ∧
        PreservesAccessibleAbsenceWitnesses f select w) ↔
      DependenceExcludesBeingWithout f.DependsForBeing (AccessibleContrast f w) := by
  constructor
  · rintro ⟨select, track, preserve⟩ x y hDepend hContrast
    obtain ⟨v, _, hPresent, _, hSelected⟩ := preserve x y hContrast
    exact track x y hDepend hSelected hPresent
  · intro strict
    refine ⟨fun _ A v => f.history.ontic.frame.access w v ∧ v ∈ A, ?_, ?_⟩
    · intro x y hDepend v hSelected hPresent
      exact strict x y hDepend ⟨v, hSelected.1, hPresent, hSelected.2⟩
    · rintro x y ⟨v, hAccess, hPresent, hAbsent⟩
      exact ⟨v, hAccess, hPresent, hAbsent, hAccess, hAbsent⟩

theorem witness_coverage_strictness : WitnessCoverageStrictness := by
  constructor
  · rintro x y ⟨v, hAccess, hPresent, hAbsent⟩
    refine ⟨v, hAccess, hPresent, hAbsent, ⟨hAccess, hAbsent⟩, ?_⟩
    rintro rfl
    cases x
    · rcases hPresent with h | h <;> cases h
    · cases hPresent
  · intro hCover
    have hAbsent : World.near ∈ absent causalFrame true := fun h => World.noConfusion h
    exact (hCover true World.near trivial hAbsent).2 rfl

end TruthCore.Results.Causality.CounterfactualWitnessCoverage
