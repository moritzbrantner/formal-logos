module

public import TruthCore.Causality.CounterfactualDependence

@[expose] public section

namespace TruthCore.Results.Causality.CounterfactualDependence

open TruthCore.Causality.Frame
open TruthCore.Causality.CounterfactualDependence
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Modal.CounterfactualSelection

theorem dependence_excludes_being_without {W B T R : Type}
    (f : CausalityFrame W B T R) (select : Selector W) (w : W)
    (CanBeWithout : B → B → Prop)
    (track : DependenceTracksSelectedAbsence f select w)
    (cover : CoversAccessibleAbsence f select w)
    (realize : BeingWithoutHasAccessibleWitness f w CanBeWithout) :
    DependenceExcludesBeingWithout f.DependsForBeing CanBeWithout := by
  intro x y hDepend hWithout
  obtain ⟨v, hAccess, hExists, hAbsent⟩ := realize x y hWithout
  exact track x y hDepend (cover y v hAccess hAbsent) hExists

/-- The accessible-contrast reading (CAN_BE_WITHOUT_1) satisfies the realization
premise trivially. -/
theorem accessibleContrast_realized {W B T R : Type} (f : CausalityFrame W B T R) (w : W) :
    BeingWithoutHasAccessibleWitness f w (AccessibleContrast f w) :=
  fun _ _ contrast => contrast

/-- Structural boundary (#2103): with the selector free, soundness and full
coverage hold for some selector exactly when the conclusion holds with
being-without read as accessible contrast. The selection adds no constraint
unless it is fixed independently. Not a registered result. -/
theorem track_cover_iff_strict {W B T R : Type} (f : CausalityFrame W B T R) (w : W) :
    (∃ select, DependenceTracksSelectedAbsence f select w ∧ CoversAccessibleAbsence f select w) ↔
      DependenceExcludesBeingWithout f.DependsForBeing (AccessibleContrast f w) := by
  constructor
  · rintro ⟨select, track, cover⟩ x y hDepend ⟨v, hAccess, hPresent, hAbsent⟩
    exact track x y hDepend (cover y v hAccess hAbsent) hPresent
  · intro strict
    refine ⟨fun _ A v => f.history.ontic.frame.access w v ∧ v ∈ A, ?_,
      fun _ _ hAccess hAbsent => ⟨hAccess, hAbsent⟩⟩
    intro x y hDepend v hSelected hPresent
    exact strict x y hDepend ⟨v, hSelected.1, hPresent, hSelected.2⟩

end TruthCore.Results.Causality.CounterfactualDependence
