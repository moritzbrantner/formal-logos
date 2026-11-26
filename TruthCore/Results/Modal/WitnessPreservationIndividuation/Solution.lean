module

public import TruthCore.Modal.WitnessPreservationIndividuation
public import TruthCore.Results.Causality.CounterfactualWitnessCoverage.Solution

@[expose] public section

namespace TruthCore.Results.Modal.WitnessPreservationIndividuation

open TruthCore.Modal.CounterfactualSelectionControls
open TruthCore.Causality.CounterfactualDependence
open World
open TruthCore.Modal.CounterfactualSelection
open TruthCore.Results.Causality.CounterfactualWitnessCoverage
open TruthCore.Modal.WitnessPreservationIndividuation

theorem origin_preserves (present : World → Prop)
    (individuate : OriginIndividuation replacementOutput present) :
    ReplacementPreservation present := by
  have onlyActual : ∀ x v, (interpretedFrame present).history.ontic.ExistsAt v x → v = actual := by
    intro x v hv
    cases x
    · have hOrigin := (individuate v).mp hv
      cases v
      · rfl
      · cases hOrigin
      · cases hOrigin
    · exact hv
  rintro x y ⟨v, _, hx, hy⟩
  obtain rfl := onlyActual x v hx
  exfalso
  cases y
  · exact hy ((individuate actual).mpr rfl)
  · exact hy rfl

theorem origin_case_exclusion (present : World → Prop)
    (individuate : OriginIndividuation replacementOutput present) :
    ReplacementExclusion present := by
  have nearLoss : ¬ present World.near := by
    intro h
    have hProducer := (individuate World.near).mp h
    cases hProducer
  exact dependence_excludes_being_without_of_witnesses
    (interpretedFrame present) (leastSelection rank) World.actual (caseCanBeWithout present)
    (case_selected_loss present nearLoss) (origin_preserves present individuate)
    (case_realization present)

end TruthCore.Results.Modal.WitnessPreservationIndividuation
