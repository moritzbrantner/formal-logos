module

public import TruthCore.Models.HyperintensionalExistence
public import TruthCore.Results.Causality.StrictGroundRepresentation.Solution

/-! Worked application of the existing Second Way route to the coextensive
existence-fact control. The selected nature edge is stipulated. Reversing its
arguments gives a test relation for the per se slot; the model's ontic cause
relation is empty. -/

@[expose] public section

namespace TruthCore.Causality.StrictGroundSupplyEdge

open TruthCore.Causality.SelectedPlgTheory
open TruthCore.Causality.SelectedPlgTheory.Control (strictForward weakOnly)
open TruthCore.Explanation.EssenceReasonSeparation (directedNature EssenceRequiresExistence)
open TruthCore.Explanation.ExistencePSR (ExistenceFact)
open TruthCore.Latin.Aquinas.SummaTheologiae (NoInfinitePerSeEfficientCauseSeriesReading)
open TruthCore.Models.HyperintensionalExistence (label supplier recipient groundProfile)
open TruthCore.Results.Causality.SelectedPlgTheory
open TruthCore.Results.Causality.StrictGroundRepresentation (foundedFromAncestralLabels)

theorem natureStrictPaths :
    DependenceHasStrictPaths (EssenceRequiresExistence directedNature)
      (fun x => label (.fact x)) strictForward := by
  rintro x y _ ⟨rfl, hy⟩
  have : y = true := ExistenceFact.fact.inj hy
  subst y
  exact ⟨label supplier, label recipient, .refl, Or.inr ⟨{false}, rfl, rfl⟩, .refl⟩

/-- This rules out every finite weak return from the endpoint of any initial
strict step, including the displayed supplier-to-recipient step. -/
theorem natureNoStrictReturn : NoStrictReturn strictForward :=
  (consistencyCriterion strictForward).mp groundProfile.1

theorem weakOnlyOmitsPath : ¬ StrictPath weakOnly (label supplier) (label recipient) := by
  obtain ⟨_, _, _, _, consistent, _, noStrictGround⟩ := groundProfile
  exact fun path => noStrictGround ((strictDerivabilityCriterion weakOnly consistent _ _).mpr path)

/-- Accessibility for the stipulated one-edge relation. The alignment is
built into the choice of relation, and the labels are finite because the
whole label type is Boolean. -/
theorem accessibleStipulatedSupply :
    NoInfinitePerSeEfficientCauseSeriesReading
      (Function.swap (EssenceRequiresExistence directedNature)) := by
  refine foundedFromAncestralLabels _ _ (fun x => label (.fact x)) strictForward
    groundProfile.1 (mapOfStrictPaths _ _ strictForward natureStrictPaths) ?_ ?_
  · rintro y x ⟨rfl, hy⟩
    have : y = true := ExistenceFact.fact.inj hy
    subst y
    exact ⟨by decide, rfl, rfl⟩
  · intro x
    exact Set.toFinite _

end TruthCore.Causality.StrictGroundSupplyEdge
