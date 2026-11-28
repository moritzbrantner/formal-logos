import TruthCore.Modal.ProbabilityUnderdetermination
import TruthCore.Results.Science.FineTuningInformation.Solution
import Mathlib.Tactic

namespace TruthCore.Results.Modal.ProbabilityUnderdetermination
open TruthCore.Modal
open TruthCore.Modal.ProbabilityUnderdetermination
open Set MeasureTheory ProbabilityTheory
open TruthCore.Logic.CarrierProbability
open TruthCore.Science.FineTuningInformation.Plenitude (ArbitraryInteriorMass)
open TruthCore.Results.Science.FineTuningInformation (arbitraryInteriorMass)
open scoped ENNReal Cardinal
universe u v

theorem noUniform : NoUniform.{u} := by
  sorry

/-- Reuses the shared interior-mass lemma of #2143 at probability one third. -/
theorem equalCardinalityDifferent : EqualCardinalityDifferent.{u} := by
  sorry

/-- Pull back the natural-number partitions along a bijection W ≃ W × ℕ.
No countable additivity or nonnegativity is used. -/
theorem noPermutationProbability : NoPermutationProbability.{u} := by
  sorry

theorem noAllSubsetsPermutationMeasure : NoAllSubsetsPermutationMeasure.{u} := by
  sorry

theorem enumerationDependence : EnumerationDependence := by
  sorry

theorem continuousControl : ContinuousControl := by
  sorry

/-- Corollary: instantiate the shared interior-mass statement at the
accessible-world subtype, with the formula's truth event as the event. -/
theorem modalProbabilityFreedom (hMass : ArbitraryInteriorMass.{u}) :
    ModalProbabilityFreedom.{u,v} := by
  sorry

end TruthCore.Results.Modal.ProbabilityUnderdetermination
