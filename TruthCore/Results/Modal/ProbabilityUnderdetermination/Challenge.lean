import TruthCore.Modal.ProbabilityUnderdetermination
import TruthCore.Results.Science.FineTuningInformation.Solution
import Mathlib.Tactic

namespace TruthCore.Results.Modal.ProbabilityUnderdetermination
open TruthCore.Modal
open TruthCore.Modal.ProbabilityUnderdetermination
open Set MeasureTheory ProbabilityTheory
open TruthCore.Science.FineTuningInformation.Plenitude (PointFullSupport InteriorRate)
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

theorem modalProbabilityFreedom : ModalProbabilityFreedom.{u,v} := by
  sorry

end TruthCore.Results.Modal.ProbabilityUnderdetermination
