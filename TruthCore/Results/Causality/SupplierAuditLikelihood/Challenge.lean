import TruthCore.Causality.SupplierAuditLikelihood
import TruthCore.Causality.PerSeRegressCardinality

namespace TruthCore.Results.Causality.SupplierAuditLikelihood

open TruthCore.Causality.FiniteReserveOdds
open TruthCore.Causality.PerSeRegressCardinality (asCaused)
open TruthCore.Causality.SupplierAudit
open TruthCore.Causality.SupplierAuditLikelihood
open TruthCore.Latin.Aquinas.SummaTheologiae
  (IsFirstEfficientCause NoInfinitePerSeEfficientCauseSeriesReading)

theorem prefixComparison (reserve : FiniteReserveComparison) : PrefixComparison := by
  sorry

theorem selectedRegressControl :
    (∀ depth, NoInfinitePerSeEfficientCauseSeriesReading (asCaused (sourced depth)) ∧
      IsFirstEfficientCause (fun supplier recipient (_ : Unit) =>
        sourced depth supplier recipient) depth) ∧
    (¬ NoInfinitePerSeEfficientCauseSeriesReading (asCaused endless)) ∧
    ∀ d, (∀ y, ¬ asCaused (sourced (d + 1)) y d) ∧ sourced (d + 1) (d + 1) d := by
  sorry

theorem prefixConditioning : PrefixConditioning := by
  sorry

end TruthCore.Results.Causality.SupplierAuditLikelihood
