import TruthCore.Causality.RelayCutSensitivity

noncomputable section

namespace TruthCore.Results.Causality.RelayCutSensitivity

open TruthCore.Causality (PowerTransmissionRule)
open TruthCore.Causality.ParallelPowerTransmission (ActivityClassification CutEffects transmissionLink)
open TruthCore.Causality.RelayCutSensitivity
open TruthCore.Causality.SupplierAuditLikelihood (PrefixComparison depthLikelihood)

theorem singleCutComparison (classification : ActivityClassification) : SingleCutComparison := by
  sorry

theorem randomizedCutComparison (cuts : SingleCutComparison)
    (prefixes : PrefixComparison) : RandomizedCutComparison := by
  sorry

end TruthCore.Results.Causality.RelayCutSensitivity
