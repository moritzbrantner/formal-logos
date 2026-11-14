import TruthCore.Causality.EsseCauseEfficiency
import TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.Solution

/-!
# Efficiency of causes of esse: derivations and controls (#1633)

The efficient reading of q.3 a.4's conclusion
(`DistinctEsseRequiresExternalEfficientCause`) follows, through the OPEN
bridge `DistinctActualEsseCauseIsEfficient`, from the mode-unspecified De ente
conclusion `DistinctEsseHasOtherActualCause` and from the q.3 a.4 dichotomy
with its no-self-sufficiency premise. It strengthens the mode-unspecified q.3
a.4 conclusion by projection, and the unrestricted bridge strengthens the
restricted one. The controls show that the bridge is needed and that the
strength orders are strict. No premise is proved here.
-/

namespace TruthCore.Results.Causality.EsseCauseEfficiency

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Latin.Aquinas.DeEnte (DistinctEsseHasOtherActualCause)
open TruthCore.Causality.EsseCauseEfficiency
open TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause
  (distinctEsseExternalFromExhaustion)

/-- De ente's mode-unspecified other actual cause of a distinct esse, with the
efficiency bridge, is an external efficient cause. -/
theorem externalEfficientEsseCauseFromDeEnte (q : EfficiencyProfile B P R)
    (hOther : DistinctEsseHasOtherActualCause q.toProfile)
    (hBridge : DistinctActualEsseCauseIsEfficient q) :
    DistinctEsseRequiresExternalEfficientCause q := by
  sorry

/-- The q.3 a.4 dichotomy and no-self-sufficiency (through the existing
transcription `distinctEsseExternalFromExhaustion`), with the efficiency
bridge, give the external efficient cause. -/
theorem externalEfficientEsseCauseFromQ3A4 (q : EfficiencyProfile B P R)
    (hExhaustive : DistinctEsseCauseDichotomyReading q.toProfile)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading q.toProfile)
    (hBridge : DistinctActualEsseCauseIsEfficient q) :
    DistinctEsseRequiresExternalEfficientCause q := by
  sorry

/-- Strength order: an external efficient cause of esse is an external cause
of esse (the efficiency conjunct is dropped). -/
theorem externalCauseFromExternalEfficientCause (q : EfficiencyProfile B P R)
    (hEfficient : DistinctEsseRequiresExternalEfficientCause q) :
    DistinctEsseRequiresExternalCauseReading q.toProfile := by
  sorry

/-- Strength order: the unrestricted bridge gives the restricted one. -/
theorem distinctActualEsseCauseEfficientFromUnrestricted (q : EfficiencyProfile B P R)
    (hAll : CausingAnothersEsseIsEfficient q) :
    DistinctActualEsseCauseIsEfficient q := by
  sorry

/-- The De ente step and the mode-unspecified q.3 a.4 conclusion are the same
proposition on the same profile: each unfolds to "every actual distinct-esse
x has some y other than x, in act as to being, that causes x's esse". -/
theorem otherActualCauseIffExternalCause (p : Profile B P R) :
    DistinctEsseHasOtherActualCause p ↔ DistinctEsseRequiresExternalCauseReading p := by
  sorry

/-- The three finite interpretations. Explicit proof terms. -/
theorem esseCauseEfficiencyControls : EsseCauseEfficiencyControls := by
  sorry

end TruthCore.Results.Causality.EsseCauseEfficiency
