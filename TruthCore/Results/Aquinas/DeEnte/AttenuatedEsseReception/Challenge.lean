import TruthCore.Latin.Aquinas.DeEnte.AttenuatedEsseReception
import TruthCore.Results.Causality.ClosedGroundingRoots.Solution

namespace TruthCore.Results.Aquinas.DeEnte.AttenuatedEsseReception

open TruthCore.Latin.Aquinas.DeEnte.AttenuatedEsseReception (AttenuatedActualEsseReception)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

/-- Specialize the closed-grounding theorem to the actual esse-cause graph. -/
theorem closedOfAttenuation {B P R : Type} (p : Profile B P R)
    (h : AttenuatedActualEsseReception p) : ClosedActualEsseCollectionsRooted p := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.AttenuatedEsseReception
