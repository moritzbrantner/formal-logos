import TruthCore.Causality.Round3CogitoBase
import TruthCore.Results.Causality.SelectedAncestry.Solution

namespace TruthCore.Results.Causality.ContingentConeRoot

open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt Profile)
open TruthCore.Causality.Round3CogitoBase (NoContingentRootAncestor)
open TruthCore.Results.Causality.SelectedAncestry (scopeComparison)

/-- Global contingent grounding rules out a contingent root in any selected cone. -/
theorem noContingentRootAncestorOfGlobalGrounding {W B : Type} (m : Profile W B)
    (w : W) (selected : B) (h : EveryContingentGroundedAt m w) :
    NoContingentRootAncestor m w selected := by
  sorry

end TruthCore.Results.Causality.ContingentConeRoot
