module

public import TruthCore.Modal.ActualistContingencyRoute
public import TruthCore.Results.Modal.ActualistDomains.Solution

@[expose] public section

namespace TruthCore.Results.Modal.ActualistContingencyRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Modal.ActualistContingencyRoute
open TruthCore.Results.Modal.ActualistDomains
  (boxAllToAllBox_iff increasing_excludes_contingency)

/-- The route's contingent bearer rules out the forward transfer policy. -/
theorem forwardTransferFails {W B : Type} (m : Profile W B) (w : W)
    (hContingent : SomeActualContingentAt m w) : NoRouteForwardTransfer m := by
  intro hTransfer
  obtain ⟨x, _, hx⟩ := hContingent
  have hIncreasing := (boxAllToAllBox_iff m.ontic).mp hTransfer
  exact increasing_excludes_contingency m.ontic hIncreasing w x hx

end TruthCore.Results.Modal.ActualistContingencyRoute
