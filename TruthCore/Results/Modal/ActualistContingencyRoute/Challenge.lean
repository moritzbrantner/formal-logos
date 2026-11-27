import TruthCore.Modal.ActualistContingencyRoute
import TruthCore.Results.Modal.ActualistDomains.Solution

namespace TruthCore.Results.Modal.ActualistContingencyRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Modal.ActualistContingencyRoute
open TruthCore.Results.Modal.ActualistDomains (checks)

/-- The route's contingent bearer rules out the forward transfer policy. -/
theorem forwardTransferFails {W B : Type} (m : Profile W B) (w : W)
    (hContingent : SomeActualContingentAt m w) : NoRouteForwardTransfer m := by
  sorry

end TruthCore.Results.Modal.ActualistContingencyRoute
