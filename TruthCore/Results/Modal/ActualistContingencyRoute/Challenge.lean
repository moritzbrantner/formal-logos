import TruthCore.Modal.ActualistContingencyRoute
import TruthCore.Results.Modal.ActualistDomains.Solution
import TruthCore.Results.Causality.ContingentBeingNode.Solution

namespace TruthCore.Results.Modal.ActualistContingencyRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ContingentBeingNode
  (SomeActualContingentAt EveryActualConcreteNecessaryAt)
open TruthCore.Modal.ActualistContingencyRoute
open TruthCore.Results.Modal.ActualistDomains (checks)
open TruthCore.Results.Causality.ContingentBeingNode (notEveryNecessary)

/-- Strength order: the forward transfer gives concrete NECESSARY_2 at each
world, through the library's correspondence with increasing domains. -/
theorem transferGivesConcreteNecessary {W B : Type} (m : Profile W B) (w : W)
    (hTransfer : RouteForwardTransfer m) : EveryActualConcreteNecessaryAt m w := by
  sorry

/-- The route's contingent bearer rules out the forward transfer policy: the
existing refutation of concrete necessitarianism composed with the strength
order. -/
theorem forwardTransferFails {W B : Type} (m : Profile W B) (w : W)
    (hContingent : SomeActualContingentAt m w) : NoRouteForwardTransfer m := by
  sorry

/-- The strictness controls. -/
theorem controls : Control.Strictness := by
  sorry

end TruthCore.Results.Modal.ActualistContingencyRoute
