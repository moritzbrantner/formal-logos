module

public import TruthCore.Causality.ContingentBeingNode
public import TruthCore.Modal.ActualistDomains

/-! The forward actualist quantifier transfer as a rival domain policy for the
contingency route. Both sides read presence and accessibility from the same
Ontic profile with rigid candidate identity and total valuation predicates. -/

@[expose] public section

namespace TruthCore.Modal.ActualistContingencyRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Modal.ActualistDomains (BoxAllToAllBox)

/-- The quantified transfer is imposed at every world of the route's Ontic. -/
def RouteForwardTransfer {W B : Type} (m : Profile W B) : Prop :=
  BoxAllToAllBox m.ontic

/-- Failure of the global transfer on this very profile. -/
def NoRouteForwardTransfer {W B : Type} (m : Profile W B) : Prop :=
  ¬ RouteForwardTransfer m

end TruthCore.Modal.ActualistContingencyRoute
