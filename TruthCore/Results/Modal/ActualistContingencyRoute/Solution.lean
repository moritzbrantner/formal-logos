module

public import TruthCore.Modal.ActualistContingencyRoute
public import TruthCore.Results.Modal.ActualistDomains.Solution

@[expose] public section

namespace TruthCore.Results.Modal.ActualistContingencyRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Modal.ActualistContingencyRoute
open TruthCore.Results.Modal.ActualistDomains (checks)

/-- The route's contingent bearer rules out the forward transfer policy. -/
theorem forwardTransferFails {W B : Type} (m : Profile W B) (w : W)
    (hContingent : SomeActualContingentAt m w) : NoRouteForwardTransfer m := by
  intro hTransfer
  obtain ⟨x, _, hx⟩ := hContingent
  obtain ⟨forwardIffIncreasing, _, excludesContingency, _⟩ := checks
  have hIncreasing := (forwardIffIncreasing W B m.ontic).mp hTransfer
  exact excludesContingency W B m.ontic hIncreasing w x hx

end TruthCore.Results.Modal.ActualistContingencyRoute
