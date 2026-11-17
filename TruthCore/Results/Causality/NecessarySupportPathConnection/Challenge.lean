import TruthCore.Causality.NecessarySupportPathConnection
import TruthCore.Results.Causality.NecessarySupportCoverage.Solution
import TruthCore.Results.Causality.NecessarySupportActualScope.Solution

namespace TruthCore.Results.Causality.NecessarySupportPathConnection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportActualScope
open TruthCore.Causality.NecessarySupportPathConnection
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

theorem restrictPaths (m : Profile W B) (w : W)
    (h : ConcreteSupportActualPaths m w) : NecessarySupportActualPaths m w := by
  sorry

theorem pathsOfPresence (m : Profile W B) (w : W)
    (h : TruthCore.Causality.UnderivedRootRoute.NecessarySupportIsPresent m w) :
    ConcreteSupportActualPaths m w := by
  sorry

theorem coverageOfPaths (m : Profile W B) (w : W)
    (h : ConcreteSupportActualPaths m w) : NecessarySupportActuallyCovered m w := by
  sorry

/-- Only the necessary-source path scope is needed. Actual WF is used to make
its actual guarded support graph and its NONEMPTY transitive closure WF. -/
theorem unionOfNecessaryPaths (m : Profile W B) (w : W)
    (hWF : TruthCore.Causality.NecessaryRootFork.ActualGroundingWF m w)
    (hPath : NecessarySupportActualPaths m w) : ConcreteNecessaryUnionWF m w := by
  sorry

/-- J1 upgrades the restricted path scope. No frame or population premise. -/
theorem upgradePaths (m : Profile W B) (w : W)
    (hNoCont : NoContingentConcreteSupport m w)
    (hPath : NecessarySupportActualPaths m w) : ConcreteSupportActualPaths m w := by
  sorry

/-- The actual-world J1 instance propagates backwards along each actual path;
the strong transport scope therefore recovers full all-admitted-world J1. -/
theorem noContingentOfActualPaths (m : Profile W B) (w : W)
    (hActual : ActualNoContingentConcreteSupport m w)
    (hPath : ConcreteSupportActualPaths m w) : NoContingentConcreteSupport m w := by
  sorry

theorem shortcutControl : Control.ShortcutControl := by
  sorry

theorem scopeControls : Control.ScopeControls := by
  sorry

end TruthCore.Results.Causality.NecessarySupportPathConnection
