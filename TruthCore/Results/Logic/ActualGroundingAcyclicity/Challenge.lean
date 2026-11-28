import TruthCore.Causality.GroundedOccupantRegress

namespace TruthCore.Results.Logic.ActualGroundingAcyclicity
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.GroundedOccupantRegress (ActualConcreteGroundingAcyclicAt)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)

/-- The regress schema's cycle exclusion on the selected actual-concrete graph. -/
theorem actualGroundingAcyclicOfWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : ActualConcreteGroundingAcyclicAt m w := by
  sorry

end TruthCore.Results.Logic.ActualGroundingAcyclicity
