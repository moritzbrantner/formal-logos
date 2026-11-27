module

public import TruthCore.Causality.GroundedOccupantRegress

@[expose] public section

namespace TruthCore.Results.Logic.ActualGroundingAcyclicity
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.GroundedOccupantRegress (ActualConcreteGroundingAcyclicAt)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)

/-- The regress schema's cycle exclusion on the selected actual-concrete graph. -/
theorem actualGroundingAcyclicOfWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : ActualConcreteGroundingAcyclicAt m w :=
  (graph m w).noCycles_of_wellFounded hWF

end TruthCore.Results.Logic.ActualGroundingAcyclicity
