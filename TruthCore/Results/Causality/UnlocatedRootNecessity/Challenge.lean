import TruthCore.Causality.GroundedOccupantRegress

namespace TruthCore.Results.Causality.UnlocatedRootNecessity

open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt NecessaryConcreteAt)
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Ontology.Spatiotemporal (Frame)

theorem necessaryConcreteOfUnlocatedFork {W B : Type}
    (m : Profile W B) (w : W) (F : Frame B) (x : {x // ActualConcrete m w x})
    (hFork : UnlocatedRootOrRegress m w F x)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w x)
    (hGrounded : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  sorry

end TruthCore.Results.Causality.UnlocatedRootNecessity
