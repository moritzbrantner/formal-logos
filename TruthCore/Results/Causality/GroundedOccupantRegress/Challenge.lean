import TruthCore.Causality.GroundedOccupantRegress
import TruthCore.Results.Causality.WorldSourceRegress.Solution

namespace TruthCore.Results.Causality.GroundedOccupantRegress
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Ontology.Naturalism (ConcreteNaturalism)
open TruthCore.Ontology.NaturalismConsequences (ConcreteNaturalismFails)
open TruthCore.Ontology.Spatiotemporal (Frame Located)

theorem unlocatedRootOrRegress {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (x : {x // ActualConcrete m w x})
    (hAcyclic : ActualConcreteGroundingAcyclicAt m w)
    (hCoverage : LocatedActualConcreteGroundedAt m w F) :
    UnlocatedRootOrRegress m w F x := by
  sorry

theorem unlocatedRoot_of_noRegress {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (x : {x // ActualConcrete m w x})
    (hFork : UnlocatedRootOrRegress m w F x)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w x) :
    UnlocatedRootPath m w F x := by
  sorry

theorem concreteNaturalismFails_of_unlocatedRoot {W B : Type} (m : Profile W B)
    (w : W) (F : Frame B) (x : {x // ActualConcrete m w x})
    (hRoot : UnlocatedRootPath m w F x) :
    ConcreteNaturalismFails m.ontic m.concrete (Located F) w := by
  sorry

theorem anchoredRegress_of_naturalism {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (x : {x // ActualConcrete m w x})
    (hFork : UnlocatedRootOrRegress m w F x)
    (hN2 : ConcreteNaturalism m.ontic m.concrete (Located F) w) :
    AnchoredConcreteGroundingRegress m w x := by
  sorry

theorem successorControl : SuccessorControl := by
  sorry

theorem fundamentalFieldControl : FundamentalFieldControl := by
  sorry

end TruthCore.Results.Causality.GroundedOccupantRegress
