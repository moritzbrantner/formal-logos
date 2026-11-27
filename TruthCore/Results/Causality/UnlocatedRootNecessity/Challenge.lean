import TruthCore.Causality.UnlocatedRootNecessity

namespace TruthCore.Results.Causality.UnlocatedRootNecessity

open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt NecessaryConcreteAt)
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Ontology.Spatiotemporal (Frame)

theorem necessaryConcreteOfUnlocatedFork {W B : Type}
    (m : Profile W B) (w : W) (F : Frame B) (x : B)
    (hActual : ActualConcrete m w x)
    (hFork : UnlocatedRootOrRegress m w F ⟨x, hActual⟩)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w ⟨x, hActual⟩)
    (hGrounded : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  sorry

open TruthCore.Causality.UnlocatedRootNecessity (EmptyPopulationOmission)

theorem emptyPopulationOmission : EmptyPopulationOmission := by
  sorry

end TruthCore.Results.Causality.UnlocatedRootNecessity
