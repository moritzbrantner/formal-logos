module

public import TruthCore.Results.Causality.GroundedOccupantRegress.Solution

@[expose] public section

namespace TruthCore.Results.Causality.UnlocatedRootNecessity

open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt NecessaryConcreteAt)
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Ontology.Spatiotemporal (Frame)


open TruthCore.Causality.NecessaryRootFork
  (contingentRootOfNonnecessary everyContingentGrounded_iff_noContingentRoot)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- Select the actual root upstream of the supplied recipient and apply the
contingent-grounding premise on the same profile and standpoint. -/
theorem necessaryConcreteOfUnlocatedFork {W B : Type}
    (m : Profile W B) (w : W) (F : Frame B) (x : {x // ActualConcrete m w x})
    (hFork : UnlocatedRootOrRegress m w F x)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w x)
    (hGrounded : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  obtain ⟨root, _, hRoot, _⟩ :=
    TruthCore.Results.Causality.GroundedOccupantRegress.unlocatedRoot_of_noRegress
      m w F x hFork hNoRegress
  refine ⟨root.val, root.property.1, root.property.2, ?_⟩
  rcases hEM (NecessaryAt m.ontic w root.val) with hNecessary | hNotNecessary
  · exact hNecessary
  · have hContingentRoot :=
      contingentRootOfNonnecessary m w hEM ⟨root.val, hRoot, hNotNecessary⟩
    exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hGrounded
      hContingentRoot).elim

end TruthCore.Results.Causality.UnlocatedRootNecessity
