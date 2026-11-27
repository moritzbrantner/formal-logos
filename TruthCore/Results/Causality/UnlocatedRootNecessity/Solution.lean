module

public import TruthCore.Causality.UnlocatedRootNecessity
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
    (m : Profile W B) (w : W) (F : Frame B) (x : B)
    (hActual : ActualConcrete m w x)
    (hFork : UnlocatedRootOrRegress m w F ⟨x, hActual⟩)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w ⟨x, hActual⟩)
    (hGrounded : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  obtain ⟨root, _, hRoot, _⟩ :=
    TruthCore.Results.Causality.GroundedOccupantRegress.unlocatedRoot_of_noRegress
      m w F ⟨x, hActual⟩ hFork hNoRegress
  refine ⟨root.val, root.property.1, root.property.2, ?_⟩
  rcases hEM (NecessaryAt m.ontic w root.val) with hNecessary | hNotNecessary
  · exact hNecessary
  · have hContingentRoot :=
      contingentRootOfNonnecessary m w hEM ⟨root.val, hRoot, hNotNecessary⟩
    exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hGrounded
      hContingentRoot).elim

open TruthCore.Causality.UnlocatedRootNecessity (EmptyPopulationOmission)

theorem emptyPopulationOmission : EmptyPopulationOmission := by
  let m : Profile Unit Unit := {
    ontic := {
      frame := ⟨fun _ _ => True⟩
      ExistsAt := fun _ _ => False
      Causes := fun _ _ _ => False }
    concrete := fun _ => True
    grounds := fun _ _ _ => False }
  exact ⟨m, allLocatedFrame (), fun h => h.2, fun x => x.property.2.elim,
    fun x => x.property.2.elim, fun _ _ h _ => h.elim, fun ⟨_, _, h, _⟩ => h⟩

end TruthCore.Results.Causality.UnlocatedRootNecessity
