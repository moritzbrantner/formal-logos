import TruthCore.Causality.GroundedOccupantRegress
import TruthCore.Results.Causality.SelectedAncestry.Solution
import TruthCore.Results.Causality.WorldSourceRegress.Solution

namespace TruthCore.Results.Causality.SelectedConeRegress
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround GroundAncestor cycleProfile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.SelectedAncestry
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.RootDescent (acc_of_map acc_of_subtype)

/-- Acyclicity makes any descending chain from this actual recipient
injective. Without such a chain the recipient is accessible, as is every
actual concrete member of its complete upstream cone. -/
theorem coneWellFounded_of_noAnchoredRegress {W B : Type} (m : Profile W B) (w : W)
    (x : {x // ActualConcrete m w x})
    (hAcyclic : ActualConcreteGroundingAcyclicAt m w)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w x) :
    ConeWellFounded m w x.val := by
  sorry

/-- Complete cone well-foundedness excludes an anchored regress at its
selected recipient without requiring acyclicity elsewhere. -/
theorem noAnchoredRegress_of_coneWellFounded {W B : Type} (m : Profile W B) (w : W)
    (x : {x // ActualConcrete m w x})
    (hWF : ConeWellFounded m w x.val) :
    NoAnchoredConcreteGroundingRegress m w x := by
  sorry

/-- Compose the new supply of cone well-foundedness with the existing
necessary-root result, retaining the original contingent-grounding and
excluded-middle inputs at the same selected world and bearer. -/
theorem necessaryRootAncestor_of_noAnchoredRegress {W B : Type}
    (m : Profile W B) (w : W) (x : {x // ActualConcrete m w x})
    (hAcyclic : ActualConcreteGroundingAcyclicAt m w)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w x)
    (hDep : ConeContingentGrounded m w x.val)
    (hEM : ExcludedMiddle) :
    NecessaryRootAncestor m w x.val := by
  sorry

/-- The existing two-cycle has a repeating descending chain, hence no
well-founded cone at its selected recipient, but no injective infinite
chain can fit in the two-node graph. -/
theorem cyclicControl :
    NoAnchoredConcreteGroundingRegress cycleProfile true ⟨true, trivial, rfl⟩ ∧
      ¬ ConeWellFounded cycleProfile true true := by
  sorry

end TruthCore.Results.Causality.SelectedConeRegress
