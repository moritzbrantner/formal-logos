module

public import TruthCore.Causality.ThroughWill
public import TruthCore.Causality.EsseCausePriority
public import TruthCore.Causality.ExistenceActuality
public import TruthCore.Causality.CausalMapsBatch1

@[expose] public section

namespace TruthCore.Results.Causality.UniversalGivingPriority

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CausalMapsBatch1 (PriorityRequiresNonmutualDependence)
open TruthCore.Causality.EsseCausePriority (DistinctEsseCausePriority)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.Round2Grounding (SimplePriorityRelatesActualConcreta)
open TruthCore.Causality.ThroughWill (IntellectualUniversalCausesAreFirst)
open TruthCore.Logic (ExcludedMiddle)

/-- A prior distinct from the universal cause would itself be caused by it. -/
theorem universalCauseIsFirstOfPriorityDependence {W B T R : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop)
    (hEndpoints : SimplePriorityRelatesActualConcreta m w F.PriorSimply)
    (hAct : ExistingInActAt m.ontic InAct F.esse w)
    (hCausePrior : DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply)
    (hNonmutual : PriorityRequiresNonmutualDependence F.PriorSimply F.DependsForBeing)
    (hEM : ExcludedMiddle) :
    IntellectualUniversalCausesAreFirst F InAct HasIntellect HasWill := by
  intro g _ _ hUniversal y hBefore
  rcases hEM (y = g) with hEqual | hDistinct
  · exact hEqual
  · have hY := hAct y (hEndpoints y g hBefore).1.2
    have hAfter := hCausePrior g y (Ne.symm hDistinct) (hUniversal y hDistinct hY)
    exact False.elim ((hNonmutual y g hBefore).2 (hNonmutual g y hAfter).1)

end TruthCore.Results.Causality.UniversalGivingPriority
