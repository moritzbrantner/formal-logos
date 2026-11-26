import TruthCore.Causality.ThroughWill
import TruthCore.Causality.EsseCausePriority
import TruthCore.Causality.ExistenceActuality
import TruthCore.Causality.CausalMapsBatch1

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
  sorry

end TruthCore.Results.Causality.UniversalGivingPriority
