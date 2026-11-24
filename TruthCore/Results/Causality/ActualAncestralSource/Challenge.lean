module

public import TruthCore.Causality.ActualAncestralSource

@[expose] public section

namespace TruthCore.Results.Causality.ActualAncestralSource
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.SourceForest (RootedAtUniqueSource)
open TruthCore.Causality.ConcreteRootAccess (UniversalRootAccess)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.ActualAncestralSource
open TruthCore.Causality.RootPositiveIntellectWill (ActualRootExistsAt)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.GodMaximalCausal (GodCausesBeingOfAllOthers)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Case.Catholicism (GodExists)
open TruthCore.Logic (ExcludedMiddle)

theorem commonAncestryOfUniqueAndAccess {W B : Type} (m : Profile W B) (w : W)
    (hUnique : UniqueActualRootAt m w) (hAccess : UniversalRootAccess m w) :
    RootedAtUniqueSource (graph m w) := by
  sorry

theorem rootAccessOfCommonAncestry {W B : Type} (m : Profile W B) (w : W)
    (h : RootedAtUniqueSource (graph m w)) : UniversalRootAccess m w := by
  sorry

theorem uniqueOfCommonAncestry {W B : Type} (m : Profile W B) (w : W)
    (h : RootedAtUniqueSource (graph m w)) : UniqueActualRootAt m w := by
  sorry

theorem ancestralNamingOfDirectCausing {W B R : Type} (m : Profile W B) (w : W)
    (IsGod : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hCausal : GodCausesBeingOfAllOthers IsGod CausesIn esse)
    (hGround : EsseCauseIsActualConcreteGround m w CausesIn esse) (em : ExcludedMiddle) :
    GodReachesActualConcreta m w IsGod := by
  sorry

theorem namedRootOfReach {W B : Type} (m : Profile W B) (w : W) (IsGod : B → Prop)
    (hReach : GodReachesActualConcreta m w IsGod) (g n : B)
    (hg : IsGod g) (hn : ActualRoot m w n) : g = n := by
  sorry

theorem commonAncestryOfNamedSource {W B : Type} (m : Profile W B) (w : W)
    (IsGod : B → Prop) (hGod : GodExists IsGod) (hRoot : ActualRootExistsAt m w)
    (hReach : GodReachesActualConcreta m w IsGod) : RootedAtUniqueSource (graph m w) := by
  sorry

theorem mediatedChain : MediatedControl := by
  sorry

end TruthCore.Results.Causality.ActualAncestralSource
