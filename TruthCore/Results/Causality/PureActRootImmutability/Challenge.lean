import TruthCore.Causality.ActualAncestralSource
import TruthCore.Causality.RootIntellectWillPureActPlurality

namespace TruthCore.Results.Causality.PureActRootImmutability
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.PartFreePlurality
open TruthCore.Causality.RootIntellectWillPureAct
open TruthCore.Causality.RootIntellectWillPureActPlurality (model hasIntellect hasWill)
open TruthCore.Case.Catholicism (GodIsImmutable IsImmutable)
open TruthCore.Latin.Aquinas.SummaTheologiae (PrimaPars)
open TruthCore.Logic (ExcludedMiddle)

theorem immutableOfReach {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill IsGod : B → Prop)
    (InPotency : B → R → Prop)
    (hRoot : NecessaryRootIntellectWillPureActAt m w p
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill InPotency)
    (hReach : GodReachesActualConcreta m w IsGod) :
    GodIsImmutable IsGod (IsImmutable InPotency) := by
  sorry

theorem reachOmission (_hEM : ExcludedMiddle) :
    let names := fun g : Being => g = .instrument
    NecessaryRootIntellectWillPureActAt model false esseProfile
      prior component composite matterForm hasIntellect hasWill moved ∧
    ¬ GodReachesActualConcreta model false names ∧
    ¬ GodIsImmutable names (IsImmutable moved) := by
  sorry

end TruthCore.Results.Causality.PureActRootImmutability
