import TruthCore.Causality.ActualAncestralSource
import TruthCore.Causality.RootIntellectWillPureActPlurality

namespace TruthCore.Results.Causality.NamedRootStructuralAttributes
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.PartFreePlurality
open TruthCore.Causality.RootIntellectWill (NecessaryRootIntellectWillAt)
open TruthCore.Causality.RootIntellectWillPureActPlurality (model hasIntellect hasWill)
open TruthCore.Causality.RootWithoutLimitingPrinciple (NecessaryRootWithoutLimitingPrincipleAt)
open TruthCore.Case.Catholicism (GodIsSimple GodHasIntellect GodHasWill)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

theorem simpleOfReach {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (Composite IsGod : B → Prop) (PriorSimply : B → B → Prop)
    (hRoot : NecessaryRootWithoutLimitingPrincipleAt m w p Composite PriorSimply)
    (hReach : GodReachesActualConcreta m w IsGod) :
    GodIsSimple IsGod Composite := by
  sorry

theorem intellectOfReach {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill IsGod : B → Prop)
    (hRoot : NecessaryRootIntellectWillAt m w p
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hReach : GodReachesActualConcreta m w IsGod) :
    GodHasIntellect IsGod HasIntellect := by
  sorry

theorem willOfReach {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill IsGod : B → Prop)
    (hRoot : NecessaryRootIntellectWillAt m w p
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hReach : GodReachesActualConcreta m w IsGod) :
    GodHasWill IsGod HasWill := by
  sorry

theorem reachOmission (hEM : ExcludedMiddle) :
    let names := fun g : Being => g = .instrument
    NecessaryRootIntellectWillAt model false esseProfile
      prior component composite matterForm hasIntellect hasWill ∧
    ¬ GodReachesActualConcreta model false names ∧
    ¬ GodHasIntellect names hasIntellect ∧ ¬ GodHasWill names hasWill := by
  sorry

end TruthCore.Results.Causality.NamedRootStructuralAttributes
