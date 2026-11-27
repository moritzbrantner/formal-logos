import TruthCore.Causality.NamedRootStructuralAttributes
import TruthCore.Causality.ActualAncestralSource
import TruthCore.Causality.RootIntellectWillPureActPlurality

namespace TruthCore.Results.Causality.NamedRootStructuralAttributes
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NamedRootStructuralAttributes (MatterFormIsComposite)
open TruthCore.Causality.PartFreePlurality
open TruthCore.Causality.RootIntellectWill (NecessaryRootIntellectWillAt)
open TruthCore.Causality.RootIntellectWillPureActPlurality (model hasIntellect hasWill)
open TruthCore.Causality.RootWithoutLimitingPrinciple (NecessaryRootWithoutLimitingPrincipleAt)
open TruthCore.Case.Catholicism (GodHasIntellect GodHasWill IsSimple RemoteFromAll)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

theorem rootIntellectWillOfNonlimitation {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill : B → Prop)
    (hRoot : NecessaryRootWithoutLimitingPrincipleAt m w p Composite PriorSimply)
    (hEM : ExcludedMiddle)
    (hMatter : MatterFormIsComposite MatterForm Composite)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill) :
    NecessaryRootIntellectWillAt m w p
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill := by
  sorry

theorem matterFormOfCompositionKinds {B P : Type} (MatterForm Composite : B → Prop)
    (essenceOf esseOf : B → P)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf) :
    MatterFormIsComposite MatterForm Composite := by
  sorry

theorem compositionKindsIff {B P : Type} (MatterForm Composite : B → Prop)
    (essenceOf esseOf : B → P) :
    MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf ↔
      MatterFormIsComposite MatterForm Composite ∧
        (∀ x, esseOf x ≠ essenceOf x → Composite x) := by
  sorry

theorem matterFormWithoutEsseEssenceKind :
    MatterFormIsComposite (fun b : Bool => b = true) (fun b => b = true) ∧
    ¬ MatterFormAndEsseEssenceAreCompositionsReading
      (fun b : Bool => b = true) (fun b => b = true) (fun _ => false) (fun _ => true) := by
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
