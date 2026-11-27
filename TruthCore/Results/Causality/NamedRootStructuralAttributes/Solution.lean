module

public import TruthCore.Causality.NamedRootStructuralAttributes
public import TruthCore.Results.Causality.ActualAncestralSource.Solution
public import TruthCore.Results.Causality.RootIntellectWillPureActPlurality.Solution

@[expose] public section

namespace TruthCore.Results.Causality.NamedRootStructuralAttributes
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Results.Causality.ActualAncestralSource (namedRootOfReach)
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
  obtain ⟨n, hActual, hNecessary, hNoLimit⟩ := hRoot
  have hSimple : IsSimple Composite n := fun h => hNoLimit (Or.inl h)
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hPrior
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hNoLimit (Or.inr (Or.inr ⟨y, hNe, hPrior⟩))).elim
  have hEsse : p.esseOf n = p.essenceOf n := by
    rcases hEM (p.esseOf n = p.essenceOf n) with hEq | hNe
    · exact hEq
    · exact (hNoLimit (Or.inr (Or.inl hNe))).elim
  have hNoMatter : ¬ MatterForm n := fun h => hSimple (hMatter n h)
  have hRemote : RemoteFromAll ComponentOf n := fun y hy => hNoComponent n y hy hFirst
  have hInt := hIntellect n hNoMatter hRemote
  exact ⟨n, hActual, hNecessary, hEsse, hSimple, hFirst, hNoMatter, hRemote,
    hInt, hWill n hInt⟩

theorem matterFormOfCompositionKinds {B P : Type} (MatterForm Composite : B → Prop)
    (essenceOf esseOf : B → P)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf) :
    MatterFormIsComposite MatterForm Composite := by
  exact fun x => (hKinds x).1

theorem compositionKindsIff {B P : Type} (MatterForm Composite : B → Prop)
    (essenceOf esseOf : B → P) :
    MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf ↔
      MatterFormIsComposite MatterForm Composite ∧
        (∀ x, esseOf x ≠ essenceOf x → Composite x) := by
  exact ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩,
    fun h x => ⟨h.1 x, h.2 x⟩⟩

theorem matterFormWithoutEsseEssenceKind :
    MatterFormIsComposite (fun b : Bool => b = true) (fun b => b = true) ∧
    ¬ MatterFormAndEsseEssenceAreCompositionsReading
      (fun b : Bool => b = true) (fun b => b = true) (fun _ => false) (fun _ => true) := by
  exact ⟨fun _ h => h, fun h => Bool.noConfusion ((h false).2 Bool.noConfusion)⟩

theorem intellectOfReach {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill IsGod : B → Prop)
    (hRoot : NecessaryRootIntellectWillAt m w p
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hReach : GodReachesActualConcreta m w IsGod) :
    GodHasIntellect IsGod HasIntellect := by
  obtain ⟨n, hActualRoot, _, _, _, _, _, _, hIntellect, _⟩ := hRoot
  intro g hg
  have hIdentity := namedRootOfReach m w IsGod hReach g n hg hActualRoot
  exact hIdentity.symm ▸ hIntellect

theorem willOfReach {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill IsGod : B → Prop)
    (hRoot : NecessaryRootIntellectWillAt m w p
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hReach : GodReachesActualConcreta m w IsGod) :
    GodHasWill IsGod HasWill := by
  obtain ⟨n, hActualRoot, _, _, _, _, _, _, _, hWill⟩ := hRoot
  intro g hg
  have hIdentity := namedRootOfReach m w IsGod hReach g n hg hActualRoot
  exact hIdentity.symm ▸ hWill

theorem reachOmission (hEM : ExcludedMiddle) :
    let names := fun g : Being => g = .instrument
    NecessaryRootIntellectWillAt model false esseProfile
      prior component composite matterForm hasIntellect hasWill ∧
    ¬ GodReachesActualConcreta model false names ∧
    ¬ GodHasIntellect names hasIntellect ∧ ¬ GodHasWill names hasWill := by
  obtain ⟨_, _, hLeft, _⟩ := TruthCore.Results.Causality.RootIntellectWillPureActPlurality.checks hEM
  obtain ⟨hRoot, hNecessary, hEsse, hSimple, hFirst, hMatter, hRemote, hIntellect, hWill, _⟩ := hLeft
  have hBundle : NecessaryRootIntellectWillAt model false esseProfile
      prior component composite matterForm hasIntellect hasWill :=
    ⟨.left, hRoot, hNecessary, hEsse, hSimple, hFirst, hMatter, hRemote, hIntellect, hWill⟩
  have hNoIntellect : ¬ GodHasIntellect (fun g : Being => g = .instrument) hasIntellect :=
    fun h => h .instrument rfl
  have hNoWill : ¬ GodHasWill (fun g : Being => g = .instrument) hasWill :=
    fun h => h .instrument rfl
  refine ⟨hBundle, ?_, hNoIntellect, hNoWill⟩
  intro hReach
  exact hNoIntellect (intellectOfReach model false esseProfile prior component composite
    matterForm hasIntellect hasWill _ hBundle hReach)

end TruthCore.Results.Causality.NamedRootStructuralAttributes
