module

public import TruthCore.Results.Causality.ActualAncestralSource.Solution
public import TruthCore.Results.Causality.RootIntellectWillPureActPlurality.Solution

@[expose] public section

namespace TruthCore.Results.Causality.NamedRootStructuralAttributes
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Results.Causality.ActualAncestralSource (namedRootOfReach)
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
  obtain ⟨n, hActualRoot, _, hNonlimitation⟩ := hRoot
  intro g hg
  have hIdentity := namedRootOfReach m w IsGod hReach g n hg hActualRoot
  have hSimple : ¬ Composite n := fun hComposite => hNonlimitation (Or.inl hComposite)
  exact hIdentity.symm ▸ hSimple

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
