module

public import TruthCore.Causality.NecessaryClassicalGodRoot
public import TruthCore.Causality.NecessaryFirstAttributes

@[expose] public section

namespace TruthCore.Results.Causality.NecessaryNegativeAttributeConnection

open TruthCore.Case.Catholicism
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.DirectEsseRootPerfectionGoodness (PerfectRootAt)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryClassicalGodRoot (NecessaryClassicalGodRootAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.NecessaryFirstAttributes (NecessaryFirstAttributesAt)
open TruthCore.Causality.RootPositiveIntellectWill (NecessaryPositiveRootIntellectWillAt)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The positive root’s uniqueness identifies the two witnesses in the same
profile and world. Carry the negative package’s potency exclusion, simplicity
and remoteness to the bearer of the positive determinations. -/
theorem classicalRootFromNegativeAndPositive {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hNegative : NecessaryFirstAttributesAt m w PriorSimply ComponentOf InPotency Composite)
    (hPositive : NecessaryPositiveRootIntellectWillAt m w p GoodIn MoreIn PriorSimply
      ComponentOf Composite MatterForm HasIntellect HasWill)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse ComponentOf σ.IsGod)
    (hOne : GodIsOne σ.IsGod)
    (hInfinity : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill) :
    NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill := by
  obtain ⟨n, hRoot, _, hIsFirst, hPure, hSimple, hRemote⟩ := hNegative
  obtain ⟨g, hPerfectRoot, hGood, hIdentity, _, _, hMatter, _, hIntellect, hWill⟩ :=
    hPositive
  have heq := hPerfectRoot.2.2.1 n hRoot
  subst n
  have hMaximum := hPerfectRoot.2.2.2.1
  have hOnlyMaximum := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot m w
    (fun x (_ : Unit) => p.InAct x p.esse) (fun (_ : Unit) y x => MoreIn p.esse y x)
    (fun c x (_ : Unit) => p.CausesIn c x p.esse) () g hRoot hEM
    (fun _ => hGenus) hExisting hEsse
  have hGod : σ.IsGod g :=
    hNaming g hMaximum (hGenus g hMaximum) hGood.2 hRemote hOnlyMaximum
  have hNine : NineClassicalAttributes (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill g :=
    ⟨hSimple, hPerfectRoot.2.2.2.2, hGood, hOne g hGod, hInfinity g hIdentity,
      hPure, hEternity g hPure, hIntellect, hWill⟩
  exact ⟨g, hPerfectRoot, hIdentity, hIsFirst, hMatter, hRemote, hGod, hNine,
    classicalAttributesFromNine σ _ _ _ _ _ _ _ _ _ hSuffice g hNine⟩

end TruthCore.Results.Causality.NecessaryNegativeAttributeConnection
