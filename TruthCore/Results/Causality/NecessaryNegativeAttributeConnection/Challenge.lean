import TruthCore.Causality.NecessaryClassicalGodRoot
import TruthCore.Causality.NecessaryFirstAttributes

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
  sorry

end TruthCore.Results.Causality.NecessaryNegativeAttributeConnection
