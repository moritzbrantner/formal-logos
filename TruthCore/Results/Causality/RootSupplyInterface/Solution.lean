module

public import TruthCore.Causality.RootSupplyInterface
public import TruthCore.Results.Causality.NecessaryClassicalGodRoot.Solution

/-!
# Root-supply interface: strength orders and one derivation against it (#1926)

Whole-roster nontrapping follows constructively from root existence and from
well-founded actual grounding. Root existence factors exactly as whole-roster
nontrapping plus population and stability of root existence. The classical
GOD_4 root of the quarta via is derived once from root existence, the
interface, instead of from population and whole-roster nontrapping. No premise
is proved here.
-/

@[expose] public section

namespace TruthCore.Results.Causality.RootSupplyInterface

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete ActualGroundingWF)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.RootPositiveIntellectWill (ActualRootExistsAt)
open TruthCore.Causality.RootSupplyInterface
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete

/-- An actual root makes the nonempty actual roster no trap: the root is a
source of the recorded actual-concrete graph. Constructive. -/
theorem wholeRosterOfActualRootExists {W B : Type} (m : Profile W B) (w : W)
    (hRoot : ActualRootExistsAt m w) : WholeRosterNotTrapped m w := by
  intro _ hTrap
  obtain ⟨n, hn⟩ := hRoot
  exact hTrap.1 ⟨n, hn.1⟩ trivial (fun ⟨y, hy⟩ => hn.2 y.1 ⟨y.2.1, y.2.2, hy⟩)

/-- Well-founded actual grounding makes the nonempty actual roster no trap:
no accessible actual concretum lies in a trap. Constructive. -/
theorem wholeRosterOfActualGroundingWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : WholeRosterNotTrapped m w := by
  intro hNonempty hTrap
  obtain ⟨a, _⟩ := hNonempty
  have key : ∀ a : {x // ActualConcrete m w x},
      Acc (fun a b : {x // ActualConcrete m w x} => m.grounds w a.1 b.1) a → False := by
    intro a hAcc
    induction hAcc with
    | intro x _ ih => exact hTrap.1 x trivial (fun ⟨y, hy⟩ => ih y hy)
  exact key a (hWF.apply a)

/-- Whole-roster nontrapping is the population-conditional, double-negated
form of root existence. Constructive. -/
theorem wholeRosterIsInhabitedRootNotAbsent : WholeRosterIsInhabitedRootNotAbsent := by
  intro W B m w
  constructor
  · intro hWhole hPop hNo
    obtain ⟨b, hb, he⟩ := hPop
    refine hWhole ⟨⟨b, hb, he⟩, trivial⟩ ⟨fun e _ hs => ?_, fun g _ _ => ?_⟩
    · exact hNo ⟨e.1, e.2, fun y hy => hs ⟨⟨y, hy.1, hy.2.1⟩, hy.2.2⟩⟩
    · obtain ⟨y, hy⟩ := g.2
      exact ⟨y, hy, trivial⟩
  · intro hImp hNonempty hTrap
    obtain ⟨a, _⟩ := hNonempty
    exact hImp ⟨a.1, a.2.1, a.2.2⟩
      (fun hRoot => wholeRosterOfActualRootExists m w hRoot ⟨a, trivial⟩ hTrap)

/-- Certified difference: root existence is whole-roster nontrapping plus
population and stability of root existence. Constructive. -/
theorem rootExistsOverWholeRosterExact : RootExistsOverWholeRosterExact := by
  intro W B m w
  constructor
  · intro hRoot
    obtain ⟨n, hn⟩ := hRoot
    exact ⟨wholeRosterOfActualRootExists m w ⟨n, hn⟩, ⟨n, hn.1.1, hn.1.2⟩,
      fun _ => ⟨n, hn⟩⟩
  · rintro ⟨hWhole, hPop, hStable⟩
    exact hStable ((wholeRosterIsInhabitedRootNotAbsent m w).mp hWhole hPop)

/-- The classical GOD_4 root of the quarta via, stated once against the
root-supply interface: an actual root of the selected relation, contingent
grounding, excluded middle and the 21 shared attribute and naming inputs.
Population and whole-roster nontrapping both follow from the root. -/
theorem deriveFromActualRoot {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hRoot : ActualRootExistsAt m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hApproach : GradesToMaximumAtBeing p.InAct MoreIn p.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading p.InAct p.CausesIn p.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn p.InAct)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite p.CausesIn p.esse)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hActPrior : ActSimplyPriorToPotencyReading p.InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading p.InAct InPotency)
    (hInfinity : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse ComponentOf σ.IsGod)
    (hGodMaximal : GodIsMaximalInBeing σ.IsGod p.InAct MoreIn p.esse)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill) :
    NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill := by
  obtain ⟨n, hn⟩ := hRoot
  exact TruthCore.Results.Causality.NecessaryClassicalGodRoot.derive σ m w p GoodIn InPotency
    MoreIn PriorSimply ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill
    ⟨n, hn.1.1, hn.1.2⟩ (wholeRosterOfActualRootExists m w ⟨n, hn⟩) hDep hEM hGenus hExisting
    hEsse hApproach hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent
    hIntellect hWill hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal hSuffice

end TruthCore.Results.Causality.RootSupplyInterface
