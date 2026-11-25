import TruthCore.Causality.RootSupplyInterface
import TruthCore.Results.Causality.NecessaryClassicalGodRoot.Solution

/-!
# Root-supply interface: strength orders and one derivation against it (#1926)

Whole-roster nontrapping follows constructively from root existence and from
well-founded actual grounding. Root existence factors exactly as whole-roster
nontrapping plus population and stability of root existence. The classical
GOD_4 root of the quarta via is derived once from root existence, the
interface, instead of from population and whole-roster nontrapping. No premise
is proved here.
-/

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
  sorry

/-- Well-founded actual grounding makes the nonempty actual roster no trap:
no accessible actual concretum lies in a trap. Constructive. -/
theorem wholeRosterOfActualGroundingWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : WholeRosterNotTrapped m w := by
  sorry

/-- Whole-roster nontrapping is the population-conditional, double-negated
form of root existence. Constructive. -/
theorem wholeRosterIsInhabitedRootNotAbsent : WholeRosterIsInhabitedRootNotAbsent := by
  sorry

/-- Certified difference: root existence is whole-roster nontrapping plus
population and stability of root existence. Constructive. -/
theorem rootExistsOverWholeRosterExact : RootExistsOverWholeRosterExact := by
  sorry

/-- Given population, stability of root existence is the implication from
nontrapping to root existence. Constructive. -/
theorem stabilityIsRootImplicationGivenPopulation :
    StabilityIsRootImplicationGivenPopulation := by
  sorry

/-- The all-subsets borrowing cut factors through its whole-roster instance.
Constructive. -/
theorem borrowingCutFactorsThroughWholeRoster : BorrowingCutFactorsThroughWholeRoster := by
  sorry

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
  sorry

end TruthCore.Results.Causality.RootSupplyInterface
