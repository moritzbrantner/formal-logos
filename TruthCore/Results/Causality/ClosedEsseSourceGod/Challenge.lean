import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution
import TruthCore.Results.Causality.SourceScopedAscent.Solution
import TruthCore.Results.Causality.DeEnteSourceGod.Solution

namespace TruthCore.Results.Causality.ClosedEsseSourceGod

open TruthCore.Case.Catholicism
  (GodExists GodNamesTheFullyDescribedPrinciple UniversalCauseTransfersPerfections)
open TruthCore.Causality
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.Q44SourceSupply (ActualEsseCauseComposes)
open TruthCore.Causality.SameSourceWitness (DeEnteSourceIsGodAt)
open TruthCore.Causality.SourceScopedAscent (IdentityCauseAscent)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- A concrete existent gives a bearer in act as to esse. The common ancestor
of the actual esse bearers must be the world-indexed grounding root: otherwise
its composed esse causality would supply an actual concrete ground of that root.
The existing reduced-description argument names this same source. -/
theorem sameSourceIsGodFromClosedCollections {W B P R : Type}
    (p : Profile B P R) (m : BruteFoundationBoundary.Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (PriorSimply ComponentOf : B → B → Prop)
    (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hRooted : ClosedActualEsseCollectionsRooted p)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hUnique : AtMostOneEsseIsEssence p)
    (hCompose : ActualEsseCauseComposes p)
    (hAscent : IdentityCauseAscent p MoreIn)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hApproach : GradesByApproachToAMaximumReading p.InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse
      ComponentOf IsGod) :
    DeEnteSourceIsGodAt m w p PriorSimply IsGod := by
  sorry

theorem godExistsFromClosedCollections {W B P R : Type}
    (p : Profile B P R) (m : BruteFoundationBoundary.Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (PriorSimply ComponentOf : B → B → Prop)
    (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hRooted : ClosedActualEsseCollectionsRooted p)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hUnique : AtMostOneEsseIsEssence p)
    (hCompose : ActualEsseCauseComposes p)
    (hAscent : IdentityCauseAscent p MoreIn)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hApproach : GradesByApproachToAMaximumReading p.InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse
      ComponentOf IsGod) :
    GodExists IsGod := by
  sorry

end TruthCore.Results.Causality.ClosedEsseSourceGod
