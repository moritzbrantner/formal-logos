module

public import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution
public import TruthCore.Results.Causality.SourceScopedAscent.Solution
public import TruthCore.Results.Causality.DeEnteSourceGod.Solution

@[expose] public section

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
  have hPopEsse : ActualEssePopulation p := by
    obtain ⟨x, _, hx⟩ := hPop
    exact ⟨x, hExisting x hx⟩
  have hSource := TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.commonSourceOfClosed
    p hRooted hOther hUnique hPopEsse hEM
  have hGenus := TruthCore.Results.Causality.SourceScopedAscent.maximalCausesFromIdentityAscent
    p MoreIn hSource hCompose hAscent hEM
  obtain ⟨n, hn, hIdentity, hUncaused, hPaths⟩ := hSource
  obtain ⟨r, hr⟩ := TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists
    m w hPop hWhole hEM
  have hEq : r = n := by
    rcases hEM (r = n) with hEq | hNe
    · exact hEq
    · have hCause := TruthCore.Results.Causality.Q44SourceSupply.causeOfChain p hCompose hn
        (hPaths r (hExisting r hr.1.2) hNe)
      exact (hr.2 n (hEsse n r (fun h => hNe h.symm) hr.1 hCause)).elim
  have hActualSource : DeEnteFirstSourceIsActualRootAt m w p :=
    ⟨n, hEq ▸ hr, hn, hIdentity, hUncaused, hPaths⟩
  exact TruthCore.Results.Causality.DeEnteSourceGod.deEnteSourceIsGod
    m w p MoreIn PriorSimply ComponentOf IsGod hActualSource hEM hPrior hGenus hExisting
    hEsse hApproach hBeing hTransfer hNoComponent hNaming

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
    GodExists IsGod :=
  TruthCore.Results.Causality.DeEnteSourceGod.godExistsOfDeEnteSourceIsGod
    m w p PriorSimply IsGod (sameSourceIsGodFromClosedCollections
      p m w MoreIn PriorSimply ComponentOf IsGod hPop hWhole hEM hPrior hExisting
      hRooted hOther hUnique hCompose hAscent hEsse hApproach hBeing hTransfer
      hNoComponent hNaming)

end TruthCore.Results.Causality.ClosedEsseSourceGod
