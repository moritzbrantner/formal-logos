module

public import TruthCore.Results.Causality.Q44SourceSupply.Solution
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Results.Causality.DirectEsseRootGodExistence.ExistenceOnly.Solution

/-! Source-first support for the existing fixed-esse maximum principle.
No new causal relation, degree scale, source-existence flag or interpretation
of temporal conservation is introduced. -/

@[expose] public section
namespace TruthCore.Results.Causality.MaximalFromEsseSource
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte (CommonEsseIsEssenceSource)
open TruthCore.Causality.Q44SourceSupply (ActualEsseCauseComposes)
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Logic (ExcludedMiddle)

theorem maximalCauses {B P R : Type} (p : Profile B P R)
    (MoreIn : R → B → B → Prop)
    (hSource : CommonEsseIsEssenceSource p)
    (hCompose : ActualEsseCauseComposes p)
    (hAscent : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse)
    (hEM : ExcludedMiddle) :
    MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse := by
  obtain ⟨n, hn, _, _, hPaths⟩ := hSource
  have hScope : ∀ x, p.InAct x p.esse → x ≠ n → p.CausesIn n x p.esse := by
    intro x hx hxn
    exact TruthCore.Results.Causality.Q44SourceSupply.causeOfChain p hCompose hn
      (hPaths x hx hxn)
  intro m hm
  have hmn : m = n := by
    rcases hEM (m = n) with heq | hne
    · exact heq
    · exact (hm.2 n (hAscent n m (fun h => hne h.symm)
        (hScope m hm.1 hne))).elim
  subst m
  intro x hxn hx
  exact hScope x hx hxn

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.DirectEsseRootRoute
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- Exact twelve-input existence bundle with only the genus principle restricted
to esse. The same root is retained through naming; no necessity is asserted. -/
theorem sameWitnessGodAtBeing {W B Respect : Type} (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    ∃ n, ActualRoot m w n ∧ IsFirstBeing PriorSimply n ∧ IsGod n := by
  obtain ⟨n, hr⟩ := TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists
    m w hPop hWhole hEM
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 y (hPrior y n hNe hy)).elim
  have hIdent : ∀ y, IsMaximumIn InAct MoreIn esse y → y = n := by
    intro y hy
    rcases hEM (y = n) with heq | hne
    · exact heq
    · exact (hr.2 y (hEsse y n hne hr.1
        (hGenus y hy n (fun h => hne h.symm) (hExisting n hr.1.2)))).elim
  obtain ⟨y, hy⟩ := maximumExistsOfExistingRoot m w InAct MoreIn esse n hr
    hExisting hApproach hEM
  have hnMax : IsMaximumIn InAct MoreIn esse n := (hIdent y hy) ▸ hy
  have hFirstMax : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
    intro z hz
    exact (hIdent z hz) ▸ hFirst
  have hNaming :=
    TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.reducedDescription
      InAct MoreIn CausesIn esse ComponentOf PriorSimply IsGod
      hBeing hTransfer hNoComponent hFirstMax hFull
  exact ⟨n, hr, hFirst, hNaming n hnMax (hGenus n hnMax) hIdent⟩

theorem godExistsAtBeing {W B Respect : Type} (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  obtain ⟨n, _, _, hGod⟩ := sameWitnessGodAtBeing m w InAct MoreIn CausesIn esse
    PriorSimply ComponentOf IsGod hPop hWhole hEM hPrior hGenus hExisting hEsse
    hApproach hBeing hTransfer hNoComponent hFull
  exact ⟨n, hGod⟩

end TruthCore.Results.Causality.MaximalFromEsseSource
