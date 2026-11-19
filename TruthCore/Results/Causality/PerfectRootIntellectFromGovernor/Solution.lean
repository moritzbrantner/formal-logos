module

public import TruthCore.Causality.RootPositiveIntellectWill
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Case.Catholicism.StageOneConvergence
public import TruthCore.Results.Causality.ActualCommonRoot.Solution
public import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution

@[expose] public section

namespace TruthCore.Results.Causality.PerfectRootIntellectFromGovernor
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Causality.RootPositiveIntellectWill
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic (ExcludedMiddle)

/-- The identity fact used by `derive` does not need a perfect or necessary
root: any maximum in the fixed esse respect would cause the esse of a distinct
actual root, contradicting that root's lack of incoming actual ground. -/
theorem maximumEqualsActualRootAtBeing {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (n : B) (hr : ActualRoot m w n) (hInActN : InAct n esse)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    ∀ d, IsMaximumIn InAct MoreIn esse d → d = n := by
  intro d hMaxD
  rcases hEM (d = n) with hEq | hNe
  · exact hEq
  · have hCause : CausesIn d n esse := hGenus d hMaxD n (Ne.symm hNe) hInActN
    exact (hr.2 d (hEsse d n hNe hr.1 hCause)).elim

/-- Capacity at exactly the supplied actual root. The governor premise supplies
an intellectual maximum; its global direction clause is unused, and no
necessity, perfect-root structure, will or actual thought occurs in this type. -/
theorem intellectAtActualRoot {W B R End : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (NaturalBody HasIntellect : B → Prop) (Directs : B → B → End → Prop)
    (n : B) (hr : ActualRoot m w n) (hInActN : InAct n esse)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hGovernor : MaximeEnsGovernsNature InAct MoreIn esse NaturalBody HasIntellect Directs) :
    IsMaximumIn InAct MoreIn esse n ∧ HasIntellect n := by
  obtain ⟨d, hMaxD, hIntD, _⟩ := hGovernor
  have hSame := maximumEqualsActualRootAtBeing m w InAct MoreIn CausesIn esse
    n hr hInActN hEM hGenus hEsse d hMaxD
  exact ⟨hSame ▸ hMaxD, hSame ▸ hIntD⟩

/-- A governor already witnesses an esse maximum, so it constructively entails
the conditional grades-to-a-maximum premise at esse. This strength implication
is not a second independent reason for the existence of a maximum. -/
theorem governorImpliesGradesAtBeing {B R End : Type}
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (NaturalBody HasIntellect : B → Prop) (Directs : B → B → End → Prop)
    (hGovernor : MaximeEnsGovernsNature InAct MoreIn esse NaturalBody HasIntellect Directs) :
    TruthCore.Causality.DirectEsseRootUniquenessAtBeing.GradesToMaximumAtBeing
      InAct MoreIn esse := by
  intro _
  obtain ⟨d, hMax, _, _⟩ := hGovernor
  exact ⟨d, hMax⟩

/-- The SAME supplied actual root is intellectual and directly grounds every
other actual concretum under the retained genus and esse-to-ground interfaces.
Uniqueness reuses `ActualCommonRoot.uniqueRoot`; the common root's witness is n. -/
theorem intellectCommonRootAtActualRoot {W B R End : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (NaturalBody HasIntellect : B → Prop) (Directs : B → B → End → Prop)
    (n : B) (hr : ActualRoot m w n)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hGovernor : MaximeEnsGovernsNature InAct MoreIn esse NaturalBody HasIntellect Directs) :
    IsMaximumIn InAct MoreIn esse n ∧ HasIntellect n ∧
      (∀ x, ActualConcrete m w x → x = n ∨ ActualConcreteGround m w n x) ∧
      UniqueActualRootAt m w := by
  obtain ⟨hMax, hInt⟩ := intellectAtActualRoot m w InAct MoreIn CausesIn esse
    NaturalBody HasIntellect Directs n hr (hExisting n hr.1.2) hEM hGenus hEsse hGovernor
  have hCover : ∀ x, ActualConcrete m w x → x = n ∨ ActualConcreteGround m w n x := by
    intro x hx
    rcases hEM (x = n) with hSame | hOther
    · exact Or.inl hSame
    · exact Or.inr (hEsse n x (fun heq => hOther heq.symm) hx
        (hGenus n hMax x hOther (hExisting x hx.2)))
  have hCommon : ActualCommonRootAt m w := ⟨n, hr, hCover⟩
  exact ⟨hMax, hInt, hCover,
    TruthCore.Results.Causality.ActualCommonRoot.uniqueRoot m w hCommon⟩

/-- Consume the supplied perfect root, retaining ONE witness throughout.
Uniqueness is only among selected actual roots, not all necessary individuals.
The source/cognitive/causal applicability of the supplied readings stays open. -/
theorem derive {W B P R End : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (GoodIn : B → R → Prop) (MoreIn : R → B → B → Prop)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill NaturalBody : B → Prop)
    (Directs : B → B → End → Prop)
    (hPerfect : NecessaryPerfectRootAt m w p.InAct MoreIn p.esse)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn p.InAct)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite p.CausesIn p.esse)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hGovernor : MaximeEnsGovernsNature p.InAct MoreIn p.esse NaturalBody HasIntellect Directs)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill) :
    NecessaryPositiveRootIntellectWillAt m w p GoodIn MoreIn PriorSimply ComponentOf
      Composite MatterForm HasIntellect HasWill := by
  obtain ⟨n, hPerfectN⟩ := hPerfect
  have hr := hPerfectN.1
  have hAtRoot := intellectAtActualRoot m w p.InAct MoreIn p.CausesIn p.esse
    NaturalBody HasIntellect Directs n hr hPerfectN.2.2.2.1.1 hEM hGenus hEsse hGovernor
  have hInt : HasIntellect n := hAtRoot.2
  have hGood := supremelyGoodOfMaximum p.InAct GoodIn MoreIn p.CausesIn p.esse n
    hPerfectN.2.2.2.1 hGenus hBeing hGoodness hTransfer
  have hSimple : IsSimple Composite n := by
    intro hComposite
    obtain ⟨c, hNe, hCause⟩ := hUniting n hComposite
    exact hr.2 c (hEsse c n hNe hr.1 hCause)
  have hIdentity : p.esseOf n = p.essenceOf n := by
    rcases hEM (p.esseOf n = p.essenceOf n) with hEq | hNe
    · exact hEq
    · exact (hSimple ((hKinds n).2 hNe)).elim
  have hFirst : IsFirstBeing PriorSimply n := by
    intro c hPriorN
    rcases hEM (c = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 c (hPrior c n hNe hPriorN)).elim
  have hMatter : ¬ MatterForm n := fun h => hSimple ((hKinds n).1 h)
  have hRemote : RemoteFromAll ComponentOf n :=
    fun y hy => hNoComponent n y hy hFirst
  exact ⟨n, hPerfectN, hGood, hIdentity, hSimple, hFirst, hMatter, hRemote,
    hInt, hWill n hInt⟩

/-- Reuse the existing roster descent only to supply an actual-root witness.
No intellect, maximum, grades or God naming is built into this projection. -/
theorem actualRootExistsOfWholeRoster {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle) :
    ActualRootExistsAt m w :=
  TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists m w hPop hWhole hEM

/-- Another existing root producer, with stronger direct-coverage content.
The existential witness is merely projected, not invented anew. -/
theorem actualRootExistsOfCommonRoot {W B : Type} (m : Profile W B) (w : W)
    (hCommon : ActualCommonRootAt m w) : ActualRootExistsAt m w := by
  obtain ⟨n, hn, _⟩ := hCommon
  exact ⟨n, hn⟩

/-- Fixed-esse same-witness God naming from an independently supplied actual
root and governor. Unlike the generic `DirectEsseRootGodExistence.godOfRoot`,
this route already has its maximum from the governor and needs neither global
grades-to-a-maximum nor all-respects genus causality. It reuses the same
`CausalPerfectionTransfer.reducedDescription` naming calculation.

The result contains an actual ROOT n, its direct coverage of every other
actual concretum, GOD_4 naming and HAS_INTELLECT_1 capacity AT THAT SAME n.
Neither occurrence of thought nor correctness of the teleological/God-naming
premises is asserted. -/
theorem intellectualGodCommonRoot {W B R End : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (PriorSimply ComponentOf : B → B → Prop)
    (IsGod NaturalBody HasIntellect : B → Prop) (Directs : B → B → End → Prop)
    (hRoot : ActualRootExistsAt m w)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hGovernor : MaximeEnsGovernsNature InAct MoreIn esse NaturalBody HasIntellect Directs)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    IntellectualGodCommonRootAt m w IsGod HasIntellect := by
  obtain ⟨n, hr⟩ := hRoot
  obtain ⟨hMax, hInt, hCover, _⟩ := intellectCommonRootAtActualRoot
    m w InAct MoreIn CausesIn esse NaturalBody HasIntellect Directs n hr
    hEM hGenus hExisting hEsse hGovernor
  have hFirst : IsFirstBeing PriorSimply n := by
    intro c hc
    rcases hEM (c = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 c (hPrior c n hNe hc)).elim
  have hMaximumAll : ∀ d, IsMaximumIn InAct MoreIn esse d → d = n :=
    maximumEqualsActualRootAtBeing m w InAct MoreIn CausesIn esse n hr
      (hExisting n hr.1.2) hEM hGenus hEsse
  have hFirstMaximum : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
    intro d hd
    have hSame := hMaximumAll d hd
    subst d
    exact hFirst
  have hNaming :=
    TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.reducedDescription
      InAct MoreIn CausesIn esse ComponentOf PriorSimply IsGod
      hBeing hTransfer hNoComponent hFirstMaximum hFull
  have hGod : IsGod n := hNaming n hMax (hGenus n hMax) hMaximumAll
  exact ⟨n, hr, hCover, hGod, hInt⟩

/-- The witness package feeds the existing GOD_4 existence-stage root.
The projection itself is an assembly, not a second proof of God existence. -/
theorem godExistsOfIntellectualRoot {W B : Type} (m : Profile W B) (w : W)
    (IsGod HasIntellect : B → Prop)
    (hRoot : IntellectualGodCommonRootAt m w IsGod HasIntellect) :
    GodExists IsGod := by
  obtain ⟨n, _, _, hGod, _⟩ := hRoot
  exact ⟨n, hGod⟩

end TruthCore.Results.Causality.PerfectRootIntellectFromGovernor
