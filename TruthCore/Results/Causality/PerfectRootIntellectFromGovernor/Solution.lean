module

public import TruthCore.Causality.RootPositiveIntellectWill
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Case.Catholicism.StageOneConvergence

@[expose] public section

namespace TruthCore.Results.Causality.PerfectRootIntellectFromGovernor
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Causality.RootPositiveIntellectWill
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic (ExcludedMiddle)

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
  obtain ⟨d, hMaxD, hIntD, _hDirection⟩ := hGovernor
  -- A distinct maximum d would cause the being of n. The SAME n has no
  -- actual concrete ground, so the esse/ground dictionary rules this out.
  have hSame : d = n := by
    rcases hEM (d = n) with hEq | hNe
    · exact hEq
    · have hCause := hGenus d hMaxD n (Ne.symm hNe) hPerfectN.2.2.2.1.1
      exact (hr.2 d (hEsse d n hNe hr.1 hCause)).elim
  have hInt : HasIntellect n := hSame ▸ hIntD
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

end TruthCore.Results.Causality.PerfectRootIntellectFromGovernor
