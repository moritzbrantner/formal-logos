module

public import TruthCore.Causality.BenefitPlanWitness

@[expose] public section

namespace TruthCore.Results.Causality.BenefitPlanWitness

open TruthCore.Causality.BenefitPlanWitness
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.PracticalSpecification
open TruthCore.Causality.ThroughWill (DivineRationalGivingWillsEsseFor)
open TruthCore.Causality.WillVersusChance (AgencyFrame)

theorem someFromEvery
    {W B T R E K : Type} {F : CausalityFrame W B T R} {M : Plan W B R E K}
    {InAct : B → R → Prop} {IsGod : B → Prop} {w : W}
    (omission : DivinePlanRejectsBenefitOmission F M InAct IsGod w) :
    SomeGoverningPlanRejectsBenefitOmission F M InAct IsGod w := by
  intro g x hg hOther hAct hExists
  obtain ⟨k, hPlan⟩ := hExists
  exact ⟨k, hPlan, omission g x k hg hOther hAct hPlan⟩

theorem recipientOfSomeGoverningPlan
    {W B T R S P E K : Type} {F : CausalityFrame W B T R} {A : AgencyFrame W B S P}
    {M : Plan W B R E K} {InAct : B → R → Prop} {IsGod : B → Prop}
    {WillsGoodFor : B → B → R → Prop} {w : W}
    (coverage : RationalGivingHasPlan F A M InAct w)
    (omission : SomeGoverningPlanRejectsBenefitOmission F M InAct IsGod w)
    (recognition : RequiredBenefitIsWilled M WillsGoodFor w) :
    DivineRationalGivingWillsEsseFor F A InAct IsGod WillsGoodFor w := by
  classical
  intro g x hg hOther hAct hGiving
  obtain ⟨k, hPlan, hReject⟩ := omission g x hg hOther hAct (coverage g x hOther hAct hGiving)
  apply recognition g x k F.esse hPlan
  by_contra hOptional
  apply hReject
  intro c hRequired
  refine ⟨hPlan.2.2 c hRequired, ?_⟩
  rintro rfl
  exact hOptional hRequired

theorem controls : Control.Comparison := by
  have forallClause (p : Clause Bool Unit Unit → Prop) :
      (∀ c, p c) ↔
        (∀ x, p (.output x)) ∧ (∀ x, p (.benefit x ())) ∧ (∀ x, p (.toward x ())) := by
    constructor
    · intro h
      exact ⟨fun x => h (.output x), fun x => h (.benefit x ()), fun x => h (.toward x ())⟩
    · rintro ⟨hOutput, hBenefit, hEnd⟩ c
      cases c with
      | output x => exact hOutput x
      | benefit x r => cases r; exact hBenefit x
      | toward x e => cases e; exact hEnd x
  open TruthCore.Causality.BenefitPlanWitness.Control
    TruthCore.Causality.PracticalSpecification.Control in
  simp [Comparison, SomeGoverningPlanRejectsBenefitOmission, plans, forallClause,
    recipientBridge, directionBridge, wills, directs,
    RationalGivingHasPlan, DivinePlanRejectsBenefitOmission, PlanRejectsEndOmission,
    RequiredBenefitIsWilled, RequiredEndIsDirected, Governing, Meets, Without,
    DivineRationalGivingWillsEsseFor,
    TruthCore.Causality.ThroughWill.RationalUniversalGivingDirects,
    TruthCore.Causality.ThroughWill.RationallyGivesAt,
    TruthCore.Causality.ThroughWill.IntellectualUniversalCausesGiveRationallyAt,
    TruthCore.Causality.ThroughWill.Control.rational, TruthCore.Causality.ThroughWill.Control.model,
    TruthCore.Causality.ThroughWill.Control.agency, TruthCore.Causality.ThroughWill.Control.acts,
    TruthCore.Causality.ThroughWill.Control.intellect, TruthCore.Causality.ThroughWill.Control.will,
    TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading,
    TruthCore.Modal.PrussPowerPremises.GivesTo, TruthCore.Causality.WillVersusChance.GivesBy,
    TruthCore.Causality.DeiFiliusAttributeField.IsCreatorOfAll, Bool.forall_bool, Bool.exists_bool]

end TruthCore.Results.Causality.BenefitPlanWitness
