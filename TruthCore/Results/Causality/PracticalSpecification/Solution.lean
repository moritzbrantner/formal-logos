module

public import TruthCore.Causality.PracticalSpecification

@[expose] public section

namespace TruthCore.Results.Causality.PracticalSpecification

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.PracticalSpecification
open TruthCore.Causality.ThroughWill (DivineRationalGivingWillsEsseFor RationalUniversalGivingDirects)
open TruthCore.Causality.WillVersusChance (AgencyFrame)

theorem recipientOfPracticalSpecification
    {W B T R S P E K : Type} {F : CausalityFrame W B T R} {A : AgencyFrame W B S P}
    {M : Plan W B R E K} {InAct : B → R → Prop} {IsGod : B → Prop}
    {WillsGoodFor : B → B → R → Prop} {w : W}
    (coverage : RationalGivingHasPlan F A M InAct w)
    (omission : DivinePlanRejectsBenefitOmission F M InAct IsGod w)
    (recognition : RequiredBenefitIsWilled M WillsGoodFor w) :
    DivineRationalGivingWillsEsseFor F A InAct IsGod WillsGoodFor w := by
  classical
  intro g x hg hOther hAct hGiving
  obtain ⟨k, hPlan⟩ := coverage g x hOther hAct hGiving
  apply recognition g x k F.esse hPlan
  by_contra hOptional
  apply omission g x k hg hOther hAct hPlan
  intro c hRequired
  refine ⟨hPlan.2.2 c hRequired, ?_⟩
  rintro rfl
  exact hOptional hRequired

theorem directionOfPracticalSpecification
    {W B T R S P E K : Type} {F : CausalityFrame W B T R} {A : AgencyFrame W B S P}
    {M : Plan W B R E K} {InAct : B → R → Prop} {HasIntellect HasWill : B → Prop}
    {Directs : B → B → E → Prop} {w : W}
    (coverage : RationalGivingHasPlan F A M InAct w)
    (omission : PlanRejectsEndOmission F M InAct w)
    (recognition : RequiredEndIsDirected M Directs w) :
    RationalUniversalGivingDirects F A InAct HasIntellect HasWill Directs w := by
  classical
  intro g _ _ _ x hOther hAct hGiving
  obtain ⟨k, hPlan⟩ := coverage g x hOther hAct hGiving
  by_contra hNoEnd
  apply omission g x k hOther hAct hPlan
  intro c hRequired
  refine ⟨hPlan.2.2 c hRequired, ?_⟩
  rintro ⟨e, rfl⟩
  exact hNoEnd ⟨e, recognition g x k e hPlan hRequired⟩

theorem controls : TruthCore.Causality.PracticalSpecification.Control.Controls := by
  open TruthCore.Causality.PracticalSpecification.Control in
  simp [Controls, coverage, benefitTest, endTest, recipientBridge, directionBridge, plan, wills,
    directs, RationalGivingHasPlan, DivinePlanRejectsBenefitOmission, PlanRejectsEndOmission,
    RequiredBenefitIsWilled, RequiredEndIsDirected, Governing, Meets, Without,
    DivineRationalGivingWillsEsseFor, RationalUniversalGivingDirects,
    TruthCore.Causality.ThroughWill.RationallyGivesAt,
    TruthCore.Causality.ThroughWill.IntellectualUniversalCausesGiveRationallyAt,
    TruthCore.Causality.ThroughWill.Control.rational, TruthCore.Causality.ThroughWill.Control.model,
    TruthCore.Causality.ThroughWill.Control.agency, TruthCore.Causality.ThroughWill.Control.acts,
    TruthCore.Causality.ThroughWill.Control.intellect, TruthCore.Causality.ThroughWill.Control.will,
    TruthCore.Modal.PrussPowerPremises.GivesTo, TruthCore.Causality.WillVersusChance.GivesBy,
    TruthCore.Causality.DeiFiliusAttributeField.IsCreatorOfAll, Bool.forall_bool]

end TruthCore.Results.Causality.PracticalSpecification
