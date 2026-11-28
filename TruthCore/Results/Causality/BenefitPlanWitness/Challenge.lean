import TruthCore.Causality.BenefitPlanWitness

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
  sorry

theorem recipientOfSomeGoverningPlan
    {W B T R S P E K : Type} {F : CausalityFrame W B T R} {A : AgencyFrame W B S P}
    {M : Plan W B R E K} {InAct : B → R → Prop} {IsGod : B → Prop}
    {WillsGoodFor : B → B → R → Prop} {w : W}
    (coverage : RationalGivingHasPlan F A M InAct w)
    (omission : SomeGoverningPlanRejectsBenefitOmission F M InAct IsGod w)
    (recognition : RequiredBenefitIsWilled M WillsGoodFor w) :
    DivineRationalGivingWillsEsseFor F A InAct IsGod WillsGoodFor w := by
  sorry

theorem controls : Control.Comparison := by
  sorry

end TruthCore.Results.Causality.BenefitPlanWitness
