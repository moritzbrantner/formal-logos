import TruthCore.Causality.PracticalSpecification

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
  sorry

theorem directionOfPracticalSpecification
    {W B T R S P E K : Type} {F : CausalityFrame W B T R} {A : AgencyFrame W B S P}
    {M : Plan W B R E K} {InAct : B → R → Prop} {HasIntellect HasWill : B → Prop}
    {Directs : B → B → E → Prop} {w : W}
    (coverage : RationalGivingHasPlan F A M InAct w)
    (omission : PlanRejectsEndOmission F M InAct w)
    (recognition : RequiredEndIsDirected M Directs w) :
    RationalUniversalGivingDirects F A InAct HasIntellect HasWill Directs w := by
  sorry

theorem controls : TruthCore.Causality.PracticalSpecification.Control.Controls := by
  sorry

end TruthCore.Results.Causality.PracticalSpecification
