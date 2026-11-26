import TruthCore.Causality.GivingPlanExceptions

namespace TruthCore.Results.Causality.GivingPlanExceptions

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.WillVersusChance (AgencyFrame)
open TruthCore.Causality.PracticalSpecification
open TruthCore.Causality.BenefitPlanWitness (SomeGoverningPlanRejectsBenefitOmission)
open TruthCore.Causality.GivingPlanExceptions (Exceptions)

theorem exceptions {W B T R S P E K : Type} (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (M : Plan W B R E K) (InAct : B → R → Prop)
    (IsGod : B → Prop) (Wills : B → B → R → Prop) (Directs : B → B → E → Prop) (w : W) :
    Exceptions F A M InAct IsGod Wills Directs w := by
  sorry

end TruthCore.Results.Causality.GivingPlanExceptions
