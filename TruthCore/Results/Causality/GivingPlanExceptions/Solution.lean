module

public import TruthCore.Causality.GivingPlanExceptions

@[expose] public section

namespace TruthCore.Results.Causality.GivingPlanExceptions

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.WillVersusChance (AgencyFrame)
open TruthCore.Causality.PracticalSpecification
open TruthCore.Causality.BenefitPlanWitness (SomeGoverningPlanRejectsBenefitOmission)
open TruthCore.Causality.GivingPlanExceptions (Exceptions)

private theorem survivesEdit {B R E : Type} {Q actual removed : Clause B R E → Prop}
    (met : ∀ c, Q c → actual c) :
    (∀ c, Q c → Without actual removed c) ↔ ∀ c, removed c → ¬ Q c := by
  constructor
  · intro h c hc hq
    exact (h c hq).2 hc
  · intro h c hq
    exact ⟨met c hq, fun hc => h c hc hq⟩

theorem exceptions {W B T R S P E K : Type} (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (M : Plan W B R E K) (InAct : B → R → Prop)
    (IsGod : B → Prop) (Wills : B → B → R → Prop) (Directs : B → B → E → Prop) (w : W) :
    Exceptions F A M InAct IsGod Wills Directs w := by
  classical
  have benefit (g x : B) (k : K) (h : Governing M w g x k) :
      Meets M k (Without (M.Realized w g x) (· = .benefit x F.esse)) ↔
      ¬ M.Requirement k (.benefit x F.esse) := by
    exact (survivesEdit h.2.2).trans (by simp)
  have ends (g x : B) (k : K) (h : Governing M w g x k) :
      Meets M k (Without (M.Realized w g x) (fun c => ∃ e, c = .toward x e)) ↔
      ∀ e, ¬ M.Requirement k (.toward x e) := by
    exact (survivesEdit h.2.2).trans (by simp)
  simp +contextual [Exceptions, RationalGivingHasPlan, SomeGoverningPlanRejectsBenefitOmission,
    DivinePlanRejectsBenefitOmission, RequiredBenefitIsWilled, PlanRejectsEndOmission,
    RequiredEndIsDirected, Classical.not_forall, benefit, ends]

end TruthCore.Results.Causality.GivingPlanExceptions
