module

public import TruthCore.Causality.BenefitPlanWitness

/-! Witness obligations for six denials in the selected-world giving argument. -/

@[expose] public section

namespace TruthCore.Causality.GivingPlanExceptions

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.WillVersusChance (AgencyFrame)
open TruthCore.Causality.ThroughWill (RationallyGivesAt)
open TruthCore.Causality.PracticalSpecification
open TruthCore.Causality.BenefitPlanWitness (SomeGoverningPlanRejectsBenefitOmission)

/-- The six exceptions are indexed separately. No common counterexample across
the six principles is asserted. Omission is expressed directly by the content
of the successful standard, independent of the assigned recognition relations. -/
def Exceptions {W B T R S P E K : Type} (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (M : Plan W B R E K) (InAct : B → R → Prop)
    (IsGod : B → Prop) (Wills : B → B → R → Prop) (Directs : B → B → E → Prop) (w : W) : Prop :=
  (¬ RationalGivingHasPlan F A M InAct w ↔
    ∃ g x, x ≠ g ∧ InAct x F.esse ∧ RationallyGivesAt F A w g x ∧
      ∀ k, ¬ Governing M w g x k) ∧
  (¬ SomeGoverningPlanRejectsBenefitOmission F M InAct IsGod w ↔
    ∃ g x, IsGod g ∧ x ≠ g ∧ InAct x F.esse ∧ (∃ k, Governing M w g x k) ∧
      ∀ k, Governing M w g x k → ¬ M.Requirement k (.benefit x F.esse)) ∧
  (¬ DivinePlanRejectsBenefitOmission F M InAct IsGod w ↔
    ∃ g x k, IsGod g ∧ x ≠ g ∧ InAct x F.esse ∧ Governing M w g x k ∧
      ¬ M.Requirement k (.benefit x F.esse)) ∧
  (¬ RequiredBenefitIsWilled M Wills w ↔
    ∃ g x k r, Governing M w g x k ∧ M.Requirement k (.benefit x r) ∧ ¬ Wills g x r) ∧
  (¬ PlanRejectsEndOmission F M InAct w ↔
    ∃ g x k, x ≠ g ∧ InAct x F.esse ∧ Governing M w g x k ∧
      ∀ e, ¬ M.Requirement k (.toward x e)) ∧
  (¬ RequiredEndIsDirected M Directs w ↔
    ∃ g x k e, Governing M w g x k ∧ M.Requirement k (.toward x e) ∧ ¬ Directs g x e)

end TruthCore.Causality.GivingPlanExceptions
