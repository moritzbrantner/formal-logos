module

public import TruthCore.Causality.PracticalSpecification

/-! # A beneficiary requirement in one governing plan

Analyst weakening of the universal benefit omission test. A standard that
counts a recipient's esse as its good can govern the same giving as a
standard concerned with an instrumental role. The distinction matters
only where both standards actually govern under the existing semantics.
-/

@[expose] public section

namespace TruthCore.Causality.BenefitPlanWitness

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.PracticalSpecification

variable {W B T R E K : Type}

/-- OPEN. For each distinct actual recipient of a GOD_4 giving with any
successful governing plan, at least one successful governing plan rejects
omitting the credit for the recipient's esse as its own good. The witness
may be different from the one used to show that a plan governs. -/
def SomeGoverningPlanRejectsBenefitOmission (F : CausalityFrame W B T R)
    (M : Plan W B R E K) (InAct : B → R → Prop) (IsGod : B → Prop) (w : W) : Prop :=
  ∀ g x, IsGod g → x ≠ g → InAct x F.esse → (∃ k, Governing M w g x k) →
    ∃ k, Governing M w g x k ∧
      ¬ Meets M k (Without (M.Realized w g x) (· = .benefit x F.esse))

namespace Control

open TruthCore.Causality.PracticalSpecification.Control (recipientBridge directionBridge wills directs)
open TruthCore.Causality.ThroughWill.Control (model agency acts intellect will rational)
open TruthCore.Latin.Aquinas.SummaTheologiae (GoodnessIsActualityReading)

/-- The two standards require the same output and placement toward an end.
The second also requires recipient credit. The first governs in both
profiles. The second is apprehended and satisfied in both, but operates
only when `useBenefitPlan` is true. Actual realization is fixed, with no
output or end-placement assigned to the source. -/
def plans (useBenefitPlan : Bool) : Plan Bool Bool Unit Unit Bool where
  Requirement := fun k c => match c with
    | .output x | .toward x _ => x = true
    | .benefit x _ => x = true ∧ k = true
  ApprehendsAsGood := fun _ g _ => g = false
  SpecifiesGiving := fun _ g x k =>
    g = false ∧ x = true ∧ (k = false ∨ useBenefitPlan = true)
  Realized := fun _ g x c => g = false ∧ x = true ∧ match c with
    | .output y | .toward y _ | .benefit y _ => y = true

/-- At the selected world both profiles have the same rational giving,
actuality-goodness coextension, recipient willing, end test and recognition
relations. Every governing plan in both profiles shares the instrumental
requirements. Only the profile using the second standard witnesses the
existential benefit test. The first standard defeats the universal test in
both profiles. The willing and appraisal relations are explicit assignments,
not reductions to plan requirements. -/
def Comparison : Prop :=
  rational true false (some true) ∧
  GoodnessIsActualityReading acts acts ∧ recipientBridge true ∧ directionBridge true ∧
  (∀ useBenefitPlan,
    RationalGivingHasPlan (model true false) (agency (some true)) (plans useBenefitPlan) acts false ∧
    Governing (plans useBenefitPlan) false false true false ∧
    (plans useBenefitPlan).ApprehendsAsGood false false true ∧
    Meets (plans useBenefitPlan) true ((plans useBenefitPlan).Realized false false true) ∧
    ¬ DivinePlanRejectsBenefitOmission (model true false) (plans useBenefitPlan) acts will false ∧
    PlanRejectsEndOmission (model true false) (plans useBenefitPlan) acts false ∧
    RequiredBenefitIsWilled (plans useBenefitPlan) (wills true) false ∧
    RequiredEndIsDirected (plans useBenefitPlan) (directs true) false) ∧
  SomeGoverningPlanRejectsBenefitOmission (model true false) (plans true) acts will false ∧
  ¬ SomeGoverningPlanRejectsBenefitOmission (model true false) (plans false) acts will false ∧
  RequiredBenefitIsWilled (plans false) (wills false) false ∧
  ¬ RequiredBenefitIsWilled (plans true) (wills false) false ∧
  ¬ recipientBridge false

end Control
end TruthCore.Causality.BenefitPlanWitness
