module

public import TruthCore.Causality.TemporalActualization
public import TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived

/-! Analyst interpretation of a fixed collection of eligible exercises and
its relation to actual esse-supplier edges. Exercise individuation and causal
adequacy are open application questions. -/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting

open TruthCore.Causality.TemporalActualization
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (sourceFreeFiniteCircle)
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived (ActualIdentityAncestryAcyclic)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

/-- Each eligible exercise at the recipient has a predecessor exercise at
the supplier for each actual esse-supplier edge. E is the selected type of
eligible exercises and C is the selected relation on those exercises. -/
def BackwardActualEsseExerciseLifting {B P R E : Type} (p : Profile B P R)
    (bearer : E → B) (C : E → E → Prop) : Prop :=
  ∀ c x, ActualEsseCause p c x → ∀ f, bearer f = x → ∃ e, bearer e = c ∧ C e f

/-- Exercise fibres need to be finite and inhabited only at actual bearers
whose represented esse equals their represented essence. -/
def ActualIdentityExerciseFibresFiniteNonempty {B P R E : Type} (p : Profile B P R)
    (bearer : E → B) : Prop :=
  ∀ r, p.InAct r p.esse → p.esseOf r = p.essenceOf r →
    { e | bearer e = r }.Finite ∧ { e | bearer e = r }.Nonempty

/-- Both bearers are actual and supply each other. Exactly the true bearer
has represented esse equal to its represented essence. -/
def exerciseFeedbackProfile : Profile Bool Bool Unit :=
  { sourceFreeFiniteCircle with esseOf := Bool.not }

/-- The bearer of exercise n alternates, with even indices on the actual
identity bearer of the feedback profile. -/
def alternatingExerciseBearer (n : ℕ) : Bool := decide (n % 2 = 0)

/-- The supplier at n+1 precedes the recipient at n in the exercise relation.
The index enumerates the chain and is not a clock. -/
def unboundedExerciseSupply (e f : ℕ) : Prop := e = f + 1

/-- Exact existence-based projection and finite inhabited identity fibres
do not suffice: the three standing feedback tokens lack backward lifting.
The same two-bearer profile supports backward lifting in the alternating
exercise chain with an inhabited infinite identity fibre. Both profiles of
exercises are acyclic while the fixed bearer relation returns to identity. -/
def ExerciseLiftingControls : Prop :=
  let p := exerciseFeedbackProfile
  (∀ r, p.InAct r p.esse ∧ p.esseOf r = p.essenceOf r ↔ r = true) ∧
  ¬ ActualIdentityAncestryAcyclic p ∧
  (EventAcyclic feedbackC ∧
    (∀ c x, ActualEsseCause p c x ↔ BeingEdge feedbackBearer feedbackC c x) ∧
    ActualIdentityExerciseFibresFiniteNonempty p feedbackBearer ∧
    ¬ BackwardActualEsseExerciseLifting p feedbackBearer feedbackC) ∧
  (EventAcyclic unboundedExerciseSupply ∧
    (∀ c x, ActualEsseCause p c x ↔
      BeingEdge alternatingExerciseBearer unboundedExerciseSupply c x) ∧
    BackwardActualEsseExerciseLifting p alternatingExerciseBearer unboundedExerciseSupply ∧
    { e | alternatingExerciseBearer e = true }.Infinite ∧
    { e | alternatingExerciseBearer e = true }.Nonempty)

end TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
