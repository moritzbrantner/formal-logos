module

public import TruthCore.Causality.OperationLocalFiniteness
public import TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise

/-! A real-clock support option for minimal eligible exercise. An application
needs an independently adequate selection of esse-supply exercises and a
physically interpreted clock on those very tokens. Clock bounds and local
finiteness concern indexed tokens in the selected fibre. -/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.BoundedIdentityExercise

open TruthCore.Causality.OperationLocalFiniteness
open TruthCore.Causality.TemporalActualization (StrictForward)
open TruthCore.Causality.TemporalEventControls (eventTime)
open TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
open TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise (ActualIdentityHasMinimalExercise)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

variable {B P R E : Type}

/-- The represented esse identity of an actual bearer has an eligible exercise. -/
def ActualIdentityExerciseFibresInhabited (p : Profile B P R) (bearer : E → B) : Prop :=
  ∀ r, p.InAct r p.esse → p.esseOf r = p.essenceOf r → ∃ e, bearer e = r

/-- Each such fibre has a lower real-time bound of its own. -/
def ActualIdentityExerciseTimesBoundedBelow (p : Profile B P R)
    (bearer : E → B) (clock : E → ℝ) : Prop :=
  ∀ r, p.InAct r p.esse → p.esseOf r = p.essenceOf r →
    ∃ lower : ℝ, ∀ e, bearer e = r → lower ≤ clock e

/-- Each such fibre is locally finite as an indexed family in the real clock. -/
def ActualIdentityExerciseTimesLocallyFinite (p : Profile B P R)
    (bearer : E → B) (clock : E → ℝ) : Prop :=
  ∀ r, p.InAct r p.esse → p.esseOf r = p.essenceOf r →
    LocallyFiniteOperationTimes (fun e : { e : E // bearer e = r } => clock e.val)

/-- Hold the exercise graph and its bearer interpretation fixed and change
only the real clock. Each clock omits one hypothesis of the interval route. -/
def BoundedIdentityExerciseControls : Prop :=
  let p := exerciseFeedbackProfile
  let bearer := alternatingExerciseBearer
  let C := unboundedExerciseSupply
  ActualIdentityExerciseFibresInhabited p bearer ∧
    BackwardActualEsseExerciseLifting p bearer C ∧
    ¬ ActualIdentityHasMinimalExercise p bearer C ∧
    (StrictForward backwardClock C ∧
      ActualIdentityExerciseTimesLocallyFinite p bearer backwardClock ∧
      ¬ ActualIdentityExerciseTimesBoundedBelow p bearer backwardClock) ∧
    (StrictForward eventTime C ∧
      ActualIdentityExerciseTimesBoundedBelow p bearer eventTime ∧
      ¬ ActualIdentityExerciseTimesLocallyFinite p bearer eventTime)

end TruthCore.Latin.Aquinas.DeEnte.BoundedIdentityExercise
