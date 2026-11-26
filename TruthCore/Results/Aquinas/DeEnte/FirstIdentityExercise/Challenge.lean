import TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise
import TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting.Solution
import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution

namespace TruthCore.Results.Aquinas.DeEnte.FirstIdentityExercise

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
open TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
open TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting (liftActualEssePath)
open TruthCore.Causality.TemporalActualization (EventAcyclic)

/-- Lift a putative return into the chosen exercise. Its predecessor would
belong to the same bearer, contrary to the choice of exercise. -/
theorem noReturnOfMinimalExercise (p : Profile B P R) (bearer : E → B) (C : E → E → Prop)
    (lift : BackwardActualEsseExerciseLifting p bearer C)
    (minimal : ActualIdentityHasMinimalExercise p bearer C) : ActualIdentityAncestryAcyclic p := by
  sorry

/-- With faithful edge projection, absence of bearer returns makes every
represented exercise of that identity bearer minimal among its own exercises. -/
theorem minimalExerciseOfNoReturn (p : Profile B P R) (bearer : E → B) (C : E → E → Prop)
    (noReturn : ActualIdentityAncestryAcyclic p)
    (inhabited : ∀ r, p.InAct r p.esse → p.esseOf r = p.essenceOf r → ∃ f, bearer f = r)
    (projects : ∀ e f, C e f → ActualEsseCause p (bearer e) (bearer f)) :
    ActualIdentityHasMinimalExercise p bearer C := by
  sorry

/-- Reuse the rooted two-dependent cycle. Give every bearer infinitely many
exercise tokens. Supply acts can cycle away from the identity bearer; that
bearer's own exercises have no predecessors among its own exercises. -/
theorem minimalWithInfiniteFibreAndOtherCycle :
    ∃ (p : Profile (Option Bool) Bool Unit) (C : (Option Bool × Nat) → (Option Bool × Nat) → Prop),
      CommonEsseIsEssenceSource p ∧ ActualIdentityHasMinimalExercise p Prod.fst C ∧
      BackwardActualEsseExerciseLifting p Prod.fst C ∧
      (∃ r, p.InAct r p.esse ∧ p.esseOf r = p.essenceOf r ∧
        {e : Option Bool × Nat | e.1 = r}.Infinite) ∧ ¬ EventAcyclic C := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.FirstIdentityExercise
