import Mathlib.Data.Set.Finite.Lemmas
import TruthCore.Latin.Aquinas.DeEnte.BoundedIdentityExercise
import TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting.Solution

namespace TruthCore.Results.Aquinas.DeEnte.BoundedIdentityExercise

open TruthCore.Causality (zenoStageTime)
open TruthCore.Causality.OperationLocalFiniteness
open TruthCore.Causality.TemporalActualization (StrictForward)
open TruthCore.Causality.TemporalEventControls (eventTime)
open TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
open TruthCore.Latin.Aquinas.DeEnte.BoundedIdentityExercise
open TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise (ActualIdentityHasMinimalExercise)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting (exerciseLiftingControls)

/-- From some exercise in the fibre, look only at the bounded interval from
the fibre's lower bound through that exercise. Its index set is finite. -/
theorem minimalExerciseOfBoundedLocallyFiniteClock {B P R E : Type}
    (p : Profile B P R) (bearer : E → B) (C : E → E → Prop) (clock : E → ℝ)
    (inhabited : ActualIdentityExerciseFibresInhabited p bearer)
    (bounded : ActualIdentityExerciseTimesBoundedBelow p bearer clock)
    (locallyFinite : ActualIdentityExerciseTimesLocallyFinite p bearer clock)
    (forward : StrictForward clock C) :
    ActualIdentityHasMinimalExercise p bearer C := by
  sorry

/-- The same alternating exercise graph works both with a locally finite
unbounded clock and with a bounded clock whose indices accumulate. -/
theorem boundedIdentityExerciseControls : BoundedIdentityExerciseControls := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.BoundedIdentityExercise
