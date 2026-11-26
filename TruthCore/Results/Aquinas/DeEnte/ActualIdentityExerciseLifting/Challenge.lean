import TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
import TruthCore.Results.Causality.TemporalActualization.Controls.Solution

namespace TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting

open TruthCore.Causality.TemporalActualization
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (sourceFreeFiniteCircle)
open TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived (ActualIdentityAncestryAcyclic)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

/-- A nonempty finite supplier path lifts backwards from any eligible
exercise at its endpoint, on the same fixed interpretation. -/
theorem liftActualEssePath {B P R E : Type} {p : Profile B P R} {bearer : E → B}
    {C : E → E → Prop} (lift : BackwardActualEsseExerciseLifting p bearer C)
    {c x : B} (path : Relation.TransGen (ActualEsseCause p) c x)
    (f : E) (target : bearer f = x) :
    ∃ e, bearer e = c ∧ Relation.TransGen C e f := by
  sorry

/-- A bearer return would lift backwards from every exercise in its fibre.
An inhabited finite identity fibre has a minimal exercise under acyclic
nonempty finite exercise reachability, contradicting that lifted return. -/
theorem actualIdentityAncestryAcyclicOfExerciseLifting {B P R E : Type}
    (p : Profile B P R) (bearer : E → B) (C : E → E → Prop)
    (acyclic : EventAcyclic C)
    (lift : BackwardActualEsseExerciseLifting p bearer C)
    (fibres : ActualIdentityExerciseFibresFiniteNonempty p bearer) :
    ActualIdentityAncestryAcyclic p := by
  sorry

/-- The existing finite feedback example fails lifting. An unbounded
alternating chain still projects to the same bearer return even when
every eligible exercise has the required supplier exercise. -/
theorem exerciseLiftingControls : ExerciseLiftingControls := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting
