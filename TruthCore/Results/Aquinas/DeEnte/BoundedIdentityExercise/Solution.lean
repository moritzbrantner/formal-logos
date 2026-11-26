module

public import Mathlib.Data.Set.Finite.Lemmas
public import TruthCore.Latin.Aquinas.DeEnte.BoundedIdentityExercise
public import TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting.Solution

@[expose] public section

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
  have increasing {e f : E} (path : Relation.TransGen C e f) : clock e < clock f := by
    induction path with
    | single edge => exact forward _ _ edge
    | tail _ edge ih => exact lt_trans ih (forward _ _ edge)
  intro r actual identity
  obtain ⟨e, he⟩ := inhabited r actual identity
  obtain ⟨lower, hLower⟩ := bounded r actual identity
  let Fibre := { d : E // bearer d = r }
  let time (d : Fibre) := clock d.val
  let interval : Set Fibre := { d | time d ∈ Set.Icc lower (clock e) }
  have finite : interval.Finite :=
    finite_operations_in_compact_interval time (locallyFinite r actual identity) lower (clock e)
  have nonempty : interval.Nonempty := ⟨⟨e, he⟩, hLower e he, le_rfl⟩
  obtain ⟨f, hf, least⟩ := interval.exists_min_image time finite nonempty
  refine ⟨f.val, f.property, ?_⟩
  intro d hd path
  have strictlyEarlier := increasing path
  have inInterval : (⟨d, hd⟩ : Fibre) ∈ interval :=
    ⟨hLower d hd, le_trans strictlyEarlier.le hf.2⟩
  exact (not_lt_of_ge (least ⟨d, hd⟩ inInterval)) strictlyEarlier

/-- The same alternating exercise graph works both with a locally finite
unbounded clock and with a bounded clock whose indices accumulate. -/
theorem boundedIdentityExerciseControls : BoundedIdentityExerciseControls := by
  obtain ⟨identityExactly, _, _, ⟨_, _, lifts, _, someExercise⟩⟩ := exerciseLiftingControls
  have inhabited : ActualIdentityExerciseFibresInhabited
      exerciseFeedbackProfile alternatingExerciseBearer := by
    intro r actual identity
    obtain rfl := (identityExactly r).mp ⟨actual, identity⟩
    exact someExercise
  have evenBearer (n : ℕ) : alternatingExerciseBearer (2 * n) = true :=
    decide_eq_true (Nat.mul_mod_right 2 n)
  have noMinimal : ¬ ActualIdentityHasMinimalExercise
      exerciseFeedbackProfile alternatingExerciseBearer unboundedExerciseSupply := by
    intro minimal
    obtain ⟨n, belongs, first⟩ := minimal true trivial rfl
    have sameBearer : alternatingExerciseBearer (n + 2) = true := by
      simpa [alternatingExerciseBearer, Nat.add_mod_right] using belongs
    have firstEdge : unboundedExerciseSupply (n + 2) (n + 1) := rfl
    have secondEdge : unboundedExerciseSupply (n + 1) n := rfl
    exact first (n + 2) sameBearer ((Relation.TransGen.single firstEdge).tail secondEdge)
  have discreteForward : StrictForward backwardClock unboundedExerciseSupply := by
    intro e f edge
    rw [show e = f + 1 from edge]
    exact (locallyFiniteTimes_with_infiniteCausalAncestry.2.1 f).1
  have discreteLocal : ActualIdentityExerciseTimesLocallyFinite
      exerciseFeedbackProfile alternatingExerciseBearer backwardClock := by
    intro r _ _
    exact LocallyFinite.comp_injective (f := fun n : ℕ => ({backwardClock n} : Set ℝ))
      backwardClock_locallyFinite (Subtype.val_injective (p := fun e => alternatingExerciseBearer e = r))
  have discreteUnbounded : ¬ ActualIdentityExerciseTimesBoundedBelow
      exerciseFeedbackProfile alternatingExerciseBearer backwardClock := by
    intro bounded
    obtain ⟨lower, hLower⟩ := bounded true trivial rfl
    obtain ⟨n, hn⟩ := exists_nat_gt (-lower)
    have grow : (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * n by omega)
    have ht := hLower (2 * n) (evenBearer n)
    dsimp [backwardClock] at ht
    linarith
  have bounds : ∀ n, 0 < eventTime n ∧ eventTime n ≤ 1 :=
    TruthCore.Results.Causality.TemporalEventControls.controls.2.1
  have zenoForward : StrictForward eventTime unboundedExerciseSupply := by
    intro e f edge
    rw [show e = f + 1 from edge]
    have scale (n : ℕ) : eventTime n = (1 / 2 : ℝ) ^ n := by
      simp [eventTime, zenoStageTime]
    have pos := (bounds f).1
    rw [scale, scale, pow_succ]
    rw [scale] at pos
    linarith
  have zenoBounded : ActualIdentityExerciseTimesBoundedBelow
      exerciseFeedbackProfile alternatingExerciseBearer eventTime :=
    fun _ _ _ => ⟨0, fun e _ => (bounds e).1.le⟩
  have zenoNonlocal : ¬ ActualIdentityExerciseTimesLocallyFinite
      exerciseFeedbackProfile alternatingExerciseBearer eventTime := by
    intro locallyFinite
    let Fibre := { e : ℕ // alternatingExerciseBearer e = true }
    let time (e : Fibre) := eventTime e.val
    have finite : (Set.univ : Set Fibre).Finite :=
      finite_operations_of_bounded time (locallyFinite true trivial rfl) 0 1
        (fun e => ⟨(bounds e.val).1.le, (bounds e.val).2⟩)
    let embed (n : ℕ) : Fibre := ⟨2 * n, evenBearer n⟩
    have injective : Function.Injective embed := by
      intro n m h
      have equal : 2 * n = 2 * m := congrArg Subtype.val h
      omega
    exact (Set.infinite_of_injective_forall_mem injective
      (fun n => Set.mem_univ (embed n))) finite
  exact ⟨inhabited, lifts, noMinimal, ⟨discreteForward, discreteLocal, discreteUnbounded⟩,
    ⟨zenoForward, zenoBounded, zenoNonlocal⟩⟩

end TruthCore.Results.Aquinas.DeEnte.BoundedIdentityExercise
