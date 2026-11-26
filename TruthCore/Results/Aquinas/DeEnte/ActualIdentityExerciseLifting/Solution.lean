module

public import TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
public import TruthCore.Results.Causality.TemporalActualization.Controls.Solution

@[expose] public section

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
  induction path generalizing f with
  | single edge =>
    obtain ⟨e, atSupplier, previous⟩ := lift _ _ edge f target
    exact ⟨e, atSupplier, .single previous⟩
  | tail _ edge ih =>
    obtain ⟨e, atSupplier, previous⟩ := lift _ _ edge f target
    obtain ⟨start, atStart, lifted⟩ := ih e atSupplier
    exact ⟨start, atStart, lifted.tail previous⟩

/-- A bearer return would lift backwards from every exercise in its fibre.
An inhabited finite identity fibre has a minimal exercise under acyclic
nonempty finite exercise reachability, contradicting that lifted return. -/
theorem actualIdentityAncestryAcyclicOfExerciseLifting {B P R E : Type}
    (p : Profile B P R) (bearer : E → B) (C : E → E → Prop)
    (acyclic : EventAcyclic C)
    (lift : BackwardActualEsseExerciseLifting p bearer C)
    (fibres : ActualIdentityExerciseFibresFiniteNonempty p bearer) :
    ActualIdentityAncestryAcyclic p := by
  intro r actual identity loop
  let Fibre : Set E := { e | bearer e = r }
  let upstream (e f : Fibre) := Relation.TransGen C e.val f.val
  obtain ⟨finite, e, atIdentity⟩ := fibres r actual identity
  let : Finite Fibre := finite
  let : IsTrans Fibre upstream := ⟨fun _ _ _ first second => first.trans second⟩
  let : Std.Irrefl upstream := ⟨fun e => acyclic e.val⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl upstream
  obtain ⟨f, _, minimal⟩ := wf.has_min Set.univ ⟨⟨e, atIdentity⟩, Set.mem_univ _⟩
  obtain ⟨previous, belongs, path⟩ := liftActualEssePath lift loop f.val f.property
  exact minimal ⟨previous, belongs⟩ (Set.mem_univ _) path

private theorem exerciseFeedbackEdge (c x : Bool) :
    ActualEsseCause exerciseFeedbackProfile c x ↔ c ≠ x :=
  ⟨fun h => h.1, fun h => ⟨h, trivial, trivial, h⟩⟩

private theorem alternatingSuccessor (n : ℕ) :
    alternatingExerciseBearer (n + 1) ≠ alternatingExerciseBearer n := by
  unfold alternatingExerciseBearer
  have next := (Nat.mod_add_mod n 2 1).symm
  rcases Nat.mod_two_eq_zero_or_one n with even | odd
  · rw [even] at next
    rw [next, even]
    decide
  · rw [odd] at next
    rw [next, odd]
    decide

/-- The existing finite feedback example fails lifting. An unbounded
alternating chain still projects to the same bearer return even when
every eligible exercise has the required supplier exercise. -/
theorem exerciseLiftingControls : ExerciseLiftingControls := by
  have feedbackIncreasing {e f : Fin 3} (path : Relation.TransGen feedbackC e f) :
      e.val < f.val := by
    induction path with
    | single edge =>
      exact Nat.lt_of_succ_le (Nat.le_of_eq edge)
    | tail _ edge ih =>
      exact Nat.lt_trans ih (Nat.lt_of_succ_le (Nat.le_of_eq edge))
  have acyclicFeedback : EventAcyclic feedbackC :=
    fun e path => Nat.lt_irrefl e.val (feedbackIncreasing path)
  have chainDecreasing {e f : ℕ} (path : Relation.TransGen unboundedExerciseSupply e f) :
      f < e := by
    induction path with
    | single edge =>
      change _ = _ + 1 at edge
      exact Nat.lt_of_succ_le (Nat.le_of_eq edge.symm)
    | tail _ edge ih =>
      change _ = _ + 1 at edge
      exact Nat.lt_trans (Nat.lt_of_succ_le (Nat.le_of_eq edge.symm)) ih
  have acyclicChain : EventAcyclic unboundedExerciseSupply :=
    fun e path => Nat.lt_irrefl e (chainDecreasing path)
  have identityExactly (r : Bool) :
      exerciseFeedbackProfile.InAct r exerciseFeedbackProfile.esse ∧
        exerciseFeedbackProfile.esseOf r = exerciseFeedbackProfile.essenceOf r ↔ r = true := by
    change (True ∧ Bool.not r = false) ↔ r = true
    cases r <;> decide
  have returns : ¬ ActualIdentityAncestryAcyclic exerciseFeedbackProfile := by
    intro acyclic
    exact acyclic true trivial rfl
      ((Relation.TransGen.single ((exerciseFeedbackEdge true false).2 (by decide))).tail
        ((exerciseFeedbackEdge false true).2 (by decide)))
  have finiteProjection (c x : Bool) :
      ActualEsseCause exerciseFeedbackProfile c x ↔ BeingEdge feedbackBearer feedbackC c x := by
    constructor
    · intro edge
      have different := edge.1
      cases c <;> cases x
      · exact (different rfl).elim
      · exact ⟨0, 1, rfl, rfl, rfl⟩
      · exact ⟨1, 2, rfl, rfl, rfl⟩
      · exact (different rfl).elim
    · rintro ⟨e, f, rfl, rfl, edge⟩
      apply (exerciseFeedbackEdge _ _).2
      have distinctBearers : ∀ e f : Fin 3, e.val + 1 = f.val →
          decide (e.val = 1) ≠ decide (f.val = 1) := by decide
      exact distinctBearers e f edge
  have finiteFibres : ActualIdentityExerciseFibresFiniteNonempty
      exerciseFeedbackProfile feedbackBearer := by
    intro r active identity
    have selected := (identityExactly r).mp ⟨active, identity⟩
    subst r
    exact ⟨Set.toFinite _, ⟨1, rfl⟩⟩
  have finiteNoLift : ¬ BackwardActualEsseExerciseLifting
      exerciseFeedbackProfile feedbackBearer feedbackC := by
    intro lift
    obtain ⟨e, _, edge⟩ := lift true false ((exerciseFeedbackEdge true false).2 (by decide)) 0 rfl
    exact Nat.succ_ne_zero e.val edge
  have infiniteLift : BackwardActualEsseExerciseLifting exerciseFeedbackProfile
      alternatingExerciseBearer unboundedExerciseSupply := by
    intro c x edge f target
    refine ⟨f + 1, ?_, rfl⟩
    have opposite := alternatingSuccessor f
    rw [target] at opposite
    have uniqueOther : ∀ c x e : Bool, c ≠ x → e ≠ x → e = c := by decide
    exact uniqueOther c x (alternatingExerciseBearer (f + 1)) edge.1 opposite
  have infiniteProjection (c x : Bool) :
      ActualEsseCause exerciseFeedbackProfile c x ↔
        BeingEdge alternatingExerciseBearer unboundedExerciseSupply c x := by
    constructor
    · intro edge
      let f := if x then 0 else 1
      have target : alternatingExerciseBearer f = x := by cases x <;> rfl
      obtain ⟨e, supplier, previous⟩ := infiniteLift c x edge f target
      exact ⟨e, f, supplier, target, previous⟩
    · rintro ⟨e, f, rfl, rfl, edge⟩
      apply (exerciseFeedbackEdge _ _).2
      change e = f + 1 at edge
      rw [edge]
      exact alternatingSuccessor f
  have infiniteFibre : { e | alternatingExerciseBearer e = true }.Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
    · intro n m equal
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) equal
    · intro n
      exact decide_eq_true (Nat.mul_mod_right 2 n)
  exact ⟨identityExactly, returns, ⟨acyclicFeedback, finiteProjection, finiteFibres, finiteNoLift⟩,
    ⟨acyclicChain, infiniteProjection, infiniteLift, infiniteFibre, ⟨0, rfl⟩⟩⟩

end TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting
