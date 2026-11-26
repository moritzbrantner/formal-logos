module

public import TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise
public import TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting.Solution
public import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.FirstIdentityExercise

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
open TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
open TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting (liftActualEssePath)
open TruthCore.Causality.TemporalActualization (EventAcyclic feedbackBearer feedbackC)

variable {B P R E : Type}

/-- Lift a putative return into the chosen exercise. Its predecessor would
belong to the same bearer, contrary to the choice of exercise. -/
theorem noReturnOfMinimalExercise (p : Profile B P R) (bearer : E → B) (C : E → E → Prop)
    (lift : BackwardActualEsseExerciseLifting p bearer C)
    (minimal : ActualIdentityHasMinimalExercise p bearer C) : ActualIdentityAncestryAcyclic p := by
  intro r hr hi loop
  obtain ⟨f, hf, first⟩ := minimal r hr hi
  obtain ⟨e, he, path⟩ := liftActualEssePath lift loop f hf
  exact first e he path

/-- With faithful edge projection, absence of bearer returns makes every
represented exercise of that identity bearer minimal among its own exercises. -/
theorem minimalExerciseOfNoReturn (p : Profile B P R) (bearer : E → B) (C : E → E → Prop)
    (noReturn : ActualIdentityAncestryAcyclic p)
    (inhabited : ∀ r, p.InAct r p.esse → p.esseOf r = p.essenceOf r → ∃ f, bearer f = r)
    (projects : ∀ e f, C e f → ActualEsseCause p (bearer e) (bearer f)) :
    ActualIdentityHasMinimalExercise p bearer C := by
  intro r hr hi
  obtain ⟨f, hf⟩ := inhabited r hr hi
  refine ⟨f, hf, ?_⟩
  intro e he path
  have mapped : Relation.TransGen (ActualEsseCause p) (bearer e) (bearer f) := by
    clear hf
    induction path with
    | single edge => exact .single (projects _ _ edge)
    | tail _ edge ih => exact ih.tail (projects _ _ edge)
  apply noReturn r hr hi
  simpa only [he, hf] using mapped

/-- Reuse the rooted two-dependent cycle. Give every bearer infinitely many
exercise tokens. Supply acts can cycle away from the identity bearer; that
bearer's own exercises have no predecessors among its own exercises. -/
theorem minimalWithInfiniteFibreAndOtherCycle :
    ∃ (p : Profile (Option Bool) Bool Unit) (C : (Option Bool × Nat) → (Option Bool × Nat) → Prop),
      CommonEsseIsEssenceSource p ∧ ActualIdentityHasMinimalExercise p Prod.fst C ∧
      BackwardActualEsseExerciseLifting p Prod.fst C ∧
      (∃ r, p.InAct r p.esse ∧ p.esseOf r = p.essenceOf r ∧
        {e : Option Bool × Nat | e.1 = r}.Infinite) ∧ ¬ EventAcyclic C := by
  obtain ⟨p, _, _, one, _, source, xy, yx⟩ :=
    TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Control.rootedCycle
  let C (e f : Option Bool × Nat) := ActualEsseCause p e.1 f.1 ∧ e.2 = f.2
  have sourceWitness := source
  obtain ⟨r, hr, hi, first, _⟩ := sourceWitness
  refine ⟨p, C, source, ?_, ?_, ?_, ?_⟩
  · intro x hx hxi
    obtain rfl := one x r hx hr hxi hi
    refine ⟨(x, 0), rfl, ?_⟩
    intro d _ path
    rcases path with last | ⟨_, last⟩ <;> exact first _ last.1
  · intro c x edge f hf
    exact ⟨(c, f.2), rfl, hf ▸ edge, rfl⟩
  · refine ⟨r, hr, hi, Set.infinite_of_injective_forall_mem (f := fun n : Nat => (r, n)) ?_ ?_⟩
    · exact fun _ _ eq => congrArg Prod.snd eq
    · exact fun _ => rfl
  · intro acyclic
    have a : C (some false, 0) (some true, 0) := ⟨xy, rfl⟩
    have b : C (some true, 0) (some false, 0) := ⟨yx, rfl⟩
    exact acyclic _ ((Relation.TransGen.single a).tail b)

/-- Checking every incoming supplier at the identity bearer's own exercises
still misses a break in the return at an intermediate bearer. -/
theorem liftingOnlyAtIdentityAllowsReturn :
    ActualIdentityHasMinimalExercise exerciseFeedbackProfile feedbackBearer feedbackC ∧
      (∀ c x, exerciseFeedbackProfile.InAct x exerciseFeedbackProfile.esse →
        exerciseFeedbackProfile.esseOf x = exerciseFeedbackProfile.essenceOf x →
        ActualEsseCause exerciseFeedbackProfile c x →
        ∀ f, feedbackBearer f = x → ∃ e, feedbackBearer e = c ∧ feedbackC e f) ∧
      ¬ ActualIdentityAncestryAcyclic exerciseFeedbackProfile := by
  have controls := TruthCore.Results.Aquinas.DeEnte.ActualIdentityExerciseLifting.exerciseLiftingControls
  have onlyOne : ∀ f : Fin 3, feedbackBearer f = true → f = 1 := by decide
  refine ⟨?_, ?_, controls.2.1⟩
  · intro x hx hi
    obtain rfl := (controls.1 x).mp ⟨hx, hi⟩
    refine ⟨1, by decide, ?_⟩
    intro e he path
    obtain rfl := onlyOne e he
    exact controls.2.2.1.1 1 path
  · intro c x hx hi edge f hf
    obtain rfl := (controls.1 x).mp ⟨hx, hi⟩
    obtain rfl := onlyOne f hf
    cases c with
    | false => exact ⟨0, by decide, rfl⟩
    | true => exact (edge.1 rfl).elim

end TruthCore.Results.Aquinas.DeEnte.FirstIdentityExercise
