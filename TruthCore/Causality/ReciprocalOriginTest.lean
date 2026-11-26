module

public import TruthCore.Causality.OriginExerciseBridge
public import TruthCore.Results.Causality.ExistentialPriorityOrder.Solution

/-! Matched controls for the diagonal origin bridge. The two exercises always
produce each other's bearers. Only the attribution of a self-origin changes. -/

@[expose] public section

namespace TruthCore.Causality.ReciprocalOriginTest

open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.OriginExerciseBridge
open TruthCore.Causality.ExistentialPriorityOrder
open TruthCore.Results.Causality.ExistentialPriorityOrder

/-- Denying the diagonal bridge requires a particular origin edge whose bearer
has no occurring, self-producing exercise. Classical only in extracting a witness. -/
theorem deniedDiagonalIff {B R E : Type} (F : CauseFrame B R)
    (occurs : E → Prop) (bearer : E → B) (produces : E → B → Prop) :
    ¬ OriginHasProductiveSelfExercise F occurs bearer produces ↔
      ∃ x, F.CausesOrigin x x ∧ ∀ a, occurs a → bearer a = x → ¬ produces a x := by
  classical
  simp [OriginHasProductiveSelfExercise, not_forall]

/-- Add just one diagonal attribution when requested. -/
def frame (diagonal : Prop) : CauseFrame Bool Unit :=
  { otherOnlyFrame with CausesOrigin := fun c x => c ≠ x ∨ (diagonal ∧ c = false ∧ x = false) }

/-- First conjunct: in both choices each bearer has a distinct `CausesOrigin`
predecessor (an originator, not an exercise witness). Separately, by direct
calculation in the fixed exercise profile, exercise `!x` occurs, is borne by
`!x` and produces `x`, so each bearer also has a distinct productive supplier;
that existential is not a conjunct of this theorem. Second conjunct: the
required edges form the same finite cycle. Even the universal exercise bridge
holds without the added diagonal edge; adding it changes the verdict on the
weak bridge as well. -/
theorem matchedOrigins (diagonal : Prop) :
    (∀ x : Bool, ∃ a : Bool, a ≠ x ∧ (frame diagonal).CausesOrigin a x) ∧
    ¬ RequiredEdgesAcyclic (fun _ : Bool => True) id (· ≠ ·) ∧
    (OriginHasProductiveExercise (frame diagonal) (fun _ : Bool => True) id (· ≠ ·) ↔
      ¬ diagonal) ∧
    (OriginHasProductiveSelfExercise (frame diagonal) (fun _ : Bool => True) id (· ≠ ·) ↔
      ¬ diagonal) := by
  have rejects (weak : OriginHasProductiveSelfExercise (frame diagonal)
      (fun _ : Bool => True) id (· ≠ ·)) : ¬ diagonal := by
    intro h
    obtain ⟨a, _, ha, hne⟩ := weak false (Or.inr ⟨h, rfl, rfl⟩)
    exact hne ha
  refine ⟨?_, fun acyclic => reciprocalControl.2
    ((exactExtension Bool Bool _ id (· ≠ ·)).mpr acyclic), ?_, ?_⟩
  · intro x
    have distinct : (!x) ≠ x := by cases x <;> decide
    exact ⟨!x, distinct, Or.inl distinct⟩
  · constructor
    · exact fun all => rejects (fun x hx => all x x hx)
    · intro absent c x edge
      exact ⟨c, trivial, rfl, edge.elim id (fun h => (absent h.1).elim)⟩
  · constructor
    · exact rejects
    · intro absent x edge
      exact (edge.elim (fun ne => ne rfl) (fun h => absent h.1)).elim

open TruthCore.Causality.ExistentialSelfActualization

/-- On the very same reciprocal production data, each of the four laws can
be the only one to fail. This locates the choice faced by a loop account. -/
theorem priorityAlternatives :
    let B := BearerPrior (fun _ : Bool => True) (id : Bool → Bool)
    let P := ProductPrior (fun _ : Bool => True) (· ≠ ·)
    let I := @IrreflexivePriority Bool Bool
    let T := @TransitivePriority Bool Bool
    (∃ r, ¬ B r ∧ P r ∧ I r ∧ T r) ∧
    (∃ r, B r ∧ ¬ P r ∧ I r ∧ T r) ∧
    (∃ r, B r ∧ P r ∧ ¬ I r ∧ T r) ∧
    (∃ r, B r ∧ P r ∧ I r ∧ ¬ T r) := by
  let bearerOnly : Sum Bool Bool → Sum Bool Bool → Prop
    | .inl b, .inr a => a = b
    | _, _ => False
  let productOnly : Sum Bool Bool → Sum Bool Bool → Prop
    | .inr a, .inl b => a ≠ b
    | _, _ => False
  refine ⟨⟨productOnly, ?_⟩, ⟨bearerOnly, ?_⟩, ⟨fun _ _ => True, ?_⟩,
    ⟨fun x y => bearerOnly x y ∨ productOnly x y, ?_⟩⟩
  all_goals
    unfold BearerPrior ProductPrior IrreflexivePriority TransitivePriority
      TruthCore.Latin.Aquinas.SummaTheologiae.NothingPriorToItselfReading
      TruthCore.Alternatives.ActPotencyRegress.SimplePriorityTransitiveReading
    simp [Sum.forall, Bool.forall_bool, bearerOnly, productOnly]

end TruthCore.Causality.ReciprocalOriginTest
