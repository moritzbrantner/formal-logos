module

@[expose] public section

/-!
Inverting an argument: which re-rootings are valid (#1674, phase 2).

`truth tree X` re-roots the argument graph at any statement. Re-rooting turns
an argument around, and only some inversions are valid. Owner clarification
(2026-11-16): from a syllogism `A ∨ B ⇒ C`, making `A` the root should give an
argument `C ∧ ¬B ⇒ A`. That inverse is valid only with an exhaustiveness
premise. This module states the boundary.

* **Contraposition is always valid.** From an argument `P₁, …, Pₙ ⊢ C`,
  `¬C` together with the other premises gives `¬Pᵢ`
  (`contrapositive`, `contrapositive_at`), and for a disjunctive antecedent
  `¬C` gives `¬A ∧ ¬B` (`contrapositive_or`). These are refutation edges
  toward the new root; `truth tree` emits them as `contrapositive` edges.
* **The abductive inverse needs exhaustiveness.** With `C → A ∨ B` ("these
  are the only routes to `C`") as an explicit premise, `C ∧ ¬B` gives `A` by
  disjunctive syllogism (`inverse_of_exhaustive`), and in general `C` with
  every other alternative refuted gives the remaining one
  (`inverse_of_exhaustive_at`, `inverse_premise_of_exhaustive_at`).
  `truth tree` emits these as `inverse_conditional` edges, listing the
  exhaustiveness premise.
* **The unconditioned inverse is invalid.** `(A ∨ B) → C` does not give
  `C ∧ ¬B → A`: take `A = B = False` and `C = True`
  (`unconditioned_inverse_invalid`, and the Boolean model checked by
  `decide` in `unconditioned_inverse_bool_countermodel`). `truth tree` never
  emits it.

Every proof here is constructive and uses no axiom: no excluded middle and
no `Classical.choice`. The case split on `Fin n` uses its decidable equality.

An inverted edge instantiates one of these lemmas at an existing result
theorem. That is a logical transformation of the result, not new philosophical
structure, so a materialized inversion is recorded as an `instantiation`
transcription (AGENTS.md invariant 16) and closes its conclusion only by the
transcription rule: when every one of its premises is already closed.
-/

namespace TruthCore.Logic.Inversion

/-- Contraposition of one premise: from `P → C` and `¬C`, `¬P`. Applied to
a result theorem `T : P₁ → … → Pₙ → C` with every premise but `Pᵢ` supplied,
it gives `¬C → ¬Pᵢ`. -/
theorem contrapositive {P C : Prop} (h : P → C) (hNotC : ¬ C) : ¬ P :=
  fun hP => hNotC (h hP)

/-- Contraposition at premise `i` of an argument whose premises are the family
`P : Fin n → Prop`: `¬C` and every other premise give `¬Pᵢ`. -/
theorem contrapositive_at {n : Nat} {P : Fin n → Prop} {C : Prop}
    (h : (∀ j, P j) → C) (i : Fin n) (hNotC : ¬ C)
    (hOthers : ∀ j, j ≠ i → P j) : ¬ P i := fun hPi =>
  hNotC (h fun j => if hj : j = i then hj ▸ hPi else hOthers j hj)

/-- Contraposition for conjunctive premises: `(A ∧ B) → C` and `¬C ∧ B`
give `¬A`. -/
theorem contrapositive_and {A B C : Prop} (h : A ∧ B → C) (hNotC : ¬ C) (hB : B) :
    ¬ A :=
  fun hA => hNotC (h ⟨hA, hB⟩)

/-- Contraposition for a disjunctive antecedent: `(A ∨ B) → C` and `¬C` give
`¬A ∧ ¬B`. -/
theorem contrapositive_or {A B C : Prop} (h : A ∨ B → C) (hNotC : ¬ C) :
    ¬ A ∧ ¬ B :=
  ⟨fun hA => hNotC (h (Or.inl hA)), fun hB => hNotC (h (Or.inr hB))⟩

/-- The exhaustiveness-conditioned inverse for two alternatives: given that
`C` holds only through `A` or `B` (`C → A ∨ B`), `C` and `¬B` give `A`. -/
theorem inverse_of_exhaustive {A B C : Prop} (hExhaustive : C → A ∨ B) (hC : C)
    (hNotB : ¬ B) : A :=
  (hExhaustive hC).elim id fun hB => absurd hB hNotB

/-- The exhaustiveness-conditioned inverse for `n` alternatives `B : Fin n →
Prop`: if `C` holds only through one of them, `C` and the failure of every
alternative but `i` give alternative `i`. -/
theorem inverse_of_exhaustive_at {n : Nat} {B : Fin n → Prop} {C : Prop}
    (hExhaustive : C → ∃ k, B k) (hC : C) (i : Fin n)
    (hOthers : ∀ k, k ≠ i → ¬ B k) : B i :=
  match hExhaustive hC with
  | ⟨k, hk⟩ => if h : k = i then h ▸ hk else absurd hk (hOthers k h)

/-- The inverse edge to one premise `A` of alternative `i`: the alternative's
premise bundle `B i` gives `A`, so `C`, exhaustiveness and the failure of the
other alternatives give `A`. -/
theorem inverse_premise_of_exhaustive_at {n : Nat} {B : Fin n → Prop} {A C : Prop}
    (hExhaustive : C → ∃ k, B k) (hC : C) (i : Fin n)
    (hOthers : ∀ k, k ≠ i → ¬ B k) (hPremise : B i → A) : A :=
  hPremise (inverse_of_exhaustive_at hExhaustive hC i hOthers)

/-- The unconditioned inverse is invalid: `(A ∨ B) → C` does not give
`C ∧ ¬B → A`. Countermodel `A = B = False`, `C = True`. -/
theorem unconditioned_inverse_invalid :
    ¬ ∀ A B C : Prop, (A ∨ B → C) → C ∧ ¬ B → A :=
  fun h => h False False True (fun _ => trivial) ⟨trivial, id⟩

/-- The same countermodel over truth values, found and checked by `decide`:
some valuation makes `(a ∨ b) → c` and `c ∧ ¬b` true and `a` false. -/
theorem unconditioned_inverse_bool_countermodel :
    ∃ a b c : Bool, (!(a || b) || c) = true ∧ (c && !b) = true ∧ a = false := by
  decide

/-- The exhaustiveness premise is what the countermodel lacks: there,
`C → A ∨ B` fails. -/
theorem unconditioned_inverse_countermodel_not_exhaustive :
    ¬ (True → False ∨ False) :=
  fun h => (h trivial).elim id id

/-! Tests: the lemmas at the shapes `truth tree` uses. -/

/-- A result theorem is curried, `P₁ → P₂ → C`; supplying every premise but
one gives the `P → C` that `contrapositive` takes. -/
example (P₁ P₂ C : Prop) (T : P₁ → P₂ → C) (hNotC : ¬ C) (h₂ : P₂) : ¬ P₁ :=
  contrapositive (fun h₁ => T h₁ h₂) hNotC

/-- Three alternatives for `C`, the second and third failing: the first one's
premise `A` follows, given exhaustiveness. -/
example (A Q C : Prop) (B : Fin 3 → Prop) (hB : B = fun k => if k = 0 then A ∧ Q else False)
    (hExhaustive : C → ∃ k, B k) (hC : C) : A :=
  inverse_premise_of_exhaustive_at hExhaustive hC 0
    (fun k hk => by subst hB; simp [hk])
    (fun h => by subst hB; exact h.1)

end TruthCore.Logic.Inversion
