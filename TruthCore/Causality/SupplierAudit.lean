module

public import Mathlib.Data.Set.Finite.Lemmas

/-! Finite observations of supplier chains and a sufficient condition on a closed finite roster. -/

@[expose] public section

namespace TruthCore.Causality.SupplierAudit

def endless (y x : Nat) := y = x + 1

def sourced (n y x : Nat) := (x < n ∧ y = x + 1) ∨ (n < x ∧ y = n)

theorem sameLists (n x y : Nat) (seen : x < n) :
    sourced n y x ↔ endless y x := by unfold sourced endless; omega

theorem endlessBorrower (x : Nat) : ∃ y, endless y x := ⟨x + 1, rfl⟩

theorem oneRoot (n x : Nat) : (∀ y, ¬ sourced n y x) ↔ x = n := by
  constructor
  · intro h
    by_cases lt : x < n
    · exact False.elim (h (x + 1) (Or.inl ⟨lt, rfl⟩))
    · by_contra ne
      exact h n (Or.inr ⟨by omega, rfl⟩)
  · rintro rfl y
    unfold sourced
    omega

-- Integer labels permit infinite descent on the full roster.
theorem finiteAudit {B : Type} (S : Set B) (r : B → B → Prop) (level : B → Int)
    (finite : S.Finite) (present : S.Nonempty)
    (closed : ∀ x ∈ S, ∀ y, r y x → y ∈ S)
    (drop : ∀ x ∈ S, ∀ y, r y x → level y < level x) :
    ∃ x ∈ S, ∀ y, ¬ r y x := by
  obtain ⟨x, hx, least⟩ := S.exists_min_image level finite present
  exact ⟨x, hx, fun y hy => (not_lt_of_ge (least y (closed x hx y hy))) (drop x hx y hy)⟩

end TruthCore.Causality.SupplierAudit
