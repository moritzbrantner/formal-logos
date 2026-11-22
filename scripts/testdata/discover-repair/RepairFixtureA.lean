/-! Fixtures for `scripts/test_discover_repair.py` (#1833): one module whose
declarations share binder names by the same-module convention. Imports only
Init. -/
namespace TruthCore.RepairFixtureA

/-- Target: every `P` is `Q`. -/
def Target (B : Type) (P Q : B → Prop) : Prop := ∀ x, P x → Q x

/-- Every `P` is `R`. -/
def PtoR (B : Type) (P R : B → Prop) : Prop := ∀ x, P x → R x

/-- Every `R` is `Q`. -/
def RtoQ (B : Type) (R Q : B → Prop) : Prop := ∀ x, R x → Q x

/-- `Q` is hereditary along successors and holds at zero (an induction
premise: Duper does not do induction, so the lemma `QEverywhere` is needed). -/
def QHereditary (Q : Nat → Prop) : Prop := Q 0 ∧ ∀ n, Q n → Q (n + 1)

/-- `Q` holds everywhere: proved from `QHereditary` by induction (the verified
lemma of the fixture corpus). -/
def QEverywhere (Q : Nat → Prop) : Prop := ∀ n, Q n

theorem qEverywhere (Q : Nat → Prop) (h : QHereditary Q) : QEverywhere Q := by
  intro n; induction n with
  | zero => exact h.1
  | succ n ih => exact h.2 n ih

/-- The target the lemma unblocks: `Q` holds at every number and its successor. -/
def QAtPairs (Q : Nat → Prop) : Prop := ∀ n, Q n ∧ Q (n + 1)

/-- Every element has `P`. -/
def AllP (B : Type) (P : B → Prop) : Prop := ∀ x, P x

/-- The literal negation of `AllP`. -/
def NotAllP (B : Type) (P : B → Prop) : Prop := ¬ AllP B P

/-- A chain of twelve implications, for the budget fixture. -/
def Chain (B : Type) (P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 : B → Prop) : Prop :=
  (∀ x, P0 x → P1 x) ∧ (∀ x, P1 x → P2 x) ∧ (∀ x, P2 x → P3 x) ∧ (∀ x, P3 x → P4 x) ∧
  (∀ x, P4 x → P5 x) ∧ (∀ x, P5 x → P6 x) ∧ (∀ x, P6 x → P7 x) ∧ (∀ x, P7 x → P8 x) ∧
  (∀ x, P8 x → P9 x) ∧ (∀ x, P9 x → P10 x) ∧ (∀ x, P10 x → P11 x) ∧ (∀ x, P11 x → P12 x)

/-- The chain's end-to-end consequence. -/
def ChainEnds (B : Type) (P0 P12 : B → Prop) : Prop := ∀ x, P0 x → P12 x

end TruthCore.RepairFixtureA
