module

public import TruthCore.Logic.AtomismIndependence

/-! Finite input repertoires and the records they can change. The three
coordinates and their parity predicate come from #1088. The moves below
specify which inputs can be composed on one fixed Boolean background. Their
availability in a physical or metaphysical account is a separate premise. -/

@[expose] public section

namespace TruthCore.Explanation.PairedInterventions
open TruthCore.Logic.AtomismIndependence (Triple Index coordinate Parity)

/-- The two edge inputs on a path each toggle both endpoints. -/
def paired (s : Triple) (left right : Bool) : Triple :=
  (s.1.xor left, (s.2.1.xor left).xor right, s.2.2.xor right)

/-- Any finite succession of independently chosen edge inputs is allowed. -/
inductive Reachable (start : Triple) : Triple → Prop where
  | stay : Reachable start start
  | step {s : Triple} : Reachable start s → (left right : Bool) →
      Reachable start (paired s left right)

/-- One optional extra input acts on the first endpoint alone. -/
def endpoint (s : Triple) (single : Bool) : Triple :=
  (s.1.xor single, s.2.1, s.2.2)

/-- Exact range from every start, including realizability of every assignment
to any two distinct coordinates, an excluded state, and the full range when
the extra endpoint input may be used once before the edge inputs. -/
def InputRange : Prop :=
  (∀ s t, Reachable s t ↔ (Parity s ↔ Parity t)) ∧
  (∀ s (i j : Index), i ≠ j → ∀ x y : Bool,
    ∃ t, Reachable s t ∧ coordinate t i = x ∧ coordinate t j = y) ∧
  (∀ s, ¬ Reachable s (endpoint s true)) ∧
  (∀ s t, ∃ single, Reachable (endpoint s single) t)

/-- The reported change between two readings equals the actual change
exactly when the readings have the same XOR offset. -/
def OffsetAccuracy : Prop :=
  ∀ p q a b : Bool, (p.xor a).xor (q.xor b) = p.xor q ↔ a = b

end TruthCore.Explanation.PairedInterventions
