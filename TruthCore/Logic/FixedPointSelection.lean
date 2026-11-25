module

/-!
# Fixed-point selection (#1926)

Purely structural equality and uniqueness lemmas for the symmetry proofs in
scientific induction, personal identity, spatial translation and temporal
relocation. No invertibility, group structure, classical choice or
philosophical interpretation is required. The caller supplies the equality
of its selected inputs and the applicable transformation law, or the
invariant condition and its unique solution.

This module has no imports beyond the Lean prelude. It does not identify
the domain-specific notions of evidence, identity or explanation.
-/

@[expose] public section

namespace TruthCore.Logic.FixedPointSelection

universe u v

/-- Equal inputs and the specified output transformation force a fixed output.
Only the selected pair of inputs is required to agree. -/
theorem fixed_output {E : Sort u} {H : Sort v}
    (select : E → H) (move : H → H) {e e' : E}
    (same : e' = e) (commutes : select e' = move (select e)) :
    move (select e) = select e :=
  commutes.symm.trans (congrArg select same)

/-- If a predicate is closed under a transformation, its unique member is
fixed by that transformation. Existence and uniqueness remain explicit. -/
theorem unique_closed_fixed {H : Sort u} (P : H → Prop) (move : H → H)
    (h : H) (member : P h) (unique : ∀ x, P x → x = h)
    (closed : ∀ x, P x → P (move x)) : move h = h :=
  unique (move h) (closed h member)

end TruthCore.Logic.FixedPointSelection
