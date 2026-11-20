import Duper
/-!
Axiom audit of Duper-reconstructed proofs (docs/axiom-policy.md, owner
decision 2026-11-19). CI elaborates this file with `lake env lean`: each
`#guard_msgs` fails the run if Duper's proof of the sample uses any axiom other
than `propext`, `Classical.choice` and `Quot.sound`. The samples cover the
shapes `truth discover` meets: a quantified relational chain, propositional
case analysis, an existential with equality reasoning, and a delta-expanded
definition.
-/

namespace DuperAxiomAudit

theorem chain (α : Type) (R : α → α → Prop) (trans : ∀ x y z, R x y → R y z → R x z)
    (a b c : α) (hab : R a b) (hbc : R b c) : R a c := by
  duper [*]

theorem cases (P Q : Prop) (h : P ∨ Q) (hp : ¬ P) : Q := by
  duper [*]

theorem involution (α : Type) (f : α → α) (hf : ∀ x, f (f x) = x) (a : α) :
    ∃ y, f y = a := by
  duper [*]

def Transitive' (α : Type) (R : α → α → Prop) : Prop := ∀ x y z, R x y → R y z → R x z

theorem unfolded (α : Type) (R : α → α → Prop) (h : Transitive' α R) (a b c : α)
    (hab : R a b) (hbc : R b c) : R a c := by
  delta Transitive' at *
  duper [*]

/-- info: 'DuperAxiomAudit.chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms chain
/-- info: 'DuperAxiomAudit.cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cases
/-- info: 'DuperAxiomAudit.involution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms involution
/-- info: 'DuperAxiomAudit.unfolded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unfolded

end DuperAxiomAudit
