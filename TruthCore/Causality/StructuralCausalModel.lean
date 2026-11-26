module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite recursive structural equations

A directed edge grants an equation access to a parent value. It can be an
unused slot. Well-founded parent adjacency is the declared evaluation
condition. Endogenous variables are finite and share one value type. The
exogenous context is supplied to every equation, with no distribution or
independence assumption in the solver. See the sustaining-versus-inertia
research note for the open interpretation of this mathematical interface.
-/

@[expose] public section

namespace TruthCore.Causality.StructuralCausalModel

structure Model (V U A : Type) [Finite V] where
  graph : Digraph V
  acyclic : WellFounded graph.Adj
  equation : (v : V) → U → ({p : V // graph.Adj p v} → A) → A

variable {V U A : Type} [Finite V]

abbrev Setting (V A : Type) := V → Option A

/-- Simultaneously replace precisely the equations with supplied constants.
The original graph remains an upper bound on which inputs can be read. The
replaced equations ignore every parent. -/
def Model.intervene (m : Model V U A) (setting : Setting V A) : Model V U A :=
  { m with equation := fun v u parent => (setting v).getD (m.equation v u parent) }

def Model.Solution (m : Model V U A) (u : U) (values : V → A) : Prop :=
  ∀ v, values v = m.equation v u (fun p => values p.val)

def Model.solve (m : Model V U A) (u : U) : V → A :=
  m.acyclic.fix (fun v previous => m.equation v u (fun p => previous p.val p.property))

theorem Model.solve_equation (m : Model V U A) (u : U) : m.Solution u (m.solve u) := by
  intro v
  exact WellFounded.fix_eq _ _ _

theorem Model.eq_solve (m : Model V U A) (u : U) {values : V → A}
    (h : m.Solution u values) : values = m.solve u := by
  funext v
  induction v using m.acyclic.induction with
  | h v ih =>
    rw [h v, m.solve_equation u v]
    congr 1
    exact funext (fun p => ih p.val p.property)

theorem Model.existsUnique_solution (m : Model V U A) (u : U) :
    ∃! values, m.Solution u values :=
  ⟨m.solve u, m.solve_equation u, fun _ => m.eq_solve u⟩

def Model.response (m : Model V U A) (u : U) (setting : Setting V A) : V → A :=
  (m.intervene setting).solve u

def setOne [DecidableEq V] (v : V) (a : A) : Setting V A :=
  fun w => if w = v then some a else none

theorem Model.response_forced (m : Model V U A) (u : U) (s : Setting V A)
    {v : V} {a : A} (h : s v = some a) : m.response u s v = a := by
  simpa [Model.response, Model.intervene, h] using (m.intervene s).solve_equation u v

theorem Model.response_unforced (m : Model V U A) (u : U) (s : Setting V A)
    {v : V} (h : s v = none) :
    m.response u s v = m.equation v u (fun p => m.response u s p.val) := by
  simpa [Model.response, Model.intervene, h] using (m.intervene s).solve_equation u v

theorem Model.response_natural (m : Model V U A) (u : U) :
    m.response u (fun _ => none) = m.solve u := rfl

/-- An untouched variable with no modified ancestor retains its original
value. The converse fails even for genuine functional input paths. -/
theorem Model.response_eq_of_unaffected (m : Model V U A) (u : U) (s : Setting V A)
    (v : V) (h : ∀ p, p = v ∨ Relation.TransGen m.graph.Adj p v → s p = none) :
    m.response u s v = m.solve u v := by
  induction v using m.acyclic.induction with
  | h v ih =>
    rw [m.response_unforced u s (h v (Or.inl rfl)), m.solve_equation u v]
    congr 1
    funext p
    apply ih p.val p.property
    intro q hq
    apply h q ∘ Or.inr
    rcases hq with rfl | path
    · exact .single p.property
    · exact path.tail p.property

/-- Push the same context law through the equations before or after surgery.
The observation function chooses which aspects of the valuation are recorded. -/
noncomputable def Model.responseLaw {O : Type} (m : Model V U A) (p : PMF U)
    (s : Setting V A) (observe : (V → A) → O) : PMF O :=
  p.map (fun u => observe (m.response u s))

end TruthCore.Causality.StructuralCausalModel
