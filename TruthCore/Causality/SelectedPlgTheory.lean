module

public import TruthCore.Causality.DependenceStrictGroundMap

@[expose] public section

namespace TruthCore.Causality.SelectedPlgTheory

open TruthCore.Modern.Fine.PureLogicOfGround
open DependenceStrictGroundMap
open Relation

/-- The selected atom type has an inhabitant, so it admits a sequent. -/
def PopulatedAtomType (Atom : Type) : Prop := Nonempty Atom

/-- A particular antecedent of an initial strict sequent, full or partial. -/
def StrictEdge {Atom : Type} (S : Set (Sequent Atom)) (a b : Atom) : Prop :=
  Sequent.strictPartial a b ∈ S ∨ ∃ premises, Sequent.strictFull premises b ∈ S ∧ a ∈ premises

/-- A particular antecedent of any initial sequent. Strict edges also count
as weak steps, by PLG subsumption. -/
def WeakEdge {Atom : Type} (S : Set (Sequent Atom)) (a b : Atom) : Prop :=
  Sequent.weakPartial a b ∈ S ∨ (∃ premises, Sequent.weakFull premises b ∈ S ∧ a ∈ premises) ∨
    StrictEdge S a b

/-- No initial strict step is followed by a finite return path using initial
edges. Zero steps are allowed, so a strict self-edge fails the test. -/
def NoStrictReturn {Atom : Type} (S : Set (Sequent Atom)) : Prop :=
  ∀ a b, StrictEdge S a b → ¬ ReflTransGen (WeakEdge S) b a

/-- A finite path of initial steps containing a strict step. -/
def StrictPath {Atom : Type} (S : Set (Sequent Atom)) (a b : Atom) : Prop :=
  ∃ u v, ReflTransGen (WeakEdge S) a u ∧ StrictEdge S u v ∧ ReflTransGen (WeakEdge S) v b

/-- Each distinct dependence edge has a finite path of initial sequents in
the separately supplied theory, with at least one strict step. The direction
is from the supplier's label to the dependent's label. -/
def DependenceHasStrictPaths {B Atom : Type}
    (D : B → B → Prop) (label : B → Atom) (S : Set (Sequent Atom)) : Prop :=
  ∀ x y, x ≠ y → D x y → StrictPath S (label y) (label x)

/-- On a populated atom type, the test characterizes consistency of the
supplied set itself, including full, partial, weak and strict assumptions. -/
def ConsistencyCriterion : Prop :=
  ∀ {Atom : Type} [Nonempty Atom] (S : Set (Sequent Atom)), Consistent S ↔ NoStrictReturn S

/-- In the same consistent theory, strict derivability is exactly the path
relation that passes through an initial strict step. -/
def StrictDerivabilityCriterion : Prop :=
  ∀ {Atom : Type} (S : Set (Sequent Atom)), Consistent S →
    ∀ a b, StrictlyGrounds S a b ↔ StrictPath S a b

namespace Control

open Sequent

def dependence (x y : Bool) : Prop := x = true ∧ y = false

def weakOnly : Set (Sequent Bool) := {weakFull {false} true}

def strictForward : Set (Sequent Bool) := {strictFull {false} true}

def withWeakReturn : Set (Sequent Bool) := insert (weakFull {true} false) strictForward

/-- On the same two labels, weak support alone fails the map, strict support
satisfies it consistently, and adding a weak return preserves the map but
makes the selected theory inconsistent. -/
def PresentationControls : Prop :=
  Consistent weakOnly ∧ ¬ DependenceMapsToStrictExistenceGround dependence id weakOnly ∧
  Consistent strictForward ∧ DependenceMapsToStrictExistenceGround dependence id strictForward ∧
  ¬ Consistent withWeakReturn ∧ DependenceMapsToStrictExistenceGround dependence id withWeakReturn

end Control
end TruthCore.Causality.SelectedPlgTheory
