module

public import TruthCore.Causality.DependenceStrictGroundMapStrength
public import Mathlib.Data.Set.Finite.Basic

/-! A representation test for the distinct-dependence-to-strict-ground bridge.
Fix the labels first. A PLG theory may then be selected to fit the data.
This selection does not identify a label with an actual existence fact. -/

@[expose] public section
namespace TruthCore.Causality.StrictGroundRepresentation

open DependenceStrictGroundMap DependenceStrictGroundMapStrength
open TruthCore.Modern.Fine.PureLogicOfGround

/-- Project each distinct dependence step to its two labels, oriented from
supplier to dependent. Different steps may project from different bearers. -/
def Projected {B Atom : Type} (D : B → B → Prop) (label : B → Atom) (a b : Atom) : Prop :=
  ∃ x y, DistinctEdge D x y ∧ label y = a ∧ label x = b

/-- Exactly the projected one-step strict sequents. -/
def edgeTheory {B Atom : Type} (D : B → B → Prop) (label : B → Atom) : Set (Sequent Atom) :=
  {s | ∃ a b, Projected D label a b ∧ s = .strictPartial a b}

/-- For a supplied labelling into a populated atom type, a consistent
theory realizing the map exists exactly when the projected steps are acyclic. -/
def FixedLabelCriterion : Prop :=
  ∀ {B Atom : Type} [Nonempty Atom] (D : B → B → Prop) (label : B → Atom),
    (∃ S, Consistent S ∧ DependenceMapsToStrictExistenceGround D label S) ↔
      ∀ a, ¬ Relation.TransGen (Projected D label) a a

/-- With each bearer as its own label, acyclicity suffices for the edge theory
to be consistent and to derive precisely the reversed nonempty finite paths
as strict partial grounds. The theory is constructed from the dependence data. -/
def IdentityRepresentation : Prop :=
  ∀ {B : Type} [Nonempty B] (D : B → B → Prop),
    DistinctDependenceAcyclic D ↔ Consistent (edgeTheory D id) ∧
      ∀ a b, StrictlyGrounds (edgeTheory D id) a b ↔ Relation.TransGen (DistinctEdge D) b a

/-- Each per se efficient-cause link supplies the dependent's being in the
selected respect, and its endpoints are distinct. -/
def PerSeDependenceLinks {B : Type} (cause D : B → B → Prop) : Prop :=
  ∀ y x, cause y x → DistinctEdge D x y

/-- For each effect separately, only finitely many labels occur among that
effect and all its per se ancestors. Bearers sharing a label can be infinite
in number, and the finite sets may vary with the effect. -/
def FiniteAncestralLabels {B Atom : Type} (cause : B → B → Prop) (label : B → Atom) : Prop :=
  ∀ x, (label '' {y | Relation.ReflTransGen cause y x}).Finite

namespace Control

/-- Two disjoint dependence steps. The first coordinate picks the pair. -/
def twoPairs (x y : Bool × Bool) : Prop :=
  x.2 = false ∧ y.2 = true ∧ x.1 = y.1

def sharedLabel (x : Bool × Bool) : Bool := xor x.1 x.2

/-- No dependency path has equal endpoint labels, yet the two pairs project
in opposite directions. No consistent theory can realize this labelling. -/
def LabelCycle : Prop :=
  DistinctDependenceAcyclic twoPairs ∧
  (∀ x y, Relation.TransGen (DistinctEdge twoPairs) x y → sharedLabel x ≠ sharedLabel y) ∧
  ¬ ∃ S, Consistent S ∧ DependenceMapsToStrictExistenceGround twoPairs sharedLabel S

end Control
end TruthCore.Causality.StrictGroundRepresentation
