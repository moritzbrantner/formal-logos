module

public import TruthCore.Logic.Regress
public import TruthCore.Mereology.AtomlessFusionProfile
public import Mathlib.Order.Atoms

/-! Structural controls for #336, analyst formulations with attribution deferred.
The inherited partial order interprets parthood only in the named mathematical
models. No identity with actual causal power, existence-grounding, substantial
unity or metaphysical possibility is built into an edge or a certificate.
-/

@[expose] public section
namespace TruthCore.Mereology.DependenceShapes
open TruthCore.Logic.Regress TruthCore.Causality
open UniversalFusionBoundary AtomlessFusionProfile

/-- Equality of strict lower cones; this is NOT equality of overlap profiles. -/
def SameProperParts {B : Type} [PartialOrder B] (x y : B) : Prop :=
  ∀ p, p < x ↔ p < y

/-- The unrestricted principle applies even to objects with empty lower cones. -/
def ProperExtensionality (B : Type) [PartialOrder B] : Prop :=
  ∀ x y : B, SameProperParts x y → x = y

/-- Restrict BOTH compared objects to composites. No restriction on their parts. -/
def CompositeExtensionality (B : Type) [PartialOrder B] : Prop :=
  ∀ x y : B, Composite x → Composite y → SameProperParts x y → x = y

/-- A stipulated whole-first star: the designated whole directly precedes
all OTHER objects. This is weaker than reversing every strict parthood edge. -/
def wholeStar {B : Type} (u : B) : Graph B :=
  ⟨fun y x => y = u ∧ x ≠ u⟩

/-- DS-1 reuses the existing graph controls and fixed-point semantics. The
finite cycle and infinite strict order separately distinguish distinct chains,
cycles and accessibility. Finite grounding does not imply graph WF. -/
def ShapeControl : Prop :=
  (∀ (B : Type) (G : Graph B), WellFounded G.edge → G.Controls) ∧
  (∃ G : Graph Unit,
    (∀ x, G.edge x x) ∧
    (¬ ∃ f : Nat → Unit, Function.Injective f) ∧
    ¬ WellFounded G.edge ∧
    (∀ x, FinitelyGroundedPower G.edge (fun _ => True) x) ∧
    (G.transmission (fun _ => False)).lfp = ∅ ∧
    (G.transmission (fun _ => False)).gfp = Set.univ) ∧
  (∀ n : Nat, n < n + 1) ∧
  (∀ n : Nat, ¬ n < n) ∧
  (∀ x y z : Nat, z < y → y < x → z < x) ∧
  ¬ WellFounded (fun y x : Nat => x < y)

/-- DS-2 keeps the existing full regular-open fusion model. Every starting
region has an injective descending proper-part chain. The reverse relation
rejects that SAME oriented chain, but still is not WF. A whole-first star on
the SAME carrier is WF; it does not include every whole-to-proper-part edge.
Mathlib atomicity/atomisticity is asserted only for the Boolean set contrast. -/
def PriorityControl : Prop :=
  GunkCertificate ∧
  (∀ U : Region, ∃ f : Nat → Region,
    f 0 = U ∧ Function.Injective f ∧ ∀ n, f (n + 1) < f n) ∧
  ¬ WellFounded (fun y x : Region => y < x) ∧
  (∀ f : Nat → Region, (∀ n, f (n + 1) < f n) →
    ∀ n, ¬ f n < f (n + 1)) ∧
  ¬ WellFounded (fun y x : Region => x < y) ∧
  (∃ u : Region, (∀ x, x ≤ u) ∧ WellFounded (wholeStar u).edge ∧
    (∀ x, (wholeStar u).Source x ↔ x = u) ∧
    ¬ (∀ x y : Region, x < y → (wholeStar u).edge y x)) ∧
  (∀ U : RegionAlgebra, ¬ IsAtom U) ∧
  IsAtomic (Set Bool) ∧ IsAtomistic (Set Bool)

/-- DS-3: unrestricted strict-part extensionality collapses all minimal
objects; strong supplementation gives composite-restricted extensionality.
The existing full-fusion Body has two distinct minimal atoms, so the
restricted principle holds while the unrestricted principle fails. Minimal
means mereologically simple here, not the Case vocabulary's richer IsSimple. -/
def ExtensionalityControl : Prop :=
  (∀ (B : Type) [PartialOrder B], ProperExtensionality B →
    ∀ x y : B, IsMin x → IsMin y → x = y) ∧
  (∀ (B : Type) [PartialOrder B],
    SupplementationFusion.StrongSupplementation B → CompositeExtensionality B) ∧
  AtomicCertificate ∧ CompositeExtensionality Body ∧
  IsMin (atom false) ∧ IsMin (atom true) ∧ atom false ≠ atom true ∧
  SameProperParts (atom false) (atom true) ∧ ¬ ProperExtensionality Body

end TruthCore.Mereology.DependenceShapes
