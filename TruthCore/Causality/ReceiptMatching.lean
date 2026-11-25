module

public import TruthCore.Causality.RootPositiveIntellectWill
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import TruthCore.Causality.ParticipatedEsseScale

/-! Transfers in a single independently specified class, for example releases
of distinct reserved items. Repeated transfers between the same endpoints can
have different event identities. Lower-grade or otherwise unselected events
are outside the transfer type. No additivity of degrees of being is assumed. -/
@[expose] public section
namespace TruthCore.Causality.ReceiptMatching

def Reaches {E V : Type} (sender receiver : E → V) : V → V → Prop :=
  Relation.ReflTransGen (fun x y => ∃ p, sender p = x ∧ receiver p = y)

def CanMatch {E V : Type} (sender receiver : E → V) (u : V) : Prop :=
  Nonempty ({p // sender p = u} ↪ {p // receiver p = u})

/-- Includes the sender's own transfers. Finiteness is only imposed on
selected exports made by vertices which can reach the marked sender. -/
def OneWayFiniteAncestry {E V : Type} (sender receiver : E → V) : Prop :=
  ∃ marked, ¬ Reaches sender receiver (receiver marked) (sender marked) ∧
    Finite {p : E // Reaches sender receiver (sender p) (sender marked)}

/-- A one-way discharge from a finite ancestry of selected exports reveals
some upstream sender whose exports cannot all be matched to distinct receipts. -/
def UnmatchedUpstream : Prop :=
  ∀ {E V : Type} (sender receiver : E → V) (marked : E),
    ¬ Reaches sender receiver (receiver marked) (sender marked) →
    Finite {p : E // Reaches sender receiver (sender p) (sender marked)} →
    ∃ u, Reaches sender receiver u (sender marked) ∧ ¬ CanMatch sender receiver u

open BruteFoundationBoundary (Profile)
open NecessaryRootFork (ActualConcrete)
open CogitoNecessaryConcrete (ActualConcreteGround)

/-- Transfer-to-grounding bridge on the actual roster. For the chosen class
every grounded bearer's exports have distinct matching receipts of that class.
This constrains their multiplicities, without tracing any particular receipt
to the export it was actually used for. -/
def GroundedCanMatch {W B E : Type} (m : Profile W B) (w : W)
    (sender receiver : E → {x // ActualConcrete m w x}) : Prop :=
  ∀ u, (∃ y, ActualConcreteGround m w y u.val) → CanMatch sender receiver u


open scoped BigOperators

/-- Finite grade counts; grade zero is the lowest positive grade. A missing
instance is counted zero times. Positive successive gaps calibrate the scale
from the fixed zero of absence. -/
def atLeast {n : Nat} (count : Fin n → Nat) (k : Fin n) : Nat :=
  ∑ j, if k ≤ j then count j else 0

def amount {n : Nat} (count gap : Fin n → Nat) : Nat :=
  ∑ j, count j * ∑ k, if k ≤ j then gap k else 0

def CoverageUnderRegrading : Prop :=
  ∀ {n : Nat} (outgoing incoming : Fin n → Nat),
    (∀ gap : Fin n → Nat, (∀ k, 0 < gap k) → amount outgoing gap ≤ amount incoming gap) ↔
      ∀ k, atLeast outgoing k ≤ atLeast incoming k

/-- Two giver stages both realize low and high determinations. Two distinct
recipients each realize just the low determination. Everything below uses the
same edge incidence and the same possession relation. -/
inductive Bearer | principal | relay | left | right
  deriving DecidableEq

instance : Fintype Bearer where
  elems := {.principal, .relay, .left, .right}
  complete x := by cases x <;> decide

def gives : Bearer → Bearer → Prop
  | .principal, .relay | .relay, .left | .relay, .right => True
  | _, _ => False

def has : Bearer → Bool → Prop
  | .principal, _ | .relay, _ => True
  | _, feature => feature = false

def level (high : Nat) (feature : Bool) : Nat := if feature then high else 2

def degree (high : Nat) : Bearer → Nat
  | .principal | .relay => high
  | .left | .right => 2

open TruthCore.Causality.ParticipatedEsseScale (realizedLevels)

instance (x y : Bearer) : Decidable (gives x y) := by
  cases x <;> cases y <;> unfold gives <;> infer_instance

/-- The proposed ledger books the recipient's degree once on each productive
edge. The existential and productive significance of this amount is open. -/
def booked (high : Nat) (x y : Bearer) : Nat :=
  if gives x y then degree high y else 0

def RelayCalibrationControl : Prop :=
  (∀ giver recipient, gives giver recipient → ∀ feature, has recipient feature → has giver feature) ∧
  (∀ high, 2 ≤ high → ∀ b, IsLUB (realizedLevels (fun _ => True) has (level high) b) (degree high b)) ∧
  (∑ x, booked 3 x .relay) = 3 ∧ (∑ y, booked 3 .relay y) = 4 ∧
  (∑ x, booked 5 x .relay) = 5 ∧ (∑ y, booked 5 .relay y) = 4

end TruthCore.Causality.ReceiptMatching
