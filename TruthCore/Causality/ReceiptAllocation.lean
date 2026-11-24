module

public import TruthCore.Causality.ExerciseContribution

/-! Provenance of a consumed input in one accounting window. The aggregate
counts concern a specified, conserved and interchangeable input at a patient.
A unit supplied in an earlier window counts as opening stock irrespective of
its historical supplier. Time of arrival, binding storage capacities, leakage,
extra outlets and restrictions on routing are outside the model. No unit of
esse or empirical law about the expenditure of causal power is postulated. -/

@[expose] public section
namespace TruthCore.Causality.ReceiptAllocation

open TruthCore.Causality.ExerciseContribution (Step)
open TruthCore.Causality.JointGroups (Exercise)

/-- Two inlet classes and two outlets. Counts are nonnegative whole units;
each counted unit reaches exactly one outlet. -/
structure Allocation where
  namedWork : Nat
  namedRemainder : Nat
  pooledWork : Nat
  pooledRemainder : Nat

def Allocation.accounts (r : Allocation) (named pooled work remainder : Nat) : Prop :=
  r.namedWork + r.namedRemainder = named ∧
  r.pooledWork + r.pooledRemainder = pooled ∧
  r.namedWork + r.pooledWork = work ∧
  r.namedRemainder + r.pooledRemainder = remainder

structure Window where
  opening : Nat
  receipt : Nat
  other : Nat
  work : Nat
  closing : Nat

def Window.balanced (w : Window) : Prop :=
  w.opening + w.receipt + w.other = w.work + w.closing

def Window.fits (w : Window) (r : Allocation) : Prop :=
  r.accounts w.receipt (w.opening + w.other) w.work w.closing

inductive Event | receipt | pool | work deriving DecidableEq

/-- A single record for work actually performed. Positive consumption of an
identified input gives it a productive step on this interpretation. The unit
scenario and identity bearer map merely index the record; the source bounds
comes from the inlet and outlet balances across admissible allocations. -/
def exercise (w : Window) (r : Allocation) : Exercise Event Event Unit Unit where
  groups := {
    contributors := fun _ e => match e with
      | .receipt => 0 < r.namedWork
      | .pool => 0 < r.pooledWork
      | .work => False
    enablers := fun _ _ => False
    effect := fun _ => .work
    admitted := fun _ => 0 < w.work }
  bearer := id
  occurs := fun _ e => match e with
    | .receipt => 0 < w.receipt
    | .pool => 0 < w.opening + w.other
    | .work => 0 < w.work
  allowed := fun _ => True
  actual := ()
  exercised := fun _ => 0 < w.work

/-- Sharp range and the precise condition for the named inlet to serve the
work in every compatible routing. Free routing is an interpretation choice. -/
def RangeCertificate : Prop :=
  ∀ w : Window, w.balanced →
    (∀ n : Nat, (∃ r, w.fits r ∧ r.namedWork = n) ↔
      w.work - (w.opening + w.other) ≤ n ∧ n ≤ min w.work w.receipt) ∧
    ((∀ r, w.fits r → Step (exercise w r) .receipt .work) ↔
      w.opening + w.other < w.work)

/-- Matched receipts, expenditure and final stock can hide opposite productive
roles. A deficit can force a current contribution to the combined work while
leaving its allocation between two particular equal outputs undecided. -/
def Controls : Prop :=
  (let w : Window := ⟨1, 1, 0, 1, 1⟩
   w.balanced ∧ ∃ use store, w.fits use ∧ w.fits store ∧
     Step (exercise w use) .receipt .work ∧ ¬ Step (exercise w store) .receipt .work) ∧
  (let w : Window := ⟨1, 1, 0, 2, 0⟩
   w.balanced ∧ (∃ r, w.fits r) ∧
     ∀ r, w.fits r → Step (exercise w r) .receipt .work ∧
       ∃ first second : Allocation, first.accounts r.namedWork r.pooledWork 1 1 ∧
         second.accounts r.namedWork r.pooledWork 1 1 ∧
         first.namedWork = 1 ∧ first.namedRemainder = 0 ∧
         second.namedWork = 0 ∧ second.namedRemainder = 1)

end TruthCore.Causality.ReceiptAllocation
