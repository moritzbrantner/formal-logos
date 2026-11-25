module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import TruthCore.Causality.EssentialPower
public import TruthCore.Causality.RootPositiveIntellectWill

@[expose] public section
open scoped ENNReal
namespace TruthCore.Causality.FiniteThroughput

/-- The amount booked on each directed transfer in one fixed ledger. The sum
counts each transfer, including successive transfers of the same resource. -/
def ReturnOrNetExport : Prop :=
  ∀ {V : Type} (flow : V → V → ℝ≥0∞),
    (∑' p : V × V, flow p.1 p.2) ≠ ⊤ →
    ∀ {a b}, 0 < flow a b →
    let reaches := Relation.ReflTransGen (fun x y => 0 < flow x y)
    reaches b a ∨ ∃ u, reaches u a ∧ (∑' x, flow x u) < ∑' y, flow u y

/-- The open interpretation maps positive ledger entries to actual exercises
and net exporters to intrinsic contributors in the selected productive respect.
Neither condition identifies a ground of the bearer's existence. -/
def GroundedExerciseAtTransfer : Prop :=
  ∀ {V : Type} (flow : V → V → ℝ≥0∞) (transmits : V → V → Prop)
    (intrinsic : V → Prop),
    (∑' p : V × V, flow p.1 p.2) ≠ ⊤ →
    (∀ x y, 0 < flow x y → transmits x y) →
    (∀ u, (∑' x, flow x u) < ∑' y, flow u y → intrinsic u) →
    ∀ {a b}, 0 < flow a b →
    ¬ Relation.ReflTransGen (fun x y => 0 < flow x y) b a →
    FinitelyGroundedPower transmits intrinsic b

open BruteFoundationBoundary (Profile)
open NecessaryRootFork (ActualConcrete ActualRoot)
open CogitoNecessaryConcrete (ActualConcreteGround)

/-- A fixed ledger on actual concrete bearers has finite total throughput and
contains one positive transfer outside any positive-transfer cycle. -/
def FiniteOneWayTransfer {V : Type} (flow : V → V → ℝ≥0∞) : Prop :=
  (∑' p : V × V, flow p.1 p.2) ≠ ⊤ ∧ ∃ a b, 0 < flow a b ∧
    ¬ Relation.ReflTransGen (fun x y => 0 < flow x y) b a

/-- Application premise: any actual concretum with an actual concrete ground
can export at most its total receipts in this very ledger. -/
def GroundedExportCovered {W B : Type} (m : Profile W B) (w : W)
    (flow : {x // ActualConcrete m w x} → {x // ActualConcrete m w x} → ℝ≥0∞) : Prop :=
  ∀ u, (∃ y, ActualConcreteGround m w y u.val) →
    (∑' v, flow u v) ≤ ∑' v, flow v u

/-- To test the evidential value of choosing the ledger after the fact, allow
any nonnegative assignments on this same roster. -/
def LedgerExistenceCriterion : Prop :=
  ∀ {W B : Type} (m : Profile W B) (w : W),
    (∃ flow, FiniteOneWayTransfer flow ∧ GroundedExportCovered m w flow) ↔
      ∃ u v, ActualRoot m w u ∧ ActualConcrete m w v ∧ u ≠ v

end TruthCore.Causality.FiniteThroughput
