module

public import TruthCore.Causality.FiniteThroughput
public import TruthCore.Causality.ReceiptMatching
public import TruthCore.Causality.SelectedSourcePath
public import Mathlib.Data.Nat.Cast.WithTop

/-! Analyst conditions on one fixed actual recipient, grounding profile and world.
The edge alignments constrain independently specified transfer data. They neither
identify grounding with transactions nor demand that every grounding edge is booked. -/

@[expose] public section

open scoped ENNReal

namespace TruthCore.Causality.SelectedConeSupply
open BruteFoundationBoundary (Profile)
open NecessaryRootFork (ActualConcrete)
open ReceiptMatching (Reaches)
open SelectedSourcePath (HasSelectedSourcePath)
open SelectedAncestry (Cone)
open WorldSourceRegress (overlap)
open Logic.Regress (Graph)

variable {W B E : Type}

/-- Every selected event follows a grounding edge. One event into the fixed
recipient has no selected return path and has finite selected export ancestry. -/
def SelectedReceiptExit (m : Profile W B) (w : W) (x : {b // ActualConcrete m w b})
    (sender receiver : E → {b // ActualConcrete m w b}) : Prop :=
  (∀ e, m.grounds w (sender e).val (receiver e).val) ∧
    ∃ e, receiver e = x ∧ ¬ Reaches sender receiver x (sender e) ∧
      Finite {p : E // Reaches sender receiver (sender p) (sender e)}

/-- Positive entries follow grounding edges. Throughput counts transfers over
the entire actual roster. Some positive entry into the recipient has no
positive-transfer return path in that ledger. -/
def SelectedThroughputExit (m : Profile W B) (w : W) (x : {b // ActualConcrete m w b})
    (flow : {b // ActualConcrete m w b} → {b // ActualConcrete m w b} → ℝ≥0∞) : Prop :=
  (∀ a b, 0 < flow a b → m.grounds w a.val b.val) ∧
    (∑' p : {b // ActualConcrete m w b} × {b // ActualConcrete m w b}, flow p.1 p.2) ≠ ⊤ ∧
    ∃ a, 0 < flow a x ∧ ¬ Relation.ReflTransGen (fun i j => 0 < flow i j) x a

/-- One natural-number rank valid on every edge of the represented graph. -/
def HasNatRank {N : Type} (G : Graph N) : Prop :=
  ∃ rank : N → Nat, ∀ ⦃y x⦄, G.edge y x → rank y < rank x

/-- Unrestricted walks count repeated vertices as well as distinct ones. -/
def NoInfiniteWalkFrom {N : Type} (G : Graph N) (x : N) : Prop :=
  ¬ ∃ f : Nat → N, f 0 = x ∧ ∀ n, G.edge (f (n + 1)) (f n)

def splitFork : Graph (Fin 3) := ⟨fun y x => y.val < 2 ∧ x = 2⟩

def topProfile : Profile Unit (WithTop Nat) where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ => (· < ·)

def rayProfile : Profile Bool (Option Nat) where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w b => w = true ∨ b ≠ some 0
    Causes := fun _ _ _ => False
  }
  concrete := fun _ => True
  grounds := fun _ => overlap.Causes ()

abbrev RayBearer := {b // ActualConcrete rayProfile true b}

def raySource : RayBearer := ⟨none, trivial, Or.inl rfl⟩

def rayTip : RayBearer := ⟨some 0, trivial, Or.inl rfl⟩

def raySender : Unit → RayBearer := fun _ => raySource

def rayReceiver : Unit → RayBearer := fun _ => rayTip

noncomputable def rayFlow (a b : RayBearer) : ℝ≥0∞ := by
  classical
  exact if a = raySource ∧ b = rayTip then 1 else 0

/-- Over all actual starting bearers, well-foundedness of the complete
selected cone is exactly the denial of an infinite upstream walk from it. -/
def ConeWalkCriterion : Prop :=
  ∀ {W B : Type} (m : Profile W B) (w : W) (x : {b // ActualConcrete m w b}),
    SelectedAncestry.ConeWellFounded m w x.val ↔
      NoInfiniteWalkFrom (ConcreteExistentialSupply.graph m w) x

end TruthCore.Causality.SelectedConeSupply
