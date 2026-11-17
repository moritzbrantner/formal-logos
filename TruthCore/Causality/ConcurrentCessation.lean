module

public import TruthCore.Causality.ConcurrentActualization
public import TruthCore.Causality.ProtectiveProcess

/-! A scoped test of the cessation argument at concurrent actualization.
The existing process dictionary supplies actual terminal occurrences and bearer
identity. The causal coverage law below is a hypothesis, not a definition of
real causation. Natural-number sampling does not cover dense-time limits or
first appearances. No productive interpretation is inferred from a loss table.
-/

@[expose] public section

namespace TruthCore.Causality.ConcurrentCessation
open TruthCore.Causality.ProtectiveProcess
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Modal.TemporalHistory

/-- The cessation instance of a causal principle: every sampled loss of an
existing bearer has a terminal process occurrence directed to that SAME bearer.
This OPEN coverage claim does not identify failure of giving with a process. -/
def CessationHasCause {B F : Type} (m : Model B F Nat) : Prop :=
  ∀ x n, m.existsAt n x → ¬ m.existsAt (n+1) x →
    ∃ p, Destroys m p n (n+1) x

/-- Restore the intended meaning of terminal destruction in the controls:
every declared destruction really loses a previously existing bearer. -/
def DestructionSound {B F : Type} (m : Model B F Nat) : Prop :=
  ∀ p n x, Destroys m p n (n+1) x →
    m.existsAt n x ∧ ¬ m.existsAt (n+1) x

def NoCessationCause {B F : Type} (m : Model B F Nat) (x : B) (n : Nat) : Prop :=
  ∀ p, ¬ Destroys m p n (n+1) x

/-- Weak giving, restricted to continuation over an immediately previous
sample. The giver may vary, be the recipient, or be unrelated to an originator.
No claim about births, time zero or dense-time limit points is included. -/
def ContinuedGiving {B F P : Type} (m : Model B F Nat)
    (G : BeingGiving Unit B Nat) (received : B → P → Prop) : Prop :=
  ∀ x n z, received x z → m.existsAt n x → m.existsAt (n+1) x →
    ∃ g, G.GivesAt () g x (n+1)

/-- The proposed no-giver/no-continuation premise. It concerns absence of ALL
givers, not withdrawal of one identified original cause. Its dependence content
is explicit; equivalence below is a diagnostic, not independent warrant. -/
def UngivenContinuationFails {B F P : Type} (m : Model B F Nat)
    (G : BeingGiving Unit B Nat) (received : B → P → Prop) : Prop :=
  ∀ x n z, received x z → m.existsAt n x →
    (¬ ∃ g, G.GivesAt () g x (n+1)) → ¬ m.existsAt (n+1) x

def Consequences : Prop := ∀ (B F P : Type) (m : Model B F Nat)
    (G : BeingGiving Unit B Nat) (received : B → P → Prop),
  (∀ x n, CessationHasCause m → m.existsAt n x →
    NoCessationCause m x n → ¬¬ m.existsAt (n+1) x) ∧
  (ContinuedGiving m G received ↔ UngivenContinuationFails m G received) ∧
  (CessationHasCause m → UngivenContinuationFails m G received →
    ∀ x n z, received x z → m.existsAt n x →
      (¬ ∃ g, G.GivesAt () g x (n+1)) → ∃ p, Destroys m p n (n+1) x)

/-- Apply the ACTUAL root-route premise at the same world, bearer and time.
The process existence dictionary must match temporal presence; the Unit giving
profile is only the restriction to the supplied world, not a world/time swap. -/
def ConsumerRestriction : Prop := ∀ (W B F P : Type) (h : History W B Nat)
    (G : BeingGiving W B Nat) (received : B → P → Prop) (v : W)
    (m : Model B F Nat),
  (∀ t x, m.existsAt t x ↔ h.IsAt v x t) →
  ConcurrentlyActualized h G received →
  ContinuedGiving m ⟨fun _ c x t => G.GivesAt v c x t⟩ received

namespace Control
open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control

/-- Reuse the existing inertia history. Its source true ceases at sample 2;
one represented process witnesses that real sampled loss, so causal coverage
is not tested solely on a loss-free population. False remains the recipient. -/
def inertialProcesses : Model Bool Unit Nat where
  threat := fun _ => ⟨false, true⟩
  occurs := fun _ s t => s = 1 ∧ t = 2
  terminal := fun _ t => t = 2
  existsAt := fun t x => inertia.IsAt () x t

/-- Reuse the existing sustained history, with no destructive processes. -/
def sustainedProcesses : Model Bool Unit Nat where
  threat := fun _ => ⟨false, true⟩
  occurs := fun _ _ _ => False
  terminal := fun _ _ => False
  existsAt := fun t x => sustained.IsAt () x t

def Controls : Prop :=
  (CessationHasCause inertialProcesses ∧ DestructionSound inertialProcesses ∧
    Destroys inertialProcesses () 1 2 true ∧
    falseReceived false () ∧ inertialProcesses.existsAt 1 false ∧
    inertialProcesses.existsAt 2 false ∧ NoCessationCause inertialProcesses false 1 ∧
    (¬ ∃ g, inertiaGiving.GivesAt () g false 2) ∧
    ¬ ContinuedGiving inertialProcesses inertiaGiving falseReceived ∧
    ¬ ConcurrentlyActualized inertia inertiaGiving falseReceived) ∧
  (CessationHasCause sustainedProcesses ∧ DestructionSound sustainedProcesses ∧
    ContinuedGiving sustainedProcesses sustainedGiving falseReceived ∧
    UngivenContinuationFails sustainedProcesses sustainedGiving falseReceived ∧
    ConcurrentlyActualized sustained sustainedGiving falseReceived)
end Control

/-- Conditional schema and populated controls about existing dictionaries.
Neither causal coverage nor a no-giving dependency is asserted of reality. -/
def Certificate : Prop := Consequences ∧ ConsumerRestriction ∧ Control.Controls

end TruthCore.Causality.ConcurrentCessation
