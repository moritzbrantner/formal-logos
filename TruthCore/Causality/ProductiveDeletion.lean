module

public import TruthCore.Causality.ParticularActuality
public import TruthCore.Causality.AcquiredHistoryTransfer

/-! Selective deletion at fixed event identities and intrinsic basis. The records and
their attribution are supplied by the application. -/

@[expose] public section
namespace TruthCore.Causality.ProductiveDeletion
open TruthCore.Causality.JointGroups (Groups Exercise)
open TruthCore.Causality.ParticularActuality (restrict)
open TruthCore.Causality.DerivativeJointPower (Supply)

variable {B E G S : Type}

def withoutInputs (h : Groups E G) (selected : Set E) : Groups E G :=
  restrict h (fun g => ∀ u ∈ h.contributors g, u ∉ selected)

/-- The recorded step is supported by an original joint derivation, including
all co-contributors. This structural relation alone says nothing about occurrence. -/
def SuppliedStep (h : Groups E G) (I : E → Prop) (u v : E) : Prop :=
  ∃ g, h.admitted g ∧ h.effect g = v ∧ u ∈ h.contributors g ∧
    ∀ e ∈ h.contributors g, Supply h I e

/-- For each token in the chosen family the diagnostic succeeds with inputs owned
by its named source. The cut preserves the intrinsic basis. No assumption
about the size of the family or the external cause dictionary is included. -/
def CoveredLosses (m : Exercise B E G S) (covered : B → E → Prop)
    (I : E → Prop) (selected : B → E → Set E) : Prop :=
  m.coherent ∧ ∀ a v, covered a v →
    (∀ u ∈ selected a v, m.bearer u = a) ∧ Supply m.exercisedGroups I v ∧
    ¬ Supply (withoutInputs m.exercisedGroups (selected a v)) I v

open TruthCore.Causality.ExerciseContribution.Press

/-- Press roots for the application episode. The maintenance and drive inputs
are distinct even though they have the same bearer. -/
def pressSeed (e : Event) : Prop := e = .maintenance ∨ e = .drive ∨ e = .giverEsse

def PressLoss : Prop :=
  let h := (exercise .application).exercisedGroups
  let cut := withoutInputs h {.drive}
  Supply h pressSeed .imprint ∧ ¬ Supply cut pressSeed .imprint ∧
    Supply cut pressSeed .giverEsse ∧ Supply cut pressSeed .agentEsse ∧
    Supply cut pressSeed .patientEsse

end TruthCore.Causality.ProductiveDeletion
