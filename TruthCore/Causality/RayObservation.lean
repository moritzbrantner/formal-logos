module

public import Mathlib.SetTheory.Cardinal.Finite
public import TruthCore.Causality.ParallelPowerTransmission

@[expose] public section

namespace TruthCore.Causality.RayObservation

open TruthCore.Causality.ParallelPowerTransmission

/-- An observation is live when every incoming link at or upstream of its
position is intact. Different panel indices can observe the same position. -/
def Live {K O : Type} (intact : K → Nat → Prop) (position : O → K × Nat) (i : O) : Prop :=
  intactTail (intact (position i).1) (position i).2

/-- The set of ray identities occurring among live observations. -/
def ObservedRays {K O : Type} (intact : K → Nat → Prop) (position : O → K × Nat) : Set K :=
  Set.range (fun i : {i : O // Live intact position i} => (position i.1).1)

/-- The ray identity of a live observation, regarded as a member of the
observed ray set. -/
def observedRay {K O : Type} {intact : K → Nat → Prop} {position : O → K × Nat}
    (i : O) (live : Live intact position i) : ObservedRays intact position :=
  ⟨(position i).1, ⟨⟨i, live⟩, rfl⟩⟩

/-- The report records the activity at each observed position in some global
solution of the local transmission rule. -/
def Feasible {K O : Type} (intact : K → Nat → Prop) (position : O → K × Nat)
    (report : O → Bool) : Prop :=
  ∃ active : K × Nat → Prop, PowerTransmissionRule (transmissionLink intact) active ∧
    ∀ i, active (position i) ↔ report i = true

/-- Every position with an upstream cut reports off, and live observations
agree whenever they come from the same ray. -/
def RayReportCharacterization : Prop :=
  ∀ (K O : Type) (intact : K → Nat → Prop) (position : O → K × Nat) (report : O → Bool),
    Feasible intact position report ↔
      (∀ i, ¬ Live intact position i → report i = false) ∧
      (∀ i j, Live intact position i → Live intact position j →
        (position i).1 = (position j).1 → report i = report j)

/-- A finite panel distinguishes exactly one Boolean choice per ray with a
live observation, even when the family of rays is infinite. -/
def FiniteRayReportCount : Prop :=
  ∀ (K O : Type) [Finite O] (intact : K → Nat → Prop) (position : O → K × Nat),
    Nat.card {report : O → Bool // Feasible intact position report} =
      2 ^ Nat.card (ObservedRays intact position)

/-- The shared switch supplies the same setting at each live position. -/
def SharedSwitchReport {K O : Type} (intact : K → Nat → Prop) (position : O → K × Nat)
    (report : O → Bool) : Prop :=
  ∃ enabled : Bool, ∀ i, report i = true ↔ enabled = true ∧ Live intact position i

/-- A report is compatible with one common setting exactly when cut
positions report off and every live reading agrees. Such a report also
extends to the original family of disjoint rays with synchronized settings.
Ray identity here is supplied by the local model, independently of the setting. -/
def SharedSwitchCharacterization : Prop :=
  ∀ (K O : Type) (intact : K → Nat → Prop) (position : O → K × Nat) (report : O → Bool),
    (SharedSwitchReport intact position report ↔
      (∀ i, ¬ Live intact position i → report i = false) ∧
      (∀ i j, Live intact position i → Live intact position j → report i = report j)) ∧
    (SharedSwitchReport intact position report ↔
      ∃ (enabled : Bool) (active : K × Nat → Prop),
        PowerTransmissionRule (transmissionLink intact) active ∧
        (∀ k n, active (k, n) ↔ enabled = true ∧ intactTail (intact k) n) ∧
        (∀ i, active (position i) ↔ report i = true))

/-- Two live positions can report opposite settings exactly when they
observe distinct rays. Every such mixed live report excludes the shared
switch. -/
def MixedLiveRayReport : Prop :=
  ∀ (K O : Type) (intact : K → Nat → Prop) (position : O → K × Nat)
    (i j : O), Live intact position i → Live intact position j →
      ((∃ report, Feasible intact position report ∧ report i = true ∧ report j = false) ↔
        (position i).1 ≠ (position j).1) ∧
      ∀ report, report i = true → report j = false → ¬ SharedSwitchReport intact position report

end TruthCore.Causality.RayObservation
