module

public import TruthCore.Causality.ParallelPowerTransmission
public import TruthCore.Causality.SupplierAuditLikelihood

/-! Interventions at different incoming links of one successor ray, with the
same position zero and the same selected power throughout. -/

@[expose] public section
noncomputable section
namespace TruthCore.Causality.RelayCutSensitivity

open TruthCore.Causality.FiniteReserveOdds (geometricPrior)
open TruthCore.Causality.PostCutStore (prefixSum)
open TruthCore.Causality.SupplierAuditLikelihood (depthLikelihood)

/-- The only removed successor link is the one from `cut + 1` into `cut`. -/
def singleCut (cut position : ℕ) : Prop :=
  position ≠ cut

/-- At each position, the same selected power is active if there is an
independent active feed there or an intact link from an active successor.
The independent input is separate from the successor link being tested. -/
def RelayActivity (intact independent active : ℕ → Prop) : Prop :=
  ∀ n, active n ↔ independent n ∨ (intact n ∧ active (n + 1))

/-- A response at each cut, tested separately from the other cuts. -/
def CutResponses (independent : ℕ → Prop) (response : ℕ → ℕ → Prop) : Prop :=
  ∀ i, RelayActivity (singleCut i) independent (response i)

/-- Both classes permit a common active baseline and a family of post-cut
responses. At a fed depth the response may differ upstream, but the outcome
at zero is fixed. The least cut preserving activity identifies the depth. -/
def SingleCutComparison : Prop :=
  (RelayActivity (fun _ => True) (fun _ => False) (fun _ => True) ∧
    ∀ d, RelayActivity (fun _ => True) (· = d) (fun _ => True)) ∧
  (∃ response, CutResponses (fun _ => False) response) ∧
  (∀ response, CutResponses (fun _ => False) response → ∀ i, ¬ response i 0) ∧
  (∀ d, ∃ response, CutResponses (· = d) response) ∧
  (∀ d response, CutResponses (· = d) response →
    ∀ i, response i 0 ↔ d ≤ i) ∧
  (∀ d response, CutResponses (· = d) response →
    IsLeast {i | response i 0} d) ∧
  (∀ k response, CutResponses (· = k + 1) response →
    (∀ i ≤ k, ¬ response i 0) ∧ response (k + 1) 0)

/-- The mass of cut positions at which the observed receiver remains active.
The weights specify the experimenter's choice of cut index. -/
def survivalMass (law : ℕ → ℝ) (response : ℕ → ℕ → Prop) : ℝ := by
  classical
  exact ∑' i, if response i 0 then law i else 0

/-- An observed survival has zero probability under the relay-only model.
A fed depth has positive survival probability exactly when its tail contains
a cut with positive mass. For a fixed law, the probabilities fall below every
positive bound eventually. -/
def RandomizedCutComparison : Prop :=
  (∀ law response, CutResponses (fun _ => False) response → survivalMass law response = 0) ∧
  (∀ law : ℕ → ℝ, (∀ i, 0 ≤ law i) → HasSum law 1 →
    (∀ d response, CutResponses (· = d) response →
      survivalMass law response = depthLikelihood law d ∧
      survivalMass law response = 1 - prefixSum law d ∧
      (0 < survivalMass law response ↔ ∃ i, d ≤ i ∧ 0 < law i) ∧
      survivalMass law response ≤ 1) ∧
    ∀ ε : ℝ, 0 < ε → ∃ start : ℕ, ∀ d ≥ start, ∀ response,
      CutResponses (· = d) response → survivalMass law response < ε) ∧
  (HasSum geometricPrior 1 ∧ (∀ i, 0 < geometricPrior i) ∧
    ∀ d response, CutResponses (· = d) response →
      survivalMass geometricPrior response = (1 / 2 : ℝ) ^ d)

end TruthCore.Causality.RelayCutSensitivity
