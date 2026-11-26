module

public import TruthCore.Causality.OccamRegress
public import TruthCore.Causality.PostCutStore

/-! Finite unit-output traces in a closed store, and a comparison using a
fixed distribution over initial stock bounds. -/
@[expose] public section
noncomputable section
namespace TruthCore.Causality.FiniteReserveOdds

open TruthCore.Causality.PostCutStore

/-- The exact trace exports one energy unit per interval. Both boundary
feeds are zero, and the initial reserve is bounded by `capacity`. -/
def UnitTraceFits (capacity periods : ℕ) : Prop :=
  ∃ stock : ℕ → ℝ,
    ObservationLedger periods capacity (fun _ => 1) (fun _ => 0)
      stock (fun _ => 1) (fun _ => 0) (fun _ => 0)

/-- The deterministic reserve model gives likelihood one when the unit
trace fits and zero when it fails. Average that likelihood over the
conditional prior on finite bounds. -/
def reserveLikelihood (prior : ℕ → ℝ) (periods : ℕ) : ℝ := by
  classical
  exact ∑' capacity : ℕ, if UnitTraceFits capacity periods then prior capacity else 0

/-- A fixed geometric distribution on all natural capacities. -/
def geometricPrior (capacity : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ capacity

/-- Positive class weights are fixed across the observations, as is the
proper conditional prior on finite capacities. The comparison weight is
the class weight multiplied by its conditional likelihood. -/
def FiniteReserveComparison : Prop :=
  (∀ capacity periods : ℕ, UnitTraceFits capacity periods ↔ periods ≤ capacity) ∧
  (∀ prior : ℕ → ℝ, (∀ capacity, 0 ≤ prior capacity) → HasSum prior 1 →
    (∀ periods, reserveLikelihood prior periods = 1 - prefixSum prior periods) ∧
      ∀ (storedPrior suppliedPrior lower : ℝ) (storedLikelihood suppliedLikelihood : ℕ → ℝ),
        0 < storedPrior → 0 < suppliedPrior → 0 < lower →
        (∀ periods, 0 ≤ storedLikelihood periods ∧
          storedLikelihood periods ≤ reserveLikelihood prior periods) →
        (∀ periods, lower ≤ suppliedLikelihood periods ∧ suppliedLikelihood periods ≤ 1) →
        ∀ factor : ℝ, 0 < factor → ∃ start : ℕ, ∀ periods ≥ start,
          factor * (storedPrior * storedLikelihood periods) <
            suppliedPrior * suppliedLikelihood periods) ∧
  (HasSum geometricPrior 1 ∧ (∀ capacity, 0 < geometricPrior capacity) ∧
    ∀ periods,
      reserveLikelihood geometricPrior periods = (1 / 2 : ℝ) ^ periods ∧
        0 < reserveLikelihood geometricPrior periods ∧
        ∀ storedPrior suppliedWeight : ℝ, 0 < storedPrior → 0 < suppliedWeight →
          ¬ ∀ factor : ℝ, 0 < factor →
            factor * (storedPrior * reserveLikelihood geometricPrior periods) ≤ suppliedWeight)

end TruthCore.Causality.FiniteReserveOdds
