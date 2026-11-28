module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.Linarith

/-!
# Normalized laws on a two-point outcome space

Shared mathematical vocabulary for the probability-law diagnostics of #2144
(`TruthCore.Causality.WillVersusChance`, where `true` is the withholding
history of its fixed giver) and #2151 (`TruthCore.Explanation.ObjectiveProbability`,
where the two points are physical outcomes). The interpretation of the two
points belongs to each user; this module fixes only the mathematics: a Mathlib
`PMF Bool` with supplied masses, and the fact that a binary law is fixed by one
mass. No propensity, causal power or metaphysical possibility is encoded.
-/

@[expose] public section

namespace TruthCore.Explanation.BinaryLaw

open scoped ENNReal

/-- The normalized law on `Bool` with mass `p` at `true` and `q` at `false`. -/
noncomputable def binaryLaw (p q : ℝ≥0∞) (h : p + q = 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then p else q) (by
    rw [Fintype.sum_bool]
    simpa using h)

theorem binaryLaw_true (p q : ℝ≥0∞) (h : p + q = 1) : binaryLaw p q h true = p := by
  simp [binaryLaw, PMF.ofFintype_apply]

theorem binaryLaw_false (p q : ℝ≥0∞) (h : p + q = 1) : binaryLaw p q h false = q := by
  simp [binaryLaw, PMF.ofFintype_apply]

/-- The two masses of any law on `Bool` sum to one. -/
theorem binary_sum (μ : PMF Bool) : μ true + μ false = 1 := by
  simpa only [tsum_fintype, Fintype.sum_bool] using μ.tsum_coe

/-- The same normalization, in real numbers. -/
theorem binary_real_sum (μ : PMF Bool) :
    (μ true).toReal + (μ false).toReal = 1 := by
  have h := congrArg ENNReal.toReal (binary_sum μ)
  simpa only [ENNReal.toReal_add (μ.apply_ne_top true) (μ.apply_ne_top false),
    ENNReal.toReal_one] using h

/-- A law on `Bool` is fixed by its mass at `true` (normalization). -/
theorem binary_unique_of_mass (μ ν : PMF Bool) (h : μ true = ν true) : μ = ν := by
  apply PMF.ext
  intro b
  cases b
  · have ht := congrArg ENNReal.toReal h
    have hf : (μ false).toReal = (ν false).toReal := by
      linarith [binary_real_sum μ, binary_real_sum ν]
    simpa only [ENNReal.ofReal_toReal (μ.apply_ne_top false),
      ENNReal.ofReal_toReal (ν.apply_ne_top false)] using congrArg ENNReal.ofReal hf
  · exact h

/-- Real-valued form: a law on `Bool` is fixed by the real value of its mass at `true`. -/
theorem binary_unique_of_real_mass (μ ν : PMF Bool)
    (h : (μ true).toReal = (ν true).toReal) : μ = ν :=
  binary_unique_of_mass μ ν
    ((ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top true) (ν.apply_ne_top true)).mp h)

end TruthCore.Explanation.BinaryLaw
