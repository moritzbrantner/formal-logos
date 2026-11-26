module

public import Mathlib.Analysis.SpecificLimits.Basic

/-! Conditional Bayesian and prefix-weight comparisons for a finite hypothesis
and an infinite regress hypothesis. The common evidence likelihood and the
assignment of independent costs to commitments are application assumptions. -/

@[expose] public section
noncomputable section
namespace TruthCore.Causality.OccamRegress

/-- The posterior of the focal hypothesis in a two-hypothesis comparison
with a common likelihood. Prior weights can be normalized together. -/
def posteriorWeight (focal other likelihood : ℝ) : ℝ :=
  focal * likelihood / (focal * likelihood + other * likelihood)

/-- Every positive real odds ratio is realized by some normalized positive
priors at any fixed common positive likelihood. -/
def EqualLikelihoodOdds : Prop :=
  (∀ finite infinite likelihood : ℝ,
    0 < finite → 0 < infinite → 0 < likelihood →
    0 < posteriorWeight finite infinite likelihood ∧
    0 < posteriorWeight infinite finite likelihood ∧
    posteriorWeight finite infinite likelihood / posteriorWeight infinite finite likelihood =
      finite / infinite) ∧
  (∀ odds likelihood : ℝ, 0 < odds → 0 < likelihood →
    ∃ finite infinite : ℝ, 0 < finite ∧ 0 < infinite ∧ finite + infinite = 1 ∧
      posteriorWeight finite infinite likelihood / posteriorWeight infinite finite likelihood =
        odds)

/-- A comparison defined by multiplication has a value even at zero rival
weight, where division would not represent ordinary odds. -/
def UnboundedPreference : Prop :=
  ∀ finite infinite : ℝ, 0 < finite → 0 ≤ infinite →
    ((∀ factor : ℝ, 0 < factor → factor * infinite ≤ finite) ↔ infinite = 0)

/-- The whole hypothesis is contained in each prefix event of a single prior
model. Each extension incurs a conditional weight at most the same q < 1.
The recurrence on prefix weights makes sense even for a zero-weight prefix. -/
def UniformPrefixDiscount : Prop :=
  ∀ (weight q : ℝ) (prefixWeight : ℕ → ℝ),
    0 ≤ weight → 0 ≤ q → q < 1 → prefixWeight 0 ≤ 1 →
    (∀ n, prefixWeight (n + 1) ≤ q * prefixWeight n) →
    (∀ n, weight ≤ prefixWeight n) → weight = 0

/-- A single charge for a shared law yields a coherent prefix-weight profile
at every depth. Prefix zero is unrestricted and every positive-length prefix
coincides with the same law event in this model. -/
def SharedLawCharge : Prop :=
  ∀ charge : ℝ, 0 < charge → charge ≤ 1 →
    ∃ prefixWeight : ℕ → ℝ, prefixWeight 0 = 1 ∧ prefixWeight 1 = charge ∧
      (∀ n, prefixWeight (n + 2) = prefixWeight (n + 1)) ∧
      (∀ n, charge ≤ prefixWeight n) ∧
      ¬ ∃ q : ℝ, q < 1 ∧ ∀ n, prefixWeight (n + 1) ≤ q * prefixWeight n

end TruthCore.Causality.OccamRegress
