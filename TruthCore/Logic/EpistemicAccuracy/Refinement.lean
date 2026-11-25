module

public import TruthCore.Logic.EpistemicAccuracy

/-!
Analyst refinement comparison: one fixed binary target, one coherent supplied
probability assessment, and a check with two possible outcomes. The expected
accuracy gain measures the difference between optimal squared error before
and after the check. No calibration, cost threshold, authority or duty to
investigate is assumed.
-/

@[expose] public section
namespace TruthCore.Logic.EpistemicAccuracy.Refinement

open TruthCore.Logic.EpistemicAccuracy

noncomputable def pooledCredence (w u v : ℝ) : ℝ :=
  w * u + (1 - w) * v

/-- Expected reduction of the optimal binary squared error under the supplied
assessment. Here w and 1-w weight the two outcomes and u,v are conditional
truth probabilities for the SAME target. The pooled prior uses those very
weights, not an independently assigned incompatible prior. -/
noncomputable def accuracyGain (w u v : ℝ) : ℝ :=
  error (pooledCredence w u v) (pooledCredence w u v) -
    (w * error u u + (1 - w) * error v v)

/-- Exact gain, finite upper budget and zero-gain boundary. Zero gain for the
selected target says nothing about another target, actual access to the
evidence, the legitimacy of an objection, or a universal stopping norm. -/
def CheckValueCertificate : Prop :=
  ∀ w u v : ℝ, 0 ≤ w → w ≤ 1 → 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
    accuracyGain w u v = w * (1 - w) * (u - v)^2 ∧
    0 ≤ accuracyGain w u v ∧
    accuracyGain w u v ≤ error (pooledCredence w u v) (pooledCredence w u v) ∧
    error (pooledCredence w u v) (pooledCredence w u v) ≤ 1/4 ∧
    (accuracyGain w u v = 0 ↔ w = 0 ∨ w = 1 ∨ u = v)

end TruthCore.Logic.EpistemicAccuracy.Refinement
