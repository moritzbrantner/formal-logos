module

public import TruthCore.Logic.EpistemicAccuracy.Refinement

/-!
Bayesian specialization of the existing binary-check accuracy comparison.
The joint-probability equations express one coherent binary hypothesis and
binary observation profile, without introducing another posterior API.
They are supplied inputs, not claims of actual calibration.
-/

@[expose] public section
namespace TruthCore.Logic.EpistemicAccuracy.BayesianRefinement

open TruthCore.Logic.EpistemicAccuracy.Refinement

/-- p is the prior of the fixed target; a,b are the likelihoods of E under
the target and its complement. w is the predictive probability of E, and u,v
are the posteriors on E and its complement. The two joint equations are
Bayes' rule with positive denominators cleared. The scaled gain identity
avoids division; w(1-w)>0 permits recovering the quotient. -/
def BayesianGainCertificate : Prop :=
  ∀ p a b w u v : ℝ,
    0 < p → p < 1 →
    0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
    0 < w → w < 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
    w = p*a + (1-p)*b →
    w*u = p*a → (1-w)*v = p*(1-a) →
    pooledCredence w u v = p ∧
    w*(1-w)*accuracyGain w u v = (p*(1-p)*(a-b))^2 ∧
    (accuracyGain w u v = 0 ↔ a = b)

end TruthCore.Logic.EpistemicAccuracy.BayesianRefinement
