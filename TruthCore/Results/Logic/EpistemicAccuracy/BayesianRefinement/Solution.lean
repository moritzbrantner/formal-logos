module

public import TruthCore.Logic.EpistemicAccuracy.BayesianRefinement

@[expose] public section
namespace TruthCore.Results.Logic.EpistemicAccuracy.BayesianRefinement
open TruthCore.Logic.EpistemicAccuracy.Refinement
open TruthCore.Logic.EpistemicAccuracy.BayesianRefinement

/-- Compose the existing check-value certificate with the coherent joint
probability equations. No actual prior, likelihood, or epistemic norm follows. -/
theorem bayesianGain (hCheck : CheckValueCertificate) : BayesianGainCertificate := by
  intro p a b w u v hp0 hp1 _ _ _ _ hw0 hw1 hu0 hu1 hv0 hv1 hm hu hv
  obtain ⟨hGain, _, _, _, hZero⟩ :=
    hCheck w u v (le_of_lt hw0) (le_of_lt hw1) hu0 hu1 hv0 hv1
  have hPool : pooledCredence w u v = p := by
    unfold pooledCredence
    rw [hu, hv]
    ring
  have hContrast : w*(1-w)*(u-v) = p*(1-p)*(a-b) := by
    calc
      w*(1-w)*(u-v) = w*u - w*pooledCredence w u v := by
        unfold pooledCredence
        ring
      _ = p*a - w*p := by rw [hu, hPool]
      _ = p*(1-p)*(a-b) := by
        rw [hm]
        ring
  have hpProd : 0 < p*(1-p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hwProd : 0 < w*(1-w) := mul_pos hw0 (sub_pos.mpr hw1)
  have hDiff : u = v ↔ a = b := by
    constructor
    · intro huv
      have hz : p*(1-p)*(a-b) = 0 := by
        rw [← hContrast, huv, sub_self, mul_zero]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hpProd))
    · intro hab
      have hz : w*(1-w)*(u-v) = 0 := by
        rw [hContrast, hab, sub_self, mul_zero]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hwProd))
  refine ⟨hPool, ?_, ?_⟩
  · calc
      w*(1-w)*accuracyGain w u v = (w*(1-w)*(u-v))^2 := by
        rw [hGain]
        ring
      _ = (p*(1-p)*(a-b))^2 := by rw [hContrast]
  · constructor
    · intro hz
      rcases hZero.mp hz with h | h | h
      · exact (ne_of_gt hw0 h).elim
      · exact (ne_of_lt hw1 h).elim
      · exact hDiff.mp h
    · intro hab
      exact hZero.mpr (Or.inr (Or.inr (hDiff.mpr hab)))

end TruthCore.Results.Logic.EpistemicAccuracy.BayesianRefinement
