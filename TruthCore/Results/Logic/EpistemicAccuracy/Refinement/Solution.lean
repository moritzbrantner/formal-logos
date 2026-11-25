module

public import TruthCore.Logic.EpistemicAccuracy.Refinement

@[expose] public section
namespace TruthCore.Results.Logic.EpistemicAccuracy.Refinement
open TruthCore.Logic.EpistemicAccuracy
open TruthCore.Logic.EpistemicAccuracy.Refinement

/-- Conditional numerical comparison, not an epistemic entitlement norm. -/
theorem checkValue : CheckValueCertificate := by
  intro w u v hw0 hw1 hu0 hu1 hv0 hv1
  have heq : accuracyGain w u v = w * (1 - w) * (u - v)^2 := by
    unfold accuracyGain pooledCredence error
    ring
  have hw' : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  have hnonneg : 0 ≤ accuracyGain w u v := by
    rw [heq]
    exact mul_nonneg (mul_nonneg hw0 hw') (sq_nonneg _)
  have herr (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ error q q := by
    unfold error
    exact add_nonneg (mul_nonneg hq0 (sq_nonneg _))
      (mul_nonneg (sub_nonneg.mpr hq1) (sq_nonneg _))
  have hupper : accuracyGain w u v ≤
      error (pooledCredence w u v) (pooledCredence w u v) := by
    unfold accuracyGain
    exact sub_le_self _ (add_nonneg (mul_nonneg hw0 (herr u hu0 hu1))
      (mul_nonneg hw' (herr v hv0 hv1)))
  have hmax (q : ℝ) : error q q ≤ 1/4 := by
    have hid : error q q = q * (1-q) := by
      unfold error
      ring
    rw [hid]
    nlinarith [sq_nonneg (q - 1/2)]
  refine ⟨heq, hnonneg, hupper, hmax _, ?_⟩
  rw [heq]
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by linarith))
    · rw [pow_two] at h
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inr (Or.inr (sub_eq_zero.mp h))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  · rintro (h | h | h) <;> rw [h] <;> ring

end TruthCore.Results.Logic.EpistemicAccuracy.Refinement
