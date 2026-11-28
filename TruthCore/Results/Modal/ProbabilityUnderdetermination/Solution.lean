module

public import TruthCore.Modal.ProbabilityUnderdetermination
public import TruthCore.Results.Science.FineTuningInformation.Solution
import Mathlib.Tactic

@[expose] public section

namespace TruthCore.Results.Modal.ProbabilityUnderdetermination
open TruthCore.Modal
open TruthCore.Modal.ProbabilityUnderdetermination
open Set MeasureTheory ProbabilityTheory
open TruthCore.Science.FineTuningInformation.Plenitude (PointFullSupport InteriorRate)
open TruthCore.Results.Science.FineTuningInformation (arbitraryInteriorMass)
open scoped ENNReal Cardinal
universe u v

theorem noUniform : NoUniform.{u} := by
  intro W _ _ _ _ μ _ h
  obtain ⟨c, hc⟩ := h
  have hs : (∑' _ : W, c) = 1 := by
    simpa only [Measure.toPMF_apply, hc] using μ.toPMF.tsum_coe
  by_cases hz : c = 0
  · simp [hz] at hs
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at hs
    simp at hs

/-- Reuses the shared interior-mass lemma of #2143 at probability one third. -/
theorem equalCardinalityDifferent : EqualCardinalityDifferent.{u} := by
  intro W _ _ _ s _ _
  refine ⟨by rw [Cardinal.mk_eq_aleph0 s, Cardinal.mk_eq_aleph0 (sᶜ : Set W)], ?_⟩
  let third : InteriorRate := ⟨⟨1/3, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  obtain ⟨μ, hμ, hf, hp⟩ := arbitraryInteriorMass W s third
  refine ⟨μ, hμ, hf, ?_⟩
  intro he
  have hs : MeasurableSet s := (Set.to_countable s).measurableSet
  have h := measureReal_add_measureReal_compl (μ := μ) hs
  rw [probReal_univ, measureReal_def, measureReal_def, ← he, ← measureReal_def, hp] at h
  norm_num [third] at h

/-- A bijection carrying even indices to multiples of three. The remaining
indices are split between the two other residue classes. -/
def twoToThree : Equiv.Perm ℕ where
  toFun n := if n % 2 = 0 then 3*(n/2)
    else if n % 4 = 1 then 3*(n/4)+1 else 3*(n/4)+2
  invFun n := if n % 3 = 0 then 2*(n/3)
    else if n % 3 = 1 then 4*(n/3)+1 else 4*(n/3)+3
  left_inv := by intro n; dsimp only; split_ifs <;> omega
  right_inv := by intro n; dsimp only; split_ifs <;> omega

theorem twoToThree_mod (n : ℕ) : n % 2 = 0 ↔ twoToThree n % 3 = 0 := by
  change n % 2 = 0 ↔ (if n % 2 = 0 then 3*(n/2)
    else if n % 4 = 1 then 3*(n/4)+1 else 3*(n/4)+2) % 3 = 0
  split_ifs <;> omega

private def swapParity : Equiv.Perm ℕ where
  toFun n := if n % 2 = 0 then n+1 else n-1
  invFun n := if n % 2 = 0 then n+1 else n-1
  left_inv := by intro n; dsimp only; split_ifs <;> omega
  right_inv := by intro n; dsimp only; split_ifs <;> omega

private def cycleThree : Equiv.Perm ℕ where
  toFun n := if n % 3 = 2 then n-2 else n+1
  invFun n := if n % 3 = 0 then n+2 else n-1
  left_inv := by intro n; dsimp only; split_ifs <;> omega
  right_inv := by intro n; dsimp only; split_ifs <;> omega

private def residue (k r : ℕ) : Set ℕ := {n | n % k = r}

private theorem natAdditiveImpossible (m : Set ℕ → ℝ)
    (ha : NormalizedAdditive m) (hi : PermutationInvariant m) : False := by
  have hf : swapParity ⁻¹' residue 2 1 = residue 2 0 := by
    ext n
    change (if n % 2 = 0 then n+1 else n-1) % 2 = 1 ↔ n % 2 = 0
    split_ifs <;> omega
  have hc1 : cycleThree ⁻¹' residue 3 1 = residue 3 0 := by
    ext n
    change (if n % 3 = 2 then n-2 else n+1) % 3 = 1 ↔ n % 3 = 0
    split_ifs <;> omega
  have hc2 : cycleThree ⁻¹' residue 3 2 = residue 3 1 := by
    ext n
    change (if n % 3 = 2 then n-2 else n+1) % 3 = 2 ↔ n % 3 = 1
    split_ifs <;> omega
  have ht : twoToThree ⁻¹' residue 3 0 = residue 2 0 := by
    ext n
    exact (twoToThree_mod n).symm
  have h01 := hi swapParity (residue 2 1)
  have h02 := hi twoToThree (residue 3 0)
  have h03 := hi cycleThree (residue 3 1)
  have h04 := hi cycleThree (residue 3 2)
  rw [hf] at h01
  rw [ht] at h02
  rw [hc1] at h03
  rw [hc2] at h04
  have hd2 : Disjoint (residue 2 0) (residue 2 1) := by
    apply Set.disjoint_left.mpr
    intro n h₁ h₂
    change n % 2 = 0 at h₁
    change n % 2 = 1 at h₂
    omega
  have hu2 : residue 2 0 ∪ residue 2 1 = univ := by
    ext n
    change n % 2 = 0 ∨ n % 2 = 1 ↔ True
    exact iff_of_true (by omega) trivial
  have hd3 : Disjoint (residue 3 0) (residue 3 1) := by
    apply Set.disjoint_left.mpr
    intro n h₁ h₂
    change n % 3 = 0 at h₁
    change n % 3 = 1 at h₂
    omega
  have hd4 : Disjoint (residue 3 0 ∪ residue 3 1) (residue 3 2) := by
    apply Set.disjoint_left.mpr
    intro n h₁ h₂
    change n % 3 = 0 ∨ n % 3 = 1 at h₁
    change n % 3 = 2 at h₂
    omega
  have hu3 : residue 3 0 ∪ residue 3 1 ∪ residue 3 2 = univ := by
    ext n
    change (n % 3 = 0 ∨ n % 3 = 1) ∨ n % 3 = 2 ↔ True
    exact iff_of_true (by omega) trivial
  have h2 := ha.2 _ _ hd2
  have h3 := ha.2 _ _ hd3
  have h4 := ha.2 _ _ hd4
  rw [hu2, ha.1] at h2
  rw [hu3, ha.1, h3] at h4
  linarith

/-- Pull back the natural-number partitions along a bijection W ≃ W × ℕ.
No countable additivity or nonnegativity is used. -/
theorem noPermutationProbability : NoPermutationProbability.{u} := by
  intro W _ m ha hi
  classical
  obtain ⟨e⟩ : Nonempty (W ≃ W × ℕ) := Cardinal.eq.mp (by
    simp)
  let g : W → ℕ := fun x => (e x).2
  let q : Set ℕ → ℝ := fun s => m (g ⁻¹' s)
  have hqa : NormalizedAdditive q := by
    constructor
    · simpa [q] using ha.1
    · intro s t hd
      have hd' : Disjoint (g ⁻¹' s) (g ⁻¹' t) :=
        Set.disjoint_left.mpr (fun _ hs ht => Set.disjoint_left.mp hd hs ht)
      change m (g ⁻¹' (s ∪ t)) = m (g ⁻¹' s) + m (g ⁻¹' t)
      rw [Set.preimage_union]
      exact ha.2 _ _ hd'
  have hqi : PermutationInvariant q := by
    intro π s
    let σ : Equiv.Perm W := (e.trans ((Equiv.refl W).prodCongr π)).trans e.symm
    have heq : σ ⁻¹' (g ⁻¹' s) = g ⁻¹' (π ⁻¹' s) := by
      ext x
      simp [σ, g]
    change m (g ⁻¹' (π ⁻¹' s)) = m (g ⁻¹' s)
    rw [← heq]
    exact hi σ _
  exact natAdditiveImpossible q hqa hqi

theorem noAllSubsetsPermutationMeasure : NoAllSubsetsPermutationMeasure.{u} := by
  intro W _ _ μ _ hall hinv
  let m : Set W → ℝ := fun s => (μ s).toReal
  apply noPermutationProbability W m
  · constructor
    · simp [m]
    · intro s t hd
      change (μ (s ∪ t)).toReal = (μ s).toReal + (μ t).toReal
      rw [measure_union hd (hall t),
        ENNReal.toReal_add (measure_ne_top μ s) (measure_ne_top μ t)]
  · intro π s
    change (μ (π ⁻¹' s)).toReal = (μ s).toReal
    exact congrArg ENNReal.toReal (hinv π s)

theorem prefix_exhausts {W : Type u} (e : ℕ ≃ W) : Exhaustion (enumPrefix e) := by
  constructor
  · intro n m h x hx
    simp only [enumPrefix, Finset.mem_map, Finset.mem_range] at hx ⊢
    obtain ⟨i, hi, he⟩ := hx
    exact ⟨i, hi.trans_le h, he⟩
  · intro x
    refine ⟨e.symm x + 1, ?_⟩
    simp only [enumPrefix, Finset.mem_map, Finset.mem_range]
    exact ⟨e.symm x, Nat.lt_succ_self _, e.apply_symm_apply x⟩

private theorem countResidue (k n : ℕ) (hk : k = 2 ∨ k = 3) :
    ((Finset.range n).filter (fun i => i % k = 0)).card = (n+k-1)/k := by
  let emb : ℕ ↪ ℕ := ⟨fun i => k*i, by
    intro i j h
    change k*i = k*j at h
    rcases hk with h₂ | h₃ <;> subst k <;> omega⟩
  have heq : (Finset.range n).filter (fun i => i % k = 0) =
      (Finset.range ((n+k-1)/k)).map emb := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map]
    constructor
    · intro ⟨hx, hm⟩
      refine ⟨x/k, ?_, ?_⟩
      · rcases hk with h₂ | h₃ <;> subst k <;> omega
      · change k*(x/k) = x
        rcases hk with h₂ | h₃ <;> subst k <;> omega
    · rintro ⟨i, hi, rfl⟩
      change k*i < n ∧ k*i % k = 0
      rcases hk with h₂ | h₃ <;> subst k <;> omega
  rw [heq, Finset.card_map, Finset.card_range]

private theorem frequency_residue (s : Set ℕ) (e : ℕ ≃ ℕ) (k n : ℕ)
    (hk : k = 2 ∨ k = 3) (he : ∀ i, e i ∈ s ↔ i % k = 0) :
    frequency s (enumPrefix e n) = (((n+k-1)/k : ℕ) : ℝ) / n := by
  classical
  have heq : ((enumPrefix e n).filter (· ∈ s)) =
      ((Finset.range n).filter (fun i => i % k = 0)).map e.toEmbedding := by
    ext x
    simp only [enumPrefix, Finset.mem_filter, Finset.mem_map, Finset.mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hx⟩
      exact ⟨i, ⟨hi, (he i).mp hx⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hm⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, (he i).mpr hm⟩
  unfold frequency
  rw [heq, Finset.card_map, countResidue k n hk]
  simp [enumPrefix]

private theorem density_residue (s : Set ℕ) (e : ℕ ≃ ℕ) (k : ℕ)
    (hk : k = 2 ∨ k = 3) (he : ∀ i, e i ∈ s ↔ i % k = 0) :
    HasDensity s (enumPrefix e) (1/(k : ℝ)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1/ε : ℝ)
  refine ⟨N+1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hNk : (N : ℝ) < n := by exact_mod_cast (show N < n by omega)
  have hsmall : (1 : ℝ) / n < ε := by
    apply (div_lt_iff₀ hnR).mpr
    have hh := (div_lt_iff₀ hε).mp (hN.trans hNk)
    simpa [mul_comm] using hh
  have hl : n ≤ k*((n+k-1)/k) := by
    rcases hk with h₂ | h₃ <;> subst k <;> omega
  have hu : k*((n+k-1)/k) < n+k := by
    rcases hk with h₂ | h₃ <;> subst k <;> omega
  have hlR : (n : ℝ) ≤ (k : ℝ) * (((n+k-1)/k : ℕ) : ℝ) := by exact_mod_cast hl
  have huR : (k : ℝ) * (((n+k-1)/k : ℕ) : ℝ) < (n : ℝ)+k := by exact_mod_cast hu
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  rw [frequency_residue s e k n hk he]
  have hlow : (1 : ℝ)/k ≤ (((n+k-1)/k : ℕ) : ℝ)/n := by
    apply (div_le_div_iff₀ hkR hnR).mpr
    simpa [mul_comm] using hlR
  have hupper : (((n+k-1)/k : ℕ) : ℝ)/n - 1/k < 1/n := by
    have hbound : (((n+k-1)/k : ℕ) : ℝ) - (n : ℝ)/k < 1 := by
      have hdiv : (((n+k-1)/k : ℕ) : ℝ) < ((n : ℝ)+k)/k :=
        (lt_div_iff₀ hkR).mpr (by simpa [mul_comm] using huR)
      rw [add_div, div_self hkR.ne'] at hdiv
      linarith
    calc
      _ = ((((n+k-1)/k : ℕ) : ℝ) - (n : ℝ)/k)/n := by
        field_simp
      _ < 1/n := (div_lt_div_iff_of_pos_right hnR).mpr hbound
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  exact hupper.trans hsmall

theorem enumerationDependence : EnumerationDependence := by
  let s := residue 2 0
  refine ⟨s, Equiv.refl ℕ, twoToThree.symm,
    prefix_exhausts _, prefix_exhausts _, ?_, ?_⟩
  · exact density_residue s (Equiv.refl ℕ) 2 (Or.inl rfl) (fun _ => Iff.rfl)
  · apply density_residue s twoToThree.symm 3 (Or.inr rfl)
    intro i
    change twoToThree.symm i % 2 = 0 ↔ i % 3 = 0
    simpa using twoToThree_mod (twoToThree.symm i)

theorem continuousControl : ContinuousControl := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [unitMeasure, Measure.restrict_apply MeasurableSet.univ]
    simp
  · intro x
    rw [unitMeasure, Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null inter_subset_left Real.volume_singleton
  · intro t ht h1
    rw [unitMeasure, Measure.restrict_apply measurableSet_Icc]
    have heq : Icc (0 : ℝ) t ∩ Icc 0 1 = Icc 0 t :=
      inter_eq_left.mpr (fun _ hx => ⟨hx.1, hx.2.trans h1⟩)
    rw [heq, Real.volume_Icc, sub_zero]

theorem modalProbabilityFreedom : ModalProbabilityFreedom.{u,v} := by
  intro W Atom F V w φ _ _ _ _ _ p
  exact arbitraryInteriorMass _ (accessibleEvent F V w φ) p

end TruthCore.Results.Modal.ProbabilityUnderdetermination
