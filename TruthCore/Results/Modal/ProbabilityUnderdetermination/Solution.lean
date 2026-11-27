module

public import TruthCore.Modal.ProbabilityUnderdetermination
import Mathlib.Tactic

@[expose] public section

namespace TruthCore.Results.Modal.ProbabilityUnderdetermination
open TruthCore.Modal
open TruthCore.Modal.ProbabilityUnderdetermination
open Set MeasureTheory ProbabilityTheory
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
    exact ENNReal.top_ne_one hs

private noncomputable def natEquiv (W : Type u) [Countable W] [Infinite W] :
    ℕ ≃ W :=
  Classical.choice (Cardinal.lift_mk_eq'.mp (by
    simp [Cardinal.mk_nat, Cardinal.mk_eq_aleph0 W]))

private noncomputable def half : unitInterval :=
  ⟨1/2, by constructor <;> norm_num⟩

private noncomputable def geom : Measure ℕ := geometricMeasure half

private theorem geom_mass_pos (n : ℕ) : 0 < geom {n} := by
  have h0 : half ≠ 0 := by
    intro h
    have h' := congrArg (fun x : unitInterval => (x : ℝ)) h
    norm_num [half] at h'
  have h1 : half ≠ 1 := by
    intro h
    have h' := congrArg (fun x : unitInterval => (x : ℝ)) h
    norm_num [half] at h'
  rw [geom, geometricMeasure_singleton h0]
  exact ENNReal.ofReal_pos.mpr (geometricMeasure_pos h0 h1 n)

private theorem geom_univ : geom univ = 1 := by
  unfold geom
  exact measure_univ

private theorem map_mass_pos {W : Type u} [MeasurableSpace W]
    [MeasurableSingletonClass W] (f : ℕ → W) (x : W) (h : ∃ n, f n = x) :
    0 < (geom.map f) {x} := by
  obtain ⟨n, hn⟩ := h
  rw [Measure.map_apply (measurable_of_countable f) (measurableSet_singleton x)]
  apply lt_of_lt_of_le (geom_mass_pos n)
  apply measure_mono
  intro i hi
  have hi' : i = n := by simpa using hi
  simpa [hi', hn]

theorem arbitraryProbability : ArbitraryProbability.{u} := by
  intro W _ _ _ s _ _ p hp0 hp1
  classical
  let e := natEquiv s
  let f := natEquiv (sᶜ : Set W)
  let l : ℕ → W := fun n => (e n).val
  let r : ℕ → W := fun n => (f n).val
  let a := geom.map l
  let b := geom.map r
  have hs : MeasurableSet s := (Set.to_countable s).measurableSet
  have ha : a univ = 1 := by
    rw [a, Measure.map_apply (measurable_of_countable l) MeasurableSet.univ]
    simpa using geom_univ
  have hb : b univ = 1 := by
    rw [b, Measure.map_apply (measurable_of_countable r) MeasurableSet.univ]
    simpa using geom_univ
  have hls : l ⁻¹' s = univ := by
    ext n
    simp only [mem_preimage, mem_univ, iff_true]
    exact (e n).property
  have hrs : r ⁻¹' s = ∅ := by
    ext n
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact (f n).property
  have has : a s = 1 := by
    rw [a, Measure.map_apply (measurable_of_countable l) hs, hls, geom_univ]
  have hbs : b s = 0 := by
    rw [b, Measure.map_apply (measurable_of_countable r) hs, hrs, measure_empty]
  refine ⟨p • a + (1-p) • b, ?_, ?_, ?_⟩
  · constructor
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, ha, hb, mul_one]
    rw [add_comm p, tsub_add_cancel_of_le hp1.le]
  · intro x
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ s
    · have h : 0 < a {x} :=
        map_mass_pos l x ⟨e.symm ⟨x, hx⟩, by simp [l]⟩
      exact lt_of_lt_of_le (mul_pos hp0 h) le_self_add
    · have h : 0 < b {x} :=
        map_mass_pos r x ⟨f.symm ⟨x, hx⟩, by simp [r]⟩
      have hq : 0 < (1-p : ℝ≥0∞) := tsub_pos_of_lt hp1
      exact lt_of_lt_of_le (mul_pos hq h) le_add_self
  · simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul, has, hbs]

theorem equalCardinalityDifferent : EqualCardinalityDifferent.{u} := by
  intro W _ _ _ s _ _
  refine ⟨by rw [Cardinal.mk_eq_aleph0 s, Cardinal.mk_eq_aleph0 (sᶜ : Set W)], ?_⟩
  obtain ⟨μ, hμ, hf, hp⟩ :=
    arbitraryProbability W s (1/3) (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure μ := hμ
  refine ⟨μ, hμ, hf, ?_⟩
  intro he
  have h := measure_add_measure_compl (μ := μ) (Set.to_countable s).measurableSet
  rw [measure_univ, ← he, hp] at h
  norm_num at h

/-- A bijection carrying even indices to multiples of three. The remaining
indices are split between the two other residue classes. -/
def twoToThree : Equiv.Perm ℕ where
  toFun n := if n % 2 = 0 then 3*(n/2)
    else if n % 4 = 1 then 3*(n/4)+1 else 3*(n/4)+2
  invFun n := if n % 3 = 0 then 2*(n/3)
    else if n % 3 = 1 then 4*(n/3)+1 else 4*(n/3)+3
  left_inv := by intro n; split_ifs <;> omega
  right_inv := by intro n; split_ifs <;> omega

theorem twoToThree_mod (n : ℕ) : n % 2 = 0 ↔ twoToThree n % 3 = 0 := by
  change n % 2 = 0 ↔ (if n % 2 = 0 then 3*(n/2)
    else if n % 4 = 1 then 3*(n/4)+1 else 3*(n/4)+2) % 3 = 0
  split_ifs <;> omega

private def flip : Equiv.Perm ℕ where
  toFun n := if n % 2 = 0 then n+1 else n-1
  invFun n := if n % 2 = 0 then n+1 else n-1
  left_inv := by intro n; split_ifs <;> omega
  right_inv := by intro n; split_ifs <;> omega

private def cycle : Equiv.Perm ℕ where
  toFun n := if n % 3 = 2 then n-2 else n+1
  invFun n := if n % 3 = 0 then n+2 else n-1
  left_inv := by intro n; split_ifs <;> omega
  right_inv := by intro n; split_ifs <;> omega

private def residue (k r : ℕ) : Set ℕ := {n | n % k = r}

private theorem natAdditiveImpossible (m : Set ℕ → ℝ)
    (ha : NormalizedAdditive m) (hi : PermutationInvariant m) : False := by
  have hf : flip ⁻¹' residue 2 1 = residue 2 0 := by
    ext n
    change (if n % 2 = 0 then n+1 else n-1) % 2 = 1 ↔ n % 2 = 0
    split_ifs <;> omega
  have hc1 : cycle ⁻¹' residue 3 1 = residue 3 0 := by
    ext n
    change (if n % 3 = 2 then n-2 else n+1) % 3 = 1 ↔ n % 3 = 0
    split_ifs <;> omega
  have hc2 : cycle ⁻¹' residue 3 2 = residue 3 1 := by
    ext n
    change (if n % 3 = 2 then n-2 else n+1) % 3 = 2 ↔ n % 3 = 1
    split_ifs <;> omega
  have ht : twoToThree ⁻¹' residue 3 0 = residue 2 0 := by
    ext n
    exact (twoToThree_mod n).symm
  have h01 := hi flip (residue 2 1)
  have h02 := hi twoToThree (residue 3 0)
  have h03 := hi cycle (residue 3 1)
  have h04 := hi cycle (residue 3 2)
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
    omega
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
    omega
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
    simpa [Cardinal.mk_nat] using (Cardinal.mk_mul_aleph0_eq (α := W)).symm)
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
    rw [hinv π s]

theorem prefix_exhausts {W : Type u} (e : ℕ ≃ W) : Exhaustion (prefix e) := by
  constructor
  · intro n m h x hx
    simp only [prefix, Finset.mem_map, Finset.mem_range] at hx ⊢
    obtain ⟨i, hi, he⟩ := hx
    exact ⟨i, hi.trans_le h, he⟩
  · intro x
    refine ⟨e.symm x + 1, ?_⟩
    simp only [prefix, Finset.mem_map, Finset.mem_range]
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
    frequency s (prefix e n) = (((n+k-1)/k : ℕ) : ℝ) / n := by
  classical
  have heq : ((prefix e n).filter (· ∈ s)) =
      ((Finset.range n).filter (fun i => i % k = 0)).map e.toEmbedding := by
    ext x
    simp only [prefix, Finset.mem_filter, Finset.mem_map, Finset.mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hx⟩
      exact ⟨i, ⟨hi, (he i).mp hx⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hm⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, (he i).mpr hm⟩
  unfold frequency
  rw [heq, Finset.card_map, countResidue k n hk]
  simp [prefix]

private theorem density_residue (s : Set ℕ) (e : ℕ ≃ ℕ) (k : ℕ)
    (hk : k = 2 ∨ k = 3) (he : ∀ i, e i ∈ s ↔ i % k = 0) :
    HasDensity s (prefix e) (1/(k : ℝ)) := by
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
      rw [sub_lt_iff_lt_add, ← div_add_one hkR.ne']
      apply (lt_div_iff₀ hkR).mpr
      simpa [mul_comm] using huR
    calc
      _ = ((((n+k-1)/k : ℕ) : ℝ) - (n : ℝ)/k)/n := by field_simp
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
    apply le_antisymm _ (zero_le _)
    calc
      volume ({x} ∩ Icc (0 : ℝ) 1) ≤ volume {x} := measure_mono inter_subset_left
      _ = 0 := Real.volume_singleton
  · intro t ht h1
    rw [unitMeasure, Measure.restrict_apply measurableSet_Icc]
    have heq : Icc (0 : ℝ) t ∩ Icc 0 1 = Icc 0 t :=
      inter_eq_left.mpr (fun _ hx => ⟨hx.1, hx.2.trans h1⟩)
    rw [heq, Real.volume_Icc, sub_zero]

theorem modalProbabilityFreedom : ModalProbabilityFreedom.{u,v} := by
  intro W Atom F V w φ _ _ _ _ _ p hp0 hp1
  exact arbitraryProbability _ (accessibleEvent F V w φ) p hp0 hp1

end TruthCore.Results.Modal.ProbabilityUnderdetermination
