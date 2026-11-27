module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.CompProdEqIff
public import TruthCore.Logic.InformationInvariance

/-!
Finite observation profiles use discrete measurable spaces and normalized
Mathlib probability measures. Shannon entropy uses natural logarithms (nats).
Zero-mass summands contribute zero, including when the whole fiber is null.
-/

@[expose] public section

namespace TruthCore.Logic.FiniteInformation

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

variable {S X Y Z : Type*} [MeasurableSpace S]

/-- Shannon entropy of a finite discrete distribution, in nats. -/
noncomputable def entropy [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] : ℝ :=
  -∑ x, μ.real {x} * Real.log (μ.real {x})

/-- Conditional Shannon entropy of a deterministic target given a deterministic
observation. Summing over states weights the conditional surprisal by the
joint target-observation law, since it is constant on each joint fiber. -/
noncomputable def conditionalEntropy [Fintype S] [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] (target : S → X) (observe : S → Y) : ℝ :=
  ∑ s, μ.real {s} *
    (-Real.log (μ.real (target ⁻¹' {target s} ∩ observe ⁻¹' {observe s}) /
      μ.real (observe ⁻¹' {observe s})))

private theorem null_iff_singletons [Fintype S] [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] (a : Set S) :
    μ.real a = 0 ↔ ∀ s ∈ a, μ.real {s} = 0 := by
  classical
  refine ⟨fun h s hs => measureReal_mono_null (singleton_subset_iff.mpr hs) h, ?_⟩
  intro h
  rw [← a.toFinite.coe_toFinset, ← sum_measureReal_singleton]
  exact Finset.sum_eq_zero fun s hs => h s (by simpa using hs)

/-- Zero residual uncertainty is exactly target invariance on positive-mass
observation fibers. Null states can violate invariance without affecting loss. -/
theorem conditionalEntropy_eq_zero_iff [Fintype S] [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] (target : S → X) (observe : S → Y) :
    conditionalEntropy μ target observe = 0 ↔
      ∀ s t, 0 < μ.real {s} → 0 < μ.real {t} → observe s = observe t →
        target s = target t := by
  classical
  let a := fun s => target ⁻¹' {target s} ∩ observe ⁻¹' {observe s}
  let b := fun s => observe ⁻¹' {observe s}
  have hab (s : S) : a s ⊆ b s := inter_subset_right
  have hsa (s : S) : {s} ⊆ a s := singleton_subset_iff.mpr ⟨rfl, rfl⟩
  have hle (s : S) : μ.real (a s) ≤ μ.real (b s) := measureReal_mono (hab s)
  have hnonneg (s : S) : 0 ≤ μ.real {s} *
      (-Real.log (μ.real (a s) / μ.real (b s))) := by
    refine mul_nonneg measureReal_nonneg (neg_nonneg.mpr (Real.log_nonpos
      (div_nonneg measureReal_nonneg measureReal_nonneg) ?_))
    by_cases hb : 0 < μ.real (b s)
    · exact (div_le_one hb).mpr (hle s)
    · rw [le_antisymm (le_of_not_gt hb) measureReal_nonneg, div_zero]
      exact zero_le_one
  change (∑ s, μ.real {s} * (-Real.log (μ.real (a s) / μ.real (b s)))) = 0 ↔ _
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hnonneg s)]
  have hcell (s : S) (hs : 0 < μ.real {s}) :
      μ.real {s} * (-Real.log (μ.real (a s) / μ.real (b s))) = 0 ↔
        μ.real (b s \ a s) = 0 := by
    have ha := hs.trans_le (measureReal_mono (hsa s))
    have hb := ha.trans_le (hle s)
    have hadd := measureReal_sdiff (μ := μ) (hab s)
      (Set.to_countable (a s)).measurableSet
    rw [mul_eq_zero, or_iff_right hs.ne', neg_eq_zero]
    constructor
    · intro h
      have hratio := Real.eq_one_of_pos_of_log_eq_zero (div_pos ha hb) h
      rw [(div_eq_one_iff_eq hb.ne').mp hratio, sub_self] at hadd
      exact hadd
    · intro h
      rw [h, eq_comm, sub_eq_zero] at hadd
      rw [hadd, div_self ha.ne', Real.log_one]
  constructor
  · intro hz s t hs ht hobs
    have hnull := (hcell s hs).mp (hz s (Finset.mem_univ s))
    by_contra hne
    have htmem : t ∈ b s \ a s := ⟨hobs.symm, fun hm => hne hm.1.symm⟩
    exact ht.ne' ((null_iff_singletons μ _).mp hnull t htmem)
  · intro hinv s _
    by_cases hs : 0 < μ.real {s}
    · apply (hcell s hs).mpr
      refine (null_iff_singletons μ _).mpr fun t ht => ?_
      by_contra hne
      have htpos := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
      exact ht.2 ⟨(hinv s t hs htpos ht.1.symm).symm, ht.1⟩
    · rw [le_antisymm (le_of_not_gt hs) measureReal_nonneg, zero_mul]

/-- Apply the existing logical factor criterion to each target value on the
positive-mass subtype. A classifier is required only on supported states. -/
theorem conditionalEntropy_eq_zero_iff_classifiers [Fintype S] [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] (target : S → X) (observe : S → Y) :
    conditionalEntropy μ target observe = 0 ↔
      ∀ x : X, ∃ classifier : Y → Prop,
        ∀ s, 0 < μ.real {s} → (classifier (observe s) ↔ target s = x) := by
  rw [conditionalEntropy_eq_zero_iff]
  constructor
  · intro h x
    obtain ⟨c, hc⟩ := (InformationInvariance.factor_iff
      (fun s : {s // 0 < μ.real {s}} => observe s)
      (fun s => target s = x)).mpr
        (fun s t eq => by rw [h s t s.property t.property eq])
    exact ⟨c, fun s hs => hc ⟨s, hs⟩⟩
  · intro h s t hs ht eq
    obtain ⟨c, hc⟩ := h (target t)
    exact (hc s hs).mp (eq ▸ (hc t ht).mpr rfl)

variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Mutual information in nats: KL divergence from the product of the
two marginals. The extended nonnegative codomain follows Mathlib's KL API. -/
noncomputable def mutualInformation (joint : Measure (X × Y))
    [IsProbabilityMeasure joint] : ℝ≥0∞ :=
  klDiv joint ((joint.map Prod.fst).prod (joint.map Prod.snd))

theorem mutualInformation_nonneg (joint : Measure (X × Y))
    [IsProbabilityMeasure joint] : 0 ≤ mutualInformation joint := zero_le

/-- The finite discrete profile has finite KL divergence: any positive joint
cell gives positive mass to both of its marginal singletons. -/
theorem mutualInformation_ne_top [Fintype X] [Fintype Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (joint : Measure (X × Y)) [IsProbabilityMeasure joint] :
    mutualInformation joint ≠ ∞ := by
  refine klDiv_ne_top_iff.mpr ⟨?_, Integrable.of_finite⟩
  intro a ha
  apply (measureReal_eq_zero_iff (measure_ne_top joint a)).mp
  apply (null_iff_singletons joint a).mpr
  rintro ⟨x, y⟩ hxy
  have hz := measure_mono_null (singleton_subset_iff.mpr hxy) ha
  rw [← singleton_prod_singleton, Measure.prod_prod] at hz
  rcases mul_eq_zero.mp hz with h | h
  · rw [Measure.map_apply measurable_fst (measurableSet_singleton _)] at h
    have hs : ({(x, y)} : Set (X × Y)) ⊆ Prod.fst ⁻¹' {x} := singleton_subset_iff.mpr rfl
    rw [measureReal_def, measure_mono_null hs h, ENNReal.toReal_zero]
  · rw [Measure.map_apply measurable_snd (measurableSet_singleton _)] at h
    have hs : ({(x, y)} : Set (X × Y)) ⊆ Prod.snd ⁻¹' {y} := singleton_subset_iff.mpr rfl
    rw [measureReal_def, measure_mono_null hs h, ENNReal.toReal_zero]

/-- Independence is equality of the joint law with the product of its marginals. -/
theorem mutualInformation_eq_zero_iff (joint : Measure (X × Y))
    [IsProbabilityMeasure joint] :
    mutualInformation joint = 0 ↔
      joint = (joint.map Prod.fst).prod (joint.map Prod.snd) := by
  exact klDiv_eq_zero_iff

/-- Under a normalized prior and Markov observation kernel, exactly the
positive-prior rows must agree for zero mutual information. -/
theorem kernel_information_eq_zero_iff [Finite X] [MeasurableSingletonClass X]
    [MeasurableSpace.CountablyGenerated Y] (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    mutualInformation (μ ⊗ₘ κ) = 0 ↔
      ∀ x, μ {x} ≠ 0 → κ x = (μ ⊗ₘ κ).map Prod.snd := by
  rw [mutualInformation_eq_zero_iff]
  change (μ ⊗ₘ κ) = (μ ⊗ₘ κ).fst.prod ((μ ⊗ₘ κ).map Prod.snd) ↔ _
  rw [Measure.fst_compProd,
    ← Measure.compProd_const, Kernel.compProd_eq_iff]
  change (∀ᵐ x ∂μ, κ x = Kernel.const X ((μ ⊗ₘ κ).map Prod.snd) x) ↔ _
  rw [ae_iff_of_countable]
  simp only [Kernel.const_apply]

/-- Data processing for deterministic postprocessing of the observation. -/
theorem mutualInformation_map_le (joint : Measure (X × Y))
    [IsProbabilityMeasure joint] (f : Y → Z) (hf : Measurable f) :
    mutualInformation (joint.map (Prod.map id f)) ≤ mutualInformation joint := by
  have hm : Measurable (Prod.map (id : X → X) f) := measurable_id.prodMap hf
  simp only [mutualInformation, Measure.map_map measurable_fst hm,
    Measure.map_map measurable_snd hm]
  change klDiv (joint.map (Prod.map id f))
    ((joint.map Prod.fst).prod (joint.map (f ∘ Prod.snd))) ≤ _
  have hprod : (((joint.map Prod.fst).prod (joint.map Prod.snd)).map (Prod.map id f)) =
      (joint.map Prod.fst).prod (joint.map (f ∘ Prod.snd)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id,
      Measure.map_map hf measurable_snd]
  rw [← hprod]
  exact klDiv_map_le _ _ hm

end TruthCore.Logic.FiniteInformation
