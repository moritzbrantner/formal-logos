module

public import TruthCore.Explanation.ObjectiveProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! Objective probability laws (#2151): determination controls, the law fork
under the contingent-fact PSR, and realization/sample controls. Analyst
formulations, attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Explanation.ObjectiveProbability

open TruthCore.Explanation.ObjectiveProbability
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.BinaryLaw
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.STIT
open scoped ENNReal

/-! ### Symmetry -/

theorem invariant_const_of_transitive {E : Type} (G : Set (Equiv.Perm E))
    (hG : ActsTransitively G) (μ : PMF E) (hμ : Invariant G μ) (x y : E) : μ y = μ x := by
  obtain ⟨g, hg, rfl⟩ := hG x y
  exact hμ g hg x

theorem invariant_mass_of_transitive {E : Type} [Fintype E] [Nonempty E]
    (G : Set (Equiv.Perm E)) (hG : ActsTransitively G) (μ : PMF E) (hμ : Invariant G μ)
    (x : E) : μ x = (Fintype.card E : ℝ≥0∞)⁻¹ := by
  have hsum : ∑ y, μ y = 1 := by simpa [tsum_fintype] using μ.tsum_coe
  have hconst : ∑ y, μ y = (Fintype.card E : ℝ≥0∞) * μ x := by
    rw [Finset.sum_congr rfl (fun y _ => invariant_const_of_transitive G hG μ hμ x y)]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hconst] at hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)

theorem uniform_invariant {E : Type} [Fintype E] [Nonempty E] (G : Set (Equiv.Perm E)) :
    Invariant G (uniformLaw E) := by
  intro g _ x
  simp [uniformLaw, PMF.ofFintype_apply]

theorem unique_invariant_of_transitive {E : Type} [Fintype E] [Nonempty E]
    (G : Set (Equiv.Perm E)) (hG : ActsTransitively G) :
    ∃! μ : PMF E, Invariant G μ := by
  refine ⟨uniformLaw E, uniform_invariant G, ?_⟩
  intro μ hμ
  apply PMF.ext
  intro x
  rw [invariant_mass_of_transitive G hG μ hμ x, uniformLaw, PMF.ofFintype_apply]

theorem firstPreserving_not_transitive : ¬ ActsTransitively firstPreserving := by
  intro h
  obtain ⟨g, hg, hgx⟩ := h (true, true) (false, true)
  rcases hg with rfl | rfl
  · simp at hgx
  · simp [flipSecond] at hgx

theorem orbitLaw_apply (p q : ℝ≥0∞) (h : p + q = 1) (x : Bool × Bool) :
    orbitLaw p q h x = if x.1 then p / 2 else q / 2 := by
  simp [orbitLaw, PMF.ofFintype_apply]

theorem orbitLaw_invariant (p q : ℝ≥0∞) (h : p + q = 1) :
    Invariant firstPreserving (orbitLaw p q h) := by
  intro g hg x
  rcases hg with rfl | rfl
  · rfl
  · simp [orbitLaw_apply, flipSecond]

theorem orbitLaw_positive (p q : ℝ≥0∞) (h : p + q = 1) (hp : 0 < p) (hq : 0 < q)
    (x : Bool × Bool) : 0 < orbitLaw p q h x := by
  rw [orbitLaw_apply]
  split
  · exact ENNReal.div_pos hp.ne' (by norm_num)
  · exact ENNReal.div_pos hq.ne' (by norm_num)

theorem orbitLaw_orbit_mass (p q : ℝ≥0∞) (h : p + q = 1) :
    orbitLaw p q h (true, true) + orbitLaw p q h (true, false) = p := by
  simp [orbitLaw_apply, ENNReal.add_halves]

theorem orbitLaw_injective (p q p' q' : ℝ≥0∞) (h : p + q = 1) (h' : p' + q' = 1)
    (he : orbitLaw p q h = orbitLaw p' q' h') : p = p' := by
  rw [← orbitLaw_orbit_mass p q h, ← orbitLaw_orbit_mass p' q' h', he]

private theorem quarters : (1 : ℝ≥0∞) / 4 + 3 / 4 = 1 := by
  rw [← ENNReal.add_div, show (1 : ℝ≥0∞) + 3 = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

private theorem quarter_ne : (1 : ℝ≥0∞) / 4 ≠ 3 / 4 :=
  ne_of_lt ((ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num)).mpr (by norm_num))

private theorem quarter_pos (a : ℝ≥0∞) (h : a ≠ 0) : 0 < a / 4 :=
  ENNReal.div_pos h (by norm_num)

theorem twoOrbitLaws :
    ∃ μ ν : PMF (Bool × Bool), Invariant firstPreserving μ ∧
      Invariant firstPreserving ν ∧ (∀ x, 0 < μ x ∧ 0 < ν x) ∧ μ ≠ ν := by
  refine ⟨orbitLaw (1 / 4) (3 / 4) quarters,
    orbitLaw (3 / 4) (1 / 4) (by rw [add_comm]; exact quarters),
    orbitLaw_invariant _ _ _, orbitLaw_invariant _ _ _, fun x => ⟨?_, ?_⟩, ?_⟩
  · exact orbitLaw_positive _ _ _ (quarter_pos 1 one_ne_zero) (quarter_pos 3 (by norm_num)) x
  · exact orbitLaw_positive _ _ _ (quarter_pos 3 (by norm_num)) (quarter_pos 1 one_ne_zero) x
  · intro he
    exact quarter_ne (orbitLaw_injective _ _ _ _ _ _ he)

/-! ### Binary stationarity -/

theorem bind_true (μ : PMF Bool) (K : Bool → PMF Bool) :
    (μ.bind K) true = μ true * K true true + μ false * K false true := by
  simp [PMF.bind_apply]

theorem stationary_iff_true (K : Bool → PMF Bool) (μ : PMF Bool) :
    Stationary K μ ↔ (μ.bind K) true = μ true :=
  ⟨fun h => by rw [show μ.bind K = μ from h], fun h => binary_unique_of_mass _ _ h⟩

theorem bind_true_real (μ : PMF Bool) (K : Bool → PMF Bool) :
    ((μ.bind K) true).toReal =
      (μ true).toReal * (1 - switchOut K) + (1 - (μ true).toReal) * switchIn K := by
  have hK := binary_real_sum (K true)
  have hμ := binary_real_sum μ
  rw [bind_true, ENNReal.toReal_add (ENNReal.mul_ne_top (μ.apply_ne_top _) ((K true).apply_ne_top _))
      (ENNReal.mul_ne_top (μ.apply_ne_top _) ((K false).apply_ne_top _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  unfold switchOut switchIn
  rw [show (K true true).toReal = 1 - (K true false).toReal by linarith,
    show (μ false).toReal = 1 - (μ true).toReal by linarith]

theorem stationary_binary_iff (K : Bool → PMF Bool) (μ : PMF Bool) :
    Stationary K μ ↔ Balance K μ := by
  rw [stationary_iff_true]
  unfold Balance
  rw [← ENNReal.toReal_eq_toReal_iff' ((μ.bind K).apply_ne_top _) (μ.apply_ne_top _),
    bind_true_real]
  constructor
  · intro h; linear_combination (-1 : ℝ) * h
  · intro h; linear_combination (-1 : ℝ) * h

theorem mass_real_nonneg (μ : PMF Bool) (b : Bool) : 0 ≤ (μ b).toReal := ENNReal.toReal_nonneg

theorem stationary_unique (K : Bool → PMF Bool) (hpos : 0 < switchOut K + switchIn K)
    (μ ν : PMF Bool) (hμ : Stationary K μ) (hν : Stationary K ν) : μ = ν := by
  rw [stationary_binary_iff] at hμ hν
  unfold Balance at hμ hν
  apply binary_unique_of_real_mass
  have h0 : ((μ true).toReal - (ν true).toReal) * (switchOut K + switchIn K) = 0 := by
    linear_combination hμ - hν
  rcases mul_eq_zero.mp h0 with h | h
  · linarith
  · exact absurd h hpos.ne'

theorem stationary_exists (K : Bool → PMF Bool) (hpos : 0 < switchOut K + switchIn K) :
    ∃ μ : PMF Bool, Stationary K μ := by
  set s := switchOut K + switchIn K
  have hout : 0 ≤ switchOut K := ENNReal.toReal_nonneg
  have hin : 0 ≤ switchIn K := ENNReal.toReal_nonneg
  set x := switchIn K / s
  have hx0 : 0 ≤ x := div_nonneg hin hpos.le
  have hx1 : x ≤ 1 := by
    rw [div_le_one hpos]; linarith
  have hsum : ENNReal.ofReal x + ENNReal.ofReal (1 - x) = 1 := by
    rw [← ENNReal.ofReal_add hx0 (by linarith)]
    simp
  refine ⟨binaryLaw (ENNReal.ofReal x) (ENNReal.ofReal (1 - x)) hsum, ?_⟩
  rw [stationary_binary_iff]
  unfold Balance
  rw [binaryLaw_true, ENNReal.toReal_ofReal hx0]
  exact div_mul_cancel₀ _ hpos.ne'

theorem stationary_of_no_switching (K : Bool → PMF Bool) (h0 : switchOut K + switchIn K = 0)
    (μ : PMF Bool) : Stationary K μ := by
  rw [stationary_binary_iff]
  unfold Balance
  have hout : 0 ≤ switchOut K := ENNReal.toReal_nonneg
  have hin : 0 ≤ switchIn K := ENNReal.toReal_nonneg
  have : switchIn K = 0 := by linarith
  rw [h0, this, mul_zero]

theorem identity_nonunique :
    ∃ μ ν : PMF Bool, μ ≠ ν ∧ Stationary identityKernel μ ∧ Stationary identityKernel ν := by
  refine ⟨PMF.pure true, PMF.pure false, ?_, PMF.bind_pure _, PMF.bind_pure _⟩
  intro h
  have := congrArg (fun μ : PMF Bool => μ true) h
  simp [PMF.pure_apply] at this

theorem reset_stationary_iff (μ : PMF Bool) : Stationary resetKernel μ ↔ μ = PMF.pure true := by
  unfold Stationary resetKernel
  rw [PMF.bind_const]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem flip_pure (b : Bool) : step flipKernel (PMF.pure b) = PMF.pure (!b) := by
  simp [step, flipKernel, PMF.pure_bind]

theorem flip_pure_not_stationary (b : Bool) : ¬ Stationary flipKernel (PMF.pure b) := by
  intro h
  have h' : PMF.pure (!b) = PMF.pure b := (flip_pure b).symm.trans h
  have := congrArg (fun μ : PMF Bool => μ b) h'
  cases b <;> simp [PMF.pure_apply] at this

theorem flip_switching : 0 < switchOut flipKernel + switchIn flipKernel := by
  simp [switchOut, switchIn, flipKernel, PMF.pure_apply]

theorem flip_iterate_pure (n : Nat) : ∃ b, (step flipKernel)^[n] (PMF.pure true) = PMF.pure b := by
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨!b, ?_⟩
    rw [Function.iterate_succ_apply', hb, flip_pure]

theorem lawDeterminationControls : LawDeterminationControls := by
  refine ⟨fun E _ _ G hG => unique_invariant_of_transitive G hG,
    fun E _ _ G hG μ hμ x => invariant_mass_of_transitive G hG μ hμ x,
    firstPreserving_not_transitive,
    fun p q h hp hq => ⟨orbitLaw_invariant p q h, orbitLaw_positive p q h hp hq⟩,
    fun p q p' q' h h' he => orbitLaw_injective p q p' q' h h' he,
    twoOrbitLaws, stationary_binary_iff, ?_, stationary_of_no_switching,
    identity_nonunique, reset_stationary_iff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K hpos
    obtain ⟨μ, hμ⟩ := stationary_exists K hpos
    exact ⟨μ, hμ, fun ν hν => stationary_unique K hpos ν μ hν hμ⟩
  · obtain ⟨μ, hμ⟩ := stationary_exists flipKernel flip_switching
    exact ⟨μ, hμ, fun ν hν => stationary_unique flipKernel flip_switching ν μ hν hμ⟩
  · intro n
    obtain ⟨b, hb⟩ := flip_iterate_pure n
    rw [hb]
    exact flip_pure_not_stationary b
  · rw [flip_pure, flip_pure]; rfl
  · rw [flip_pure]
    intro h
    have := congrArg (fun μ : PMF Bool => μ true) h
    simp [PMF.pure_apply] at this
  · intro I E G π ν hν g hg x
    simp only [PMF.bind_apply]
    exact tsum_congr fun i => by rw [hν i g hg x]
  · intro ν hne π π' he
    have h1 := congrArg (fun μ : PMF Bool => (μ true).toReal) he
    simp only [bind_true] at h1
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (π.apply_ne_top _) ((ν true).apply_ne_top _))
        (ENNReal.mul_ne_top (π.apply_ne_top _) ((ν false).apply_ne_top _)),
      ENNReal.toReal_add (ENNReal.mul_ne_top (π'.apply_ne_top _) ((ν true).apply_ne_top _))
        (ENNReal.mul_ne_top (π'.apply_ne_top _) ((ν false).apply_ne_top _)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul] at h1
    have hπ := binary_real_sum π
    have hπ' := binary_real_sum π'
    have hc : (ν true true).toReal ≠ (ν false true).toReal := fun h =>
      hne ((ENNReal.toReal_eq_toReal_iff' ((ν true).apply_ne_top _)
        ((ν false).apply_ne_top _)).mp h)
    apply binary_unique_of_real_mass
    have h2 : ((π true).toReal - (π' true).toReal) *
        ((ν true true).toReal - (ν false true).toReal) = 0 := by
      rw [show (π false).toReal = 1 - (π true).toReal by linarith,
        show (π' false).toReal = 1 - (π' true).toReal by linarith] at h1
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · exact absurd (by linarith) hc
  · intro I E ρ π π'
    rw [PMF.bind_const, PMF.bind_const]

/-! ### The law fork -/

theorem value_fork {W B F X : Type} (A : Arena W B F) (f : F) (sel : W → X) (a : W)
    (hT : TracksValue A f sel a) (hPSR : ContingentPSR A a) :
    (∀ v, Access A a v → sel v = sel a) ∨
      ((∃ v, Access A a v ∧ sel v ≠ sel a) ∧ Explained A a f) := by
  by_cases hconst : ∀ v, Access A a v → sel v = sel a
  · exact Or.inl hconst
  · push Not at hconst
    obtain ⟨v, hv, hne⟩ := hconst
    refine Or.inr ⟨⟨v, hv, hne⟩, hPSR f ⟨(hT a).mpr rfl, v, hv, fun h => hne ((hT v).mp h)⟩⟩

theorem constant_value_not_contingent {W B F X : Type} (A : Arena W B F) (f : F)
    (sel : W → X) (a : W) (hT : TracksValue A f sel a)
    (hconst : ∀ v, Access A a v → sel v = sel a) : ¬ Contingent A a f := by
  rintro ⟨_, v, hv, hnot⟩
  exact hnot ((hT v).mpr (hconst v hv))

theorem adopted_law_symmetric {W B F O : Type} (A : Arena W B F) (law adopt : F)
    (laws adopted : W → PMF O) (a : W) (hL : TracksValue A law laws a)
    (hA : TracksValue A adopt adopted a) (hEq : ∀ w, laws w = adopted w)
    (hPSR : ContingentPSR A a) (hvar : ∃ v, Access A a v ∧ laws v ≠ laws a) :
    Explained A a law ∧ Explained A a adopt := by
  obtain ⟨v, hv, hne⟩ := hvar
  refine ⟨hPSR law ⟨(hL a).mpr rfl, v, hv, fun h => hne ((hL v).mp h)⟩,
    hPSR adopt ⟨(hA a).mpr rfl, v, hv, fun h => hne ?_⟩⟩
  rw [hEq, hEq]
  exact (hA v).mp h

theorem favoring_true : favoring true true = 3 / 4 := by
  simp [favoring, binaryLaw_true]

theorem favoring_false : favoring false true = 1 / 4 := by
  simp [favoring, binaryLaw_true]

theorem favoring_positive (h b : Bool) : 0 < favoring h b := by
  cases h <;> cases b <;>
    simp [favoring, binaryLaw_true, binaryLaw_false]

theorem favoring_ne : favoring true ≠ favoring false := by
  intro h
  have := congrArg (fun μ : PMF Bool => μ true) h
  simp only [favoring_true, favoring_false] at this
  exact quarter_ne this.symm

theorem favoring_injective : Function.Injective favoring := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact absurd h.symm favoring_ne
  · exact absurd h favoring_ne
  · rfl

theorem likelihood_nonzero (h : Bool) (xs : List Bool) : iidLikelihood (favoring h) xs ≠ 0 := by
  induction xs with
  | nil => simp [iidLikelihood]
  | cons x xs ih => exact mul_ne_zero (favoring_positive h x).ne' ih

theorem lawArena_tracks (r : Bool) (xs : List Bool) :
    TracksValue (lawArena r) .actualLaw (matched xs).propensity true := by
  intro w
  change w = true ↔ favoring w = favoring true
  exact ⟨fun h => by rw [h], fun h => favoring_injective h⟩

theorem lawArena_contingent (r : Bool) : Contingent (lawArena r) true .actualLaw :=
  ⟨rfl, false, trivial, fun h => Bool.noConfusion h⟩

theorem lawSelectionFork : LawSelectionFork := by
  refine ⟨fun W B F X A f sel a hT hPSR => value_fork A f sel a hT hPSR,
    fun W B F X A f sel a hT hconst => constant_value_not_contingent A f sel a hT hconst,
    fun W B F O A law adopt laws adopted a hL hA hEq hPSR hvar =>
      adopted_law_symmetric A law adopt laws adopted a hL hA hEq hPSR hvar, ?_⟩
  intro xs
  dsimp only
  refine ⟨rfl, rfl, favoring_ne, likelihood_nonzero true xs, likelihood_nonzero false xs,
    fun r => lawArena_tracks r xs, lawArena_contingent false, ?_, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
  · intro h
    obtain ⟨r, hr⟩ := h .actualLaw (lawArena_contingent false)
    exact Bool.noConfusion hr.1
  · intro f hf
    cases f with
    | base =>
      obtain ⟨_, v, _, hv⟩ := hf
      exact absurd trivial hv
    | actualLaw => exact ⟨.base, rfl, rfl, rfl⟩
  · intro h
    exact favoring_ne (h false trivial trivial).symm

/-! ### Realization and sample -/

theorem outputLaw_support_matches (p : OutputProfile Bool EffectBeing Unit)
    (hout : ∀ v x, p.output v () x ↔ x = some v)
    (μ : PMF Bool) (hμ : ∀ b, 0 < μ b) : SupportMatches p (outputLaw μ) := by
  intro x
  rw [outputLaw, PMF.support_map]
  constructor
  · rintro ⟨b, _, rfl⟩
    exact ⟨b, (hout b _).mpr rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, (PMF.mem_support_iff μ v).mpr (hμ v).ne', ((hout v x).mp hv).symm⟩

theorem varying_realized : RealizedOutputs varying := by
  intro v a x _ hx
  exact ⟨rfl, hx⟩

theorem emptied_not_realized : ¬ RealizedOutputs emptied := by
  intro h
  exact h false () (some false) trivial rfl

theorem lawAdopted_dstit : Dstit () (lawHistory true true) LawAdopted := by
  refine ⟨?_, ?_⟩
  · intro k hk
    exact hk.symm
  · intro h
    exact Bool.noConfusion (h (lawHistory false true))

theorem sample_not_settled :
    ¬ Cstit () (lawHistory true true) SampleTrue ∧
      ¬ Cstit () (lawHistory true true) (fun h => ¬ SampleTrue h) := by
  constructor
  · intro h
    exact Bool.noConfusion (h (lawHistory true false) rfl)
  · intro h
    exact h (lawHistory true true) rfl rfl

theorem realizationSampleControls : RealizationSampleControls := by
  refine ⟨fun μ hμ => ⟨outputLaw_support_matches varying (fun _ _ => Iff.rfl) μ hμ,
      outputLaw_support_matches emptied (fun _ _ => Iff.rfl) μ hμ⟩,
    rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl,
    varying_realized, emptied_not_realized, lawAdopted_dstit, rfl, sample_not_settled⟩

end TruthCore.Results.Explanation.ObjectiveProbability
