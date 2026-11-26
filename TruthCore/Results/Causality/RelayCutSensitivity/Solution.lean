module

public import TruthCore.Causality.RelayCutSensitivity

@[expose] public section
noncomputable section

namespace TruthCore.Results.Causality.RelayCutSensitivity

open TruthCore.Causality (PowerTransmissionRule)
open TruthCore.Causality.ParallelPowerTransmission (ActivityClassification CutEffects transmissionLink)
open TruthCore.Causality.RelayCutSensitivity
open TruthCore.Causality.SupplierAuditLikelihood (PrefixComparison depthLikelihood)

private theorem relayOnlyLosesBottom (cutEffects : CutEffects) (i : ℕ) (active : ℕ → Prop)
    (equation : RelayActivity (singleCut i) (fun _ => False) active) : ¬ active 0 := by
  let intact (_ : Unit) := singleCut i
  let activeOnRay (position : Unit × ℕ) := active position.2
  have law : PowerTransmissionRule (transmissionLink intact) activeOnRay := by
    rintro ⟨k, n⟩
    constructor
    · intro atPosition
      obtain ⟨link, upstream⟩ := ((equation n).mp atPosition).resolve_left id
      exact ⟨(k, n + 1), ⟨rfl, link⟩, upstream⟩
    · rintro ⟨_, ⟨rfl, link⟩, upstream⟩
      exact (equation n).mpr (Or.inr ⟨link, upstream⟩)
  exact (cutEffects Unit intact).1 activeOnRay law () 0 i (Nat.zero_le i)
    (fun available => available rfl)

private theorem cutStep {d i n : ℕ} (below : n < d) :
    (n ≠ i ∧ (i < n + 1 ∨ d ≤ i)) ↔ i < n ∨ d ≤ i := by
  constructor
  · rintro ⟨intact, before | reaches⟩
    · exact Or.inl (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ before) intact.symm)
    · exact Or.inr reaches
  · rintro (before | reaches)
    · exact ⟨Nat.ne_of_gt before, Or.inl (Nat.lt_succ_of_lt before)⟩
    · exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le below reaches), Or.inr reaches⟩

private theorem fedResponseBelow (d i : ℕ) (active : ℕ → Prop)
    (equation : RelayActivity (singleCut i) (· = d) active) :
    ∀ distance n, n + distance = d → (active n ↔ i < n ∨ d ≤ i) := by
  intro distance
  induction distance with
  | zero =>
    intro n equal
    change n = d at equal
    subst n
    exact ⟨fun _ => (Nat.lt_or_ge i d),
      fun _ => (equation d).mpr (Or.inl rfl)⟩
  | succ distance ih =>
    intro n equal
    have sumEq : (n + 1) + distance = d := by
      rw [Nat.succ_add, ← Nat.add_succ]
      exact equal
    have below : n < d := equal ▸ Nat.lt_succ_of_le (Nat.le_add_right n distance)
    refine (equation n).trans ⟨?_, ?_⟩
    · rintro (atDepth | ⟨intact, on⟩)
      · exact False.elim ((Nat.ne_of_lt below) atDepth)
      · exact (cutStep below).mp ⟨intact, (ih (n + 1) sumEq).mp on⟩
    · intro on
      obtain ⟨intact, next⟩ := (cutStep below).mpr on
      exact Or.inr ⟨intact, (ih (n + 1) sumEq).mpr next⟩

theorem singleCutComparison (classification : ActivityClassification) : SingleCutComparison := by
  have threshold d response (valid : CutResponses (· = d) response) i :
      response i 0 ↔ d ≤ i :=
    (fedResponseBelow d i (response i) (valid i) d 0 (Nat.zero_add d)).trans
      ⟨fun h => h.elim (fun impossible => False.elim (Nat.not_lt_zero i impossible)) id, Or.inr⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, threshold, ?_, ?_⟩
  · intro _
    exact ⟨fun _ => Or.inr ⟨trivial, trivial⟩, fun _ => trivial⟩
  · intro _ _
    exact ⟨fun _ => Or.inr ⟨trivial, trivial⟩, fun _ => trivial⟩
  · refine ⟨fun i n => i < n, ?_⟩
    intro i n
    refine ⟨fun on => Or.inr ⟨Nat.ne_of_gt on, Nat.lt_succ_of_lt on⟩, ?_⟩
    rintro (impossible | ⟨intact, on⟩)
    · exact False.elim impossible
    · exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ on) intact.symm
  · intro response valid i
    exact relayOnlyLosesBottom classification.2 i (response i) (valid i)
  · intro d
    refine ⟨fun i n => n ≤ d ∧ (i < n ∨ d ≤ i), ?_⟩
    intro i n
    rcases Nat.lt_trichotomy n d with below | atDepth | above
    · constructor
      · rintro ⟨_, on⟩
        obtain ⟨intact, next⟩ := (cutStep below).mpr on
        exact Or.inr ⟨intact, Nat.succ_le_of_lt below, next⟩
      · rintro (atDepth | ⟨intact, _, next⟩)
        · exact False.elim (Nat.ne_of_lt below atDepth)
        · exact ⟨below.le, (cutStep below).mp ⟨intact, next⟩⟩
    · subst n
      exact ⟨fun _ => Or.inl rfl, fun _ => ⟨le_rfl, (Nat.lt_or_ge i d)⟩⟩
    · constructor
      · rintro ⟨bounded, _⟩
        exact False.elim (Nat.not_le_of_gt above bounded)
      · rintro (atDepth | ⟨_, bounded, _⟩)
        · exact False.elim (Nat.ne_of_gt above atDepth)
        · exact False.elim (Nat.not_le_of_gt (Nat.lt_succ_of_lt above) bounded)
  · intro d response valid
    exact ⟨(threshold d response valid d).mpr le_rfl,
      fun i hi => (threshold d response valid i).mp hi⟩
  · intro k response valid
    refine ⟨?_, (threshold (k + 1) response valid (k + 1)).mpr le_rfl⟩
    intro i below on
    exact Nat.not_le_of_gt (Nat.lt_succ_of_le below) ((threshold _ response valid i).mp on)

theorem randomizedCutComparison (cuts : SingleCutComparison)
    (prefixes : PrefixComparison) : RandomizedCutComparison := by
  classical
  obtain ⟨_, _, relayOnly, _, threshold, _, _⟩ := cuts
  obtain ⟨prefixThreshold, _, _, _, _, tailLaw, geometricProper, geometricPositive, geometric⟩ :=
    prefixes
  have mass_eq_tail law d response (valid : CutResponses (· = d) response) :
      survivalMass law response = depthLikelihood law d := by
    unfold survivalMass depthLikelihood
    exact tsum_congr fun i => by rw [threshold d response valid i, prefixThreshold]
  refine ⟨?_, ?_, geometricProper, geometricPositive, ?_⟩
  · intro law response valid
    calc
      survivalMass law response = ∑' i : ℕ, (0 : ℝ) :=
        tsum_congr fun i => ite_eq_right (relayOnly response valid i)
      _ = 0 := tsum_zero
  · intro law nonnegative proper
    obtain ⟨complement, small⟩ := tailLaw law nonnegative proper
    constructor
    · intro d response valid
      have equal := mass_eq_tail law d response valid
      refine ⟨equal, equal.trans (complement d), ?_⟩
      let survives (i : ℕ) := if response i 0 then law i else 0
      have nonneg i : 0 ≤ survives i := by
        unfold survives
        split_ifs <;> first | exact nonnegative i | exact le_rfl
      have bounded i : survives i ≤ law i := by
        unfold survives
        split_ifs <;> first | exact le_rfl | exact nonnegative i
      have sum : Summable survives := .of_nonneg_of_le nonneg bounded proper.summable
      change (0 < ∑' i, survives i ↔ ∃ i, d ≤ i ∧ 0 < law i) ∧
        (∑' i, survives i) ≤ 1
      refine ⟨?_, (sum.tsum_le_tsum bounded proper.summable).trans_eq proper.tsum_eq⟩
      constructor
      · intro positive
        by_contra noPositiveCut
        have zeroAt i : survives i = 0 := by
          by_cases on : response i 0
          · have reaches := (threshold d response valid i).mp on
            have zero : law i = 0 := le_antisymm
              (le_of_not_gt fun positive => noPositiveCut ⟨i, reaches, positive⟩)
              (nonnegative i)
            simp [survives, on, zero]
          · simp [survives, on]
        exact (lt_irrefl (0 : ℝ)) (by simpa only [zeroAt, tsum_zero] using positive)
      · rintro ⟨i, reaches, positive⟩
        have on := (threshold d response valid i).mpr reaches
        exact positive.trans_le (by simpa [survives, on] using sum.le_tsum i (fun j _ => nonneg j))
    · intro ε positiveε
      obtain ⟨start, after⟩ := small 1 ε 1 zero_lt_one positiveε zero_lt_one
      refine ⟨start, fun d afterStart response valid => ?_⟩
      simpa only [mass_eq_tail law d response valid, one_mul] using after d afterStart
  · intro d response valid
    exact (mass_eq_tail _ d response valid).trans (geometric d).1

end TruthCore.Results.Causality.RelayCutSensitivity
