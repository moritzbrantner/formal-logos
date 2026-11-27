module

public import TruthCore.Explanation.ObjectiveProbability
public import TruthCore.Results.Explanation.PSRLaterAxes.Solution
public import TruthCore.Results.Causality.SelectedAncestry.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.ObjectiveProbability

open TruthCore.Explanation.ObjectiveProbability
open TruthCore.Explanation.PSRStrength
open scoped ENNReal

theorem binary_apply (h b : Bool) :
    binaryLaw h b = (if b = h then (3 : ℝ≥0∞) / 4 else 1 / 4) := by
  simp [binaryLaw, PMF.ofFintype_apply]

theorem binary_positive (h b : Bool) : 0 < binaryLaw h b := by
  rw [binary_apply]
  split <;> exact ENNReal.div_pos (by norm_num) (by norm_num)

theorem binary_ne : binaryLaw true ≠ binaryLaw false := by
  intro he
  have h := congrArg (fun μ : PMF Bool => μ true) he
  simp only [binary_apply] at h
  change (3 : ℝ≥0∞) / 4 = 1 / 4 at h
  have hlt : (1 : ℝ≥0∞) / 4 < 3 / 4 :=
    (ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num)).mpr (by norm_num)
  exact (ne_of_gt hlt) h

theorem likelihood_nonzero (h : Bool) (xs : List Bool) :
    iidLikelihood (binaryLaw h) xs ≠ 0 := by
  induction xs with
  | nil => simp [iidLikelihood]
  | cons x xs ih =>
    exact mul_ne_zero (ne_of_gt (binary_positive h x)) ih

theorem binary_controls : BinaryControls :=
  ⟨binary_positive, by simp [binary_apply], by simp [binary_apply],
    binary_ne, fun xs => ⟨likelihood_nonzero true xs, likelihood_nonzero false xs⟩⟩

theorem matched_controls (xs : List Bool) :
    let L := matched xs
    let a : Bool × Bool := (true, true)
    let v : Bool × Bool := (false, true)
    let absent : Bool × Bool := (true, false)
    L.operative a ∧ L.operative v ∧
    (∀ b, L.admitted a b ↔ L.admitted v b) ∧
    L.record a = L.record v ∧ L.credence a = L.credence v ∧
    L.propensity a ≠ L.propensity v ∧
    L.propensity a = L.propensity absent ∧ ¬ L.operative absent ∧
    FixedBy L Prod.fst ∧ ¬ FixedBy L (fun _ => ()) ∧
    RepresentsLaw (lawArena false) L .actualLaw (L.propensity a) ∧
    Contingent (lawArena false) a .actualLaw ∧
    ¬ ContingentPSR (lawArena false) a ∧
    (lawArena true).explains a .base .actualLaw ∧
    ¬ FixesLaw (lawArena true) L a .base := by
  dsimp only
  refine ⟨rfl, rfl, fun _ => Iff.rfl, rfl, rfl, binary_ne, rfl, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [matched]
  · intro w v _ _ h
    exact congrArg binaryLaw h
  · intro h
    exact binary_ne (h (true, true) (false, true) rfl rfl rfl)
  · intro w
    change (w.1 = true ∧ w.2 = true) ↔
      w.2 = true ∧ binaryLaw w.1 = binaryLaw true
    rcases w with ⟨b, c⟩
    cases b
    · simp [Ne.symm binary_ne]
    · simp
  · exact ⟨⟨rfl, rfl⟩, (false, true), trivial, fun h => Bool.noConfusion h.1⟩
  · intro h
    obtain ⟨r, hr⟩ := h .actualLaw
      ⟨⟨rfl, rfl⟩, (false, true), trivial, fun h => Bool.noConfusion h.1⟩
    exact Bool.noConfusion hr.1
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    exact binary_ne (h (false, true) trivial trivial rfl).symm

theorem law_contingency {W B F O : Type} (A : Arena W B F)
    (L : LawProfile W O) (a v : W) (f : F)
    (hRep : RepresentsLaw A L f (L.propensity a))
    (ha : L.operative a) (hv : Access A a v) (hop : L.operative v)
    (hne : L.propensity v ≠ L.propensity a) :
    Contingent A a f ∧ (ContingentPSR A a → Explained A a f) := by
  have hc : Contingent A a f :=
    ⟨(hRep a).mpr ⟨ha, rfl⟩, v, hv, fun hf => hne ((hRep v).mp hf).2⟩
  exact ⟨hc, fun h => h f hc⟩

theorem productive_control : ProductiveControl := by
  exact ⟨rfl,
    TruthCore.Results.Explanation.UltimateAdequacy.actual_occurs .single 2,
    TruthCore.Results.Explanation.UltimateAdequacy.actual_occurs .chain 2,
    TruthCore.Results.Explanation.UltimateAdequacy.single_supply 2,
    TruthCore.Results.Explanation.UltimateAdequacy.chain_no_supply 2⟩

theorem realization_route : RealizationRoute := by
  intro W B O m w selected μ realizes hactual hreal hWF hDep hEM
  exact ⟨hreal, TruthCore.Results.Causality.SelectedAncestry.necessaryRootAncestor
    m w selected (hactual selected μ hreal) hWF hDep hEM⟩

theorem certificate : Certificate := by
  refine ⟨binary_controls, matched_controls, ?_, ?_, productive_control, realization_route⟩
  · intro W B F O A L a v f hRep ha hv hop hne
    exact law_contingency A L a v f hRep ha hv hop hne
  · intro W O E L essence a v hFix ha hv hne he
    exact hne (hFix a v ha hv he)

end TruthCore.Results.Explanation.ObjectiveProbability
