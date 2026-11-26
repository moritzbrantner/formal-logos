module

public import TruthCore.Causality.SupplierPanelLikelihood

@[expose] public section

namespace TruthCore.Results.Causality.SupplierPanelLikelihood

open MeasureTheory Set TruthCore.Causality.RayObservation TruthCore.Logic.PrefaceConnectivity
open TruthCore.Causality.SupplierPanelLikelihood
open scoped ENNReal

variable {K O Γ Λ : Type} {intact : K → Nat → Prop} {position : O → K × Nat} {n : ℕ}

private theorem allPositive_eq (index : ObservedRays intact position ≃ Fin n)
    (G : Set Γ) (C : Set Λ) (live : ∀ i, Live intact position i) :
    allPositive index G C = allTrue G C n := by
  ext x
  constructor
  · intro observed
    apply mem_iInter.mpr
    intro j
    obtain ⟨k, hk⟩ := index.surjective j
    obtain ⟨i, hi⟩ := k.property
    obtain ⟨_, h⟩ := mem_iInter.mp observed i.val
    have heq : observedRay i.val (live i.val) = k :=
      Subtype.ext hi
    simpa only [heq, hk] using h
  · intro allOn
    apply mem_iInter.mpr
    intro i
    exact ⟨live i, mem_iInter.mp allOn _⟩

theorem probabilitiesOfObservedRays (realize : RayReportCharacterization)
    (prob : ProfileProbabilities) : PanelProbabilities := by
  classical
  intro K O Γ Λ _ _ _ _ _ _ κ _ ν _ intact position n index G C
  refine ⟨?_, ?_, ?_⟩
  · intro x
    let report (i : O) := decide (x ∈ positiveAt index G C i)
    have on (i : O) : report i = true ↔ x ∈ positiveAt index G C i := by simp [report]
    refine ⟨report, (realize K O intact position report).mpr ⟨?_, ?_⟩, on⟩
    · intro i cut
      cases h : report i
      · rfl
      · exact (cut ((on i).mp h).choose).elim
    · intro i j hi hj same
      have eqRay :
          observedRay i hi = observedRay j hj := Subtype.ext same
      apply Bool.eq_iff_iff.mpr
      rw [on, on]
      constructor
      · rintro ⟨_, h⟩
        exact ⟨hj, eqRay ▸ h⟩
      · rintro ⟨_, h⟩
        exact ⟨hi, eqRay.symm ▸ h⟩
  · rintro ⟨i, cut⟩
    have empty : allPositive index G C = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun x hx => cut ((mem_iInter.mp hx i).choose)
    simp [empty]
  · intro live
    rw [allPositive_eq index G C live]
    by_cases h : n = 0
    · subst n
      simp [allTrue, profile]
    · simpa [h] using (prob Γ Λ κ ν G C ∅ n (Nat.pos_of_ne_zero h)).2.1

end TruthCore.Results.Causality.SupplierPanelLikelihood
