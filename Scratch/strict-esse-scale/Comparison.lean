import TruthCore.Causality.StrictEsseScale
import Mathlib.Data.ENat.Basic

namespace StrictEsseScaleComparison

/-- With the weak bound secured, strict separation occurs exactly when
the recipient's degree is not an upper bound for the source's levels. -/
theorem strictIffUnboundedItem {D : Type} [Preorder D] (x c : Set D) (dx dc : D)
    (hx : IsLUB x dx) (hc : IsLUB c dc) (hincl : x ⊆ c) :
    dx < dc ↔ ∃ v ∈ c, ¬ v ≤ dx := by
  constructor
  · intro h
    by_contra! hall
    exact h.not_ge (hc.2 hall)
  · rintro ⟨v, hv, hn⟩
    exact lt_of_le_not_ge (hx.mono hc hincl) (fun he => hn (le_trans (hc.1 hv) he))

/-- An omitted lower determination is invisible at the scalar maximum. -/
theorem dominatedOmission :
    ({2} : Set Nat) ⊂ {1, 2} ∧ IsLUB ({2} : Set Nat) 2 ∧ IsLUB ({1, 2} : Set Nat) 2 := by
  refine ⟨Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩, isLUB_singleton, ?_⟩
  · intro i hi
    simpa only [Set.mem_singleton_iff.mp hi] using (show 2 ∈ ({1, 2} : Set Nat) by simp)
  · intro he
    have : 1 ∈ ({2} : Set Nat) := he ▸ (show 1 ∈ ({1, 2} : Set Nat) by simp)
    simp at this
  · apply IsGreatest.isLUB
    refine ⟨by simp, ?_⟩
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl <;> decide

/-- The source attains its top. The recipient omits it and realizes finite
levels cofinal below it. Even attainment on only one side leaves a tie. -/
theorem cofinalOmission :
    (⊤ : ℕ∞) ∉ Set.Iio ⊤ ∧ (⊤ : ℕ∞) ∈ Set.univ ∧
    IsLUB (Set.Iio (⊤ : ℕ∞)) ⊤ ∧ IsLUB (Set.univ : Set ℕ∞) ⊤ := by
  refine ⟨(show ¬ (⊤ : ℕ∞) < ⊤ from lt_irrefl _), Set.mem_univ _, ⟨fun _ _ => le_top, ?_⟩, ?_⟩
  · intro k hk
    by_contra h
    have hk' : k ≠ ⊤ := fun he => h (le_of_eq he.symm)
    obtain ⟨n, hn⟩ := ENat.exists_nat_gt hk'
    exact hn.not_ge (hk (ENat.natCast_lt_top n))
  · exact ⟨fun _ _ => le_top, fun _ h => h (Set.mem_univ _)⟩

/-- Set-valued levels compare the whole profile. The least bound of its
singleton features is the profile itself. -/
theorem profileCalibration {A : Type} (features : Set A) :
    IsLUB ((fun a : A => ({a} : Set A)) '' features) features := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact Set.singleton_subset_iff.mpr ha
  · intro upper hu a ha
    have hsub : ({a} : Set A) ⊆ upper := hu ⟨a, ha, rfl⟩
    exact hsub (Set.mem_singleton a)

theorem profileStrict {A : Type} {recipient giver : Set A} (hp : recipient ⊆ giver)
    {a : A} (hc : a ∈ giver) (hx : a ∉ recipient) : recipient < giver :=
  lt_of_le_not_ge hp (fun h => hx (h hc))

end StrictEsseScaleComparison
