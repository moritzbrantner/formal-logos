module

public import TruthCore.Causality.FullnessCandidates
public import TruthCore.Results.Causality.Q44SourceSupply.Solution

@[expose] public section
namespace TruthCore.Results.Causality.FullnessCandidates
open TruthCore.Causality.FullnessCandidates

theorem contentAudit : ContentAudit := by
  intro B R F Pure c x hEM hFull
  have hSub : possessionContent F Pure x ⊆ possessionContent F Pure c := by
    intro r hr
    exact ⟨hr.1, hFull r hr.1⟩
  refine ⟨hSub, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hStrict
    rcases hEM (∃ r, Pure r ∧ ¬ F.InActFormallyOrVirtually x r) with h | h
    · exact h
    · exfalso
      apply (lt_iff_le_not_ge.mp hStrict).2
      intro r hr
      refine ⟨hr.1, ?_⟩
      rcases hEM (F.InActFormallyOrVirtually x r) with hx | hx
      · exact hx
      · exact (h ⟨r, hr.1, hx⟩).elim
  · rintro ⟨r, hp, hMissing⟩
    apply lt_iff_le_not_ge.mpr
    refine ⟨hSub, ?_⟩
    intro hBack
    exact hMissing (hBack ⟨hp, hFull r hp⟩).2
  · intro hEqual r hp
    have hr : r ∈ possessionContent F Pure c := ⟨hp, hFull r hp⟩
    rw [← hEqual] at hr
    exact hr.2
  · intro hx
    apply Set.ext
    intro r
    constructor
    · exact fun hr => hSub hr
    · exact fun hr => ⟨hr.1, hx r hr.1⟩

theorem footprintAudit : FootprintAudit := by
  intro B P R p hSource hCompose
  obtain ⟨n, hn, hid, hNoIncoming, hPaths⟩ := hSource
  have hScope : ∀ x, p.InAct x p.esse → x ≠ n → p.CausesIn n x p.esse := by
    intro x hx hxn
    exact TruthCore.Results.Causality.Q44SourceSupply.causeOfChain p hCompose hn
      (hPaths x hx hxn)
  refine ⟨n, hn, hid, ?_⟩
  intro x hx hxn
  apply lt_iff_le_not_ge.mpr
  constructor
  · intro y hy
    have hyn : y ≠ n := by
      intro heq
      subst y
      exact hNoIncoming x hy
    exact ⟨fun h => hyn h.symm, hn, hy.2.2.1, hScope y hy.2.2.1 hyn⟩
  · intro hBack
    have hnx : n ≠ x := fun h => hxn h.symm
    have hxIn : x ∈ actualEsseEffects p n := ⟨hnx, hn, hx, hScope x hx hxn⟩
    exact (hBack hxIn).1 rfl

end TruthCore.Results.Causality.FullnessCandidates
