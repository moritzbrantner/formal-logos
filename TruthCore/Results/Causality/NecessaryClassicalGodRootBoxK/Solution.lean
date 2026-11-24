module

public import TruthCore.Causality.NecessaryClassicalGodRootBoxK

/-! Structural projection (assembly), no new philosophical inference: the
witness of `NecessaryClassicalGodRootAt` is an actual root (first conjunct of
`PerfectRootAt`), its necessity `NecessaryAt m.ontic w n` is the box K
existence of the same bearer over the same frame (`necessaryAt_iff_boxExistsAt`,
`Iff.rfl`), and it is God, the one God (fourth of the nine case predicates)
and has the classical attributes. So the box K node of the sense fork holds
for the same signature, Profile and world. It closes the box K node only if its
premise is closed (invariant 16). Uniqueness of the selected root, maximum,
perfection, firstness, esse/essence identity, matter/form exclusion,
remoteness and the other eight case predicates are discarded. -/

@[expose] public section

namespace TruthCore.Results.Causality.NecessaryClassicalGodRootBoxK
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.NecessaryClassicalGodRootBoxK
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

theorem boxKOfClassicalGodRoot {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill) :
    NecessaryRootBoxK σ m w CN := by
  obtain ⟨n, ⟨hRoot, hNec, -, -, -⟩, -, -, -, -, hGod, hNine, hField⟩ := h
  exact ⟨n, (necessaryAt_iff_boxExistsAt m.ontic w n).mp hNec,
    hRoot, hGod, hNine.2.2.2.1, hField⟩

theorem separator : Separation.Separator := by
  refine ⟨⟨(), fun _ _ => trivial, ⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩,
    trivial, fun _ _ => rfl, trivial⟩, ?_⟩
  rintro ⟨_, -, -, -, -, -, -, hNine, -⟩
  exact hNine.2.2.2.2.2.2.2.1

end TruthCore.Results.Causality.NecessaryClassicalGodRootBoxK
