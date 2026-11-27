module

public import TruthCore.Causality.GoodFavouring

@[expose] public section

namespace TruthCore.Results.Causality.GoodFavouring

open TruthCore.Modal.STIT
open TruthCore.Causality.SelectionScope
open TruthCore.Causality.GoodFavouring
open TruthCore.Causality.GoodFavouring.Model
open TruthCore.Causality.PracticalSpecification (Plan Meets Clause)

/-! ## Part A -/

section A

variable {M H A X C : Type} {F : BranchingFrame M H A} {m : M}

theorem nontrivial (fav : C → X → X → Prop) (e : F.Through m → C) (out : F.Through m → X)
    (h : F.Through m) (hind : OutcomeIndependent e) (hasym : ∀ c, Std.Asymm (fav c))
    (hcont : ContingentOutcome h out) : ¬ SelectsAtEveryHistory fav e out := by
  intro hall
  obtain ⟨k, hk⟩ := hcont
  have h1 : fav (e h) (out h) (out k) := hall h (out k) ⟨k, rfl⟩ hk
  have h2 : fav (e k) (out k) (out h) := hall k (out h) ⟨h, rfl⟩ (Ne.symm hk)
  rw [hind k h] at h2
  exact (hasym (e h)).asymm _ _ h1 h2

theorem redescription (out : F.Through m → X) (h : F.Through m) :
    SelectsAtEveryHistory outcomeFavour out out ∧ (∀ c : X, Std.Asymm (outcomeFavour c)) ∧
      (ContingentOutcome h out → ¬ OutcomeIndependent out) := by
  refine ⟨fun k y _ hy => ⟨rfl, hy⟩, fun c => ⟨fun x y hxy hyx => hyx.2 hxy.1⟩, ?_⟩
  rintro ⟨k, hk⟩ hind
  exact hk (hind k h)

theorem invariant_independent (a : A) (e : F.Through m → C) (hinv : InvariantExplanans F m a)
    (hfac : ∀ h k, (F.choice m a).r h k → e h = e k) : OutcomeIndependent e :=
  fun h k => hfac h k (hinv h k)

theorem tie (fav : C → X → X → Prop) (e : F.Through m → C) (out : F.Through m → X)
    (h : F.Through m) (G : X → X → Prop) (y : X) (hb : GoodBounded fav e G)
    (hy : y ∈ RealizedRange out) (hne : y ≠ out h) (hG : ¬ G (out h) y) :
    ¬ FavouringSelects fav e h out :=
  fun hs => hG (hb h _ _ (hs y hy hne))

theorem noBest (fav : C → X → X → Prop) (e : F.Through m → C) (out : F.Through m → X)
    (h : F.Through m) (G : X → X → Prop) (hb : GoodBounded fav e G) (hG : Std.Asymm G)
    (himp : ∀ x ∈ RealizedRange out, ∃ y ∈ RealizedRange out, G y x) :
    ¬ FavouringSelects fav e h out := by
  intro hs
  obtain ⟨y, hy, hyx⟩ := himp (out h) ⟨h, rfl⟩
  have hne : y ≠ out h := by
    rintro rfl
    exact hG.asymm _ _ hyx hyx
  exact hG.asymm _ _ hyx (hb h _ _ (hs y hy hne))

end A

theorem favouringStandardLaws : FavouringStandardLaws :=
  ⟨fun _ _ _ _ _ _ _ fav e out h => nontrivial fav e out h,
    fun _ _ _ _ _ _ out h => redescription out h,
    fun _ _ _ _ _ _ a e => invariant_independent a e,
    fun _ _ _ _ _ _ _ fav e out h G y => tie fav e out h G y,
    fun _ _ _ _ _ _ _ fav e out h G => noBest fav e out h G⟩

/-! ## Part B -/

theorem goodDependenceLaws : GoodDependenceLaws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro S X Z g ctrl φ s x y hfac ⟨-, hφ, t, hct, -, hnt⟩
    exact hnt (by rw [hfac hct]; exact hφ)
  · rintro S X Z g ctrl φ s x y hfix ⟨-, hφ, t, -, -, hnt⟩
    exact hnt ((hfix s t x y).1 hφ)
  · intro S X Z f g ctrl φ s x y htr
    have htr' : ∀ s x y, φ s x y ↔ f s x y := htr
    simp only [DependsUnder, htr']
  · rintro S X Z g ctrl φ s x y hfac ⟨hg, -, t, hct, hng, -⟩
    exact hng (by rw [hfac hct]; exact hg)
  · intro S X f φ hfix htr s t x y
    rw [← htr s x y, ← htr t x y]
    exact hfix s t x y
  · intro S X Z f g ctrl φ ψ s x y hφ hψ
    have hφ' : ∀ s x y, φ s x y ↔ f s x y := hφ
    have hψ' : ∀ s x y, ψ s x y ↔ f s x y := hψ
    simp only [DependsUnder, hφ', hψ']
  · intro W B R E K X Z P desc app spec ctrl φ k x y
    exact ⟨rfl, Iff.rfl⟩
  · intro M H A X C F m fav fav' e out h hag
    exact ⟨fun y => hag _ _, fun hs y hy hne => (hag _ _).1 (hs y hy hne),
      fun hs y hy hne => (hag _ _).2 (hs y hy hne)⟩

/-! ## Part C -/

private theorem fits_actual (o : Outcome) : fits .actual o = true ↔ Fit o := by
  cases o <;> simp [fits, Fit]

private theorem fits_valueless : fits .valueless = fits .actual := by
  funext o
  cases o <;> rfl

private theorem range_frame (y : Outcome) :
    y ∈ RealizedRange (outcome : frame.Through () → Outcome) ↔ y = .c ∨ y = .d := by
  constructor
  · rintro ⟨⟨o, ho⟩, rfl⟩
    cases o
    · exact (show False from ho).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (show False from ho).elim
  · rintro (rfl | rfl)
    · exact ⟨hc, rfl⟩
    · exact ⟨hd, rfl⟩

private theorem bg1_dNature : BecauseOfContent fitOrder dNature .actual .c .z :=
  ⟨by simp [fitOrder, fits], by simp [dNature, fitOrder, fits], .reversal, rfl,
    by simp [fitOrder, fits], by simp [dNature, fitOrder, fits]⟩

private theorem bg1_goodGeneral : BecauseOfContent fitOrder goodGeneral .actual .c .z :=
  ⟨by simp [fitOrder, fits], by simp [goodGeneral, better, fitOrder, fits], .reversal, rfl,
    by simp [fitOrder, fits], by simp [goodGeneral, better, fitOrder, fits]⟩

private theorem bg2_goodGeneral : BecauseOfGoodness better fits goodGeneral .actual .c .z :=
  ⟨by simp [better, fitOrder, fits], by simp [goodGeneral, better, fitOrder, fits], .valueless,
    fits_valueless, by simp [better], by simp [goodGeneral, better]⟩

private theorem not_bg2_dNature : ¬ BecauseOfGoodness better fits dNature .actual .c .z := by
  rintro ⟨-, -, t, hct, -, hnt⟩
  exact hnt (by simp only [dNature, fitOrder, hct]; simp [fits])

theorem goodFavouringTable : GoodFavouringTable := by
  refine ⟨fits_actual, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨rfl, rfl⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro φ hφ
    have hsel : ∀ ψ : Profile Scenario Outcome, ¬ ψ .actual .c .d →
        ¬ FavouringSelects ψ (at_ .actual) hc outcome :=
      fun ψ hn hs => hn (hs .d ((range_frame _).2 (Or.inr rfl)) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, hsel _ ?_⟩ <;>
      simp [FavouringExplains, at_, hc, outcome, proxy, dNature, determinedWill, goodGeneral,
        rational, physOrder, fitOrder, better, physical, fits]
  · intro y h
    exact h
  · intro y hy hne
    rcases (range_frame y).1 hy with rfl | rfl
    · exact absurd rfl hne
    · simp [at_, hc, outcome, goodGeneral, better]
  · intro y hy hne
    rcases (range_frame y).1 hy with rfl | rfl
    · exact absurd rfl hne
    · simp [at_, hc, outcome, rational, better]
  · simp [FavouringExplains, at_, hc, outcome, dNature, fitOrder, fits]
  · simp [FavouringExplains, hc, outcome, proxy, physOrder, physical]
  · exact (redescription (F := frame) (m := ()) outcome hc).1
  · intro hind
    have h : Outcome.c = Outcome.d := hind hc hd
    cases h
  · intro C fav e hind hasym
    exact nontrivial fav e outcome hc hind hasym ⟨hd, by decide⟩
  · exact bg1_dNature
  · exact bg1_goodGeneral
  · exact bg1_goodGeneral
  · simp [proxy, physOrder, physical]
  · rintro ⟨-, -, t, -, -, hnt⟩
    exact hnt (by simp [proxy, physOrder, physical])
  · rintro ⟨-, h, -⟩
    exact h
  · exact bg2_goodGeneral
  · exact bg2_goodGeneral
  · exact ⟨by simp [dNature, fitOrder, fits], by simp [better, fitOrder, fits]⟩
  · exact not_bg2_dNature
  · exact not_bg2_dNature
  · rintro ⟨-, -, t, -, -, hnt⟩
    exact hnt (by simp [proxy, physOrder, physical])
  · rintro ⟨-, h, -⟩
    exact h
  · exact ⟨rfl, rfl, rfl⟩
  · simp [better, fitOrder, fits]
  · rintro ⟨hg, -⟩
    simp [better, fitOrder, fits] at hg
  · intro y hy hne
    rcases (range_frame y).1 hy with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inr ⟨rfl, rfl, rfl⟩
  · rintro ⟨hg, -⟩
    simp [better, fitOrder, fits] at hg
  · exact ⟨by simp [better, fitOrder, fits], by simp [dNature, fitOrder, fits], bg1_dNature⟩
  · rintro ⟨-, h⟩
    exact not_bg2_dNature h
  · exact ⟨⟨by simp [better, fitOrder, fits], by simp [goodGeneral, better, fitOrder, fits],
      bg1_goodGeneral⟩, bg2_goodGeneral⟩
  · rintro ⟨-, -, -, -, t, -, -, hnt⟩
    exact hnt (by simp [proxy, physOrder, physical])

end TruthCore.Results.Causality.GoodFavouring
