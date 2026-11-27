module

public import TruthCore.Causality.AxiarchicGuidance
public import TruthCore.Results.Causality.AxiarchicFoundation.Solution

@[expose] public section

namespace TruthCore.Results.Causality.AxiarchicGuidance

open TruthCore.Causality.AxiarchicGuidance
open TruthCore.Causality.GoodFavouring (Profile Tracks Fixed)
open TruthCore.Causality.AxiarchicFoundation (FavouringRealizedOnItems FavouringIrreflexive)

/-! ## Counterfactual guidance by an outweighed reason -/

/-- A profile blind to respect `r` (the same wherever every other respect weighs
alike) is guided by no outweighed `r`-reason: raising `y` in `r` alone leaves it
favouring `x` over `y`, and asymmetry excludes `y` over `x`. -/
theorem respectBlindNotGuided {S X R Z : Type} (w : S → R → X → Nat)
    (good : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (r : R) (hBlind : BlindTo w φ r)
    (hasymm : ∀ s x y, φ s x y → ¬ φ s y x) (s : S) (x y : X) :
    ¬ GuidedByOutweighed w good ctrl φ s r x y := by
  rintro ⟨⟨-, -, h⟩, t, -, ⟨hOther, -, -⟩, ht⟩
  exact hasymm s x y h ((hBlind s t hOther y x).2 ht)

/-- A profile that follows one respect `r₀` alone (the D-nature's form when the
end content is one respect of a graded value) is guided by no outweighed reason
in any respect: an outweighed `r₀`-reason never arises for it, and it is blind to
every other respect. -/
theorem singleRespectTrackerNotGuided {S X R Z : Type} [DecidableEq R] (w : S → R → X → Nat)
    (good : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (r₀ : R)
    (hφ : ∀ s x y, φ s x y ↔ w s r₀ y < w s r₀ x) (s : S) (r : R) (x y : X) :
    ¬ GuidedByOutweighed w good ctrl φ s r x y := by
  rintro ⟨⟨hrw, -, h⟩, t, -, ⟨hOther, -, -⟩, ht⟩
  have h₀ : w s r₀ y < w s r₀ x := (hφ s x y).1 h
  by_cases hr : r = r₀
  · subst hr
    exact Nat.lt_asymm hrw h₀
  · have hx : w t r₀ x = w s r₀ x := hOther r₀ x (fun e => hr e.symm)
    have hy : w t r₀ y = w s r₀ y := hOther r₀ y (fun e => hr e.symm)
    have ht' : w t r₀ x < w t r₀ y := (hφ t y x).1 ht
    rw [hx, hy] at ht'
    exact Nat.lt_asymm ht' h₀

/-- For a profile tracking overall betterness, guidance holds exactly when the
value structure supplies it. Who bears the profile plays no role. -/
theorem guidanceOfTracking {S X R Z : Type} (w : S → R → X → Nat)
    (good : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (hφ : Tracks φ good)
    (s : S) (r : R) (x y : X) :
    GuidedByOutweighed w good ctrl φ s r x y ↔
      w s r x < w s r y ∧ good s x y ∧
        ∃ t, ctrl t = ctrl s ∧ RaisesOnly w s t r y ∧ good t y x := by
  constructor
  · rintro ⟨⟨hr, hg, -⟩, t, hc, hra, hφt⟩
    exact ⟨hr, hg, t, hc, hra, (hφ t y x).1 hφt⟩
  · rintro ⟨hr, hg, t, hc, hra, hgt⟩
    exact ⟨⟨hr, hg, (hφ s x y).2 hg⟩, t, hc, hra, (hφ t y x).2 hgt⟩

/-- Label independence: profiles tracking the same feature receive the same
guidance verdicts. -/
theorem guidanceLabelIndependent {S X R Z : Type} (w : S → R → X → Nat)
    (good : S → X → X → Prop) (ctrl : S → Z) (f : S → X → X → Prop) (φ ψ : Profile S X)
    (hφ : Tracks φ f) (hψ : Tracks ψ f) (s : S) (r : R) (x y : X) :
    GuidedByOutweighed w good ctrl φ s r x y ↔ GuidedByOutweighed w good ctrl ψ s r x y := by
  have hsame : ∀ s x y, φ s x y ↔ ψ s x y := fun s x y => (hφ s x y).trans (hψ s x y).symm
  constructor
  · rintro ⟨⟨hr, hg, h⟩, t, hc, hra, ht⟩
    exact ⟨⟨hr, hg, (hsame s x y).1 h⟩, t, hc, hra, (hsame t y x).1 ht⟩
  · rintro ⟨⟨hr, hg, h⟩, t, hc, hra, ht⟩
    exact ⟨⟨hr, hg, (hsame s x y).2 h⟩, t, hc, hra, (hsame t y x).2 ht⟩

/-- A fixed, asymmetric profile is guided by no outweighed reason. -/
theorem fixedNotGuided {S X R Z : Type} (w : S → R → X → Nat)
    (good : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (hfix : Fixed φ)
    (hasymm : ∀ s x y, φ s x y → ¬ φ s y x) (s : S) (r : R) (x y : X) :
    ¬ GuidedByOutweighed w good ctrl φ s r x y := by
  rintro ⟨⟨-, -, h⟩, t, -, -, ht⟩
  exact hasymm t x y ((hfix s t x y).1 h) ht

/-- Registration: if a respect's ranking is realized on stand-ins that carry only
an overall degree `deg`, and the ranking is irreflexive, then it ranks no
candidate over another of the same degree. A degree-only stand-in does not
register a respect in which two overall-tied candidates differ. -/
theorem degreeOnlyRegistersNoRespectBetweenTies {X C : Type} (rkr : X → X → Prop)
    (rel : C → C → Prop) (deg : X → C) (hReal : ∀ x y, rkr x y ↔ InvImage rel deg x y)
    (hIrr : ∀ x, ¬ rkr x x) (x y : X) (hTie : deg x = deg y) : ¬ rkr y x :=
  TruthCore.Results.Causality.AxiarchicFoundation.unindividuatedNotFavoured rkr rel deg hReal hIrr
    y x hTie.symm

/-! ## Self-application -/

/-- Self-application individuates at second order: with realization and
irreflexivity for second-order favourings, the stand-in of the bearer's own
favouring differs from that of `d`; with determinations as candidates the round-2
result is the second-order criterion. -/
theorem selfApplicationIndividuates {B D S X C : Type} (Has : B → D → Prop)
    (favours : Profile S X → D) (favours2 : Profile S D → D) (stand : B → D → C)
    (rel : B → Profile S D → S → C → C → Prop)
    (hReal : FavouringRealizedOnItems Has favours2 stand rel)
    (hIrr : FavouringIrreflexive Has favours2) (b : B) (h : SelfApplies Has favours favours2 b) :
    ∃ φ d, Has b (favours φ) ∧ stand b (favours φ) ≠ stand b d := by
  obtain ⟨ψ, φ, s, d, hψ, hφ, hfav⟩ := h
  exact ⟨φ, d, hφ, TruthCore.Results.Causality.AxiarchicFoundation.favouredIndividuated (ψ s)
    (rel b ψ s) (stand b) (hReal b ψ hψ s) (hIrr b ψ hψ s) _ _ hfav⟩

/-- The second-order standard is scenario-invariant, so no second-order profile
depends on it under any control (law 4). This does not make any profile `Fixed`;
see `SecondOrderStandardAt` for the scenario-relative reading. -/
theorem secondOrderStandardNotDependedOn {S X D Z : Type} (good : S → X → X → Prop)
    (favours : Profile S X → D) (ctrl : S → Z) (ψ : Profile S D) (s : S) (d d' : D) :
    ¬ TruthCore.Causality.GoodFavouring.DependsUnder (SecondOrderStandard good favours) ctrl ψ s
      d d' :=
  TruthCore.Results.Causality.GoodFavouring.goodDependenceLaws.2.2.2.1 S D Z _ ctrl ψ s d d'
    (fun _ _ _ => rfl)

/-- Under the scenario-relative standard, if each profile's agreement with value
is scenario-invariant (only where value does not vary, not the good-general
setting), the standard is invariant and nothing depends on it under any control. -/
theorem invariantAlignmentNoSecondOrderDependence {S X D Z : Type} (good : S → X → X → Prop)
    (favours : Profile S X → D)
    (hInv : ∀ φ s t, TruthCore.Causality.GoodFavouring.AlignedAt φ good s ↔
      TruthCore.Causality.GoodFavouring.AlignedAt φ good t)
    (ctrl : S → Z) (ψ : Profile S D) (s : S) (d d' : D) :
    ¬ TruthCore.Causality.GoodFavouring.DependsUnder (SecondOrderStandardAt good favours) ctrl ψ
      s d d' := by
  apply TruthCore.Results.Causality.GoodFavouring.goodDependenceLaws.2.2.2.1 S D Z _ ctrl ψ s d d'
  intro a b _
  funext e e'
  apply propext
  constructor
  · rintro ⟨φ, φ', h1, h2, h3, h4⟩
    exact ⟨φ, φ', h1, h2, (hInv φ a b).1 h3, fun h => h4 ((hInv φ' a b).2 h)⟩
  · rintro ⟨φ, φ', h1, h2, h3, h4⟩
    exact ⟨φ, φ', h1, h2, (hInv φ a b).2 h3, fun h => h4 ((hInv φ' a b).1 h)⟩

/-! ## Control -/

section Control

open TruthCore.Causality.AxiarchicGuidance.Control

theorem guidanceTable : GuidanceTable := by
  have hRaise : RaisesOnly w .base .raised .fit .d := by
    refine ⟨?_, ?_, by decide⟩
    · intro r' z hr; cases r' <;> cases z <;> first | rfl | exact absurd rfl hr
    · intro z hz; cases z <;> first | rfl | exact absurd rfl hz
  have hOutX : ∀ φ : Profile Scen Cand, φ .base .c .d → Outweighed w good φ .base .fit .c .d :=
    fun φ h => ⟨by decide, trivial, h⟩
  have hBlindExtra : BlindTo w extraOnly .fit := by
    intro s t hOther x y
    show w s .extra y < w s .extra x ↔ w t .extra y < w t .extra x
    rw [hOther .extra x (by decide), hOther .extra y (by decide)]
  have hAsymmExtra : ∀ s x y, extraOnly s x y → ¬ extraOnly s y x :=
    fun _ _ _ h h' => Nat.lt_asymm h h'
  have hFixed : Fixed fixedC := fun _ _ _ _ => Iff.rfl
  have hAsymmFixed : ∀ s x y, fixedC s x y → ¬ fixedC s y x := by
    rintro _ _ _ ⟨rfl, rfl⟩ ⟨h, -⟩; exact Cand.noConfusion h
  have hTrackGood : Tracks goodTracking good := fun _ _ _ => Iff.rfl
  have hNotTrackExtra : ¬ Tracks extraOnly good := by
    intro h
    have := (h .raised .c .d).1 (by decide : w Scen.raised .extra .d < w Scen.raised .extra .c)
    exact this
  refine ⟨hRaise, ⟨hOutX _ trivial, .raised, rfl, hRaise, trivial⟩,
    ⟨hOutX _ (show w .base .extra .d < w .base .extra .c by decide), respectBlindNotGuided w good noCtrl extraOnly .fit
      hBlindExtra hAsymmExtra .base .c .d⟩,
    ⟨hOutX _ ⟨rfl, rfl⟩, fixedNotGuided w good noCtrl fixedC hFixed hAsymmFixed .base .fit .c .d⟩,
    ?_, fun _ => ⟨goodTracking, extraOnly, rfl, rfl, hTrackGood, hNotTrackExtra⟩⟩
  rintro ⟨-, -, h⟩
  exact absurd (show w .base .fit .d < w .base .fit .c from h) (by decide)

/-- Lean-only: under the scenario-relative standard a second-order profile can
depend on it. The first-ranked favouring tracks value everywhere (it can be a
necessary source's own); the dependence comes from the alternative's agreement
varying, not from the bearer being contingent. -/
theorem scenarioRelativeStandardDependedOn :
    TruthCore.Causality.GoodFavouring.DependsUnder (SecondOrderStandardAt good id) noCtrl
      (SecondOrderStandardAt good id) .raised goodTracking extraOnly := by
  have hAlignG : ∀ s, TruthCore.Causality.GoodFavouring.AlignedAt goodTracking good s :=
    fun _ _ _ => Iff.rfl
  have hBaseAligned : TruthCore.Causality.GoodFavouring.AlignedAt extraOnly good .base := by
    intro x y
    cases x <;> cases y <;> simp [extraOnly, good, w]
  have hRaisedNot : ¬ TruthCore.Causality.GoodFavouring.AlignedAt extraOnly good .raised := by
    intro h
    exact (h .c .d).1 (show w .raised .extra .d < w .raised .extra .c by decide)
  have hStd : SecondOrderStandardAt good id .raised goodTracking extraOnly :=
    ⟨goodTracking, extraOnly, rfl, rfl, hAlignG _, hRaisedNot⟩
  refine ⟨hStd, hStd, .base, rfl, ?_, ?_⟩ <;>
  · rintro ⟨φ, φ', h1, h2, -, h4⟩
    subst h1; subst h2
    exact h4 hBaseAligned

end Control

end TruthCore.Results.Causality.AxiarchicGuidance
