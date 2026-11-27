module

public import TruthCore.Causality.AxiarchicGuidance
public import TruthCore.Results.Causality.AxiarchicFoundation.Solution

@[expose] public section

namespace TruthCore.Results.Causality.AxiarchicGuidance

open TruthCore.Causality.AxiarchicGuidance
open TruthCore.Causality.GoodFavouring (Profile Tracks Fixed)
open TruthCore.Causality.AxiarchicFoundation (FavouringRealizedOnItems FavouringIrreflexive)

/-! ## Counterfactual guidance is a property of the profile and the value structure -/

/-- For a profile that tracks overall betterness, guidance by an outweighed reason
holds exactly when the value structure supplies it: the respect ranks `y` over
`x` and `x` is better overall at `s`, and some scenario agreeing on the control
keeps the respect's ranking and makes `y` better overall. Who bears the profile
plays no role. -/
theorem guidanceOfTracking {S X R Z : Type} (rk : R → S → X → X → Prop)
    (good : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (hφ : Tracks φ good)
    (s : S) (r : R) (x y : X) :
    GuidedByOutweighed rk good ctrl φ s r x y ↔
      rk r s y x ∧ good s x y ∧ ∃ t, ctrl t = ctrl s ∧ rk r t y x ∧ good t y x := by
  constructor
  · rintro ⟨⟨hr, hg, -⟩, t, hc, hrt, hφt⟩
    exact ⟨hr, hg, t, hc, hrt, (hφ t y x).1 hφt⟩
  · rintro ⟨hr, hg, t, hc, hrt, hgt⟩
    exact ⟨⟨hr, hg, (hφ s x y).2 hg⟩, t, hc, hrt, (hφ t y x).2 hgt⟩

/-- Label independence: two profiles that track the same feature receive the same
guidance verdicts. The personal source and the imitability-exemplar rival share
their profile, so this test cannot separate them. -/
theorem guidanceLabelIndependent {S X R Z : Type} (rk : R → S → X → X → Prop)
    (good : S → X → X → Prop) (ctrl : S → Z) (f : S → X → X → Prop) (φ ψ : Profile S X)
    (hφ : Tracks φ f) (hψ : Tracks ψ f) (s : S) (r : R) (x y : X) :
    GuidedByOutweighed rk good ctrl φ s r x y ↔ GuidedByOutweighed rk good ctrl ψ s r x y := by
  have hsame : ∀ s x y, φ s x y ↔ ψ s x y := fun s x y => (hφ s x y).trans (hψ s x y).symm
  constructor
  · rintro ⟨⟨hr, hg, h⟩, t, hc, hrt, ht⟩
    exact ⟨⟨hr, hg, (hsame s x y).1 h⟩, t, hc, hrt, (hsame t y x).1 ht⟩
  · rintro ⟨⟨hr, hg, h⟩, t, hc, hrt, ht⟩
    exact ⟨⟨hr, hg, (hsame s x y).2 h⟩, t, hc, hrt, (hsame t y x).2 ht⟩

/-- A fixed, asymmetric profile is guided by no outweighed reason: it favours
`x` over `y` in every scenario and so never `y` over `x`. -/
theorem fixedNotGuided {S X R Z : Type} (rk : R → S → X → X → Prop)
    (good : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (hfix : Fixed φ)
    (hasymm : ∀ s x y, φ s x y → ¬ φ s y x) (s : S) (r : R) (x y : X) :
    ¬ GuidedByOutweighed rk good ctrl φ s r x y := by
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

/-! ## Control -/

section Control

open TruthCore.Causality.AxiarchicGuidance.Control

theorem guidanceTable : GuidanceTable := by
  refine ⟨⟨⟨trivial, trivial, trivial⟩, .alt, rfl, trivial, trivial⟩,
    ⟨⟨trivial, trivial, rfl, rfl⟩, ?_⟩, ?_⟩
  · rintro ⟨-, t, -, -, ht⟩
    exact Cand.noConfusion ht.1
  · rintro ⟨-, -, h⟩
    exact h

end Control

end TruthCore.Results.Causality.AxiarchicGuidance
