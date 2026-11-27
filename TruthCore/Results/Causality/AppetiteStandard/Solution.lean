module

public import TruthCore.Causality.AppetiteStandard
public import TruthCore.Results.Causality.PurityCriteria.Solution

@[expose] public section

namespace TruthCore.Results.Causality.AppetiteStandard

open TruthCore.Causality.AppetiteStandard
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple UnlimitedDeterminationsArePure)
open TruthCore.Causality.ImpersonalFoundationJoint (GoodGeneral ActualRootFavouringIsGoodGeneral)
open TruthCore.Causality.PurityCriteria
  (ValueStandardOrder BetternessVariesWithinEndClass MissesVerdict UnbackedVerdict
    MissingValueVerdictIsImpure UnbackedValueVerdictIsImpure)
open TruthCore.Causality.GoodFavouring (Tracks OriginalFinalityForGood)
open TruthCore.Logic (ExcludedMiddle)

/-! ## The formal-object route to horn A's conclusion -/

/-- Horn A's conclusion `7fca65ec` from the per-bearer standard and the object
premise. Let `r` be an actual root and `favours φ` one of its determinations.
Actual roots have no represented limiting principle (its distinct simply prior
being is the frame's `PriorSimply`), so by the RootPurity bridge `favours φ` is
pure. By the per-bearer bridge a pure favouring makes exactly the verdicts of its
formal object, and by the object premise that object is the value order `v`
(STANDARD_OF_FAVOURING_1). Betterness varies within an end-realization class, so
`φ` favours `x` over `y` at the witness scenario and not at the other scenario of
the same end-realization class: `φ` is good-general. Neither the per-bearer
bridge nor the object premise mentions whether the favouring is a natural or a
rational appetite. -/
theorem actualRootFavouringIsGoodGeneralFromFormalObject {W B T R D P S X Z : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop) (Composite : B → Prop) (essence esse : B → P)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (obj : TruthCore.Causality.GoodFavouring.Profile S X → S → X → X → Prop)
    (v : ValueStandardOrder S X) (fitOf : S → Z) (Present : S → X → Prop)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite F.PriorSimply essence esse)
    (hPurity : UnlimitedDeterminationsArePure Composite F.PriorSimply essence esse Has Pure)
    (hOwn : PureFavouringTracksItsObject Pure favours obj)
    (hObj : ActualRootFavouringObjectIsValue m w Has favours obj v)
    (hVaries : BetternessVariesWithinEndClass v fitOf Present) :
    ActualRootFavouringIsGoodGeneral m w Has favours v.better fitOf Present := by
  intro r hr φ hφ
  have hT : Tracks φ (obj φ) := hOwn φ (hPurity r (hRoots r hr) (favours φ) hφ)
  rw [hObj r hr φ hφ] at hT
  obtain ⟨s, x, y, ⟨hg, -, t, ht, hng, -⟩, hPres⟩ := hVaries
  exact ⟨s, x, y, ⟨hg, (hT s x y).2 hg, t, ht, hng, fun h => hng ((hT t x y).1 h)⟩, hPres⟩

/-! ## Mode: the fixer law and determination to one end (Lean-only) -/

/-- Lean-only FIXER LAW. If a favouring is fixed by a feature `f` and is
good-general, then `f` itself separates two scenarios of one end-realization
class at which the standard ranks the witnessing pair differently. Whatever
fixes a good-general favouring (a natural state, an apprehension state, the
value order itself) must carry the variation of value within an end-realization
class. -/
theorem fixerCarriesValueVariation {S X Z K : Type} (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (φ : TruthCore.Causality.GoodFavouring.Profile S X) (f : S → K)
    (hFix : FixedBy φ f) (hGG : GoodGeneral good fitOf Present φ) :
    ∃ s t x y, fitOf t = fitOf s ∧ f s ≠ f t ∧ good s x y ∧ ¬ good t x y := by
  obtain ⟨s, x, y, ⟨hg, hφ, t, ht, hng, hnφ⟩, -⟩ := hGG
  refine ⟨s, t, x, y, ht, fun hst => hnφ ?_, hg, hng⟩
  have hEq : φ s = φ t := hFix hst
  rw [← hEq]
  exact hφ

/-- Lean-only. A rational appetite of a constant apprehension state (in
particular of a bearer that apprehends nothing) is not good-general. -/
theorem constantApprehensionNotGoodGeneral {S X Z Y : Type} (good : S → X → X → Prop)
    (fitOf : S → Z) (Present : S → X → Prop) (a : ApprehensionState S Y)
    (φ : TruthCore.Causality.GoodFavouring.Profile S X) (hC : ConstantApprehension a)
    (hR : RationalAppetite a φ) : ¬ GoodGeneral good fitOf Present φ := by
  intro hGG
  obtain ⟨s, t, -, -, -, hne, -, -⟩ := fixerCarriesValueVariation good fitOf Present φ a.state hR hGG
  exact hne (hC s t)

/-- Lean-only. A natural appetite of a natural state determined to one end (ad
unum: the state factors through end-realization) is not good-general. -/
theorem adUnumNaturalNotGoodGeneral {S X Z K : Type} (good : S → X → X → Prop)
    (fitOf : S → Z) (Present : S → X → Prop) (n : NaturalState S K)
    (φ : TruthCore.Causality.GoodFavouring.Profile S X) (hAd : NaturalStateAdUnum n fitOf)
    (hN : NaturalAppetite n φ) : ¬ GoodGeneral good fitOf Present φ := by
  intro hGG
  obtain ⟨s, t, -, -, ht, hne, -, -⟩ := fixerCarriesValueVariation good fitOf Present φ n.state hN hGG
  exact hne (hAd ht.symm)

/-- Lean-only SEPARATION. Under the mode dichotomy (the favouring is a natural
appetite of `n` or a rational appetite of `a`) and determination of the natural
state to one end, a good-general favouring is a rational appetite. The
countermodel for dropping ad unum is row 1 of `AppetiteGrid`. -/
theorem goodGeneralIsRationalUnderAdUnum {S X Z K Y : Type} (good : S → X → X → Prop)
    (fitOf : S → Z) (Present : S → X → Prop) (n : NaturalState S K) (a : ApprehensionState S Y)
    (φ : TruthCore.Causality.GoodFavouring.Profile S X) (hAd : NaturalStateAdUnum n fitOf)
    (hMode : NaturalAppetite n φ ∨ RationalAppetite a φ) (hGG : GoodGeneral good fitOf Present φ) :
    RationalAppetite a φ :=
  hMode.resolve_left fun hN => adUnumNaturalNotGoodGeneral good fitOf Present n φ hAd hN hGG

/-- Lean-only. Under the mode dichotomy and ad unum, a bearer with a constant
apprehension state (a noncognitive bearer) has no good-general favouring. This
is the cognition criterion's exclusion for a noncognitive bearer, reached from
ad unum instead. -/
theorem adUnumNoncognitiveNotGoodGeneral {S X Z K Y : Type} (good : S → X → X → Prop)
    (fitOf : S → Z) (Present : S → X → Prop) (n : NaturalState S K) (a : ApprehensionState S Y)
    (φ : TruthCore.Causality.GoodFavouring.Profile S X) (hAd : NaturalStateAdUnum n fitOf)
    (hC : ConstantApprehension a) (hMode : NaturalAppetite n φ ∨ RationalAppetite a φ) :
    ¬ GoodGeneral good fitOf Present φ := fun hGG =>
  constantApprehensionNotGoodGeneral good fitOf Present a φ hC
    (goodGeneralIsRationalUnderAdUnum good fitOf Present n a φ hAd hMode hGG) hGG

/-! ## Object: per-bearer and common-value forms (Lean-only) -/

/-- Lean-only. The two value-sense bridges (`720bccc2`, `a141e6a8`, lane P's
common value standard) are the per-bearer bridge with every favouring measured
by value. -/
theorem valueBridgesArePerBearerConstant {D S X : Type} (Pure : D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D) (v : ValueStandardOrder S X)
    (hEM : ExcludedMiddle) (hLoss : MissingValueVerdictIsImpure Pure favours v)
    (hBacked : UnbackedValueVerdictIsImpure Pure favours v) :
    PureFavouringTracksItsObject Pure favours (fun _ => v.better) := by
  intro φ hP s x y
  exact ⟨fun hf => (hEM (v.better s x y)).elim id fun hn => (hBacked φ ⟨s, x, y, hf, hn⟩ hP).elim,
    fun hg => (hEM (φ s x y)).elim id fun hn => (hLoss φ ⟨s, x, y, hg, hn⟩ hP).elim⟩

/-- Lean-only converse of `valueBridgesArePerBearerConstant`: the per-bearer bridge
with every favouring measured by value gives both value-sense bridges. -/
theorem perBearerConstantGivesValueBridges {D S X : Type} (Pure : D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D) (v : ValueStandardOrder S X)
    (hOwn : PureFavouringTracksItsObject Pure favours (fun _ => v.better)) :
    MissingValueVerdictIsImpure Pure favours v ∧ UnbackedValueVerdictIsImpure Pure favours v :=
  ⟨fun φ ⟨s, x, y, hg, hn⟩ hP => hn ((hOwn φ hP s x y).2 hg),
    fun φ ⟨s, x, y, hf, hn⟩ hP => hn ((hOwn φ hP s x y).1 hf)⟩

/-- Lean-only. The per-bearer bridge and the object premise give, for every pure
favouring of an actual root, neither a missed nor an unbacked value verdict: the
value-sense bridges restricted to actual roots. -/
theorem perBearerAndObjectGiveRootValueVerdicts {W B D S X : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (obj : TruthCore.Causality.GoodFavouring.Profile S X → S → X → X → Prop)
    (v : ValueStandardOrder S X) (hOwn : PureFavouringTracksItsObject Pure favours obj)
    (hObj : ActualRootFavouringObjectIsValue m w Has favours obj v) :
    ∀ r, ActualRoot m w r → ∀ φ, Has r (favours φ) → Pure (favours φ) →
      ¬ MissesVerdict v.better φ ∧ ¬ UnbackedVerdict v.better φ := by
  intro r hr φ hφ hP
  have hT : Tracks φ (obj φ) := hOwn φ hP
  rw [hObj r hr φ hφ] at hT
  exact ⟨fun ⟨s, x, y, hg, hn⟩ => hn ((hT s x y).2 hg),
    fun ⟨s, x, y, hf, hn⟩ => hn ((hT s x y).1 hf)⟩

/-- Lean-only. The kind rule for rational appetite gives the object premise when
every favouring of an actual root is a rational appetite. The converse fails:
`FormalObjectControls` row 1 meets the object premise with a natural appetite
and no apprehension. -/
theorem rationalKindGivesObject {W B D S X Y : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (obj : TruthCore.Causality.GoodFavouring.Profile S X → S → X → X → Prop)
    (v : ValueStandardOrder S X) (app : B → ApprehensionState S Y)
    (hKind : RationalObjectIsValue app obj v)
    (hRat : ∀ r, ActualRoot m w r → ∀ φ, Has r (favours φ) → RationalAppetite (app r) φ) :
    ActualRootFavouringObjectIsValue m w Has favours obj v :=
  fun r hr φ hφ => hKind r φ (hRat r hr φ hφ)

/-- Lean-only. ORIGINAL_FINALITY_2 at one scenario and pair, with one candidate
not a present input, is good-generality of the same profile. Reading commitment
(e) in sense 2 at a root (where nothing is a present input) therefore delivers
horn A's conclusion for that favouring without the purity family. -/
theorem originalFinalityForGoodGivesGoodGeneral {S X Z : Type} (good fit : S → X → X → Prop)
    (fitOf : S → Z) (Present : S → X → Prop) (φ : TruthCore.Causality.GoodFavouring.Profile S X)
    (s : S) (x y : X) (h : OriginalFinalityForGood good fit fitOf φ s x y)
    (hP : ¬ Present s x ∨ ¬ Present s y) : GoodGeneral good fitOf Present φ :=
  ⟨s, x, y, h.2, hP⟩

/-! ## Finite controls -/

section Controls

open TruthCore.Causality.AppetiteStandard.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok noInputs hasSrc personalSrc dNatureSrc purePos pureNoGG roots criterion appSource
    appNone)
open TruthCore.Causality.PurityCriteria.Control (purity varies generalFor chanceSrc pureChance)
open TruthCore.Results.Causality.ImpersonalFoundationJoint (ggBetter dNatureFactors notGGdNature
  dNatureNeBetter)

private theorem betterActualCBetterDiffer : better .actual ≠ better .cBetter := by
  intro h
  have := congrFun (congrFun h .c) .d
  simp [better, fitOrder, fits] at this

private theorem fitOrderActualReversalDiffer : fitOrder .actual ≠ fitOrder .reversal := by
  intro h
  have := congrFun (congrFun h .c) .z
  simp [fitOrder, fits] at this

private theorem fitsActualCBetter : fits .actual = fits .cBetter := by
  funext o
  cases o <;> rfl

private theorem natContentBetter : NaturalAppetite contentState better :=
  fun _ _ h => congrArg better h

private theorem notRatNoneBetter : ¬ RationalAppetite noApprehension better :=
  fun h => betterActualCBetterDiffer (h (a := .actual) (b := .cBetter) rfl)

private theorem notCriterionNone : ¬ criterion personalSrc appNone := by
  intro h
  obtain ⟨_, _, -, hc⟩ := h true better (by simp [hasSrc, personalSrc, favTok]) ggBetter
  exact hc

private theorem criterionSource : criterion personalSrc appSource := by
  intro x φ hφ _
  cases x
  · simp [hasSrc, favTok] at hφ
  · exact ⟨.c, .c, rfl, rfl⟩

private theorem purePosFavH (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : purePos (Det.fav φ)) : φ = better := by
  rcases h with h | h | h
  · exact Det.noConfusion h
  · exact Det.noConfusion h
  · exact Det.fav.inj h

private theorem pureNoGGFavH (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : pureNoGG (Det.fav φ)) : φ = dNature := by
  rcases h with h | h
  · exact Det.noConfusion h
  · exact Det.fav.inj h

private theorem ownPosBetter : ownObj purePos (objAll better) := by
  intro φ hP
  obtain rfl := purePosFavH φ hP
  exact fun _ _ _ => Iff.rfl

private theorem ownNoGGFit : ownObj pureNoGG (objAll fitOrder) := by
  intro φ hP
  obtain rfl := pureNoGGFavH φ hP
  exact fun _ _ _ => Iff.rfl

private theorem objectAll (src : Set Det) (std : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome) :
    object src (objAll std) std :=
  fun _ _ _ _ => rfl

theorem appetiteGrid : AppetiteGrid := by
  refine ⟨⟨natContentBetter, notRatNoneBetter, ggBetter, ?_⟩,
    ⟨fun _ _ h => congrArg better h, fun h => betterActualCBetterDiffer (h (a := .actual)
      (b := .cBetter) rfl), ggBetter⟩,
    ⟨dNatureFactors, fun _ _ h => h, fun h => fitOrderActualReversalDiffer
      (h (a := .actual) (b := .reversal) rfl), notGGdNature⟩,
    ⟨fun _ _ h => congrArg determinedWill h, fun h => fitOrderActualReversalDiffer
      (h (a := .actual) (b := .reversal) rfl), notGGdNature⟩,
    ⟨fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      ⟨.cBetter, .c, .d, Or.inr ⟨rfl, rfl⟩, by simp [determinedWill, fitOrder, fits]⟩⟩,
    ⟨fun ⟨_, _, _, h, hn⟩ => hn h, fun ⟨_, _, _, h, hn⟩ => hn h,
      ⟨.cBetter, .c, .d, Or.inr ⟨rfl, rfl⟩, by simp [dNature, fitOrder, fits]⟩⟩,
    criterionSource, notCriterionNone⟩
  intro h
  have := h fitsActualCBetter
  exact Scenario.noConfusion this

theorem formalObjectControls : FormalObjectControls := by
  obtain ⟨⟨hR, hPurPos, -, -, hVar, hGenPos⟩, ⟨hNotR, hPurComp, -, -, -, hGenD⟩,
    ⟨-, hNotPurD, -, -, -, -⟩, ⟨-, hPurChance, -, -, -, hGenChance⟩, -,
    ⟨-, hPurNoGG, -, -, hNotVarFit, hGenFit⟩⟩ :=
    TruthCore.Results.Causality.PurityCriteria.standardControls
  refine ⟨⟨hR, hPurPos, ownPosBetter, objectAll _ _, hVar, hGenPos, natContentBetter,
      notRatNoneBetter, notCriterionNone⟩,
    ⟨hNotR, hPurComp, ownPosBetter, objectAll _ _, hVar, hGenD⟩,
    ⟨hR, hNotPurD, ownPosBetter, objectAll _ _, hVar, hGenD⟩,
    ⟨hR, hPurChance, ?_, objectAll _ _, hVar, hGenChance⟩,
    ⟨hR, hPurNoGG, ownNoGGFit, ?_, hVar, hGenD⟩,
    ⟨hR, hPurNoGG, ownNoGGFit, objectAll _ _, hNotVarFit, hGenFit⟩⟩
  · intro h
    exact ((h chance (Or.inr rfl)) .actual .c .z).2 (show fitOrder .actual .c .z from ⟨rfl, rfl⟩)
  · intro h
    exact dNatureNeBetter (h true ((TruthCore.Results.Causality.RootPerfectionExclusion.rootIff true).2 rfl)
      dNature (by simp [hasSrc, dNatureSrc, favTok]))

end Controls

end TruthCore.Results.Causality.AppetiteStandard
