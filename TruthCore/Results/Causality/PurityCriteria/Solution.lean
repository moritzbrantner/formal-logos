module

public import TruthCore.Causality.PurityCriteria
public import TruthCore.Results.Causality.ImpersonalFoundationJoint.Solution
public import TruthCore.Results.Causality.RootPerfectionIntellect.Solution

@[expose] public section

namespace TruthCore.Results.Causality.PurityCriteria

open TruthCore.Causality.PurityCriteria
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple UnlimitedDeterminationsArePure)
open TruthCore.Causality.ImpersonalFoundationJoint
  (GoodGeneral ActualRootFavouringIsGoodGeneral OneFavouringRealization)
open TruthCore.Causality.RootPerfectionIntellect (ExclusionFreeAdmissible PureRequiresNoPureLack)
open TruthCore.Causality.RootPerfectionExclusion (ActualProfile UnexplainedAbsence)
open TruthCore.Logic (ExcludedMiddle)

/-! ## A. The standard route to horn A's conclusion -/

/-- Horn A's conclusion `7fca65ec` without the admissible family, joint
compossibility, the purity of good-generality or one-favouring realization.
Let `r` be an actual root and `favours φ` one of its determinations. Actual roots
have no represented limiting principle, so by the RootPurity bridge `favours φ`
is pure. By the loss and arbitrariness bridges (and excluded middle), `φ` makes
exactly the verdicts of the standard `good`. Betterness varies within an
end-realization class, so the standard itself is good-general, and a profile with
exactly its verdicts is good-general at the same witness. The distinct simply
prior being of the limiting principle is the frame's `PriorSimply`. -/
theorem actualRootFavouringIsGoodGeneralFromStandard {W B T R D P S X Z : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop) (Composite : B → Prop) (essence esse : B → P)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (hEM : ExcludedMiddle)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite F.PriorSimply essence esse)
    (hPurity : UnlimitedDeterminationsArePure Composite F.PriorSimply essence esse Has Pure)
    (hLoss : MissingVerdictIsImpure Pure favours good)
    (hBacked : UnbackedVerdictIsImpure Pure favours good)
    (hVaries : BetternessVariesWithinEndClass good fitOf Present) :
    ActualRootFavouringIsGoodGeneral m w Has favours good fitOf Present := by
  intro r hr φ hφ
  have hP : Pure (favours φ) := hPurity r (hRoots r hr) (favours φ) hφ
  have hGe : ∀ s x y, good s x y → φ s x y := fun s x y hg =>
    (hEM (φ s x y)).elim id fun hn => (hLoss φ ⟨s, x, y, hg, hn⟩ hP).elim
  have hLe : ∀ s x y, φ s x y → good s x y := fun s x y hf =>
    (hEM (good s x y)).elim id fun hn => (hBacked φ ⟨s, x, y, hf, hn⟩ hP).elim
  obtain ⟨s, x, y, ⟨hg, -, t, ht, hng, -⟩, hPres⟩ := hVaries
  exact ⟨s, x, y, ⟨hg, hGe s x y hg, t, ht, hng, fun h => hng (hLe t x y h)⟩, hPres⟩

/-- Lean-only. The two standard bridges give one favouring per actual root: two
favouring determinations of an actual root are pure, so both track `good` and
name the same profile. A bearer-level counterpart of the uniqueness clause of
`3e6ae3e7`, derived, not that statement (which concerns admissible profiles). -/
theorem actualRootHasOneFavouringFromStandard {W B T R D P S X : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop) (Composite : B → Prop) (essence esse : B → P)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop)
    (hEM : ExcludedMiddle)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite F.PriorSimply essence esse)
    (hPurity : UnlimitedDeterminationsArePure Composite F.PriorSimply essence esse Has Pure)
    (hLoss : MissingVerdictIsImpure Pure favours good)
    (hBacked : UnbackedVerdictIsImpure Pure favours good) :
    ∀ r, ActualRoot m w r → ∀ φ ψ, Has r (favours φ) → Has r (favours ψ) → φ = ψ := by
  intro r hr φ ψ hφ hψ
  have hTrack : ∀ χ, Has r (favours χ) → ∀ s x y, χ s x y ↔ good s x y := by
    intro χ hχ s x y
    have hP : Pure (favours χ) := hPurity r (hRoots r hr) (favours χ) hχ
    exact ⟨fun hf => (hEM (good s x y)).elim id fun hn => (hBacked χ ⟨s, x, y, hf, hn⟩ hP).elim,
      fun hg => (hEM (χ s x y)).elim id fun hn => (hLoss χ ⟨s, x, y, hg, hn⟩ hP).elim⟩
  funext s x y
  exact propext ((hTrack φ hφ s x y).trans (hTrack ψ hψ s x y).symm)

/-- Lean-only. Horn A's premises entail the variation premise: pure admissibility,
the purity of good-generality and one-favouring realization give a good-general
profile, whose dependence on `good` is a variation witness for `good` itself. -/
theorem hornAPremisesGiveVariation {D S X Z : Type} (Admissible : Set D → Prop)
    (Pure : D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (goodGen : D) (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (hPureAdm : TruthCore.Causality.RootPerfectionExclusion.PureDeterminationsAdmissible
      Admissible Pure)
    (hPureGG : TruthCore.Causality.ImpersonalFoundationJoint.GoodGeneralityIsPure Pure goodGen)
    (hOne : OneFavouringRealization Admissible favours goodGen good fitOf Present) :
    BetternessVariesWithinEndClass good fitOf Present := by
  obtain ⟨q, hq, hg⟩ := hPureAdm goodGen hPureGG
  obtain ⟨ψ, -, hgg⟩ := hOne q hq
  obtain ⟨s, x, y, ⟨hs, -, t, ht, hnt, -⟩, hPres⟩ := hgg hg
  exact ⟨s, x, y, ⟨hs, hs, t, ht, hnt, hnt⟩, hPres⟩

/-- Lean-only. If betterness varies within an end-realization class, every
profile that factors through end-realization (a nature determined to its end
content) either misses a verdict of the standard or makes an unbacked one, at
the two scenarios of the variation witness. -/
theorem variationForcesLossOrArbitrariness {S X Z : Type} (good : S → X → X → Prop)
    (fitOf : S → Z) (Present : S → X → Prop) (hVaries : BetternessVariesWithinEndClass good fitOf Present)
    (φ : TruthCore.Causality.GoodFavouring.Profile S X) (hFac : Function.FactorsThrough φ fitOf) :
    MissesVerdict good φ ∨ UnbackedVerdict good φ := by
  obtain ⟨s, x, y, ⟨hg, -, t, ht, hng, -⟩, -⟩ := hVaries
  by_cases hφ : φ s x y
  · have hEq : φ t = φ s := hFac ht
    exact Or.inr ⟨t, x, y, by rw [hEq]; exact hφ, hng⟩
  · exact Or.inl ⟨s, x, y, hg, hφ⟩

/-! ## Symmetric alternatives -/

/-- Lean-only. The favouring tokens of one-favouring realization are exclusive. -/
theorem favouringTokensExclusive {D S X Z : Type} (Admissible : Set D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D) (goodGen : D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (hOne : OneFavouringRealization Admissible favours goodGen good fitOf Present) :
    ExclusiveTokens Admissible favours := by
  intro q hq a b ha hb
  obtain ⟨ψ, hu, -⟩ := hOne q hq
  exact (hu a ha).trans (hu b hb).symm

/-- Lean-only. Under the requirement-form premises of #2162 (the sufficiency
direction of member grounding and "no pure determination requires the lack of
pure determinations"), two distinct exclusive tokens are not both pure: the pair
would be an all-pure, hence admissible, profile with two tokens. -/
theorem exclusiveAlternativesNotBothPure {D A : Type} (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (Pure : D → Prop) (tok : A → D)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure)
    (hEx : ExclusiveTokens Admissible tok) {a b : A} (hab : a ≠ b) :
    ¬ (Pure (tok a) ∧ Pure (tok b)) := by
  rintro ⟨ha, hb⟩
  have hAdm : Admissible {tok a, tok b} :=
    TruthCore.Results.Causality.RootPerfectionIntellect.allPureAdmissible Admissible RequiresLack
      Pure hSuff hPure _ fun d hd => by
        rcases hd with rfl | hd
        · exact ha
        · rw [Set.mem_singleton_iff.1 hd]; exact hb
  exact hab (hEx _ hAdm a b (by simp) (by simp))

/-- Lean-only. An intrinsic choice token `tok a` with an exclusive alternative
`tok b` on a par in purity is had by no actual root, under RootPurity and the
requirement-form premises. It hits personal and impersonal roots alike and does
not touch a selection that is not a token of the root's profile. -/
theorem parAlternativeExcludedAtRoot {W B D P A : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P)
    (tok : A → D)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite Prior essence esse)
    (hPurity : UnlimitedDeterminationsArePure Composite Prior essence esse Has Pure)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure)
    (hEx : ExclusiveTokens Admissible tok) {a b : A} (hab : a ≠ b)
    (hPar : PurityParity Pure tok a b) :
    ∀ r, ActualRoot m w r → ¬ Has r (tok a) := by
  intro r hr ha
  have hPa : Pure (tok a) := hPurity r (hRoots r hr) _ ha
  exact exclusiveAlternativesNotBothPure Admissible RequiresLack Pure tok hSuff hPure hEx hab
    ⟨hPa, hPar.1 hPa⟩

/-! ## D. Two favourings and their union -/

/-- Lean-only. If `ψ` has a good-generality witness at which `φ` is silent, the
union `ψ ⊔ φ` is good-general at the same witness. With `φ` factoring through
end-realization, silence at the witness scenario suffices. -/
theorem unionGoodGeneral {S X Z : Type} (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (ψ φ : TruthCore.Causality.GoodFavouring.Profile S X)
    (hFac : Function.FactorsThrough φ fitOf)
    (hW : ∃ s x y, (TruthCore.Causality.GoodFavouring.BecauseOfGoodness good fitOf ψ s x y ∧
      (¬ Present s x ∨ ¬ Present s y)) ∧ ¬ φ s x y) :
    GoodGeneral good fitOf Present (ψ ⊔ φ) := by
  obtain ⟨s, x, y, ⟨⟨hg, hψ, t, ht, hng, hnψ⟩, hPres⟩, hnφ⟩ := hW
  have hEq : φ t = φ s := hFac ht
  refine ⟨s, x, y, ⟨hg, Or.inl hψ, t, ht, hng, ?_⟩, hPres⟩
  rintro (h | h)
  · exact hnψ h
  · exact hnφ (by rw [← hEq]; exact h)

/-! ## B. The enumerative rule overgeneralizes -/

/-- Lean-only reference-class core. If every known instance of every kind has a
feature (finitude) that is impure, the enumerative rule makes that feature
constitutive of every kind with a known instance, and so no such kind is pure. A
position that holds some determination pure while it is known only through
finite instances cannot also hold the rule. -/
theorem enumerativeRuleOvergeneralizes {Y K F : Type} (KnownInstance : Y → K → Prop)
    (HasFeature : Y → F → Prop) (Constitutive : F → K → Prop) (ImpureFeature : F → Prop)
    (PureKind : K → Prop) (fin : F) (k₀ : K)
    (hRule : EnumerativeConstitutivity KnownInstance HasFeature Constitutive)
    (hImp : ImpureConstitutiveMakesImpure Constitutive ImpureFeature PureKind)
    (hFinImpure : ImpureFeature fin) (hAllFinite : ∀ y k, KnownInstance y k → HasFeature y fin)
    (hPure : PureKind k₀) (hKnown : ∃ y, KnownInstance y k₀) : False :=
  hImp k₀ fin (hRule k₀ fin hKnown fun y hy => hAllFinite y k₀ hy) hFinImpure hPure

/-! ## C. Tensed omniscience and immutability -/

/-- Lean-only core of the tensed reading: a knower whose state is tensed-omniscient,
veridical and immutable is impossible as soon as some content is true at one
time and false at another. -/
theorem tensedOmniscienceExcludesImmutability {T C : Type} (TrueAt KnowsAt : T → C → Prop)
    (hOmni : TensedOmniscience TrueAt KnowsAt) (hVer : Veridical TrueAt KnowsAt)
    (hImm : ImmutableState KnowsAt) (hTensed : HasTensedContent TrueAt) : False := by
  obtain ⟨c, t, t', hc, hnc⟩ := hTensed
  exact hnc (hVer t' c ((hImm t t' c).1 (hOmni t c hc)))

/-! ## Controls -/

section Controls

open TruthCore.Causality.PurityCriteria.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok noInputs hasSrc personalSrc dNatureSrc purePos pureNoGG roots gg anyFamily)
open TruthCore.Results.Causality.ImpersonalFoundationJoint
  (ggBetter dNatureFactors notGGdNature dNatureNeBetter factorsThroughNotGoodGeneral)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootPerfectionExclusion.Control (composite rep)

private theorem rootIffP (r : Bool) : ActualRoot rootProfile true r ↔ r = true :=
  TruthCore.Results.Causality.RootPerfectionExclusion.rootIff r

private theorem rootsIffP (c : Prop) : roots c ↔ ¬ c :=
  TruthCore.Results.Causality.RootPerfectionExclusion.rootsIff c

private theorem limitingIffP (c : Prop) (x : Bool) :
    TruthCore.Causality.RootMultiplication.HasLimitingPrinciple (composite c)
      TruthCore.Causality.ImpersonalFoundationJoint.Control.jointFrame.PriorSimply rep rep x ↔
      (x = true ∧ c) ∨ x = false :=
  TruthCore.Results.Causality.RootPerfectionExclusion.limitingIff c x

private theorem purityOf (src : Set Det) (pure : Det → Prop) (c : Prop)
    (h : ¬ c → ∀ d ∈ src, pure d) : purity src pure c := by
  intro x hx d hd
  cases x with
  | false => exact (hx ((limitingIffP c false).2 (Or.inr rfl))).elim
  | true =>
    have hc : ¬ c := fun hc => hx ((limitingIffP c true).2 (Or.inl ⟨rfl, hc⟩))
    exact h hc d hd

private theorem notPurityOf (src : Set Det) (pure : Det → Prop) (d : Det) (hd : d ∈ src)
    (hn : ¬ pure d) : ¬ purity src pure False := by
  intro h
  exact hn (h true (fun hl => by
    rcases (limitingIffP False true).1 hl with ⟨-, h⟩ | h
    · exact h
    · exact Bool.noConfusion h) d hd)

private theorem notGeneralOf (std : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (src : Set Det) (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (hφ : Det.fav φ ∈ src) (hn : ¬ GoodGeneral std fits noInputs φ) : ¬ generalFor std src :=
  fun h => hn (h true ((rootIffP true).2 rfl) φ hφ)

private theorem constNotGG (std : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome) (h : ∀ s t, φ s = φ t) :
    ¬ GoodGeneral std fits noInputs φ :=
  factorsThroughNotGoodGeneral std fits noInputs φ fun a b _ => h a b

/-- A token of `purePos` that is a favouring names `better`. -/
private theorem purePosFav (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : purePos (Det.fav φ)) : φ = better := by
  rcases h with h | h | h
  · exact Det.noConfusion h
  · exact Det.noConfusion h
  · exact Det.fav.inj h

private theorem lossOf (pure : Det → Prop) (std φ₀ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (hOnly : ∀ φ, pure (Det.fav φ) → φ = φ₀) (h : ¬ MissesVerdict std φ₀) : loss pure std := by
  intro φ hm hp
  exact h (hOnly φ hp ▸ hm)

private theorem backedOf (pure : Det → Prop) (std φ₀ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (hOnly : ∀ φ, pure (Det.fav φ) → φ = φ₀) (h : ¬ UnbackedVerdict std φ₀) : backed pure std := by
  intro φ hm hp
  exact h (hOnly φ hp ▸ hm)

private theorem noMissSelf (std : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome) :
    ¬ MissesVerdict std std := fun ⟨_, _, _, h, hn⟩ => hn h

private theorem noUnbackedSelf (std : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome) :
    ¬ UnbackedVerdict std std := fun ⟨_, _, _, h, hn⟩ => hn h

private theorem chanceOnly (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : pureChance (Det.fav φ)) : φ = chance := by
  rcases h with h | h
  · exact Det.noConfusion h
  · exact Det.fav.inj h

private theorem everythingOnly (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : pureEverything (Det.fav φ)) : φ = everything := by
  rcases h with h | h
  · exact Det.noConfusion h
  · exact Det.fav.inj h

private theorem dNatureOnly (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : pureNoGG (Det.fav φ)) : φ = dNature := by
  rcases h with h | h
  · exact Det.noConfusion h
  · exact Det.fav.inj h

private theorem variesBetter : varies better := ggBetter

theorem standardControls : StandardControls := by
  have hR : roots False := (rootsIffP False).2 id
  have hLossPos : loss purePos better := lossOf _ _ _ purePosFav (noMissSelf better)
  have hBackPos : backed purePos better := backedOf _ _ _ purePosFav (noUnbackedSelf better)
  have hGenD : ¬ generalFor better dNatureSrc :=
    notGeneralOf _ _ dNature (by simp [dNatureSrc]) notGGdNature
  refine ⟨⟨hR, ?_, hLossPos, hBackPos, variesBetter, ?_⟩,
    ⟨fun h => (rootsIffP True).1 h trivial, ?_, hLossPos, hBackPos, variesBetter, hGenD⟩,
    ⟨hR, ?_, hLossPos, hBackPos, variesBetter, hGenD⟩,
    ⟨hR, ?_, ?_, ?_, variesBetter, ?_⟩,
    ⟨hR, ?_, ?_, ?_, variesBetter, ?_⟩,
    ⟨hR, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- row 1
  · refine purityOf _ _ _ (fun _ d hd => ?_)
    simp [personalSrc] at hd
    rcases hd with rfl | rfl | rfl <;> simp [purePos]
  · intro r hr φ hφ
    obtain rfl := (rootIffP r).1 hr
    simp [favTok, hasSrc, personalSrc] at hφ
    subst hφ
    exact ggBetter
  -- row 2
  · exact purityOf _ _ _ (fun h => (h trivial).elim)
  -- row 3
  · refine notPurityOf _ _ (Det.fav dNature) (by simp [dNatureSrc]) fun h => ?_
    exact dNatureNeBetter (purePosFav _ h)
  -- row 4
  · refine purityOf _ _ _ (fun _ d hd => ?_)
    simp [chanceSrc] at hd
    rcases hd with rfl | rfl <;> simp [pureChance]
  · intro h
    exact h chance ⟨.actual, .c, .z, by simp [better, fitOrder, fits], fun h => h⟩ (Or.inr rfl)
  · exact backedOf _ _ _ chanceOnly fun ⟨_, _, _, h, _⟩ => h
  · exact notGeneralOf _ _ chance (by simp [chanceSrc]) (constNotGG _ _ fun _ _ => rfl)
  -- row 5
  · refine purityOf _ _ _ (fun _ d hd => ?_)
    simp [everythingSrc] at hd
    rcases hd with rfl | rfl <;> simp [pureEverything]
  · exact lossOf _ _ _ everythingOnly fun ⟨_, _, _, _, hn⟩ => hn trivial
  · intro h
    exact h everything ⟨.actual, .c, .c, trivial, by simp [better, fitOrder]⟩ (Or.inr rfl)
  · exact notGeneralOf _ _ everything (by simp [everythingSrc]) (constNotGG _ _ fun _ _ => rfl)
  -- row 6
  · refine purityOf _ _ _ (fun _ d hd => ?_)
    simp [dNatureSrc] at hd
    rcases hd with rfl | rfl <;> simp [pureNoGG]
  · exact lossOf _ _ _ dNatureOnly (noMissSelf fitOrder)
  · exact backedOf _ _ _ dNatureOnly (noUnbackedSelf fitOrder)
  · exact factorsThroughNotGoodGeneral fitOrder fits noInputs fitOrder dNatureFactors
  · exact notGeneralOf _ _ dNature (by simp [dNatureSrc])
      (factorsThroughNotGoodGeneral fitOrder fits noInputs dNature dNatureFactors)

theorem standardRelativity : StandardRelativity := by
  refine ⟨?_, ⟨Or.inr ⟨rfl, rfl⟩, by simp [dNature, fitOrder, fits]⟩,
    ⟨.cBetter, .c, .d, Or.inr ⟨rfl, rfl⟩, by simp [dNature, fitOrder, fits]⟩,
    ⟨.cBetter, .c, .d, Or.inr ⟨rfl, rfl⟩, by simp [fitOrder, fits]⟩,
    noMissSelf _, noUnbackedSelf _, noMissSelf _, noUnbackedSelf _⟩
  intro s x y hs hne
  cases s <;> cases x <;> cases y <;> simp_all [dNature, better, fitOrder, fits]

theorem refinementCondemnsGoodTracking : RefinementCondemnsGoodTracking := by
  refine ⟨le_sup_left, ?_, ?_, ⟨.reversal, .c, .z, Or.inr ?_, ?_⟩⟩
  · intro h
    have := congrFun (congrFun (congrFun h .reversal) .c) .z
    simp [better, fitOrder, fits, physTieBreak, physOrder, physical] at this
  · intro s x y ⟨h1, h2⟩
    rcases h2 with h2 | ⟨-, h2⟩
    · cases s <;> cases x <;> cases y <;> simp_all [better, fitOrder, fits]
    · exact h2 h1
  · simp [better, fitOrder, fits, physTieBreak, physOrder, physical]
  · simp [better, fitOrder, fits]

/-- Lean-only. The two non-conflicting favourings of row 7 of horn A's controls
(the D-directed and the good-tracking profile), read as one real favouring, give
a good-general union. In the row-7 family every profile is admissible, so the
D-directed root's lack of the good-generality token and of the good-tracking
favouring are unexplained absences (case (iii)): the row violates the #2153 E
premise. -/
theorem rowSevenUnionAndAbsence :
    gg (better ⊔ dNature) ∧
    UnexplainedAbsence anyFamily (hasSrc dNatureSrc) true Det.goodGen ∧
    UnexplainedAbsence anyFamily (hasSrc dNatureSrc) true (Det.fav better) := by
  refine ⟨unionGoodGeneral better fits noInputs better dNature dNatureFactors
    ⟨.cBetter, .c, .d, ⟨⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, .actual,
      by funext o; cases o <;> rfl, by simp [better, fitOrder, fits],
      by simp [better, fitOrder, fits]⟩, Or.inl id⟩, ?_⟩, ?_, ?_⟩
  · simp [dNature, fitOrder, fits]
  · refine ⟨by simp [hasSrc, dNatureSrc], ⟨insert Det.goodGen dNatureSrc, trivial,
      fun d hd => Set.mem_insert_of_mem _ hd, Set.mem_insert _ _⟩⟩
  · refine ⟨fun h => ?_, ⟨insert (Det.fav better) dNatureSrc, trivial,
      fun d hd => Set.mem_insert_of_mem _ hd, Set.mem_insert _ _⟩⟩
    simp [hasSrc, dNatureSrc] at h
    exact dNatureNeBetter h.symm

theorem tenselessReading : TenselessReading := by
  refine ⟨fun _ _ _ => Iff.rfl, fun t c h => h t, fun t => ⟨rfl, fun _ => rfl⟩,
    fun t t' h => ?_, fun h => ?_, ⟨.now true, true, false, rfl, by simp [trueAt]⟩⟩
  · have h1 := h (!t')
    simp [trueAt] at h1
  · have := h true (.now true) rfl
    have h1 := this false
    simp [trueAt] at h1

end Controls

end TruthCore.Results.Causality.PurityCriteria
