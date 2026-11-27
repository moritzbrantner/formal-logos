module

public import TruthCore.Causality.ImpersonalFoundationJoint
public import TruthCore.Results.Causality.RootPerfectionExclusion.Solution
public import TruthCore.Results.Causality.GoodFavouring.Solution
public import TruthCore.Results.Causality.ActualAncestralSource.Solution
public import TruthCore.Results.Causality.SelectionScope.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ImpersonalFoundationJoint

open TruthCore.Causality.ImpersonalFoundationJoint
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple UnlimitedDeterminationsArePure)
open TruthCore.Causality.RootPerfectionExclusion
  (ActualProfile RootProfilesAdmissible PureDeterminationsAdmissible PureExtensionsAdmissible
    PositiveProfileExclusionLimits)
open TruthCore.Causality.SourceIntellectControls (HasCompatibleExtension)
open TruthCore.Causality.GoodFavouring (BecauseOfGoodness)
open TruthCore.Causality.RootPositiveIntellectWill (ActualRootExistsAt)
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Case.Catholicism (GodHasIntellect)
open TruthCore.Logic (ExcludedMiddle)

/-! ## A. The favouring horn meets the limitation results -/

/-- Horn A, E-free. Let `r` be an actual root and `favours φ` one of its real
determinations. If `φ` were not good-general, then by one-favouring realization
no admissible profile could contain `r`'s actual profile together with the
good-general token: its single favouring would be `φ`, and the token requires it
to be good-general. So `r`'s admissible profile would exclude a pure determination
that is admissible somewhere, and the structural L bridge (the distinct simply
prior being read as the frame's `PriorSimply`) would give `r` a represented
limiting principle, which actual roots lack. No premise mentions an absence or
its explanation: the excluding determination is the favouring itself. -/
theorem actualRootFavouringIsGoodGeneral {W B T R D P S X Z : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (Composite : B → Prop) (essence esse : B → P)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D) (goodGen : D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (hEM : ExcludedMiddle)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite F.PriorSimply essence esse)
    (hLimits : PositiveProfileExclusionLimits Admissible Has Pure Composite F.PriorSimply
      essence esse)
    (hRootAdm : RootProfilesAdmissible m w Admissible Has)
    (hPureAdm : PureDeterminationsAdmissible Admissible Pure)
    (hPureGG : GoodGeneralityIsPure Pure goodGen)
    (hOne : OneFavouringRealization Admissible favours goodGen good fitOf Present) :
    ActualRootFavouringIsGoodGeneral m w Has favours good fitOf Present := by
  intro r hr φ hφ
  cases hEM (GoodGeneral good fitOf Present φ) with
  | inl hGood => exact hGood
  | inr hNot =>
    refine (hRoots r hr (hLimits r goodGen (hRootAdm r hr) hPureGG (hPureAdm goodGen hPureGG)
      ?_)).elim
    rintro ⟨q, hq, hsub, hgq⟩
    obtain ⟨ψ, huniq, hgg⟩ := hOne q hq
    have hEq : φ = ψ := huniq φ (hsub hφ)
    subst hEq
    exact hNot (hgg hgq)

/-! ## B. The good-general horn meets the cognition criterion -/

/-- Horn B. Every actual root has an own favouring determination (the weakest
form of commitment (e) used); by horn A it is good-general; the cognition
criterion then gives an apprehended content about a candidate. -/
theorem actualRootsApprehendThroughGoodGeneralFavouring {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hGeneral : ActualRootFavouringIsGoodGeneral m w Has favours good fitOf Present)
    (hFavouring : ActualRootsHaveOwnFavouring m w Has favours)
    (hCriterion : GoodGeneralFavouringIsApprehension Has favours good fitOf Present About
      Apprehends) :
    ActualRootsApprehendThroughGoodGeneralFavouring m w Has favours good fitOf Present About
      Apprehends := by
  intro r hr
  obtain ⟨φ, hφ⟩ := hFavouring r hr
  have hg := hGeneral r hr φ hφ
  exact ⟨⟨φ, hφ, hg⟩, hCriterion r φ hφ hg⟩

/-! ## C. To GOD_4 HAS_INTELLECT_1 -/

/-- Some actual root exists at `w` (`dc397705`). Finite grounding reach
(`75974d26`) makes every GOD_4 that root (`namedRootOfReach`). The root-level
premise gives it apprehension through good-general favouring, and the open
recognition bridge gives HAS_INTELLECT_1. -/
theorem godHasIntellectFromGoodGeneralApprehension {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (IsGod HasIntellect : B → Prop) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hRoot : ActualRootExistsAt m w)
    (hReach : GodReachesActualConcreta m w IsGod)
    (hApprehends : ActualRootsApprehendThroughGoodGeneralFavouring m w Has favours good fitOf
      Present About Apprehends)
    (hRecognition : GodGoodGeneralApprehensionIsIntellect IsGod HasIntellect Has favours good
      fitOf Present About Apprehends) :
    GodHasIntellect IsGod HasIntellect := by
  intro g hg
  obtain ⟨n, hn⟩ := hRoot
  have hIdentity : g = n :=
    TruthCore.Results.Causality.ActualAncestralSource.namedRootOfReach m w IsGod hReach g n hg hn
  subst hIdentity
  exact hRecognition g hg (hApprehends g hn)

/-! ## Lean-only consequences, cores and boundaries -/

/-- A favouring that factors through the end-realization feature (a nature
determined to its end content D, or a law selecting by its own fixed functional)
is not good-general: law 1 of `GoodDependenceLaws`. -/
theorem factorsThroughNotGoodGeneral {S X Z : Type} (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (φ : TruthCore.Causality.GoodFavouring.Profile S X)
    (hfac : Function.FactorsThrough φ fitOf) : ¬ GoodGeneral good fitOf Present φ := by
  rintro ⟨s, x, y, hdep, -⟩
  exact TruthCore.Results.Causality.GoodFavouring.goodDependenceLaws.1 S X Z good fitOf φ s x y
    hfac hdep

/-- Corollary of horn A: no favouring determination of an actual root factors
through end-realization. The D-directed generative nature of Lane 2b is excluded
at an actual root under the premises of `actualRootFavouringIsGoodGeneral`. -/
theorem noActualRootFavouringFixedToEnd {W B D S X Z : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (hGeneral : ActualRootFavouringIsGoodGeneral m w Has favours good fitOf Present) :
    ∀ r, ActualRoot m w r → ∀ φ, Has r (favours φ) → ¬ Function.FactorsThrough φ fitOf :=
  fun r hr φ hφ hfac => factorsThroughNotGoodGeneral good fitOf Present φ hfac (hGeneral r hr φ hφ)

/-- One-favouring realization gives the #2153 exclusion form: a favouring token
whose profile is not good-general shares no admissible profile with the
good-general token. -/
theorem favouringExcludesGoodGenerality {D S X Z : Type} (Admissible : Set D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D) (goodGen : D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (hOne : OneFavouringRealization Admissible favours goodGen good fitOf Present)
    (φ : TruthCore.Causality.GoodFavouring.Profile S X)
    (hNot : ¬ GoodGeneral good fitOf Present φ) :
    ∀ q, Admissible q → favours φ ∈ q → goodGen ∉ q := by
  intro q hq hφ hg
  obtain ⟨ψ, huniq, hgg⟩ := hOne q hq
  have hEq : φ = ψ := huniq φ hφ
  subst hEq
  exact hNot (hgg hg)

/-- Variation core. If betterness factors through end-realization (no variation
of goodness at fixed end content), no profile is good-general (law 4), so
one-favouring realization keeps the good-general token out of every admissible
profile, which contradicts its purity together with pure admissibility. At least
one of the four must go; the core does not say which. -/
theorem variationCore {D S X Z : Type} (Admissible : Set D → Prop) (Pure : D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D) (goodGen : D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (hFixed : Function.FactorsThrough good fitOf)
    (hOne : OneFavouringRealization Admissible favours goodGen good fitOf Present)
    (hPureAdm : PureDeterminationsAdmissible Admissible Pure)
    (hPureGG : GoodGeneralityIsPure Pure goodGen) : False := by
  obtain ⟨q, hq, hg⟩ := hPureAdm goodGen hPureGG
  obtain ⟨ψ, -, hgg⟩ := hOne q hq
  obtain ⟨s, x, y, hdep, -⟩ := hgg hg
  exact TruthCore.Results.Causality.GoodFavouring.goodDependenceLaws.2.2.2.1 S X Z good fitOf ψ
    s x y hFixed hdep

/-- A comparator all of whose candidates are present inputs (a balance) is not
good-general, whatever it tracks. -/
theorem presentInputsNotGoodGeneral {S X Z : Type} (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (hAll : ∀ s x, Present s x)
    (φ : TruthCore.Causality.GoodFavouring.Profile S X) : ¬ GoodGeneral good fitOf Present φ := by
  rintro ⟨s, x, y, -, hx | hy⟩
  · exact hx (hAll s x)
  · exact hy (hAll s y)

/-- The incompatible core of the impersonal foundation. With an actual root,
the premises of horns A and B, commitment (e) in its weakest form and commitment
(c) (no actual root apprehends any content) cannot all hold. At least one member
must be rejected; the core does not select which. -/
theorem impersonalFoundationCore {W B T R D P S X Z C : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (Composite : B → Prop) (essence esse : B → P)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D) (goodGen : D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite F.PriorSimply essence esse)
    (hLimits : PositiveProfileExclusionLimits Admissible Has Pure Composite F.PriorSimply
      essence esse)
    (hRootAdm : RootProfilesAdmissible m w Admissible Has)
    (hPureAdm : PureDeterminationsAdmissible Admissible Pure)
    (hPureGG : GoodGeneralityIsPure Pure goodGen)
    (hOne : OneFavouringRealization Admissible favours goodGen good fitOf Present)
    (hFavouring : ActualRootsHaveOwnFavouring m w Has favours)
    (hCriterion : GoodGeneralFavouringIsApprehension Has favours good fitOf Present About
      Apprehends)
    (hRoot : ActualRootExistsAt m w)
    (hNoncognitive : ∀ r, ActualRoot m w r → ∀ c, ¬ Apprehends r c) : False := by
  obtain ⟨n, hn⟩ := hRoot
  obtain ⟨-, c, -, -, hc⟩ := actualRootsApprehendThroughGoodGeneralFavouring m w Has favours
    good fitOf Present About Apprehends
    (actualRootFavouringIsGoodGeneral F m w Admissible Has Pure Composite essence esse favours
      goodGen good fitOf Present hEM hRoots hLimits hRootAdm hPureAdm hPureGG hOne)
    hFavouring hCriterion n hn
  exact hNoncognitive n hn c hc


/-! ## Controls -/

section Controls

open TruthCore.Causality.ImpersonalFoundationJoint.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile frame)
open TruthCore.Causality.RootPerfectionExclusion.Control (composite rep prior)

private theorem rootIffJ (r : Bool) : ActualRoot rootProfile true r ↔ r = true :=
  TruthCore.Results.Causality.RootPerfectionExclusion.rootIff r

private theorem limitingIffJ (c : Prop) (x : Bool) :
    HasLimitingPrinciple (composite c) jointFrame.PriorSimply rep rep x ↔
      (x = true ∧ c) ∨ x = false :=
  TruthCore.Results.Causality.RootPerfectionExclusion.limitingIff c x

private theorem rootsIffJ (c : Prop) : roots c ↔ ¬ c :=
  TruthCore.Results.Causality.RootPerfectionExclusion.rootsIff c

theorem ggBetter : gg better :=
  ⟨.cBetter, .c, .d, ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, .actual,
    by funext o; cases o <;> rfl, by simp [better, fitOrder, fits],
    by simp [better, fitOrder, fits]⟩, Or.inl id⟩

theorem dNatureFactors : Function.FactorsThrough dNature fits := by
  intro a b h
  funext x y
  simp only [dNature, fitOrder, h]

theorem notGGdNature : ¬ gg dNature :=
  factorsThroughNotGoodGeneral better fits noInputs dNature dNatureFactors

theorem dNatureNeBetter : dNature ≠ better := by
  intro h
  have := congrFun (congrFun (congrFun h .cBetter) .c) .d
  simp [dNature, better, fitOrder, fits] at this

private theorem favMem (src : Set Det) (h : ∀ φ, Det.fav φ ∈ src → φ = better) :
    simpleFamily src :=
  ⟨fun φ ψ hφ hψ => (h φ hφ).trans (h ψ hψ).symm,
    fun _ φ hφ => (h φ hφ) ▸ ggBetter⟩

private theorem purePosSimple (q : Set Det) (h : ∀ d ∈ q, purePos d) : simpleFamily q :=
  favMem q fun φ hφ => by
    rcases h _ hφ with h | h | h <;> simp_all

private theorem personalSimple : simpleFamily personalSrc :=
  favMem _ fun φ hφ => by simp [personalSrc] at hφ; exact hφ

private theorem dNatureSimple : simpleFamily dNatureSrc :=
  ⟨fun φ ψ hφ hψ => by simp [dNatureSrc] at hφ hψ; rw [hφ, hψ],
    fun h => by simp [dNatureSrc] at h⟩

private theorem notMixedSimple : ¬ simpleFamily mixedSrc :=
  fun h => notGGdNature (h.2 (by simp [mixedSrc]) dNature (by simp [mixedSrc]))

private theorem realizesOf (adm : Set Det → Prop) (h : ∀ q, adm q → simpleFamily q) :
    realizes adm := by
  intro q hq
  by_cases hex : ∃ φ, Det.fav φ ∈ q
  · obtain ⟨φ, hφ⟩ := hex
    exact ⟨φ, fun ψ hψ => (h q hq).1 ψ φ hψ hφ, fun hg => (h q hq).2 hg φ hφ⟩
  · exact ⟨better, fun ψ hψ => (hex ⟨ψ, hψ⟩).elim, fun _ => ggBetter⟩

private theorem notRealizesAny : ¬ realizes anyFamily := by
  intro h
  obtain ⟨ψ, hu, hg⟩ := h {Det.fav dNature, Det.goodGen} trivial
  have hEq : dNature = ψ := hu dNature (by simp [favTok])
  subst hEq
  exact notGGdNature (hg (by simp))

private theorem rootAdmIff (adm : Set Det → Prop) (src : Set Det) :
    rootAdm adm src ↔ adm src := by
  constructor
  · intro h; exact h true ((rootIffJ true).2 rfl)
  · intro h r hr
    obtain rfl := (rootIffJ r).1 hr
    exact h

/-- L holds when the root's admissible profile is compatible with every pure
determination that is admissible somewhere, or the root is composite. -/
private theorem limitsOf (adm : Set Det → Prop) (src : Set Det) (pure : Det → Prop) (c : Prop)
    (h : adm src → ¬ c → ∀ k, pure k → (∃ q, adm q ∧ k ∈ q) →
      HasCompatibleExtension adm src k) : limits adm src pure c := by
  intro x k hAdm hk hkAdm hEx
  cases x with
  | false => exact (limitingIffJ c false).2 (Or.inr rfl)
  | true =>
    refine (limitingIffJ c true).2 (Or.inl ⟨rfl, ?_⟩)
    exact Classical.byContradiction fun hc => hEx (h hAdm hc k hk hkAdm)

private theorem notLimitsOf (adm : Set Det → Prop) (src : Set Det) (pure : Det → Prop) (k : Det)
    (hAdm : adm src) (hk : pure k) (hkAdm : ∃ q, adm q ∧ k ∈ q)
    (hEx : ¬ HasCompatibleExtension adm src k) : ¬ limits adm src pure False := by
  intro h
  rcases (limitingIffJ False true).1 (h true k hAdm hk hkAdm hEx) with ⟨-, h⟩ | h
  · exact h
  · exact Bool.noConfusion h

private theorem compatibleSelf (adm : Set Det → Prop) (src : Set Det) (k : Det)
    (hAdm : adm src) (hk : k ∈ src) : HasCompatibleExtension adm src k :=
  ⟨src, hAdm, fun _ h => h, hk⟩

private theorem ggExcludedByDNature (adm : Set Det → Prop) (hadm : ∀ q, adm q → simpleFamily q) :
    ¬ HasCompatibleExtension adm dNatureSrc Det.goodGen := by
  rintro ⟨q, hq, hsub, hg⟩
  exact notGGdNature ((hadm q hq).2 hg dNature (hsub (by simp [dNatureSrc])))

private theorem generalOf (src : Set Det) (h : ∀ φ, Det.fav φ ∈ src → gg φ) : general src := by
  intro r hr φ hφ
  obtain rfl := (rootIffJ r).1 hr
  exact h φ hφ

private theorem notGeneralDNature (src : Set Det) (h : Det.fav dNature ∈ src) : ¬ general src :=
  fun hg => notGGdNature (hg true ((rootIffJ true).2 rfl) dNature h)

private theorem purityOfJ (src : Set Det) (pure : Det → Prop) (h : ∀ d ∈ src, pure d) :
    purity src pure False := by
  intro x hx d hd
  cases x with
  | false => exact (hx ((limitingIffJ False false).2 (Or.inr rfl))).elim
  | true => exact h d hd

private theorem singletonSimple (k : Det) (hk : ∀ φ, k = Det.fav φ → φ = better) :
    simpleFamily {k} :=
  favMem _ fun φ hφ => hk φ (by simp at hφ; exact hφ.symm)

private theorem singleFavSimple (φ0 : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome) :
    simpleFamily {Det.fav φ0} :=
  ⟨fun φ ψ hφ hψ => by
      rw [Set.mem_singleton_iff] at hφ hψ
      exact (Det.fav.inj hφ).trans (Det.fav.inj hψ).symm,
    fun h => Det.noConfusion (Set.mem_singleton_iff.1 h)⟩

private theorem pureAdmPos : pureAdm simpleFamily purePos := by
  intro k hk
  exact ⟨personalSrc, personalSimple, by rcases hk with rfl | rfl | rfl <;> simp [personalSrc]⟩

theorem favouringControls : FavouringControls := by
  have hR : roots False := (rootsIffJ False).2 id
  refine ⟨⟨hR, ?_, (rootAdmIff _ _).2 personalSimple, pureAdmPos, Or.inr (Or.inl rfl),
      realizesOf _ fun _ h => h, generalOf _ fun φ hφ => ?_, purityOfJ _ _ ?_, ?_⟩,
    ⟨fun h => (rootsIffJ True).1 h trivial, ?_, (rootAdmIff _ _).2 dNatureSimple, pureAdmPos,
      Or.inr (Or.inl rfl), realizesOf _ fun _ h => h, notGeneralDNature _ (by simp [dNatureSrc])⟩,
    ⟨hR, ?_, (rootAdmIff _ _).2 dNatureSimple, pureAdmPos, Or.inr (Or.inl rfl),
      realizesOf _ fun _ h => h, notGeneralDNature _ (by simp [dNatureSrc]), ?_, ?_⟩,
    ⟨hR, ?_, (rootAdmIff _ _).2 dNatureSimple, ?_, Or.inr (Or.inl rfl),
      realizesOf _ fun _ h => h, notGeneralDNature _ (by simp [dNatureSrc]),
      purityOfJ _ _ ?_, ?_⟩,
    ⟨hR, ?_, fun h => notMixedSimple ((rootAdmIff _ _).1 h), pureAdmPos, Or.inr (Or.inl rfl),
      realizesOf _ fun _ h => h, notGeneralDNature _ (by simp [mixedSrc])⟩,
    ⟨hR, ?_, (rootAdmIff _ _).2 ⟨dNatureSimple, by simp [dNatureSrc]⟩, ?_, Or.inr rfl,
      realizesOf _ fun _ h => h.1, notGeneralDNature _ (by simp [dNatureSrc])⟩,
    ⟨hR, ?_, (rootAdmIff _ _).2 dNatureSimple, ?_, ?_, realizesOf _ fun _ h => h,
      notGeneralDNature _ (by simp [dNatureSrc])⟩,
    ⟨hR, ?_, (rootAdmIff _ _).2 trivial, fun k _ => ⟨{k}, trivial, rfl⟩, Or.inr (Or.inl rfl),
      notRealizesAny, notGeneralDNature _ (by simp [dNatureSrc])⟩⟩
  -- row 1
  · exact limitsOf _ _ _ _ fun hAdm _ k hk _ =>
      compatibleSelf _ _ _ hAdm (by rcases hk with rfl | rfl | rfl <;> simp [personalSrc])
  · simp [personalSrc] at hφ; exact hφ ▸ ggBetter
  · intro d hd; simp [personalSrc] at hd; rcases hd with rfl | rfl | rfl <;> simp [purePos]
  · intro q k hq hall hk _
    exact purePosSimple _ fun d hd => by
      rcases Set.mem_insert_iff.1 hd with rfl | h
      · exact hk
      · exact hall d h
  -- row 2
  · exact limitsOf _ _ _ _ fun _ hc => (hc trivial).elim
  -- row 3a
  · exact notLimitsOf _ _ _ Det.goodGen dNatureSimple (Or.inr (Or.inl rfl))
      ⟨{Det.goodGen}, singletonSimple _ (by simp), rfl⟩ (ggExcludedByDNature _ fun _ h => h)
  · intro h
    have hp := h true (fun hl => by
      rcases (limitingIffJ False true).1 hl with ⟨-, h⟩ | h
      · exact h
      · exact Bool.noConfusion h) (Det.fav dNature) (by simp [hasSrc, dNatureSrc])
    rcases hp with h | h | h
    · exact Det.noConfusion h
    · exact Det.noConfusion h
    · exact dNatureNeBetter (Det.fav.inj h)
  · intro q k hq hall hk _
    exact purePosSimple _ fun d hd => by
      rcases Set.mem_insert_iff.1 hd with rfl | h
      · exact hk
      · exact hall d h
  -- row 3b
  · exact notLimitsOf _ _ _ Det.goodGen dNatureSimple (Or.inr (Or.inl rfl))
      ⟨{Det.goodGen}, singletonSimple _ (by simp), rfl⟩ (ggExcludedByDNature _ fun _ h => h)
  · intro k hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨personalSrc, personalSimple, by simp [personalSrc]⟩
    · exact ⟨personalSrc, personalSimple, by simp [personalSrc]⟩
    · exact ⟨personalSrc, personalSimple, by simp [personalSrc]⟩
    · exact ⟨dNatureSrc, dNatureSimple, by simp [dNatureSrc]⟩
  · intro d hd; simp [dNatureSrc] at hd; rcases hd with rfl | rfl <;> simp [pureRival]
  · intro h
    have hAdm := h {Det.fav dNature} Det.goodGen (singleFavSimple dNature)
      (fun d hd => by rw [Set.mem_singleton_iff] at hd; exact hd ▸ Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))
      ⟨{Det.goodGen}, singletonSimple _ (by simp), rfl⟩
    exact notGGdNature (hAdm.2 (by simp) dNature (by simp))
  -- row 4
  · exact limitsOf _ _ _ _ fun hAdm => (notMixedSimple hAdm).elim
  -- row 5
  · refine limitsOf _ _ _ _ fun hAdm _ k hk hkAdm => ?_
    rcases hk with rfl | rfl
    · exact compatibleSelf _ _ _ hAdm (by simp [dNatureSrc])
    · obtain ⟨q, hq, hg⟩ := hkAdm
      exact (hq.2 hg).elim
  · intro h
    obtain ⟨q, hq, hg⟩ := h Det.goodGen (Or.inr rfl)
    exact hq.2 hg
  -- row 6
  · exact limitsOf _ _ _ _ fun hAdm _ k hk _ =>
      compatibleSelf _ _ _ hAdm (by rcases hk with rfl | rfl <;> simp [dNatureSrc])
  · intro k hk
    exact ⟨dNatureSrc, dNatureSimple, by rcases hk with rfl | rfl <;> simp [dNatureSrc]⟩
  · intro h
    rcases h with h | h
    · exact Det.noConfusion h
    · exact Det.noConfusion h
  -- row 7
  · exact limitsOf _ _ _ _ fun _ _ k _ _ =>
      ⟨insert k dNatureSrc, trivial, Set.subset_insert _ _, Set.mem_insert _ _⟩

theorem apprehensionControls : ApprehensionControls := by
  have hGenP : general personalSrc :=
    generalOf _ fun φ hφ => by simp [personalSrc] at hφ; exact hφ ▸ ggBetter
  have hFavP : favouring personalSrc := fun r hr => by
    obtain rfl := (rootIffJ r).1 hr
    exact ⟨better, by simp [favTok, hasSrc, personalSrc]⟩
  have hCrit : ∀ src, criterion src appSource := fun src x φ hφ _ => by
    cases x with
    | true => exact ⟨.c, .c, rfl, rfl⟩
    | false => exact Det.noConfusion (show Det.fav φ = Det.esse from hφ)
  have hRoot : ActualRoot rootProfile true true := (rootIffJ true).2 rfl
  refine ⟨⟨hGenP, hFavP, hCrit _, ?_⟩,
    ⟨notGeneralDNature _ (by simp [dNatureSrc]), ?_, hCrit _, ?_⟩,
    ⟨generalOf _ fun φ hφ => by simp [bareGGSrc] at hφ, ?_, hCrit _, ?_⟩,
    ⟨hGenP, hFavP, ?_, ?_⟩⟩
  · exact actualRootsApprehendThroughGoodGeneralFavouring _ _ _ _ _ _ _ _ _ hGenP hFavP (hCrit _)
  · intro r hr
    obtain rfl := (rootIffJ r).1 hr
    exact ⟨dNature, by simp [favTok, hasSrc, dNatureSrc]⟩
  · intro h
    obtain ⟨⟨φ, hφ, hg⟩, -⟩ := h true hRoot
    have hφ' : Det.fav φ = Det.esse ∨ Det.fav φ = Det.fav dNature := by
      simpa [favTok, hasSrc, dNatureSrc] using hφ
    rcases hφ' with h | h
    · exact Det.noConfusion h
    · exact notGGdNature (Det.fav.inj h ▸ hg)
  · intro h
    obtain ⟨φ, hφ⟩ := h true hRoot
    simp [favTok, hasSrc, bareGGSrc] at hφ
  · intro h
    obtain ⟨⟨φ, hφ, -⟩, -⟩ := h true hRoot
    simp [favTok, hasSrc, bareGGSrc] at hφ
  · intro h
    obtain ⟨_, _, _, hc⟩ := h true better (by simp [favTok, hasSrc, personalSrc]) ggBetter
    exact hc
  · intro h
    obtain ⟨-, _, _, _, hc⟩ := h true hRoot
    exact hc

private theorem constNotGG (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : ∀ s t, φ s = φ t) : ¬ gg φ :=
  factorsThroughNotGoodGeneral better fits noInputs φ fun a b _ => h a b

theorem criterionTable : CriterionTable := by
  refine ⟨⟨ggBetter, ggBetter, rfl⟩, ⟨notGGdNature, notGGdNature,
    constNotGG _ fun _ _ => rfl, constNotGG _ fun _ _ => rfl⟩,
    presentInputsNotGoodGeneral better fits allPresent (fun _ _ => trivial) better, ?_⟩
  rintro ⟨s, x, y, hdep, -⟩
  exact TruthCore.Results.Causality.GoodFavouring.goodDependenceLaws.2.2.2.1 _ _ _ fitOrder
    fits better s x y (fun a b hab => by funext x y; simp only [fitOrder, hab]) hdep

private theorem reachIffJ (n : Bool) : reach n ↔ n = true := by
  constructor
  · intro h
    have hPath := h n rfl true ⟨trivial, Or.inl rfl⟩
    rcases Relation.ReflTransGen.cases_tail hPath with h | ⟨c, _, hEdge⟩
    · exact h.symm
    · exact (Bool.noConfusion hEdge.2.2.2.2 : False).elim
  · rintro rfl g hg x _
    subst hg
    cases x with
    | true => exact Relation.ReflTransGen.refl
    | false => exact Relation.ReflTransGen.single ⟨trivial, Or.inl rfl, rfl, rfl, rfl⟩

private theorem noGGFavIn (x : Bool) (src : Set Det) (hsrc : ∀ φ, Det.fav φ ∈ src → φ = dNature)
    (h : ∃ φ, hasSrc src x (favTok φ) ∧ gg φ) : False := by
  obtain ⟨φ, hφ, hg⟩ := h
  cases x with
  | true => exact notGGdNature (hsrc φ hφ ▸ hg)
  | false => exact Det.noConfusion (show Det.fav φ = Det.esse from hφ)

private theorem dNatureOnly : ∀ φ, Det.fav φ ∈ dNatureSrc → φ = dNature := fun φ hφ => by
  simp [dNatureSrc] at hφ; exact hφ

theorem intellectStepControls : IntellectStepControls := by
  have hApp := apprehensionControls.1.2.2.2
  have hNotApp := apprehensionControls.2.1.2.2.2
  have hRoot : ActualRoot rootProfile true true := (rootIffJ true).2 rfl
  refine ⟨⟨⟨true, hRoot⟩, (reachIffJ true).2 rfl, hApp, ?_, ?_⟩,
    ⟨(reachIffJ true).2 rfl, hNotApp, ?_, fun h => (h true rfl).2⟩,
    ⟨fun h => Bool.noConfusion ((reachIffJ false).1 h), hApp, ?_,
      fun h => Bool.noConfusion (h false rfl).1⟩,
    ⟨(reachIffJ true).2 rfl, hApp, fun h => (h true rfl (hApp true hRoot)).2,
      fun h => (h true rfl).2⟩⟩
  · intro g hg _; exact ⟨hg, trivial⟩
  · intro g hg; exact ⟨hg, trivial⟩
  · intro g hg hA
    exact (noGGFavIn g dNatureSrc dNatureOnly hA.1).elim
  · intro g hg hA
    subst hg
    obtain ⟨φ, hφ, -⟩ := hA.1
    exact Det.noConfusion (show Det.fav φ = Det.esse from hφ)

theorem jointConfigurations : JointConfigurations := by
  have hTable := TruthCore.Results.Causality.GoodFavouring.goodFavouringTable
  have hOmit := TruthCore.Results.Causality.SelectionScope.omissionScopeTable
  have hA := apprehensionControls
  refine ⟨⟨TruthCore.Results.Causality.IntentionalExemplarExtension.ObjectiveEminence.controls.1.1,
      (rootsIffJ False).2 id, ⟨rfl, rfl, rfl⟩, by simp [rootProfile, TruthCore.Causality.IntentionalExemplarExtension.Control.frame],
      (hOmit.1 _ _ _ _ _ false TruthCore.Modal.PrussPowerPremises.Model.Bg.g).2 hOmit.2.2.2.2.1.1, hOmit.2.2.2.2.1.2.1,
      hOmit.2.2.2.2.1.2.2.1⟩,
    ⟨by simp [hasSrc, dNatureSrc], hTable.2.2.2.2.2.2.2.2.1, hTable.2.2.2.2.2.2.2.2.2.1,
      fun _ h => h, hA.2.1.2.1, fun x φ hφ hg => (noGGFavIn x dNatureSrc dNatureOnly ⟨φ, hφ, hg⟩).elim,
      hA.2.1.1⟩,
    ⟨by simp [hasSrc, personalSrc, goodGeneral], hTable.2.2.2.2.2.2.2.2.2.2.1, fun _ h => h,
      hA.1.1, hA.1.2.1, hA.2.2.2.2.2.1⟩,
    ⟨by simp [hasSrc, personalSrc, rational], hTable.2.2.2.2.2.2.1.1 ▸ hTable.2.2.2.2.2.2.2.2.2.2.1,
      rfl, hA.1.1, hA.1.2.1, hA.1.2.2.1, hA.1.2.2.2⟩⟩

end Controls

end TruthCore.Results.Causality.ImpersonalFoundationJoint
