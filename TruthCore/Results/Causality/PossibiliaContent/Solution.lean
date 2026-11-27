module

public import TruthCore.Causality.PossibiliaContent
public import TruthCore.Results.Causality.AxiarchicFoundation.Solution

@[expose] public section

namespace TruthCore.Results.Causality.PossibiliaContent

open TruthCore.Causality.PossibiliaContent
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.AxiarchicFoundation
open TruthCore.Causality.ImpersonalFoundationJoint
  (GoodGeneral GoodGeneralFavouringIsApprehension ActualRootFavouringIsGoodGeneral
    ActualRootsHaveOwnFavouring ActualRootsApprehendThroughGoodGeneralFavouring)
open TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence (ConstitutivelySimple)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Results.Causality.AxiarchicFoundation (favouredIndividuated)

/-! ## The shared demand, derived -/

/-- Excluded middle and the two locus bridges put the stand-in of a non-present
candidate in the bearer (CONTAINED_IN_1). Lane C's disjunctive syllogism. -/
theorem containedOfLoci {B D S X C : Type} (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D) (Present : S → X → Prop)
    (stand : B → X → C) (Contains Produces : B → C → Prop) (hEM : ExcludedMiddle)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (b : B) (φ : TruthCore.Causality.GoodFavouring.Profile S X) (hφ : Has b (favours φ))
    (s : S) (v : X) (hv : ¬ Present s v) : ContainsGenerically Contains b (stand b v) := by
  cases hEM (ContainsGenerically Contains b (stand b v)) with
  | inl hc => exact hc
  | inr hnc =>
    cases hEM (Produces b (stand b v)) with
    | inl hp => exact (hNotMade b φ s v hφ hv ⟨hp, hnc⟩).elim
    | inr hnp => exact (hOwn b φ s v hφ hv ⟨hnc, hnp⟩).elim

/-- Two distinct items are not both real constituents of a constitutively simple
bearer. -/
theorem distinctNotBothReal {B C : Type} (RealConstituent : B → C → Prop) (b : B)
    (hSimple : ConstitutivelySimple RealConstituent b) (e e' : C) (hne : e ≠ e') :
    ¬ (RealConstituent b e ∧ RealConstituent b e') :=
  fun h => hne (hSimple e e' h.1 h.2)

/-- THE SHARED DEMAND. A simple bearer whose good-general favouring has only
non-present candidates has a stand-in in it that is not a real constituent:
realization and irreflexivity give two distinct stand-ins, the locus bridges put
both in the bearer, and simplicity forbids both being real. It binds the personal
source (no real plurality of ideas) and the rival (none of modes or powers). -/
theorem simpleBearerHasNonRealStandIn {B D S X Z C : Type}
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (rel : B → TruthCore.Causality.GoodFavouring.Profile S X → S → C → C → Prop)
    (Contains Produces RealConstituent : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hReal : FavouringRealizedOnItems Has favours stand rel)
    (hIrr : FavouringIrreflexive Has favours)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hNoPresent : NoPresentCandidates Present)
    (b : B) (hSimple : ConstitutivelySimple RealConstituent b)
    (φ : TruthCore.Causality.GoodFavouring.Profile S X) (hφ : Has b (favours φ))
    (hGG : GoodGeneral good fitOf Present φ) :
    ∃ s x, ¬ Present s x ∧ NonRealContained Contains RealConstituent b (stand b x) := by
  obtain ⟨s, x, y, hdep, -⟩ := hGG
  have hne : stand b x ≠ stand b y :=
    favouredIndividuated (φ s) (rel b φ s) (stand b) (hReal b φ hφ s) (hIrr b φ hφ s) x y hdep.2.1
  have hx := containedOfLoci Has favours Present stand Contains Produces hEM hOwn hNotMade b φ hφ s x
    (hNoPresent s x)
  have hy := containedOfLoci Has favours Present stand Contains Produces hEM hOwn hNotMade b φ hφ s y
    (hNoPresent s y)
  cases hEM (RealConstituent b (stand b x)) with
  | inr hnx => exact ⟨s, x, hNoPresent s x, hx, hnx⟩
  | inl hrx =>
    cases hEM (RealConstituent b (stand b y)) with
    | inr hny => exact ⟨s, y, hNoPresent s y, hy, hny⟩
    | inl hry =>
      exact (distinctNotBothReal RealConstituent b hSimple _ _ hne ⟨hrx, hry⟩).elim

/-- Lane H1 question C, both sides: if every contained stand-in of a simple,
patientless bearer is a real constituent (Molnar-type real directed powers, or
real representations), none of its favourings is good-general. Real directedness
cannot supply the distinct stand-ins at a simple root; nor can real ideas. -/
theorem realStandInsGiveNoGoodGeneralFavouring {B D S X Z C : Type}
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (rel : B → TruthCore.Causality.GoodFavouring.Profile S X → S → C → C → Prop)
    (Contains Produces RealConstituent : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hReal : FavouringRealizedOnItems Has favours stand rel)
    (hIrr : FavouringIrreflexive Has favours)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hNoPresent : NoPresentCandidates Present)
    (b : B) (hSimple : ConstitutivelySimple RealConstituent b)
    (hAllReal : ∀ x, ContainsGenerically Contains b (stand b x) → RealConstituent b (stand b x))
    (φ : TruthCore.Causality.GoodFavouring.Profile S X) (hφ : Has b (favours φ)) :
    ¬ GoodGeneral good fitOf Present φ := by
  intro hGG
  obtain ⟨_, x, -, hc, hnr⟩ := simpleBearerHasNonRealStandIn Has favours good fitOf Present stand rel
    Contains Produces RealConstituent hEM hReal hIrr hOwn hNotMade hNoPresent b hSimple φ hφ hGG
  exact hnr (hAllReal x hc)

/-! ## The root criterion from conceptualism about non-real being -/

/-- The root cognition criterion, derived. An actual root `r` has a good-general
favouring. Roots are constitutively simple and no candidate is a present input,
so (`simpleBearerHasNonRealStandIn`) some candidate's stand-in is in `r` without
being a real constituent of it. The conceptualist premise makes `r` apprehend it,
and the content premise makes it about its candidate. -/
theorem simpleRootGoodGeneralFavouringIsApprehension {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (rel : B → TruthCore.Causality.GoodFavouring.Profile S X → S → C → C → Prop)
    (Contains Produces RealConstituent : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hReal : FavouringRealizedOnItems Has favours stand rel)
    (hIrr : FavouringIrreflexive Has favours)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hSimple : RootsConstitutivelySimple m w RealConstituent)
    (hNoPresent : NoPresentCandidates Present)
    (hNRA : NonRealContainmentIsApprehension Contains RealConstituent Apprehends)
    (hAbout : NonRealStandInIsAbout Has favours Present stand Contains RealConstituent About) :
    RootGoodGeneralFavouringIsApprehension m w Has favours good fitOf Present About Apprehends := by
  intro r hr φ hφ hGG
  obtain ⟨s, x, hx, hnr⟩ := simpleBearerHasNonRealStandIn Has favours good fitOf Present stand rel
    Contains Produces RealConstituent hEM hReal hIrr hOwn hNotMade hNoPresent r (hSimple r hr) φ hφ hGG
  exact ⟨stand r x, x, hAbout r φ s x hφ hx hnr, hNRA r (stand r x) hnr⟩

/-- Strength order: the cognition criterion implies its restriction to actual
roots. -/
theorem rootCriterionOfCriterion {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hCriterion : GoodGeneralFavouringIsApprehension Has favours good fitOf Present About
      Apprehends) :
    RootGoodGeneralFavouringIsApprehension m w Has favours good fitOf Present About Apprehends :=
  fun r _ φ hφ hg => hCriterion r φ hφ hg

/-- The root criterion in place of the cognition criterion: commitment (e) in
its weakest favouring form and the good-generality of root favouring give every
actual root apprehension through good-general favouring. -/
theorem actualRootsApprehendFromRootCriterion {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hGeneral : ActualRootFavouringIsGoodGeneral m w Has favours good fitOf Present)
    (hFavouring : ActualRootsHaveOwnFavouring m w Has favours)
    (hRootCriterion : RootGoodGeneralFavouringIsApprehension m w Has favours good fitOf Present
      About Apprehends) :
    ActualRootsApprehendThroughGoodGeneralFavouring m w Has favours good fitOf Present About
      Apprehends := by
  intro r hr
  obtain ⟨φ, hφ⟩ := hFavouring r hr
  have hg := hGeneral r hr φ hφ
  exact ⟨⟨φ, hφ, hg⟩, hRootCriterion r hr φ hφ hg⟩

/-! ## Lean-only: relocation probe

Given the other premises, the root criterion is equivalent to the weakened
existential form `NonRealStandInYieldsApprehension` (some apprehended content
about some candidate, not the stand-in itself). The conceptualist premise, even
restricted to the route, is strictly stronger than the root criterion given them
(`rootCriterionWithoutConceptualism`). -/

/-- The root criterion implies the weakened existential form. -/
theorem rootCriterionGivesExistentialStandInApprehension {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (Contains RealConstituent : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (h : RootGoodGeneralFavouringIsApprehension m w Has favours good fitOf Present About
      Apprehends) :
    NonRealStandInYieldsApprehension m w Has favours good fitOf Present stand Contains
      RealConstituent About Apprehends :=
  fun r hr φ _ _ hφ hg _ _ => h r hr φ hφ hg

/-- The weakened existential form with the other premises (minus the
conceptualist and content premises) gives the root criterion. -/
theorem existentialStandInApprehensionGivesRootCriterion {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (rel : B → TruthCore.Causality.GoodFavouring.Profile S X → S → C → C → Prop)
    (Contains Produces RealConstituent : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hReal : FavouringRealizedOnItems Has favours stand rel)
    (hIrr : FavouringIrreflexive Has favours)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hSimple : RootsConstitutivelySimple m w RealConstituent)
    (hNoPresent : NoPresentCandidates Present)
    (hW : NonRealStandInYieldsApprehension m w Has favours good fitOf Present stand Contains
      RealConstituent About Apprehends) :
    RootGoodGeneralFavouringIsApprehension m w Has favours good fitOf Present About Apprehends := by
  intro r hr φ hφ hGG
  obtain ⟨s, x, hx, hnr⟩ := simpleBearerHasNonRealStandIn Has favours good fitOf Present stand rel
    Contains Produces RealConstituent hEM hReal hIrr hOwn hNotMade hNoPresent r (hSimple r hr) φ hφ hGG
  exact hW r hr φ s x hφ hGG hx hnr

/-! ## Controls -/

section Controls

open TruthCore.Causality.PossibiliaContent.Control
open TruthCore.Causality.AxiarchicFoundation.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better fitOrder)
open TruthCore.Causality.ImpersonalFoundationJoint.Control (Det favTok hasSrc personalSrc noInputs)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)

private theorem hasPersonal' (b : Bool) (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : hasSrc personalSrc b (favTok φ)) : b = true ∧ φ = better := by
  cases b with
  | true => simp [hasSrc, personalSrc, favTok] at h; exact ⟨rfl, h⟩
  | false => exact Det.noConfusion (show Det.fav φ = Det.esse from h)

private theorem hasBetter' : hasSrc personalSrc true (favTok better) := by
  simp [hasSrc, personalSrc, favTok]

private theorem betterIrrefl' (s : Scenario) (x : Outcome) : ¬ better s x x := by
  cases s <;> cases x <;> simp [better, fitOrder, fits]

private theorem depBetter' :
    TruthCore.Causality.GoodFavouring.BecauseOfGoodness better fits better .cBetter .c .d :=
  ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, .actual,
    by funext o; cases o <;> rfl, by simp [better, fitOrder, fits],
    by simp [better, fitOrder, fits]⟩

private theorem ggWith (Pres : Scenario → Outcome → Prop) (h : ¬ Pres .cBetter .c) :
    GoodGeneral better fits Pres better :=
  ⟨.cBetter, .c, .d, depBetter', Or.inl h⟩

private theorem rootTrue : ActualRoot rootProfile true true :=
  (TruthCore.Results.Causality.RootPerfectionExclusion.rootIff true).2 rfl

private theorem emProof : ExcludedMiddle := fun p => Classical.em p

private theorem laneCOf (Cont : Bool → Item → Prop) (Pres : Scenario → Outcome → Prop)
    (k : Outcome → Item) (hk : ∀ x y, k x = k y → x = y)
    (hc : ∀ s o, ¬ Pres s o → Cont true (k o))
    (hNotProd : ∀ o, ¬ produces true (k o)) : laneC Cont Pres k := by
  refine ⟨emProof, ?_, ?_, ?_, ?_⟩
  · intro b φ hφ s x y
    obtain ⟨-, rfl⟩ := hasPersonal' b φ hφ
    constructor
    · intro h; exact ⟨x, y, rfl, rfl, h⟩
    · rintro ⟨x', y', hx, hy, h⟩
      rw [hk x' x hx, hk y' y hy] at h
      exact h
  · intro b φ hφ s x
    obtain ⟨-, rfl⟩ := hasPersonal' b φ hφ
    exact betterIrrefl' s x
  · intro b φ s x hφ hx hind
    obtain ⟨rfl, -⟩ := hasPersonal' b φ hφ
    exact hind.1 (hc s x hx)
  · intro b φ s x hφ _ ⟨hp, _⟩
    obtain ⟨rfl, -⟩ := hasPersonal' b φ hφ
    exact hNotProd x hp

private theorem innerInj' : ∀ x y : Outcome, Item.inner x = Item.inner y → x = y :=
  fun _ _ h => Item.inner.inj h

private theorem laneCInner : laneC contains noInputs Item.inner :=
  laneCOf _ _ _ innerInj' (fun _ o _ => ⟨rfl, Or.inr ⟨o, rfl⟩⟩)
    (fun o h => by obtain ⟨-, o', h⟩ := h; cases h)

private theorem patientInj : ∀ x y : Outcome, patientStand x = patientStand y → x = y := by
  intro x y h
  cases x <;> cases y <;> simp_all [patientStand]

private theorem laneCPatient : laneC containsBlob onlyCAbsent patientStand := by
  refine laneCOf _ _ _ patientInj ?_ ?_
  · intro s o ho
    have : o = Outcome.c := by
      by_contra hne
      exact ho hne
    subst this
    exact ⟨rfl, rfl⟩
  · intro o h
    obtain ⟨-, o', h⟩ := h
    cases o <;> simp [patientStand] at h

private theorem simpleBlob : simple realBlob := by
  intro r _ a b ha hb
  rw [ha.2, hb.2]

private theorem notSimpleContained : ¬ simple realContained := by
  intro h
  have := h true rootTrue (Item.inner .c) (Item.inner .d) ⟨rfl, Or.inr ⟨.c, rfl⟩⟩
    ⟨rfl, Or.inr ⟨.d, rfl⟩⟩
  cases this

private theorem noPresentNone : NoPresentCandidates noInputs := fun _ _ h => h

private theorem nraInner : nra contains realBlob appInner := by
  rintro b e ⟨⟨hb, he | ⟨o, he⟩⟩, hnr⟩
  · exact (hnr ⟨hb, he⟩).elim
  · exact ⟨hb, o, he⟩

private theorem nraVacuousContained (app : Bool → Item → Prop) :
    nra contains realContained app :=
  fun _ _ h => (h.2 h.1).elim

private theorem nraVacuousBlob (app : Bool → Item → Prop) : nra containsBlob realBlob app :=
  fun _ _ h => (h.2 h.1).elim

private theorem caInner (real : Bool → Item → Prop) :
    ca contains noInputs Item.inner real aboutItem :=
  fun _ _ _ _ _ _ _ => Or.inl rfl

private theorem nonRealInner (o : Outcome) :
    NonRealContained contains realBlob true (Item.inner o) :=
  ⟨⟨rfl, Or.inr ⟨o, rfl⟩⟩, by rintro ⟨-, h⟩; cases h⟩

private theorem critInner : rootCrit noInputs aboutItem appInner := by
  intro r _ φ hφ _
  obtain ⟨rfl, -⟩ := hasPersonal' r φ hφ
  exact ⟨Item.inner .c, .c, Or.inl rfl, rfl, .c, rfl⟩

private theorem notCritNone (Pres : Scenario → Outcome → Prop) (h : ¬ Pres .cBetter .c) :
    ¬ rootCrit Pres aboutItem appNone := by
  intro hc
  obtain ⟨_, _, _, hn⟩ := hc true rootTrue better hasBetter' (ggWith Pres h)
  exact hn

/-- One carrier, five rows (see `PossibiliaControls`). -/
theorem possibiliaControls : PossibiliaControls := by
  have hNot : ¬ noInputs Scenario.cBetter Outcome.c := fun h => h
  refine ⟨⟨laneCInner, simpleBlob, noPresentNone, nraInner, caInner _, critInner⟩,
    ⟨laneCInner, simpleBlob, noPresentNone, ?_, caInner _, notCritNone _ hNot⟩,
    ⟨laneCInner, notSimpleContained, noPresentNone, nraVacuousContained _, caInner _,
      notCritNone _ hNot⟩,
    ⟨laneCInner, simpleBlob, noPresentNone, nraInner, ?_, ?_⟩,
    ⟨laneCPatient, simpleBlob, ?_, nraVacuousBlob _, ?_,
      notCritNone _ (fun h => h rfl)⟩⟩
  -- row 2: the conceptualist premise fails
  · intro h
    exact h true (Item.inner .c) (nonRealInner .c)
  -- row 4: the content premise fails, and so does the root criterion
  · intro h
    exact h true better .cBetter .c hasBetter' hNot (nonRealInner .c)
  · intro hc
    obtain ⟨_, _, ha, _⟩ := hc true rootTrue better hasBetter' (ggWith _ hNot)
    exact ha
  -- row 5: present inputs
  · intro h
    exact h .actual .d (fun h' => Outcome.noConfusion h')
  · intro _ _ _ _ _ _ hnr
    exact (hnr.2 hnr.1).elim

/-- Relocation probe (see `RootCriterionWithoutConceptualism`). -/
theorem rootCriterionWithoutConceptualism : RootCriterionWithoutConceptualism := by
  refine ⟨laneCInner, simpleBlob, noPresentNone, caInner _, ?_, ?_⟩
  · intro r _ φ hφ _
    obtain ⟨rfl, -⟩ := hasPersonal' r φ hφ
    exact ⟨Item.inner .c, .c, Or.inl rfl, rfl, rfl⟩
  · intro h
    obtain ⟨-, hd⟩ := h true (Item.inner .d) (nonRealInner .d)
    cases hd

end Controls

end TruthCore.Results.Causality.PossibiliaContent
