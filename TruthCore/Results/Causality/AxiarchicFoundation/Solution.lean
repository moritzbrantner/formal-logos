module

public import TruthCore.Causality.AxiarchicFoundation
public import TruthCore.Results.Causality.ImpersonalFoundationJoint.Solution

@[expose] public section

namespace TruthCore.Results.Causality.AxiarchicFoundation

open TruthCore.Causality.AxiarchicFoundation
open TruthCore.Causality.GoodFavouring (BecauseOfGoodness)
open TruthCore.Causality.ImpersonalFoundationJoint (GoodGeneral GoodGeneralFavouringIsApprehension)
open TruthCore.Logic (ExcludedMiddle)

/-! ## The nowhere horn -/

/-- The nowhere horn. If a profile is the inverse image of an item relation and
favours no candidate over itself, it favours no candidate over another that has
the same item: unindividuated candidates are not favoured one over the other. -/
theorem unindividuatedNotFavoured {X C : Type} (φ : X → X → Prop) (r : C → C → Prop)
    (f : X → C) (hReal : ∀ x y, φ x y ↔ InvImage r f x y) (hIrr : ∀ x, ¬ φ x x) (x y : X)
    (hSame : f x = f y) : ¬ φ x y := by
  intro h
  have hr : r (f x) (f y) := (hReal x y).1 h
  rw [hSame] at hr
  exact hIrr y ((hReal y y).2 hr)

/-- Individuation: a realized, irreflexive favouring of `x` over `y` gives `x`
and `y` distinct items. -/
theorem favouredIndividuated {X C : Type} (φ : X → X → Prop) (r : C → C → Prop)
    (f : X → C) (hReal : ∀ x y, φ x y ↔ InvImage r f x y) (hIrr : ∀ x, ¬ φ x x) (x y : X)
    (h : φ x y) : f x ≠ f y :=
  fun hSame => unindividuatedNotFavoured φ r f hReal hIrr x y hSame h

/-! ## The criterion from the individuation premises -/

/-- The cognition criterion, derived. Let `b` have a good-general favouring
determination `favours φ`: for some scenario `s` and pair `x`, `y`, at least one
not a present input, `φ` depends on value with end content fixed, so in
particular `φ s x y`. Item realization and irreflexivity make the stand-ins of
`x` and `y` distinct (the nowhere horn is excluded). Take the non-present one,
`z`. By excluded middle its stand-in is contained in `b`, or produced by `b`, or
independent of `b`; the own-favouring bridge excludes the independent realm and
the source-of-differences bridge the merely produced one, so it is contained. The
containment-recognition bridge then makes it a content about `z` that `b`
apprehends. -/
theorem goodGeneralFavouringIsApprehensionOfIndividuation {B D S X Z C : Type}
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (rel : B → TruthCore.Causality.GoodFavouring.Profile S X → S → C → C → Prop)
    (Contains Produces : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hReal : FavouringRealizedOnItems Has favours stand rel)
    (hIrr : FavouringIrreflexive Has favours)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hRecog : ContainedStandInIsApprehended Has favours good fitOf Present stand Contains About
      Apprehends) :
    GoodGeneralFavouringIsApprehension Has favours good fitOf Present About Apprehends := by
  intro b φ hφ hGG
  obtain ⟨s, x, y, hdep, hnp⟩ := hGG
  have hne : stand b x ≠ stand b y :=
    favouredIndividuated (φ s) (rel b φ s) (stand b) (hReal b φ hφ s) (hIrr b φ hφ s) x y hdep.2.1
  have hContained : ∀ v, ¬ Present s v →
      TruthCore.Causality.AxiarchicFoundation.ContainsGenerically Contains b (stand b v) := by
    intro v hv
    cases hEM (TruthCore.Causality.AxiarchicFoundation.ContainsGenerically Contains b (stand b v)) with
    | inl hc => exact hc
    | inr hnc =>
      cases hEM (Produces b (stand b v)) with
      | inl hp => exact (hNotMade b φ s v hφ hv ⟨hp, hnc⟩).elim
      | inr hnp' => exact (hOwn b φ s v hφ hv ⟨hnc, hnp'⟩).elim
  cases hnp with
  | inl hx =>
    obtain ⟨hab, -, -, hap⟩ := hRecog b φ s x y hφ (Or.inl hdep) hx (hContained x hx) hne
    exact ⟨stand b x, x, hab, hap⟩
  | inr hy =>
    obtain ⟨hab, -, -, hap⟩ := hRecog b φ s y x hφ (Or.inr hdep) hy (hContained y hy) hne.symm
    exact ⟨stand b y, y, hab, hap⟩

/-! ## Lean-only: what the derivation relocates (semantic challenge probes)

Given the other five premises, the registered recognition bridge is strictly
stronger than the criterion: the criterion implies the weakened bridge, the
weakened bridge with the five premises implies the criterion, and on the control
carrier the criterion and the five premises hold while the registered bridge
fails (`criterionDoesNotGiveRecognition`). The derivation therefore localizes
the dispute; it adds no warrant against a rival who grants the other premises. -/

/-- The criterion alone implies the weakened recognition bridge. -/
theorem criterionGivesWeakRecognition {B D S X Z C : Type}
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (Contains : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (h : GoodGeneralFavouringIsApprehension Has favours good fitOf Present About Apprehends) :
    ContainedStandInYieldsApprehension Has favours good fitOf Present stand Contains About
      Apprehends := by
  intro b φ s z w hφ hdep hz _ _
  apply h b φ hφ
  rcases hdep with hd | hd
  · exact ⟨s, z, w, hd, Or.inl hz⟩
  · exact ⟨s, w, z, hd, Or.inr hz⟩

/-- The weakened recognition bridge, with the other five premises, gives the
criterion. -/
theorem weakRecognitionGivesCriterion {B D S X Z C : Type}
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (rel : B → TruthCore.Causality.GoodFavouring.Profile S X → S → C → C → Prop)
    (Contains Produces : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hReal : FavouringRealizedOnItems Has favours stand rel)
    (hIrr : FavouringIrreflexive Has favours)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hW : ContainedStandInYieldsApprehension Has favours good fitOf Present stand Contains About
      Apprehends) :
    GoodGeneralFavouringIsApprehension Has favours good fitOf Present About Apprehends := by
  intro b φ hφ hGG
  obtain ⟨s, x, y, hdep, hnp⟩ := hGG
  have hne : stand b x ≠ stand b y :=
    favouredIndividuated (φ s) (rel b φ s) (stand b) (hReal b φ hφ s) (hIrr b φ hφ s) x y hdep.2.1
  have hContained : ∀ v, ¬ Present s v →
      TruthCore.Causality.AxiarchicFoundation.ContainsGenerically Contains b (stand b v) := by
    intro v hv
    cases hEM (TruthCore.Causality.AxiarchicFoundation.ContainsGenerically Contains b (stand b v)) with
    | inl hc => exact hc
    | inr hnc =>
      cases hEM (Produces b (stand b v)) with
      | inl hp => exact (hNotMade b φ s v hφ hv ⟨hp, hnc⟩).elim
      | inr hnp' => exact (hOwn b φ s v hφ hv ⟨hnc, hnp'⟩).elim
  cases hnp with
  | inl hx => exact hW b φ s x y hφ (Or.inl hdep) hx (hContained x hx) hne
  | inr hy => exact hW b φ s y x hφ (Or.inr hdep) hy (hContained y hy) hne.symm

/-- Without the individuation conjunct, realization and irreflexivity are not
needed: the nowhere exclusion only discharges that conjunct. Containment of the
non-present candidate's stand-in follows from excluded middle and the two locus
bridges alone. -/
theorem recognitionWithoutIndividuationGivesCriterion {B D S X Z C : Type}
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (Contains Produces : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hR : ∀ b φ s z w, Has b (favours φ) →
      (BecauseOfGoodness good fitOf φ s z w ∨ BecauseOfGoodness good fitOf φ s w z) →
      ¬ Present s z → TruthCore.Causality.AxiarchicFoundation.ContainsGenerically Contains b (stand b z) →
        About (stand b z) z ∧ Apprehends b (stand b z)) :
    GoodGeneralFavouringIsApprehension Has favours good fitOf Present About Apprehends := by
  intro b φ hφ hGG
  obtain ⟨s, x, y, hdep, hnp⟩ := hGG
  have hContained : ∀ v, ¬ Present s v →
      TruthCore.Causality.AxiarchicFoundation.ContainsGenerically Contains b (stand b v) := by
    intro v hv
    cases hEM (TruthCore.Causality.AxiarchicFoundation.ContainsGenerically Contains b (stand b v)) with
    | inl hc => exact hc
    | inr hnc =>
      cases hEM (Produces b (stand b v)) with
      | inl hp => exact (hNotMade b φ s v hφ hv ⟨hp, hnc⟩).elim
      | inr hnp' => exact (hOwn b φ s v hφ hv ⟨hnc, hnp'⟩).elim
  cases hnp with
  | inl hx => exact ⟨_, _, hR b φ s x y hφ (Or.inl hdep) hx (hContained x hx)⟩
  | inr hy => exact ⟨_, _, hR b φ s y x hφ (Or.inr hdep) hy (hContained y hy)⟩

/-- Item realization with a profile-indexed relation does not force one favouring
per bearer: the identity assignment realizes any family of profiles, each by
itself. (With a relation not indexed by the profile, realization would force all
favourings of a bearer to be equal.) -/
theorem realizationAllowsSeveralFavourings {B S X : Type}
    (Has : B → TruthCore.Causality.GoodFavouring.Profile S X → Prop) :
    FavouringRealizedOnItems Has id (fun _ x => x) (fun _ φ s => φ s) :=
  fun _ _ _ _ _ _ => Iff.rfl

/-! ## Controls -/

section Controls

open TruthCore.Causality.AxiarchicFoundation.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better fitOrder)
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok hasSrc personalSrc noInputs gg)

private theorem hasPersonal (b : Bool) (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : hasSrc personalSrc b (favTok φ)) : b = true ∧ φ = better := by
  cases b with
  | true => simp [hasSrc, personalSrc, favTok] at h; exact ⟨rfl, h⟩
  | false => exact Det.noConfusion (show Det.fav φ = Det.esse from h)

private theorem hasAllIn (b : Bool) (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (h : hasSrc allInSrc b (favTok φ)) : b = true ∧ φ = allIn := by
  cases b with
  | true => simp [hasSrc, allInSrc, favTok] at h; exact ⟨rfl, h⟩
  | false => exact Det.noConfusion (show Det.fav φ = Det.esse from h)

private theorem hasBetter : hasSrc personalSrc true (favTok better) := by
  simp [hasSrc, personalSrc, favTok]

private theorem betterIrrefl (s : Scenario) (x : Outcome) : ¬ better s x x := by
  cases s <;> cases x <;> simp [better, fitOrder, fits]

private theorem realizedInj (k : Outcome → Item) (hk : ∀ x y, k x = k y → x = y) :
    realized personalSrc k (relVia k) := by
  intro b φ hφ s x y
  obtain ⟨-, rfl⟩ := hasPersonal b φ hφ
  constructor
  · intro h; exact ⟨x, y, rfl, rfl, h⟩
  · rintro ⟨x', y', hx, hy, h⟩
    rw [hk x' x hx, hk y' y hy] at h
    exact h

private theorem irreflPersonal : irrefl personalSrc := by
  intro b φ hφ s x
  obtain ⟨-, rfl⟩ := hasPersonal b φ hφ
  exact betterIrrefl s x

private theorem ownOf (src : Set Det) (k : Outcome → Item)
    (hsrc : ∀ b φ, hasSrc src b (favTok φ) → b = true)
    (h : ∀ o, contains true (k o) ∨ produces true (k o)) : own src k := by
  intro b φ s x hφ _ hind
  obtain rfl := hsrc b φ hφ
  rcases h x with hc | hp
  · exact hind.1 hc
  · exact hind.2 hp

private theorem notMadeOf (src : Set Det) (k : Outcome → Item)
    (hsrc : ∀ b φ, hasSrc src b (favTok φ) → b = true)
    (h : ∀ o, ¬ produces true (k o) ∨ contains true (k o)) : notMade src k := by
  intro b φ s x hφ _ ⟨hp, hnc⟩
  obtain rfl := hsrc b φ hφ
  rcases h x with h1 | h1
  · exact h1 hp
  · exact hnc h1

/-- Recognition holds vacuously when no stand-in is contained. -/
private theorem recogNoContained (src : Set Det) (k : Outcome → Item) (app : Bool → Item → Prop)
    (h : ∀ b o, ¬ contains b (k o)) : recog src k app := by
  intro b φ s z₀ w₀ _ _ _ hc _
  exact (h b z₀ hc).elim

/-- Recognition holds vacuously when every candidate has the same stand-in. -/
private theorem recogConst (src : Set Det) (e : Item) (app : Bool → Item → Prop) :
    recog src (fun _ => e) app := by
  intro b φ s _ _ _ _ _ _ hne
  exact (hne rfl).elim

private theorem critNone (src : Set Det) (φ : TruthCore.Causality.GoodFavouring.Profile Scenario Outcome)
    (hφ : hasSrc src true (favTok φ)) (hg : gg φ) : ¬ crit src appNone := by
  intro h
  obtain ⟨_, _, _, hc⟩ := h true φ hφ hg
  exact hc

private theorem personalTrue : ∀ b φ, hasSrc personalSrc b (favTok φ) → b = true :=
  fun b φ hφ => (hasPersonal b φ hφ).1

private theorem innerInj : ∀ x y : Outcome, Item.inner x = Item.inner y → x = y :=
  fun _ _ h => Item.inner.inj h
private theorem realmInj : ∀ x y : Outcome, Item.realm x = Item.realm y → x = y :=
  fun _ _ h => Item.realm.inj h
private theorem madeInj : ∀ x y : Outcome, Item.made x = Item.made y → x = y :=
  fun _ _ h => Item.made.inj h

private theorem ggAllIn : gg allIn :=
  ⟨.cBetter, .c, .d, ⟨Or.inr ⟨rfl, rfl⟩, rfl, .actual,
    by funext o; cases o <;> rfl, by simp [better, fitOrder, fits],
    by simp [allIn]⟩, Or.inl id⟩

private theorem depBetter : BecauseOfGoodness better fits better .cBetter .c .d :=
  ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, .actual,
    by funext o; cases o <;> rfl, by simp [better, fitOrder, fits],
    by simp [better, fitOrder, fits]⟩

private theorem ggBetter' : gg better :=
  TruthCore.Results.Causality.ImpersonalFoundationJoint.ggBetter

/-- The individuation trilemma on one carrier (see `AxiarchicControls`). -/
theorem axiarchicControls : AxiarchicControls := by
  have hOwnInner : own personalSrc Item.inner :=
    ownOf _ _ personalTrue fun o => Or.inl ⟨rfl, Or.inr ⟨o, rfl⟩⟩
  have hMadeInner : notMade personalSrc Item.inner :=
    notMadeOf _ _ personalTrue fun o => Or.inr ⟨rfl, Or.inr ⟨o, rfl⟩⟩
  have hNoCritP : ¬ crit personalSrc appNone := critNone _ better hasBetter ggBetter'
  refine ⟨⟨realizedInj _ innerInj, irreflPersonal, hOwnInner, hMadeInner, ?_, ?_⟩,
    ⟨realizedInj _ innerInj, irreflPersonal, hOwnInner, hMadeInner, ?_, hNoCritP⟩,
    ⟨realizedInj _ realmInj, irreflPersonal, ?_, ?_, ?_, hNoCritP⟩,
    ⟨realizedInj _ madeInj, irreflPersonal, ?_, ?_, ?_, hNoCritP⟩,
    ⟨?_, irreflPersonal, ?_, ?_, recogConst _ _ _, hNoCritP⟩,
    ⟨?_, ?_, ?_, ?_, recogConst _ _ _, ggAllIn, rfl, critNone _ allIn ?_ ggAllIn⟩⟩
  -- row 1: recognition and the criterion
  · intro b φ s z₀ w₀ hφ _ _ _ _
    obtain ⟨rfl, -⟩ := hasPersonal b φ hφ
    exact ⟨Or.inl rfl, ⟨rfl, Or.inr ⟨z₀, rfl⟩⟩, ⟨z₀, Or.inl rfl⟩, rfl, z₀, rfl⟩
  · intro b φ hφ _
    obtain ⟨rfl, -⟩ := hasPersonal b φ hφ
    exact ⟨Item.inner .c, .c, Or.inl rfl, rfl, .c, rfl⟩
  -- row 2: recognition fails
  · intro h
    obtain ⟨-, -, -, hc⟩ := h true better .cBetter .c .d hasBetter
      (Or.inl depBetter) (fun h => h)
      ⟨rfl, Or.inr ⟨.c, rfl⟩⟩ (by simp [standVia])
    exact hc
  -- row 3: the independent realm
  · intro h
    refine h true better .actual .c hasBetter (fun h => h) ⟨?_, ?_⟩
    · rintro ⟨-, h | ⟨o, h⟩⟩ <;> simp [standVia] at h
    · rintro ⟨-, o, h⟩; simp [standVia] at h
  · exact notMadeOf _ _ personalTrue fun o => Or.inl (by rintro ⟨-, o', h⟩; simp at h)
  · exact recogNoContained _ _ _ fun b o h => by
      obtain ⟨-, h | ⟨o', h⟩⟩ := h <;> simp at h
  -- row 4: the produced realm
  · exact ownOf _ _ personalTrue fun o => Or.inr ⟨rfl, o, rfl⟩
  · intro h
    refine h true better .actual .c hasBetter (fun h => h) ⟨⟨rfl, .c, rfl⟩, ?_⟩
    rintro ⟨-, h | ⟨o, h⟩⟩ <;> simp [standVia] at h
  · exact recogNoContained _ _ _ fun b o h => by
      obtain ⟨-, h | ⟨o', h⟩⟩ := h <;> simp at h
  -- row 5: nowhere, good-tracking
  · intro rel h
    have h1 := (h true better hasBetter .cBetter .c .d).1 (Or.inr ⟨rfl, rfl⟩)
    exact betterIrrefl .cBetter .c ((h true better hasBetter .cBetter .c .c).2 h1)
  · exact ownOf _ _ personalTrue fun _ => Or.inl ⟨rfl, Or.inl rfl⟩
  · exact notMadeOf _ _ personalTrue fun _ => Or.inr ⟨rfl, Or.inl rfl⟩
  -- row 6: nowhere, realized, reflexive
  · intro b φ hφ s x y
    obtain ⟨-, rfl⟩ := hasAllIn b φ hφ
    exact Iff.rfl
  · intro h
    exact h true allIn (by simp [hasSrc, allInSrc, favTok]) .cBetter .c rfl
  · exact ownOf _ _ (fun b φ hφ => (hasAllIn b φ hφ).1) fun _ => Or.inl ⟨rfl, Or.inl rfl⟩
  · exact notMadeOf _ _ (fun b φ hφ => (hasAllIn b φ hφ).1) fun _ => Or.inr ⟨rfl, Or.inl rfl⟩
  · simp [hasSrc, allInSrc, favTok]

/-- Lean-only (semantic challenge probe): on the personal row's carrier, with the
same stand-ins, relation and loci (so the other five premises hold, as in
`axiarchicControls` row 1), the criterion holds while the registered recognition
bridge fails: the source apprehends only its one nature, which counts as about
every outcome, and not the contained stand-in. So the criterion and the other
premises do not give the bridge. -/
theorem criterionDoesNotGiveRecognition :
    GoodGeneralFavouringIsApprehension (hasSrc personalSrc) favTok better fits noInputs
        aboutOrBlob appBlob ∧
      ¬ ContainedStandInIsApprehended (hasSrc personalSrc) favTok better fits noInputs
        (standVia Item.inner) contains aboutOrBlob appBlob := by
  constructor
  · intro b φ hφ _
    obtain ⟨rfl, -⟩ := hasPersonal b φ hφ
    exact ⟨Item.blob, .c, Or.inl rfl, rfl, rfl⟩
  · intro h
    obtain ⟨-, -, -, -, hc⟩ := h true better .cBetter .c .d hasBetter (Or.inl depBetter) (fun h => h)
      ⟨rfl, Or.inr ⟨.c, rfl⟩⟩ (by simp [standVia])
    cases hc

/-- Lean-only: value-dependence of an aligned order witnesses coincidence on the
witnessing pair only (see `AlignmentControl`). -/
theorem witnessOnlyAlignment :
    TruthCore.Causality.AxiarchicFoundation.AlignmentControl.WitnessOnlyAlignment := by
  open TruthCore.Causality.AxiarchicFoundation.AlignmentControl in
  refine ⟨⟨.s0, .a, .b, ⟨trivial, trivial, .s1, rfl, fun h => h, fun h => h⟩, Or.inl id⟩,
    ?_, ?_, ?_, ?_, trivial, trivial⟩
  · intro s x y h h'
    cases s <;> cases x <;> cases y <;> simp_all [value]
  · intro s x y h h'
    cases s <;> cases x <;> cases y <;> simp_all [power]
  · intro s x y z h h'
    cases s <;> cases x <;> cases y <;> cases z <;> simp_all [value]
  · intro s x y z h h'
    cases s <;> cases x <;> cases y <;> cases z <;> simp_all [power]

end Controls

end TruthCore.Results.Causality.AxiarchicFoundation
