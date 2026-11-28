module

public import TruthCore.Causality.ImitabilityPlurality
public import TruthCore.Results.Causality.AxiarchicGuidance.Solution
public import TruthCore.Results.Causality.PossibiliaContent.Solution
public import TruthCore.Results.Causality.IntentionalExemplarExtension.Solution
public import TruthCore.Results.Causality.ImitabilityGrounding.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ImitabilityPlurality

open TruthCore.Causality.ImitabilityPlurality

/-- The identity step uses injectivity; the ranking step reuses the earlier
degree-only realization theorem; the symmetry step transports a ranked pair
to its reverse and applies asymmetry. No cognitive premise is used. -/
theorem identityAndRankingLaws : IdentityAndRankingLaws := by
  refine ⟨?_, ?_, ?_⟩
  · intro B C A RealConstituent b realize hSimple hReal hInjective
    exact ⟨fun c d => hInjective (hSimple _ _ (hReal c) (hReal d))⟩
  · intro B C A RealConstituent b realize rank realRank hSimple hReal hIrr hFactor c d
    exact TruthCore.Results.Causality.AxiarchicGuidance.degreeOnlyRegistersNoRespectBetweenTies
      rank realRank realize hFactor hIrr d c (hSimple _ _ (hReal d) (hReal c))
  · intro C K description rank hAsymm hRespect σ hPreserve c d hc hd hRank
    have hReverse := (hRespect σ hPreserve c d).1 hRank
    rw [hc, hd] at hReverse
    exact hAsymm c d hRank hReverse

section Controls

open TruthCore.Causality.ImitabilityPlurality.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better fitOrder)
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok hasSrc personalSrc noInputs)
open TruthCore.Causality.AxiarchicFoundation.Control
  (Item contains produces aboutItem appInner appNone)
open TruthCore.Causality.PossibiliaContent (NonRealContained)
open TruthCore.Causality.PossibiliaContent.Control (realBlob)
open TruthCore.Causality.IntentionalExemplarExtension.Control (frame rootProfile)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

private theorem weightRealizesOrder (s : Scenario) (x y : Outcome) :
    better s x y ↔ weight s y < weight s x := by
  cases s <;> cases x <;> cases y <;> simp [better, fitOrder, fits, weight]

private theorem baseAsymmetric (x y : Outcome) :
    better .cBetter x y → ¬ better .cBetter y x := by
  rw [weightRealizesOrder, weightRealizesOrder]
  exact Nat.lt_asymm

private theorem baseFavours : better .cBetter .c .d := Or.inr ⟨rfl, rfl⟩

private theorem sharedIntrinsicStructure : SharedIntrinsicStructure := by
  obtain ⟨⟨hLane, hSimple, hNoPresent, _, _, _⟩, _⟩ :=
    TruthCore.Results.Causality.PossibiliaContent.possibiliaControls
  obtain ⟨_, hAdapter, hRoot, hNecessary, _, _, _, _⟩ :=
    TruthCore.Results.Causality.IntentionalExemplarExtension.controls
  refine ⟨hRoot, hNecessary, ?_, hAdapter, ⟨rfl, rfl, rfl⟩, ?_, ?_,
    hSimple, hLane, hNoPresent, ?_,
    TruthCore.Results.Causality.ImpersonalFoundationJoint.ggBetter, ?_, ?_,
    weightRealizesOrder, ?_, ?_⟩
  · refine ⟨Or.inr rfl, false, trivial, ?_⟩
    simp [producingFrame, frame]
  · rintro g x ⟨h, _, _⟩
    cases h
  · rintro w g x t ⟨rfl, rfl, rfl⟩
    exact ⟨Or.inl rfl, Or.inr rfl, rfl, rfl⟩
  · simp [hasSrc, personalSrc, favTok]
  · intro o
    refine ⟨⟨⟨rfl, Or.inr ⟨o, rfl⟩⟩, ?_⟩, ?_⟩
    · rintro ⟨_, h⟩
      cases h
    · rintro ⟨_, o', h⟩
      cases h
  · intro o
    exact ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
  · intro o
    rfl
  · intro a _
    exact Subsingleton.elim _ _

private theorem matchedApprehensionAssignments : MatchedApprehensionAssignments := by
  obtain ⟨⟨_, _, _, _, _, hPersonal⟩, ⟨_, _, _, _, _, hNoncognitive⟩, _⟩ :=
    TruthCore.Results.Causality.PossibiliaContent.possibiliaControls
  obtain ⟨⟨_, _, _, _, hRecognition, _⟩, ⟨_, _, _, _, hNoRecognition, _⟩, _⟩ :=
    TruthCore.Results.Causality.AxiarchicFoundation.axiarchicControls
  refine ⟨sharedIntrinsicStructure, ⟨?_, hPersonal, hRecognition⟩,
    ⟨fun _ _ h => h, ?_, hNoncognitive, hNoRecognition⟩⟩
  · exact ⟨(), rfl, fun a _ => Subsingleton.elim _ _,
      fun o => ⟨rfl, rfl, o, rfl⟩⟩
  · rintro ⟨_, _, _, h⟩
    exact (h .c).2

private theorem identityAndSymmetryControls : IdentityAndSymmetryControls := by
  have hSource : PreservesDescription realBearer exchange := fun _ => rfl
  have hAct : PreservesDescription actOf exchange := fun _ => rfl
  have hIrr (o : Outcome) : ¬ better .cBetter o o :=
    fun h => baseAsymmetric o o h h
  refine ⟨⟨by decide, rfl, rfl⟩, ?_, ?_, hSource, hAct, ?_,
    (fun _ => rfl), baseAsymmetric, baseFavours, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hcd := h (show realBearer .c = realBearer .d from rfl)
    cases hcd
  · intro h
    have hcd := h (show actOf .c = actOf .d from rfl)
    cases hcd
  · intro o
    exact propext ⟨fun _ => ⟨rfl, o, rfl⟩, fun _ => ⟨rfl, exchange o, rfl⟩⟩
  · intro h
    exact identityAndRankingLaws.2.2 Outcome Bool realBearer (better .cBetter)
      baseAsymmetric h exchange hSource .c .d rfl rfl baseFavours
  · intro h
    exact identityAndRankingLaws.2.2 Outcome Unit actOf (better .cBetter)
      baseAsymmetric h exchange hAct .c .d rfl rfl baseFavours
  · intro σ hσ x y
    rw [weightRealizesOrder, weightRealizesOrder, hσ x, hσ y]
  · intro h
    have hcd : (1 : Nat) = 2 := h .c
    cases hcd
  · intro rel hFactor
    exact TruthCore.Results.Causality.AxiarchicFoundation.unindividuatedNotFavoured
      (better .cBetter) rel realBearer hFactor hIrr .c .d rfl baseFavours
  · intro rel hFactor
    exact TruthCore.Results.Causality.AxiarchicFoundation.unindividuatedNotFavoured
      (better .cBetter) rel actOf hFactor hIrr .c .d rfl baseFavours

/-- The matched assignments preserve the shared source and nonempty production;
the additional controls isolate injectivity and explanatory completeness. -/
theorem intrinsicPluralityControls : Control.IntrinsicPluralityControls :=
  ⟨matchedApprehensionAssignments, identityAndSymmetryControls⟩

end Controls

section Positive

open TruthCore.Causality.ImitabilityPlurality.Control
open TruthCore.Causality.ImitabilityPlurality.PositiveControl
open TruthCore.Causality.ImitabilityGrounding
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.IntentionalExemplarExtension.Control (frame)

private theorem sourceExists (v : Bool) :
    producingFrame.history.ontic.ExistsAt v true := Or.inl rfl

private theorem natureHolds (personal : Bool) (value : Outcome → Nat) (v : Bool) :
    holds personal value v .nature := ⟨sourceExists v, fun _ => rfl⟩

private theorem modeHolds (personal : Bool) (value : Outcome → Nat) (v : Bool) (o : Outcome) :
    holds personal value v (.mode o) := ⟨sourceExists v, rfl⟩

private theorem selectedStrict : sourceValue values true .d < sourceValue values true .c := by
  change (1 : Nat) < 2
  decide

private theorem rankingHolds (personal : Bool) (v : Bool) :
    holds personal values v .ranking := ⟨sourceExists v, selectedStrict⟩

private theorem pathFactive {personal : Bool} {value : Outcome → Nat} {v : Bool} {p q : Fact}
    (h : Relation.TransGen (step personal value v) p q) :
    holds personal value v p ∧ holds personal value v q := by
  induction h with
  | single hStep => exact ⟨hStep.1, hStep.2.1⟩
  | tail _ hStep ih => exact ⟨ih.1, hStep.2.1⟩

private theorem pathIncreases {personal : Bool} {value : Outcome → Nat} {v : Bool} {p q : Fact}
    (h : Relation.TransGen (step personal value v) p q) : level p < level q := by
  induction h with
  | single hStep => exact hStep.2.2.1
  | tail _ hStep ih => exact Nat.lt_trans ih hStep.2.2.1

private theorem strictPriority (personal : Bool) (value : Outcome → Nat) (v : Bool) :
    FactPriorityAsymmetricAt (arena personal value) v ∧
      FactPriorityTransitiveAt (arena personal value) v :=
  ⟨fun _ _ h h' => Nat.lt_asymm (pathIncreases h) (pathIncreases h'),
    fun _ _ _ h h' => h.trans h'⟩

private theorem cognitiveMode (v : Bool) (o : Outcome) :
    (arena true values).explains v .cognition (.mode o) :=
  Relation.TransGen.single
    ⟨⟨sourceExists v, rfl⟩, modeHolds true values v o, by change (2 : Nat) < 3; decide,
      Or.inr (Or.inl ⟨rfl, rfl, o, rfl⟩)⟩

private theorem natureMode (personal : Bool) (v : Bool) (o : Outcome) :
    (arena personal values).explains v .nature (.mode o) := by
  cases personal with
  | false =>
    exact Relation.TransGen.single
      ⟨natureHolds false values v, modeHolds false values v o, by change (1 : Nat) < 3; decide,
        Or.inl ⟨rfl, Or.inl ⟨rfl, o, rfl⟩⟩⟩
  | true =>
    have h : (arena true values).explains v .nature .cognition :=
      Relation.TransGen.single
        ⟨natureHolds true values v, ⟨sourceExists v, rfl⟩, by decide,
          Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    exact h.trans (cognitiveMode v o)

private theorem modeRanking (personal : Bool) (v : Bool) :
    (arena personal values).explains v (.mode .c) .ranking :=
  Relation.TransGen.single
    ⟨modeHolds personal values v .c, rankingHolds personal v, by decide,
      Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩))⟩

private theorem natureRanking (personal : Bool) (v : Bool) :
    (arena personal values).explains v .nature .ranking :=
  (natureMode personal v .c).trans (modeRanking personal v)

private theorem rankingExercise (personal : Bool) :
    (arena personal values).explains true .ranking .exercise :=
  Relation.TransGen.single
    ⟨rankingHolds personal true, ⟨rfl, selectedStrict⟩, by decide,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩

private theorem exerciseEffect (personal : Bool) :
    (arena personal values).explains true .exercise .effectExists :=
  Relation.TransGen.single
    ⟨⟨rfl, selectedStrict⟩, Or.inr rfl, by decide,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩

private theorem givingPriority (personal : Bool) :
    GivingExercisePriorityAt (directedFrame values) (arena personal values)
      true true .exercise () := by
  rintro effect ⟨⟨_, _, rfl⟩, _⟩
  exact exerciseEffect personal

private theorem sourceBasedAccount (personal : Bool) : SourceBasedAccount personal values := by
  refine ⟨?_, ?_, ?_, ?_, (fun v => ⟨rfl, rfl, sourceExists v⟩),
    (fun v o => ⟨modeHolds personal values v o, natureMode personal v o⟩),
    (fun v => ⟨rankingHolds personal v, natureRanking personal v⟩), ?_, ?_,
    strictPriority personal values, rankingExercise personal, givingPriority personal, ?_⟩
  · intro v b
    cases b <;> rfl
  · intro v p q h
    exact pathFactive h
  · constructor
    · rintro v b f ⟨rfl, rfl, _⟩
      exact natureHolds personal values v
    · rintro v b f ⟨_, _, h⟩
      exact h
  · rintro w b f ⟨rfl, rfl, _⟩ v _ h
    exact ⟨h, fun _ => rfl⟩
  · simp [arena, directedFrame, producingFrame, frame]
  · intro h
    have hImpossible : holds personal values false .exercise :=
      h true .ranking .exercise (rankingExercise personal) false trivial
        (rankingHolds personal false)
    cases hImpossible.1
  · exact TruthCore.Results.Causality.ImitabilityGrounding.noEffectGroundedGiving
      (directedFrame values) (arena personal values) true true .ranking .exercise ()
      (strictPriority personal values true).1 (strictPriority personal values true).2
      (rankingExercise personal) (givingPriority personal)

private theorem noCognitivePath (v : Bool) (f : Fact) :
    ¬ (arena false values).explains v .cognition f := by
  intro h
  have hCognition : holds false values v .cognition := (pathFactive h).1
  cases hCognition.2

private theorem oneCognitiveAct : OneActApprehendsModes (apprehends true) :=
  matchedApprehensionAssignments.2.1.1

/-- The two positive explanatory interpretations meet the same source-nature,
availability and productive-relevance requirements. Their cognitive priority
paths differ explicitly; the extensional production and ranking agree. -/
theorem intrinsicGroundingControls : PositiveControl.Certificate := by
  refine ⟨sharedIntrinsicStructure, sourceBasedAccount false, sourceBasedAccount true,
    ?_, (fun _ _ h => h), (fun v o => noCognitivePath v (.mode o)),
    (fun v => noCognitivePath v .ranking), cognitiveMode,
    (fun v => (cognitiveMode v .c).trans (modeRanking true v)),
    oneCognitiveAct, ?_, ⟨⟨rfl, rfl, rfl⟩, selectedStrict⟩, ?_⟩
  · intro personal v
    cases personal with
    | false =>
      constructor
      · intro h
        cases h.2
      · rintro ⟨_, _, _, h⟩
        exact False.elim (h .c).2
    | true => exact ⟨fun _ => oneCognitiveAct, fun _ => ⟨sourceExists v, rfl⟩⟩
  · intro v b e t
    constructor
    · exact And.left
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨_, rfl, _⟩ := h
      exact selectedStrict
  · rintro v b e t ⟨_, h⟩
    cases b <;> exact Nat.lt_irrefl 0 h

end Positive

end TruthCore.Results.Causality.ImitabilityPlurality
