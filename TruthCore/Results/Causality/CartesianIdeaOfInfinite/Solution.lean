module

public import TruthCore.Causality.CartesianIdeaOfInfinite

/-! The idea-of-the-infinite argument over the grades frame (analyst
formulations, attribution deferred; navigation: Descartes, *Meditation* III).

* `meditationThree`: from the meditator's idea of the infinite (P1), the
  caused objective reality of occurring ideas (P2), objective adequacy (P3) and
  the meditator's lacking the infinite (P4), something other than the meditator
  is in act in the infinite and causes the meditator's idea of it.
* `meditationThreePremisesSatisfiable`: P1-P4 hold together on a finite
  interpretation.
* `objectiveAdequacySeparationControl`: formal containment in every cause and
  q.4 a.2 preexistence, with P1, P2 and P4, do not give P3 or the conclusion.
* `maximeEnsOfIdeaOfInfinite`: with the open bridge "whatever is in act in the
  infinite is maximal in being" and the genus principle at being, the
  conclusion gives the quarta via's conclusion: something maximal in being
  causes the being of every other being.
* `thoughtOccursOfMeditatorThinks`: strength order, the first-person cogito
  entails that some thought occurs. -/

@[expose] public section

namespace TruthCore.Results.Causality.CartesianIdeaOfInfinite

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.CartesianAdequacy (ContainmentInEveryCause gradesOf)
open TruthCore.Causality.CartesianIdeaOfInfinite
open TruthCore.Latin.Aquinas.SummaTheologiae
  (MaximumInBeingCausesAllBeingsReading MaximeEnsCausesBeingOfAllReading)
open TruthCore.Logic.CogitoSubject (ThoughtOccurs)

/-- The idea-of-the-infinite argument: P1 gives an occurring idea `e` of the
infinite borne by the meditator; P2 gives a cause `c` of its representing the
infinite; P3 puts `c` in act in the infinite; since the meditator is not (P4),
`c` is not the meditator. -/
theorem meditationThree {W B T R Episode : Type} (F : GradesFrame W B T R)
    (I : IdeaFrame B R Episode)
    (hIdea : MeditatorHasIdeaOfInfinite I)
    (hCaused : ObjectiveRealityIsCaused I)
    (hAdequacy : ObjectiveAdequacy F I)
    (hFinite : MeditatorLacksInfinite F I) :
    InfiniteCauseOfIdea F I := by
  obtain ⟨e, hOcc, hBears, hRep⟩ := hIdea
  obtain ⟨c, hc⟩ := hCaused e I.inf hOcc hRep
  have hInf : F.InAct c I.inf := hAdequacy c e I.inf hc
  refine ⟨c, e, hOcc, hBears, hRep, hc, ?_, hInf⟩
  intro hEq
  exact hFinite (hEq ▸ hInf)

/-- P1-P4 hold together: the second being of two is in act in every respect
and causes the meditator's idea of the infinite. -/
theorem meditationThreePremisesSatisfiable : MeditationThreePremisesSatisfiable := by
  let I : IdeaFrame Bool Bool Unit :=
    { Occurs := fun _ => True, Bears := fun _ _ => True,
      Represents := fun _ r => r = true, ObjCause := fun c _ _ => c = true,
      inf := true, me := false }
  refine ⟨gradesOf (fun c _ => c = true) (fun _ _ _ => False) (fun _ _ _ => False) false,
    I, ⟨(), trivial, trivial, rfl⟩, ?_, ?_, ?_⟩
  · intro e r _ _
    exact ⟨true, rfl⟩
  · intro c e r hc
    exact hc
  · intro h
    exact Bool.false_ne_true h

/-- The separation control: on the one-being frame of `selfCausedIdea`, every
cause is the meditator causing itself, so formal containment and q.4 a.2
preexistence hold, while the meditator, the only cause of its idea's objective
reality, has the representing feature `some false` but lacks the infinite. -/
theorem objectiveAdequacySeparationControl : ObjectiveAdequacySeparationControl := by
  refine ⟨gradesOf (fun _ r => r ≠ some true) (fun _ _ _ => False) (fun _ _ _ => True) none,
    selfCausedIdea, fun _ => rfl, rfl, (fun h => by cases h), ?_,
    fun h => Bool.false_ne_true (Option.some.inj h), fun _ => trivial,
    ?_, ?_, ⟨(), trivial, trivial, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨fun _ => ⟨(), trivial, trivial, rfl⟩,
      fun _ h => Bool.false_ne_true (Option.some.inj h)⟩
  · intro c x r _ hx
    exact hx
  · intro c x r _ hx
    exact hx
  · intro e r _ _
    exact ⟨(), trivial⟩
  · intro h
    exact h rfl
  · intro h
    exact h () () (some true) trivial rfl
  · rintro ⟨c, hc⟩
    exact hc rfl

/-- With the open bridge from the infinite to maximality in being and the
genus principle at being, the cause of the idea of the infinite is a maximum in
being that causes the being of every other being. -/
theorem maximeEnsOfIdeaOfInfinite {W B T R Episode : Type} (F : GradesFrame W B T R)
    (I : IdeaFrame B R Episode)
    (hCause : InfiniteCauseOfIdea F I)
    (hMax : InfiniteIsMaximalInBeing F I)
    (hGenus : MaximumInBeingCausesAllBeingsReading F.InAct F.MoreIn F.CausesIn F.esse) :
    MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse := by
  obtain ⟨c, _, _, _, _, _, _, hInf⟩ := hCause
  have hm := hMax c hInf
  exact ⟨c, hm, hGenus c hm⟩

/-- Strength order: the first-person cogito (the meditator bears some
occurring episode) entails that some thought occurs. -/
theorem thoughtOccursOfMeditatorThinks {B R Episode : Type} (I : IdeaFrame B R Episode)
    (hThinks : MeditatorThinks I) : ThoughtOccurs I.Occurs := by
  obtain ⟨e, hOcc, _⟩ := hThinks
  exact ⟨e, hOcc⟩

/-- Apply actuality-to-being to the very cause and respect supplied by the original result. -/
theorem infiniteCauseWithEsse {W B T R Episode : Type} (F : GradesFrame W B T R)
    (I : IdeaFrame B R Episode) (hCause : InfiniteCauseOfIdea F I)
    (hBeing : TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading
      F.InAct F.esse) : InfiniteCauseOfIdeaWithEsse F I := by
  obtain ⟨c, e, hOcc, hBears, hRep, hc, hOther, hInf⟩ := hCause
  exact ⟨c, e, hOcc, hBears, hRep, hc, hOther, hInf, hBeing c I.inf hInf⟩

/-- The weaker endpoint requires only impersonal occurrence with this content.
The designated meditator still occurs in the lack and distinctness clauses. -/
theorem distinctPossessorWithoutBearer {W B T R Episode : Type} (F : GradesFrame W B T R)
    (I : IdeaFrame B R Episode) (hRep : ∃ e, I.Occurs e ∧ I.Represents e I.inf)
    (hCaused : ObjectiveRealityIsCaused I) (hAdequacy : ObjectiveAdequacy F I)
    (hFinite : MeditatorLacksInfinite F I) : ∃ c, c ≠ I.me ∧ F.InAct c I.inf := by
  obtain ⟨e, hOcc, he⟩ := hRep
  obtain ⟨c, hc⟩ := hCaused e I.inf hOcc he
  have hInf := hAdequacy c e I.inf hc
  exact ⟨c, fun h => hFinite (h ▸ hInf), hInf⟩

private def twoBeingIdea : IdeaFrame Bool Bool Unit :=
  { Occurs := fun _ => True, Bears := fun c _ => c = false,
    Represents := fun _ r => r = true, ObjCause := fun c _ r => c = true ∧ r = true,
    inf := true, me := false }

/-- Positive model with a surpassed cause. Both beings have esse; the meditator
strictly surpasses the unique content cause at esse. This isolates the extra
maximality commitment even after the actuality-to-being premise is granted. -/
theorem surpassedCauseWithEsse :
    ∃ (F : GradesFrame Unit Bool Unit Bool) (I : IdeaFrame Bool Bool Unit),
      MeditatorHasIdeaOfInfinite I ∧ ObjectiveRealityIsCaused I ∧ ObjectiveAdequacy F I ∧
      MeditatorLacksInfinite F I ∧ TruthCore.Causality.Grades.ActualityOnlyInsofarAsBeing F ∧
      InfiniteCauseOfIdeaWithEsse F I ∧
      (∀ c, F.InAct c I.inf → F.MoreIn F.esse I.me c) ∧ ¬ InfiniteIsMaximalInBeing F I := by
  let I := twoBeingIdea
  let F := gradesOf (fun c r : Bool => r = false ∨ c = true)
    (fun r x y => r = false ∧ x = false ∧ y = true) (fun _ _ _ => False) false
  have hIdea : MeditatorHasIdeaOfInfinite I := ⟨(), trivial, rfl, rfl⟩
  have hCaused : ObjectiveRealityIsCaused I := fun _ _ _ hr => ⟨true, rfl, hr⟩
  have hAdequacy : ObjectiveAdequacy F I := fun _ _ _ hc => Or.inr hc.1
  have hFinite : MeditatorLacksInfinite F I :=
    fun h => h.elim (Ne.symm Bool.false_ne_true) Bool.false_ne_true
  have hBeing : TruthCore.Causality.Grades.ActualityOnlyInsofarAsBeing F :=
    fun _ _ _ => Or.inl rfl
  refine ⟨F, I, hIdea, hCaused, hAdequacy, hFinite, hBeing,
    infiniteCauseWithEsse F I (meditationThree F I hIdea hCaused hAdequacy hFinite) hBeing,
    ?_, ?_⟩
  · intro c h
    exact ⟨rfl, rfl, h.resolve_left (Ne.symm Bool.false_ne_true)⟩
  · intro h
    exact (h true (Or.inr rfl)).2 false ⟨rfl, rfl, rfl⟩

/-- Dropping actuality-to-being can lose esse specifically at the cause:
the meditator has esse, the only infinite cause lacks it. -/
theorem causeWithoutEsse :
    ∃ (F : GradesFrame Unit Bool Unit Bool) (I : IdeaFrame Bool Bool Unit),
      MeditatorHasIdeaOfInfinite I ∧ ObjectiveRealityIsCaused I ∧ ObjectiveAdequacy F I ∧
      MeditatorLacksInfinite F I ∧ F.InAct I.me F.esse ∧ InfiniteCauseOfIdea F I ∧
      ¬ InfiniteCauseOfIdeaWithEsse F I := by
  let I := twoBeingIdea
  let F := gradesOf (fun c r : Bool => c = r)
    (fun _ _ _ => False) (fun _ _ _ => False) false
  have hIdea : MeditatorHasIdeaOfInfinite I := ⟨(), trivial, rfl, rfl⟩
  have hCaused : ObjectiveRealityIsCaused I := fun _ _ _ hr => ⟨true, rfl, hr⟩
  have hAdequacy : ObjectiveAdequacy F I := fun _ _ _ hc => hc.1.trans hc.2.symm
  have hFinite : MeditatorLacksInfinite F I := Bool.false_ne_true
  refine ⟨F, I, hIdea, hCaused, hAdequacy, hFinite, rfl,
    meditationThree F I hIdea hCaused hAdequacy hFinite, ?_⟩
  rintro ⟨c, _, _, _, _, _, _, hinf, hesse⟩
  exact (Ne.symm Bool.false_ne_true) (hinf.symm.trans hesse)

/-- Both finite rules accept lengths above every bound. At the next length
only the unrestricted rule accepts. The mark stream and transition stay fixed.
This is a mathematical content control, with no metaphysical interpretation
of an input length as a being or perfection. -/
theorem finiteRulesDiscriminateAboveEveryBound (k : Nat) :
    ∃ n, k < n ∧ acceptsLength false n ∧ acceptsLength true n ∧
      acceptsLength false (n + 1) ∧ ¬ acceptsLength true (n + 1) := by
  have pair : ∀ n, parityState n = true → acceptsLength false n ∧ acceptsLength true n ∧
      acceptsLength false (n + 1) ∧ ¬ acceptsLength true (n + 1) := by
    intro n hn
    refine ⟨Or.inl rfl, Or.inr hn, Or.inl rfl, ?_⟩
    intro h
    have hFalse : parityState (n + 1) = false := congrArg Bool.not hn
    exact h.elim (Ne.symm Bool.false_ne_true) (fun hs => Bool.false_ne_true (hFalse.symm.trans hs))
  cases h : parityState (k + 1) with
  | false =>
    refine ⟨k + 2, Nat.lt_succ_of_lt (Nat.lt_succ_self k), pair _ ?_⟩
    change !(parityState (k + 1)) = true
    rw [h]
    rfl
  | true => exact ⟨k + 1, Nat.lt_succ_self k, pair _ h⟩

end TruthCore.Results.Causality.CartesianIdeaOfInfinite
