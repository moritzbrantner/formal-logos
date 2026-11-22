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
reality, lacks the infinite. -/
theorem objectiveAdequacySeparationControl : ObjectiveAdequacySeparationControl := by
  refine ⟨gradesOf (fun _ r => r ≠ some true) (fun _ _ _ => False) (fun _ _ _ => True) none,
    selfCausedIdea, ?_, ?_, ⟨(), trivial, trivial, rfl⟩, ?_, ?_, ⟨fun h => Bool.false_ne_true (Option.some.inj h), trivial⟩, ?_, ?_⟩
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

end TruthCore.Results.Causality.CartesianIdeaOfInfinite
