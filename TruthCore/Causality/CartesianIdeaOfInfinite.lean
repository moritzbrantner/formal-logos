module

public import TruthCore.Causality.CartesianAdequacy
public import TruthCore.Causality.ThinkingRootFork
public import TruthCore.Logic.CogitoSubject
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder

/-!
# The idea of the infinite over the grades frame

Analyst formulations, attribution deferred (owner direction 2026-11-05). The
names Descartes, *Meditation* III and the Second Replies serve as navigation
only; no source, passage or claim record is attached. Plan and rejected
readings: attempt `7e8fcf16-0e3e-43b4-954e-08926ebc7c8a`; the formal
containment clause it is compared with is `TruthCore.Causality.CartesianAdequacy`.

Every perfection statement is over the shared `GradesFrame` (#1784): `F.InAct`
is IN_ACT_4 (act, mode of possession left open, so "formally or eminently"),
`F.MoreIn` is MORE_1 and `F.esse` is the respect of being. The frame has no
field for ideas, so the primitives of this argument form a second, separate
structure, `IdeaFrame`, over the same beings and respects. Nothing relates its
fields to the frame's fields or to each other; every bridge is an explicit
premise.

* `Occurs` and `Bears` are the existing cogito binders (`CogitoSubject`,
  `ThinkingRootFork.Thinks`): an episode occurs; a being bears an episode.
* `Represents e r`: the episode `e` presents the perfection `r` as its content
  (the idea's *objective* reality). Representing `r` is not having `r`: the
  idea of heat is not hot.
* `ObjCause c e r`: `c` is a cause of `e`'s representing `r`, of the idea's
  objective reality, not of `e`'s being or of any perfection `e` has. It is
  not the frame's `CausesIn` (CAUSE_2), which relates a cause to a being's
  being in act in a respect.
* `inf`: the perfection of infinite substance (INFINITE_3), a respect of the
  frame's carrier. Nothing relates it to `esse` or to any other respect.
* `me`: the meditator, a designated being of the carrier.

The argument: (P1) some occurring episode borne by the meditator represents
`inf`; (P2) the objective reality of every occurring idea has a cause; (P3)
objective adequacy: whatever causes an idea's representing `r` is in act in
`r`; (P4) the meditator is not in act in `inf`. Hence something other than the
meditator is in act in `inf` and causes the meditator's idea of `inf`.

Objective adequacy (P3) is a separate premise, not an instance of the formal
containment clause (`ContainmentInEveryCause`): see
`ObjectiveAdequacySeparationControl`.
-/

@[expose] public section

namespace TruthCore.Causality.CartesianIdeaOfInfinite

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.CartesianAdequacy (ContainmentInEveryCause)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (IsMaximumIn PerfectionsOfEffectPreexistInCauseReading)

/-- The primitives of the idea-of-the-infinite argument, over beings `B`,
respects `R` and episodes `Episode`. Each field is primitive; no law is
imposed and no field is related to another or to the grades frame. -/
structure IdeaFrame (B R Episode : Type) where
  /-- `Occurs e`: the episode `e` occurs (the cogito's occurrence binder). -/
  Occurs : Episode → Prop
  /-- `Bears x e`: the being `x` bears the episode `e` (the cogito's bearer
  binder). Not a substance relation, not uniqueness of the bearer. -/
  Bears : B → Episode → Prop
  /-- `Represents e r`: the episode `e` presents the perfection `r` as its
  content, the idea's objective reality. Not having `r`, not being caused to
  have `r`, not a true representation of an existing bearer of `r`. -/
  Represents : Episode → R → Prop
  /-- `ObjCause c e r`: `c` is a cause of `e`'s representing `r`, of the
  objective reality `r` of the idea `e`. Not a cause of `e`'s being or of a
  perfection `e` has; not the grades frame's `CausesIn`. -/
  ObjCause : B → Episode → R → Prop
  /-- `inf`: the perfection of infinite substance (INFINITE_3), the respect an
  idea of the infinite presents. Nothing relates it to `esse` or to maximality
  in being. -/
  inf : R
  /-- `me`: the meditator, a designated being. Nothing says that it exists at a
  world, is concrete, is finite or bears any episode. -/
  me : B

variable {W B T R Episode : Type}

/-- P1: some occurring episode borne by the meditator represents the
infinite. First-person and existential: a particular idea of the meditator. -/
def MeditatorHasIdeaOfInfinite (I : IdeaFrame B R Episode) : Prop :=
  ∃ e, I.Occurs e ∧ I.Bears I.me e ∧ I.Represents e I.inf

/-- P2: the objective reality of every occurring idea has a cause: whatever
an occurring episode represents, something causes its representing it. -/
def ObjectiveRealityIsCaused (I : IdeaFrame B R Episode) : Prop :=
  ∀ e r, I.Occurs e → I.Represents e r → ∃ c, I.ObjCause c e r

/-- P3, objective adequacy: whatever causes an idea's representing `r` is in
act in `r` (IN_ACT_4, mode left open: formally or eminently). Every cause,
partial causes included: stronger than "efficient and total cause", so with P4
the meditator is not even a partial cause of its idea's representing `inf`. A
separate premise, not an instance of the formal containment clause. -/
def ObjectiveAdequacy (F : GradesFrame W B T R) (I : IdeaFrame B R Episode) : Prop :=
  ∀ c e r, I.ObjCause c e r → F.InAct c r

/-- P4: the meditator is not in act in the infinite, formally or eminently.
About the meditator only, not about every thinker. -/
def MeditatorLacksInfinite (F : GradesFrame W B T R) (I : IdeaFrame B R Episode) : Prop :=
  ¬ F.InAct I.me I.inf

/-- Conclusion: something other than the meditator is in act in the infinite
and causes the objective reality of an occurring idea of the infinite that the
meditator bears. -/
def InfiniteCauseOfIdea (F : GradesFrame W B T R) (I : IdeaFrame B R Episode) : Prop :=
  ∃ c e, I.Occurs e ∧ I.Bears I.me e ∧ I.Represents e I.inf ∧ I.ObjCause c e I.inf ∧
    c ≠ I.me ∧ F.InAct c I.inf

/-- Bridge from the infinite to maximality in being (open): whatever is in act
in the perfection of infinite substance is maximal in being (MAXIME_1: it has
being and nothing is more a being than it). Not a definitional equality:
`inf` and `esse` are unrelated respects of the frame. -/
def InfiniteIsMaximalInBeing (F : GradesFrame W B T R) (I : IdeaFrame B R Episode) : Prop :=
  ∀ c, F.InAct c I.inf → IsMaximumIn F.InAct F.MoreIn F.esse c

/-- The first-person cogito: the meditator thinks, i.e. bears some occurring
episode (`ThinkingRootFork.Thinks` at the meditator). -/
def MeditatorThinks (I : IdeaFrame B R Episode) : Prop :=
  TruthCore.Causality.ThinkingRootFork.Thinks I.Occurs I.Bears I.me

/-! ## Finite interpretations -/

/-- An idea frame on one being (the meditator), three respects (`none` being,
`some true` the infinite, `some false` representing the infinite) and one
episode: the episode
occurs, the meditator bears it, it represents only the infinite, and the
meditator is the cause of its objective reality. -/
def selfCausedIdea : IdeaFrame Unit (Option Bool) Unit where
  Occurs := fun _ => True
  Bears := fun _ _ => True
  Represents := fun _ r => r = some true
  ObjCause := fun _ _ _ => True
  inf := some true
  me := ()

/-- The separation control for objective adequacy. On one finite grades frame
with the idea frame `selfCausedIdea`, all of the following hold and are part of
the statement:

* the meditator is the only being, and the frame's respect of being is `none`;
* the meditator is in act in being;
* the respect `some false` is the representing feature of the infinite: a being
  is in act in it exactly when it bears an occurring episode that represents
  the infinite, and the meditator is in act in it;
* the meditator causes its own being in act in every respect (CAUSE_2);
* formal containment in every cause (partial causes included) and q.4 a.2
  preexistence hold;
* the meditator has an occurring idea of the infinite whose objective reality
  has a cause (P1, P2) and lacks the infinite (P4);
* objective adequacy fails and nothing is in act in the infinite.

So, on this interpretation, the formal clause does not yield P3 or the
conclusion: the cause of the idea has the representing feature but not the
infinite. A statement about this interpretation only. -/
def ObjectiveAdequacySeparationControl : Prop :=
  ∃ (F : GradesFrame Unit Unit Unit (Option Bool)) (I : IdeaFrame Unit (Option Bool) Unit),
    (∀ x, x = I.me) ∧ F.esse = none ∧ F.InAct I.me F.esse ∧
      (∀ x, F.InAct x (some false) ↔
        ∃ e, I.Occurs e ∧ I.Bears x e ∧ I.Represents e I.inf) ∧
      F.InAct I.me (some false) ∧ (∀ r, F.CausesIn I.me I.me r) ∧
      ContainmentInEveryCause F ∧
      PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse ∧
      MeditatorHasIdeaOfInfinite I ∧ ObjectiveRealityIsCaused I ∧
      MeditatorLacksInfinite F I ∧
      ¬ ObjectiveAdequacy F I ∧ ¬ ∃ c, F.InAct c I.inf

/-- Nonvacuity of the four premises: on a two-being, two-respect grades frame
(`true` the infinite) in which the second being is in act in every respect
and causes the meditator's idea of the infinite, P1-P4 all hold. A statement
about this interpretation only, not that such a cause exists. -/
def MeditationThreePremisesSatisfiable : Prop :=
  ∃ (F : GradesFrame Unit Bool Unit Bool) (I : IdeaFrame Bool Bool Unit),
    MeditatorHasIdeaOfInfinite I ∧ ObjectiveRealityIsCaused I ∧
      ObjectiveAdequacy F I ∧ MeditatorLacksInfinite F I

/-- The cause from Meditation III, with act of esse predicated of that same being. -/
def InfiniteCauseOfIdeaWithEsse (F : GradesFrame W B T R) (I : IdeaFrame B R Episode) : Prop :=
  ∃ c e, I.Occurs e ∧ I.Bears I.me e ∧ I.Represents e I.inf ∧ I.ObjCause c e I.inf ∧
    c ≠ I.me ∧ F.InAct c I.inf ∧ F.InAct c F.esse

/-- A two-state recognizer on unary inputs. Zero starts in the accepting state;
each mark flips the state. The input length indexes runs, not internal memory. -/
def parityState : Nat → Bool
  | 0 => true
  | n + 1 => !(parityState n)

/-- A single choice of output rule selects all lengths or just even lengths. -/
def acceptsLength (evenOnly : Bool) (n : Nat) : Prop :=
  evenOnly = false ∨ parityState n = true

end TruthCore.Causality.CartesianIdeaOfInfinite
