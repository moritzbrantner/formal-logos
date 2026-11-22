module

public import TruthCore.Causality.GradesFrame
public import TruthCore.Causality.Round3FourthWay

/-!
# Cartesian causal adequacy over the grades frame

Analyst formulations, attribution deferred (owner direction 2026-11-05). The
names Descartes and *Meditation* III serve as navigation only; no source,
passage or claim record is attached. The principle navigated to is the one
usually cited as "there must be at least as much reality in the efficient and
total cause as in its effect", together with the clause that whatever is in an
effect is in its cause formally or eminently.

Everything is stated over the shared `GradesFrame` (#1784): `F.InAct` is the
frame's act primitive with the mode of possession left open (IN_ACT_4), so
"formally or eminently" is not a further disjunction here but the open mode of
that one primitive; `F.CausesIn` is CAUSE_2 (cause of a thing's being `r`, as
fire of heat); `F.MoreIn` is the primitive comparative (MORE_1).

One primitive is added as an explicit binder, because the frame has no field
for it:

* `Total c x r`: `c`'s causing `x`'s being `r` is **total**: it needs no
  co-cause alongside `c` (the contrast is a partial cause, *concausa*). It is
  not "sole cause" (two total causes of one effect are not excluded), not
  "first cause", and not sufficiency in a modal sense. Nothing relates it to
  `CausesIn`; `TotalCauseIn` below conjoins the two.

The comparison targets on the case's root routes are
`PerfectionsOfEffectPreexistInCauseReading` (PEPC, q.4 a.2),
`CauseOfBeingCausesEveryPerfection` and the Aristotelian strict comparative
`CauseOfQualityInAnotherIsMoreSuchReading`. Results in
`TruthCore.Results.Causality.CartesianAdequacy`.
-/

@[expose] public section

namespace TruthCore.Causality.CartesianAdequacy

open TruthCore.Causality.Grades (GradesFrame)

variable {W B T R : Type}

/-- `c` is an efficient and total cause of `x`'s being `r`: a cause of it in
the frame's CAUSE_2 sense whose causing needs no co-cause (`Total`). -/
def TotalCauseIn (F : GradesFrame W B T R) (Total : B → B → R → Prop)
    (c x : B) (r : R) : Prop :=
  F.CausesIn c x r ∧ Total c x r

/-- Respect-wise containment, every cause (analyst strengthening, not
attributed): whatever causes `x`'s being `r`, where `x` is in act in `r`, is
itself in act in `r` (formally or eminently, the open mode of IN_ACT_4).
Partial causes are included. -/
def ContainmentInEveryCause (F : GradesFrame W B T R) : Prop :=
  ∀ c x r, F.CausesIn c x r → F.InAct x r → F.InAct c r

/-- Respect-wise containment, total causes only: whatever is the efficient and
total cause of `x`'s being `r`, where `x` is in act in `r`, is itself in act in
`r`, formally or eminently. The faithful analyst reading of the Cartesian
containment clause. -/
def ContainmentInTotalCause (F : GradesFrame W B T R)
    (Total : B → B → R → Prop) : Prop :=
  ∀ c x r, TotalCauseIn F Total c x r → F.InAct x r → F.InAct c r

/-- "At least as much reality in the total cause as in its effect", read on a
represented degree (the non-strict counterpart of MORE_2,
`Grades.DegreeComparative`): the effect's degree of `r` is at most the total
cause's. `≤` in a preorder is "at least as much", not merely "not exceeded". -/
def AtLeastAsMuchDegreeInTotalCause {D : Type} [Preorder D]
    (F : GradesFrame W B T R) (Total : B → B → R → Prop) (deg : R → B → D) :
    Prop :=
  ∀ c x r, TotalCauseIn F Total c x r → deg r x ≤ deg r c

/-- "At least as much reality in the total cause", read on the primitive
comparative MORE_1, where no non-strict comparative is defined: the effect is
not more `r` than its total cause. Not a corpus statement on its own; it is the
target of the MORE_1 control below. -/
def NoEffectExceedsTotalCause (F : GradesFrame W B T R)
    (Total : B → B → R → Prop) : Prop :=
  ∀ c x r, TotalCauseIn F Total c x r → ¬ F.MoreIn r x c

/-! ## Finite interpretations -/

/-- The trivial temporal history on one world and one moment. -/
def unitHistory (B : Type) : TruthCore.Modal.TemporalHistory.History Unit B Unit where
  ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True,
             Causes := fun _ _ _ => False }
  IsAt := fun _ _ _ => True
  now := ()

/-- A grades frame on one world and one moment from its act, comparative and
cause relations; the unused causality fields are empty. -/
def gradesOf {B R : Type} (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) : GradesFrame Unit B Unit R where
  history := unitHistory B
  GivesAt := fun _ _ _ _ => False
  CausesIn := CausesIn
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := esse
  InAct := InAct
  MoreIn := MoreIn

/-- Total-cause containment and q.4 a.2 preexistence are independent: on finite
grades frames (two beings, two respects, `false` the respect of being) each
holds where the other fails. First, a cause of a perfection other than being
that lacks it, with no cause of being at all: PEPC holds vacuously and
total-cause containment fails. Second, a cause of a thing's being (total in
being, only partial in the other perfection) that lacks that other perfection:
total-cause containment holds and PEPC fails. Statements about these
interpretations only. -/
def ContainmentAndPreexistenceIndependent : Prop :=
  (∃ (F : GradesFrame Unit Bool Unit Bool) (Total : Bool → Bool → Bool → Prop),
      TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
          F.InAct F.CausesIn F.esse ∧
        ¬ ContainmentInTotalCause F Total) ∧
    (∃ (F : GradesFrame Unit Bool Unit Bool) (Total : Bool → Bool → Bool → Prop),
      ContainmentInTotalCause F Total ∧
        ¬ TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
          F.InAct F.CausesIn F.esse)

/-- The MORE_1 control: on a two-being, one-respect grades frame where each
being totally causes the other and is in act, and the primitive comparative
holds of every pair in both directions, the Aristotelian strict comparative and
"more such has the perfection" both hold, while the non-strict MORE_1 reading of
"at least as much reality in the total cause" fails (each effect is more than
its distinct total cause). So, without an asymmetry or calibration premise, the
strict comparative does not yield the non-strict one on MORE_1. A statement
about this interpretation only. -/
def StrictComparativeWithoutNonStrictAdequacy : Prop :=
  ∃ (F : GradesFrame Unit Bool Unit Unit) (Total : Bool → Bool → Unit → Prop),
    TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
        F.CausesIn F.MoreIn ∧
      TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading
        F.InAct F.MoreIn ∧
      ¬ NoEffectExceedsTotalCause F Total

end TruthCore.Causality.CartesianAdequacy
