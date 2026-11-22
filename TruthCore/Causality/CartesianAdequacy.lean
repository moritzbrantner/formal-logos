module

public import TruthCore.Causality.GradesFrame
public import TruthCore.Causality.Round3FourthWay
public import TruthCore.Causality.TermSenseForks2
public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing

/-!
# Cartesian causal adequacy over the grades frame

Analyst formulations, attribution deferred (owner direction 2026-11-05). The
names Descartes and *Meditation* III serve as navigation only; no source,
passage or claim record is attached. The principle navigated to is the one
usually cited as "there must be at least as much reality in the efficient and
total cause as in its effect", together with the clause that whatever is in an
effect is in its cause formally or eminently.

Everything is stated over the shared `GradesFrame` (#1784): `F.InAct` is the
frame's act primitive with the mode of possession left open (IN_ACT_4);
`F.CausesIn` is CAUSE_2 (cause of a thing's being `r`, as fire of heat);
`F.MoreIn` is the primitive comparative (MORE_1). The containment statements
use one `InAct` on both sides: a **uniform IN_ACT_4 reading**. The
mode-asymmetric reading (formal in the effect, formal or eminent in the cause)
is now a separate sibling using TermSenseForks.ActFrame. Translating the
uniform IN_ACT_4 to it takes TWO directed sense calibrations; neither is a
definition of the grades frame's primitive or an implication from causing alone.

Two scope readings of the containment clause are kept as siblings
(disambiguation "Scope of the Cartesian containment clause"): respect-wise
(`ContainmentInTotalCause`, a total cause of `x`'s being `r` has `r`) and
whole-effect (`WholeEffectContainmentInTotalCause`, a total cause of `x`'s
being has every perfection of `x`, as with the stone that cannot begin to exist
unless produced by something containing everything in the stone).

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
itself in act in `r`, uniform IN_ACT_4 reading on both sides. Partial causes
are included. -/
def ContainmentInEveryCause (F : GradesFrame W B T R) : Prop :=
  ∀ c x r, F.CausesIn c x r → F.InAct x r → F.InAct c r

/-- Respect-wise containment, total causes only: whatever is the efficient and
total cause of `x`'s being `r`, where `x` is in act in `r`, is itself in act in
`r`. Analyst reading of the Cartesian containment clause on its respect-wise
scope, with a uniform IN_ACT_4 reading of act on both sides (the
mode-asymmetric reading is an unformalized sibling). -/
def ContainmentInTotalCause (F : GradesFrame W B T R)
    (Total : B → B → R → Prop) : Prop :=
  ∀ c x r, TotalCauseIn F Total c x r → F.InAct x r → F.InAct c r

/-- Whole-effect containment, total causes of being only: whatever is the
efficient and total cause of `x`'s being has every perfection `x` is in act in
(uniform IN_ACT_4 reading). The whole-effect sibling of
`ContainmentInTotalCause`; PEPC entails it. -/
def WholeEffectContainmentInTotalCause (F : GradesFrame W B T R)
    (Total : B → B → R → Prop) : Prop :=
  ∀ c x r, TotalCauseIn F Total c x F.esse → F.InAct x r → F.InAct c r

/-- "At least as much reality in the total cause as in its effect", read on a
represented degree (the non-strict counterpart of MORE_2,
`Grades.DegreeComparative`): the effect's degree of `r` is at most the total
cause's. `≤` in a preorder is "at least as much", not merely "not exceeded".
Per respect: an analyst generalization of a single overall degree of reality. -/
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


/-! ## Formal effect / formal-or-eminent cause (IN_ACT_1 → IN_ACT_3)

The q.4 a.2 formula and the uniform Cartesian containment statements quantify
over a SINGLE `GradesFrame.InAct` (IN_ACT_4). Here the effect is formally in
act, and the cause is formally OR virtually in act. The `ActFrame` is the
existing sense fork, not a parallel ontology. The direction-specific
calibrations below are substantive OPEN semantic bridges: they are not a
definition of IN_ACT_4, and no claim is made that eminent intellectual
perfection already constitutes the intrinsic power HAS_INTELLECT_1.
-/

open TruthCore.Causality.TermSenseForks (ActFrame)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (PerfectionsOfEffectPreexistInCauseReading MaximumInBeingCausesAllBeingsReading
  ActualityOnlyInsofarAsBeingReading)
open TruthCore.Case.Catholicism (GodIsMaximalInBeing)

/-- A formally possessed effect-perfection preexists formally or eminently in
its cause of being. Same cause/being relation as q.4 a.2, but two different
act senses. No total-cause restriction is silently introduced. -/
def FormalEffectPreexistsInclusively (F : GradesFrame W B T R)
    (A : ActFrame B R) : Prop :=
  ∀ c x r, F.CausesIn c x F.esse →
    A.InActFormally x r → A.InActFormallyOrVirtually c r

/-- Effect-side sense bridge, from IN_ACT_1 to the grades IN_ACT_4. -/
def FormalActEntersGrades (F : GradesFrame W B T R)
    (A : ActFrame B R) : Prop :=
  ∀ x r, A.InActFormally x r → F.InAct x r

/-- Cause-side sense bridge, from grades IN_ACT_4 to IN_ACT_3. This is not
equivalent to the preceding bridge. -/
def GradesActIsInclusive (F : GradesFrame W B T R)
    (A : ActFrame B R) : Prop :=
  ∀ x r, F.InAct x r → A.InActFormallyOrVirtually x r

/-- Every supplied GOD_4 bearer contains the specified intellectual respect in
formal or eminent act. This is NOT the primitive `GodHasIntellect`, which
denotes intrinsic cognitive capacity, still less its current exercise. -/
def GodContainsIntellectualPerfection (A : ActFrame B R)
    (IsGod : B → Prop) (intellectual : R) : Prop :=
  ∀ g, IsGod g → A.InActFormallyOrVirtually g intellectual

/-! ## Populated finite semantic controls (structural surrogates)

There are exactly two beings: false is an intellectual effect; true is the
universal source for both the being and cognitive respects. The source is
assigned the cognitive respect *virtually* but not formally, and the primitive
`intellect` (the stand-in for `HasIntellect`) is not assigned to it. A second
reading removes the virtual perfection at the source without changing its
causing of the effect. Both retain the two directed calibrations.

These tables are STRUCTURAL SURROGATES. `InActVirtually` and `intellect` are
independent primitives here, assigned by stipulation. The first table
certifies only that, in this primitive profile, the listed input bundle of
`godContainsFromIntellectualExemplar` does not entail the eminent-recognition
premise (virtual intellectual possession at the GOD_4 bearer gives
`HasIntellect`). It is NOT evidence of a difference in meaning between eminent
intellectual containment and intrinsic intellect: whether eminent containment
in DEF-IN-ACT-VIRTUALLY's "higher way" sense includes intrinsic intellect is
OPEN, and on that substantive-eminence reading the table is not an admissible
model. The models do not certify the real-world truth or falsity of the q.4
premise or a complete GOD_4 root bundle. No capacity/exercise relation is
formalized here.
-/
namespace FormalEminentControl

def formal (b r : Bool) : Prop :=
  r = false ∨ (b = false ∧ r = true)

def virtual (b r : Bool) : Prop :=
  b = true ∧ r = true

def inclusive (b r : Bool) : Prop :=
  formal b r ∨ virtual b r

def more (_ : Bool) (c x : Bool) : Prop :=
  c = true ∧ x = false

def causes (c x : Bool) (_ : Bool) : Prop :=
  c = true ∧ x = false

def grades : GradesFrame Unit Bool Unit Bool :=
  gradesOf inclusive more causes false

def formalOnlyGrades : GradesFrame Unit Bool Unit Bool :=
  gradesOf formal more causes false

def act : ActFrame Bool Bool where
  InActFormally := formal
  InActVirtually := virtual
  InPotency := fun _ _ => False
  MovedIn := fun _ _ => False
  MovesIn := fun _ _ _ => False

def formalOnlyAct : ActFrame Bool Bool where
  InActFormally := formal
  InActVirtually := fun _ _ => False
  InPotency := fun _ _ => False
  MovedIn := fun _ _ => False
  MovesIn := fun _ _ _ => False

def source (b : Bool) : Prop := b = true
def intellect (b : Bool) : Prop := b = false

/-- First table: every non-logical hypothesis of
`godContainsFromIntellectualExemplar` holds (GOD_4 maximality, being-only genus
causality, actuality-to-being, an intellectual exemplar and its formal
calibration, the effect-side calibration and asymmetric preexistence; excluded
middle is a logical principle, not a model clause), together with the
cause-side calibration, uniform q.4 preexistence and the formal-recognition
premise, even in universal form. So the table is a joint nonvacuity witness of
that bundle, while the GOD_4-restricted eminent-recognition premise fails.
Within this primitive profile that pins which recognition premise the bundle
leaves open; it says nothing about the substantive-eminence reading (see the
section comment). Second table: cognitive production, maximality, being-only
genus causality and both calibrations hold, while asymmetric
formal-or-eminent preexistence fails. -/
def Controls : Prop :=
  (∃ x, intellect x ∧ grades.CausesIn true x grades.esse ∧
    act.InActFormally x true) ∧
  (∀ x, intellect x → act.InActFormally x true) ∧
  FormalActEntersGrades grades act ∧
  GradesActIsInclusive grades act ∧
  PerfectionsOfEffectPreexistInCauseReading
    grades.InAct grades.CausesIn grades.esse ∧
  FormalEffectPreexistsInclusively grades act ∧
  GodIsMaximalInBeing source grades.InAct grades.MoreIn grades.esse ∧
  MaximumInBeingCausesAllBeingsReading
    grades.InAct grades.MoreIn grades.CausesIn grades.esse ∧
  ActualityOnlyInsofarAsBeingReading grades.InAct grades.esse ∧
  GodContainsIntellectualPerfection act source true ∧
  (∀ b, act.InActFormally b true → intellect b) ∧
  ¬ (∀ g, source g → act.InActVirtually g true → intellect g) ∧
  FormalActEntersGrades formalOnlyGrades formalOnlyAct ∧
  GradesActIsInclusive formalOnlyGrades formalOnlyAct ∧
  (∃ x, intellect x ∧ formalOnlyGrades.CausesIn true x formalOnlyGrades.esse ∧
    formalOnlyAct.InActFormally x true) ∧
  GodIsMaximalInBeing source formalOnlyGrades.InAct formalOnlyGrades.MoreIn
    formalOnlyGrades.esse ∧
  MaximumInBeingCausesAllBeingsReading
    formalOnlyGrades.InAct formalOnlyGrades.MoreIn formalOnlyGrades.CausesIn
    formalOnlyGrades.esse ∧
  ¬ FormalEffectPreexistsInclusively formalOnlyGrades formalOnlyAct

end FormalEminentControl


end TruthCore.Causality.CartesianAdequacy
