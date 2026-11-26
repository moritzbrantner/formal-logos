module

public import TruthCore.Causality.AppetitePowerExercise
public import TruthCore.Causality.IntellectualInclination
public import TruthCore.Case.Catholicism.StageTwo

/-! A same-bearer fragment of the will argument. The appraisal relation says
that the subject apprehends a good under the indicated form. The inclination
is the form-relative orientation of the existing argument. Recognition of
that orientation as will remains an explicit premise. -/

@[expose] public section

namespace TruthCore.Causality.IntellectualAppetite

open TruthCore.Causality.AppetitePowerExercise (Interpretation Exercise)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

variable {B F : Type}

/-- The same bearer is actualized by an intelligible form and apprehends
something as good under that form. The object is represented by its form
index here. This is an analyst premise about intellectual GOD_4 bearers. -/
def GodIntellectApprehendsGood (IsGod HasIntellect : B → Prop)
    (HasForm Appraises : B → F → Prop) (Intelligible : F → Prop) : Prop :=
  ∀ g, IsGod g → HasIntellect g → ∃ f, HasForm g f ∧ Intelligible f ∧ Appraises g f

/-- Orientation follows actualization by a form under which its bearer
apprehends a good. This is a restriction on the form-inclination principle. -/
def AppraisedFormInclines (IsGod : B → Prop) (HasForm Appraises InclinedTo : B → F → Prop)
    (Intelligible : F → Prop) : Prop :=
  ∀ g f, IsGod g → HasForm g f → Intelligible f → Appraises g f → InclinedTo g f

/-- Recognize the orientation following this appraised form as possession
of will by that bearer. Application requires that the orientation is toward
the good under the apprehended aspect. The clause supplies no act. -/
def AppraisedInclinationIsWill (IsGod : B → Prop) (Appraises InclinedTo : B → F → Prop)
    (Intelligible : F → Prop) (HasWill : B → Prop) : Prop :=
  ∀ g f, IsGod g → Intelligible f → Appraises g f → InclinedTo g f → HasWill g

/-- OPEN calibration at a selected bearer, apprehended possessed good, and
occasion. The disjunction uses the intrinsic respect supplied by the
interpretation. A dormant capacity or an unproduced external effect alone
does not validate this calibration. -/
def ExerciseOrPotency {m : Interpretation} {R : Type}
    (HasWill : m.Subject → Prop) (InPotency : m.Subject → R → Prop)
    (g : m.Subject) (o : m.Object) (t : m.Occasion) (r : R) : Prop :=
  HasWill g → m.apprehendsGood g o t → m.possessed g o t →
    Nonempty (Exercise m g o t) ∨ InPotency g r

end TruthCore.Causality.IntellectualAppetite
