module

public import Mathlib.Order.Basic
public import TruthCore.Causality.Frame
public import TruthCore.Case.Catholicism.CausalPerfectionTransfer
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1

/-!
# The grades frame: the Fourth Way's primitives over the causality frame

Owner decision 2026-11-19 (#1784, shared frames for new work). The *quarta via*
cluster (ST I q.2 a.3, q.4 a.1-2 and the Stage-one bridges built on them) states
every proposition over its own binders `InAct`, `MoreIn`, `CausesIn` and `esse`.
`truth discover` therefore saw the grades, maximum and cause-of-perfection
premises of different modules as statements about unrelated relations (attempt
`9869069b-393d-4562-9be4-c0ac1a8d374d`). This module gives the cluster's
vocabulary one shared frame. It **defines none of the primitives**:

* `InAct x r` (IN_ACT_4): `x` is in act in the perfection `r`, actually has
  it, with the mode of possession (formal, virtual or eminent) left open, as
  DISAMB-IN-ACT requires of the case's single act parameter (DEF-ACT).
* `MoreIn r x y` (MORE_1): `x` is more `r` than `y`, the primitive comparative
  *magis* (DEF-MORE-IN). No order law is imposed.
* `CausesIn` and `esse` are the causality frame's fields (CAUSE_2 and the esse
  respect, DEF-ESSE); they are inherited, not redeclared.

Each field is a primitive by design. A faithful definition from more basic
shared vocabulary was looked for and not found: `InAct`, `CausesIn` and `esse`
are the basic vocabulary of the family, and every proposed definition of
`MoreIn` is a contested reading. The represented-degree comparative
(`DegreeComparative`, MORE_2) is recorded below as a sibling definition, not as
the meaning of `MoreIn`. The calibrations between the two
(`Round3FourthWay.MoreInExceedsDegree`, `DegreeExcessAmongBearersIsMoreIn`)
remain open bridge premises. The checks at the end show that they differ: a
represented-degree comparative is a strict order, the primitive is not
constrained to be one.

The adapters instantiate existing statements, unchanged, from frame fields. Each
comes with an `Iff.rfl` check of its unfolded body. No relation between fields
is assumed; applicability of every field to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.Grades

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The Fourth Way's primitives over the shared causality frame. `InAct` and
`MoreIn` are the two primitives the causality frame lacks; nothing relates them
to each other or to the inherited fields. -/
structure GradesFrame (W B T R : Type) extends CausalityFrame W B T R where
  /-- `InAct x r`: `x` actually has the perfection `r`, as fire is actually hot
  (DEF-ACT), with the mode of possession left open (IN_ACT_4). Not formal act
  (IN_ACT_1), virtual act (IN_ACT_2) or their disjunction (IN_ACT_3) by
  definition: those are candidate determinations of it. -/
  InAct : B → R → Prop
  /-- `MoreIn r x y`: `x` is more `r` than `y` (*magis*), more good, more true,
  more noble, more hot (DEF-MORE-IN, MORE_1). Only the comparative is
  primitive: no irreflexivity, transitivity, totality or measure. -/
  MoreIn : R → B → B → Prop

/-- MORE_2, the represented-degree comparative: `x` is more `r` than `y` when
the represented degree of `x` in `r` strictly exceeds that of `y`, for a degree
assignment `deg : R → B → D` in a Mathlib `Preorder` (DEF-PER-RESPECT-DEGREE-FAMILY).
It is the strict preimage order `(deg r) ⁻¹'o (· > ·)`; written out so that the
direction is visible. A sibling of the primitive comparative, not its
definition: identifying the two would conceal the open calibration bridges. -/
def DegreeComparative {B R D : Type} [Preorder D] (deg : R → B → D)
    (r : R) (x y : B) : Prop :=
  deg r y < deg r x

/-! ## The two comparatives differ -/

/-- A represented-degree comparative is irreflexive in every respect. -/
theorem degreeComparative_irrefl {B R D : Type} [Preorder D] (deg : R → B → D)
    (r : R) (x : B) : ¬ DegreeComparative deg r x x :=
  lt_irrefl _

/-- A represented-degree comparative is transitive in every respect. -/
theorem degreeComparative_trans {B R D : Type} [Preorder D] (deg : R → B → D)
    (r : R) {x y z : B} (hxy : DegreeComparative deg r x y)
    (hyz : DegreeComparative deg r y z) : DegreeComparative deg r x z :=
  lt_trans hyz hxy

/-- The primitive comparative is not constrained to be irreflexive: on a
one-being, one-respect carrier the comparative that holds everywhere is a value
of the field, and no represented degree yields it. So MORE_1 and MORE_2 are not
the same relation by their formal types; any passage between them is a bridge
premise. -/
theorem primitive_not_degreeComparative :
    ∃ MoreIn : Unit → Unit → Unit → Prop, MoreIn () () () ∧
      ∀ (D : Type) (_ : Preorder D) (deg : Unit → Unit → D),
        ¬ ∀ r x y, MoreIn r x y ↔ DegreeComparative deg r x y :=
  ⟨fun _ _ _ => True, trivial, fun _ _ deg h =>
    degreeComparative_irrefl deg () () ((h () () ()).mp trivial)⟩

/-! ## Adapters: existing cluster statements over one frame -/

variable {W B T R : Type} (F : GradesFrame W B T R)

/-- Grades by approach to a maximum (ST I q.2 a.3), over the frame. -/
def GradesByApproachToAMaximum : Prop :=
  GradesByApproachToAMaximumReading F.InAct F.MoreIn

theorem gradesByApproachToAMaximum_iff :
    GradesByApproachToAMaximum F ↔
      ∀ r, (∃ x y, F.MoreIn r x y) → ∃ m, F.InAct m r ∧ ∀ y, ¬ F.MoreIn r y m :=
  Iff.rfl

/-- The maximum in a genus causes all in the genus, over the frame. -/
def MaximumInGenusCausesAllInGenus : Prop :=
  MaximumInGenusCausesAllInGenusReading F.InAct F.MoreIn F.CausesIn

theorem maximumInGenusCausesAllInGenus_iff :
    MaximumInGenusCausesAllInGenus F ↔
      ∀ r m, (F.InAct m r ∧ ∀ y, ¬ F.MoreIn r y m) →
        ∀ x, x ≠ m → F.InAct x r → F.CausesIn m x r :=
  Iff.rfl

/-- What is maximally true is maximally being, over the frame, at a supplied
respect of truth `verum`. -/
def MostTrueIsMostBeing (verum : R) : Prop :=
  MostTrueIsMostBeingReading F.InAct F.MoreIn verum F.esse

theorem mostTrueIsMostBeing_iff (verum : R) :
    MostTrueIsMostBeing F verum ↔
      ∀ m, IsMaximumIn F.InAct F.MoreIn verum m → IsMaximumIn F.InAct F.MoreIn F.esse m :=
  Iff.rfl

/-- Nothing has actuality except insofar as it is (q.4 a.1 ad 3), over the frame. -/
def ActualityOnlyInsofarAsBeing : Prop :=
  ActualityOnlyInsofarAsBeingReading F.InAct F.esse

theorem actualityOnlyInsofarAsBeing_iff :
    ActualityOnlyInsofarAsBeing F ↔ ∀ x r, F.InAct x r → F.InAct x F.esse :=
  Iff.rfl

/-- The perfections of an effect preexist in its cause (q.4 a.2), over the frame. -/
def PerfectionsOfEffectPreexistInCause : Prop :=
  PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse

theorem perfectionsOfEffectPreexistInCause_iff :
    PerfectionsOfEffectPreexistInCause F ↔
      ∀ c x r, F.CausesIn c x F.esse → F.InAct x r → F.InAct c r :=
  Iff.rfl

/-- The cause of a thing's being causes each of its perfections, over the frame. -/
def CauseOfBeingCausesEveryPerfection : Prop :=
  TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection F.InAct F.CausesIn F.esse

theorem causeOfBeingCausesEveryPerfection_iff :
    CauseOfBeingCausesEveryPerfection F ↔
      ∀ c x r, F.CausesIn c x F.esse → F.InAct x r → F.CausesIn c x r :=
  Iff.rfl

/-- The universal-cause transfer premise, over the frame. -/
def UniversalCauseTransfersPerfections : Prop :=
  TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections F.InAct F.CausesIn F.esse

/-- The residual transfer premise, over the frame. -/
def ResidualPerfectionTransfer : Prop :=
  TruthCore.Case.Catholicism.ResidualPerfectionTransfer F.InAct F.CausesIn F.esse

/-- Composition through the shared symbols: over one frame, the universal and
the residual transfer premises give the cause-of-being transfer. Over separate
binders (the situation `truth discover` met before the parameter tags) the
same composition cannot even be stated. This is a check of the adapters, not a
new corpus result; the premises remain OPEN. -/
theorem causeOfBeingCausesEveryPerfection_of_transfers
    (hU : UniversalCauseTransfersPerfections F) (hR : ResidualPerfectionTransfer F) :
    CauseOfBeingCausesEveryPerfection F := by
  intro c x r hc hx
  by_cases hall : CausesAllInGenus F.InAct F.CausesIn F.esse c
  · by_cases hxc : x = c
    · subst hxc
      exact hR.2 x r hc hx
    · exact hU c hall x r hxc hc hx
  · exact hR.1 c hall x r hc hx

end TruthCore.Causality.Grades
