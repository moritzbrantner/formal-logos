module

public import TruthCore.Causality.CartesianAdequacy
public import TruthCore.Case.Catholicism.CausalPerfectionTransfer
public import TruthCore.Causality.CausalMapsBatch1
public import TruthCore.Case.Catholicism.StageTwo

/-!
# Preexistence at the universal source

Analyst formulations, attribution deferred. This module serves the warrant
evaluation of q.4 a.2 preexistence `64498e7e` (`PerfectionsOfEffectPreexistInCauseReading`:
every perfection of a thing whose being a cause causes is in that cause, one
`InAct` on both sides). Every derivation of that premise in the corpus uses the
unrestricted transfer `f8ba2429` (the cause of a thing's being causes each of its
perfections), whose nonuniversal part `10cd24ed` has no positive warrant on file.

The consumers of `64498e7e` on the God routes apply it only with a universal
source of being as the cause (a maximum that causes the being of every other
being, the first mover causing all, or GOD_4 so characterized). This module
states the restriction to such a source and derives it from the universal-scope
transfer `b26c10a0` and possession restricted to universal sources, with no
nonuniversal transfer.

Everything is over the shared `GradesFrame`: `F.InAct` is IN_ACT_4 (mode of
possession left open), `F.CausesIn` is CAUSE_2, `F.esse` is being.
`CausesAllInGenus F.InAct F.CausesIn F.esse c` (DEF-UNIVERSAL-ESSE-CAUSE-SCOPE)
says that `c` causes the being of every other being that has being.

The `Control` namespace gives one finite interpretation of an impersonal
universal source: on the inclusive reading of act (formal or virtual) the
universal-source premises and q.4 a.2 preexistence all hold, while the source
lacks life formally. -/

@[expose] public section

namespace TruthCore.Causality.UniversalPreexistence

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.TermSenseForks (ActFrame)
open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus)

variable {W B T R : Type}

/-- Preexistence at a universal source: if `c` causes the being of every other
being that has being, then every perfection of any other thing whose being `c`
causes is in `c` (in the frame's mode-open act). It is q.4 a.2 preexistence
restricted to universal causes of being and to distinct effects. -/
def UniversalSourcePreexistence (F : GradesFrame W B T R) : Prop :=
  ∀ c, CausesAllInGenus F.InAct F.CausesIn F.esse c →
    ∀ x r, x ≠ c → F.CausesIn c x F.esse → F.InAct x r → F.InAct c r

/-- Possession at a universal source: a universal cause of being has every
perfection it causes in another thing whose being it causes. It is the
cause-of-being possession `d0fc96b7` restricted to universal causes and to
distinct effects. -/
def UniversalSourceHasWhatItGives (F : GradesFrame W B T R) : Prop :=
  ∀ c, CausesAllInGenus F.InAct F.CausesIn F.esse c →
    ∀ x r, x ≠ c → F.CausesIn c x F.esse → F.CausesIn c x r → F.InAct c r

/-! ## An impersonal universal source -/

namespace Control

/-- Three beings: `0` the source, `1` a living effect, `2` a nonliving effect. -/
abbrev Being := Fin 3

/-- Two respects: `false` being, `true` life. -/
abbrev Respect := Bool

/-- Formal possession: everything has being formally; only the living effect
has life formally. -/
def formal (b : Being) (r : Respect) : Prop := r = false ∨ (b = 1 ∧ r = true)

/-- Virtual possession: the source has life virtually, as a power to produce it. -/
def virtual (b : Being) (r : Respect) : Prop := b = 0 ∧ r = true

/-- Inclusive act: formal or virtual. -/
def inclusive (b : Being) (r : Respect) : Prop := formal b r ∨ virtual b r

/-- The source causes the being, and every formally had perfection, of each
other being; nothing else causes anything. -/
def causes (c x : Being) (r : Respect) : Prop := c = 0 ∧ x ≠ 0 ∧ formal x r

/-- No comparative is used. -/
def more (_ : Respect) (_ _ : Being) : Prop := False

def act : ActFrame Being Respect where
  InActFormally := formal
  InActVirtually := virtual
  InPotency := fun _ _ => False
  MovedIn := fun _ _ => False
  MovesIn := fun _ _ _ => False

def grades : GradesFrame Unit Being Unit Respect :=
  TruthCore.Causality.CartesianAdequacy.gradesOf inclusive more causes false

/-- Statements about this interpretation only. With inclusive act as the frame's
act: the source is a universal cause of being; universal-scope transfer
`b26c10a0`, universal-source possession, universal-source preexistence, q.4 a.2
preexistence `64498e7e`, unrestricted transfer `f8ba2429` and "nothing has
actuality except insofar as it is" all hold; the source has life inclusively, and it is perfect in the inclusive sense of
`GodIsPerfect` when it alone is named; yet the source does not have life
formally. -/
def Controls : Prop :=
  CausesAllInGenus grades.InAct grades.CausesIn grades.esse 0 ∧
  TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections
    grades.InAct grades.CausesIn grades.esse ∧
  UniversalSourceHasWhatItGives grades ∧
  UniversalSourcePreexistence grades ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
    grades.InAct grades.CausesIn grades.esse ∧
  TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection
    grades.InAct grades.CausesIn grades.esse ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading
    grades.InAct grades.esse ∧
  grades.InAct 0 true ∧
  TruthCore.Case.Catholicism.GodIsPerfect (fun b => b = 0) grades.InAct ∧
  ¬ act.InActFormally 0 true

end Control

end TruthCore.Causality.UniversalPreexistence
