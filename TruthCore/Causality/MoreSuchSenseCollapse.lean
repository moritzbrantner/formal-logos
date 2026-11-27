module

public import TruthCore.Causality.CartesianAdequacy
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer

/-!
# The "more such" package and the mode of possession

Analyst formulations, attribution deferred. This module serves the warrant
evaluation of the shared bottleneck premise family "nothing gives what it does
not have" (unrestricted 376d6a5a; its distinct-cause version 2c0b9bd7; the
Metaphysics alpha "more such" premise d5a94eb1 and "what is more such has the
perfection" c11369aa). It adds no new primitive relation.

Everything is stated over the shared frames: `G : GradesFrame` supplies
`G.CausesIn` (CAUSE_2) and `G.MoreIn` (MORE_1, the primitive comparative);
`A : ActFrame` supplies `A.InActFormally` (IN_ACT_1) and `A.InActVirtually`
(IN_ACT_2). The reception primitives `ReceivedIn` and `LimitedBy` are the
parameters of `CausalMapsBatch1` (DEF-PERFECTION-RECEIVED-IN,
DEF-PERFECTION-LIMITED-BY); no frame has fields for them.

The registered derivations of the case compose in a cycle:
`moreSuchOfDistinctCauseGives` (distinct-cause possession with the five-premise
reception bundle gives "more such") and `distinctCauseGivesOfMoreSuch` ("more
such" with "what is more such has the perfection" gives distinct-cause
possession). Each step is stated for one act predicate `InAct`, and the
statements leave its mode open. `MoreSuchPackageForcesFormalPossession` records
what happens when the two steps are read with different modes: possession in
any mode, fed through the comparative package with a *formal* more-such bearer,
comes back as formal possession. So the eminence clause of the possession
premise ("formally or eminently") is undone by the package unless the
comparative and its bearer premise are read in the same eminent mode.

`FormalPossessionGap` is the exact negation of the formal reading: some distinct
cause of a perfection in another does not formally have it. Its warrant is an
observation outside Lean (induction heating; docs note), not anything proved
here. The `Control` namespace gives one finite interpretation shaped like that
case and the uniform eminent reinterpretation of the same case.
-/

@[expose] public section

namespace TruthCore.Causality.MoreSuchSenseCollapse

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.TermSenseForks (ActFrame)
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (DistinctCauseHasWhatItGives)
open TruthCore.Causality.CausalMapsBatch1
  (CausedPerfectionIsReceivedInEffect ReceivedPerfectionIsLimitedByRecipient
    PerfectionLimitedOnlyThroughReception CauseHasPerfectionNotAsReceivedInEffect
    UnlimitedPossessionExceedsLimited)
open TruthCore.Latin.Aquinas.SummaTheologiae (MoreSuchHasThePerfectionReading)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

variable {W B T R : Type}

/-- Formal distinct-cause possession (IN_ACT_1 reading of 2c0b9bd7): whatever,
distinct from `x`, causes `x`'s being `r` (CAUSE_2) has `r` formally, in the same
form in which it produces it, as fire that is hot makes wood hot. -/
def FormalDistinctCausePossession (G : GradesFrame W B T R) (A : ActFrame B R) : Prop :=
  DistinctCauseHasWhatItGives G.CausesIn A.InActFormally

/-- The exact negation of the formal reading, with its original scope: some
`c`, distinct from `x`, causes `x`'s being `r` (CAUSE_2) and does not have `r`
formally. It says nothing about virtual or eminent possession. -/
def FormalPossessionGap (G : GradesFrame W B T R) (A : ActFrame B R) : Prop :=
  ∃ c x r, c ≠ x ∧ G.CausesIn c x r ∧ ¬ A.InActFormally c r

/-- The "more such" package with a formal more-such bearer forces formal
possession, for whatever single act predicate `InAct` the possession premise and
the exceeding step share: distinct-cause possession in `InAct`, the five
reception and exceeding premises of `moreSuchOfDistinctCauseGives` (the exceeding
step in `InAct`), and "what is more such has the perfection" read with formal
act together entail formal distinct-cause possession. -/
def MoreSuchPackageForcesFormalPossession (G : GradesFrame W B T R) (A : ActFrame B R)
    (InAct : B → R → Prop) (ReceivedIn LimitedBy : B → R → B → Prop) : Prop :=
  DistinctCauseHasWhatItGives G.CausesIn InAct →
  CausedPerfectionIsReceivedInEffect G.CausesIn ReceivedIn →
  ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy →
  PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy →
  CauseHasPerfectionNotAsReceivedInEffect G.CausesIn ReceivedIn →
  UnlimitedPossessionExceedsLimited InAct LimitedBy G.MoreIn →
  MoreSuchHasThePerfectionReading A.InActFormally G.MoreIn →
  FormalDistinctCausePossession G A

/-! ## A finite interpretation shaped like induction heating -/

namespace Control

/-- Beings: `false` is the source (the coil), `true` the recipient (the
workpiece). Respects: `false` is being (esse), `true` is heat. The source causes
the recipient's heat, and nothing else is caused. -/
def causes (c x r : Bool) : Prop := c = false ∧ x = true ∧ r = true

/-- Both have being formally; only the recipient is formally hot. -/
def formal (b r : Bool) : Prop := r = false ∨ (b = true ∧ r = true)

/-- The source has heat virtually: as a power to produce it, not in the same
form. -/
def virtual (b r : Bool) : Prop := b = false ∧ r = true

/-- The recipient's heat is received in the recipient. -/
def received (y r z : Bool) : Prop := y = true ∧ r = true ∧ z = true

/-- The recipient's heat is limited by the recipient, and only by reception. -/
def limited (y r z : Bool) : Prop := received y r z

/-- Formal comparative: the recipient is hotter than the source. -/
def moreFormal (r x y : Bool) : Prop := r = true ∧ x = true ∧ y = false

/-- Eminent comparative: the source, having heat as a power to produce it,
exceeds the recipient in heat by eminence. -/
def moreEminent (r x y : Bool) : Prop := r = true ∧ x = false ∧ y = true

def act : ActFrame Bool Bool where
  InActFormally := formal
  InActVirtually := virtual
  InPotency := fun _ _ => False
  MovedIn := fun _ _ => False
  MovesIn := fun _ _ _ => False

/-- The case with the formal comparative. Its frame `InAct` is the inclusive
reading; the controls below name the act predicate of each premise explicitly. -/
def formalGrades : GradesFrame Unit Bool Unit Bool :=
  TruthCore.Causality.CartesianAdequacy.gradesOf act.InActFormallyOrVirtually moreFormal
    causes false

/-- The same case with the eminent comparative. -/
def eminentGrades : GradesFrame Unit Bool Unit Bool :=
  TruthCore.Causality.CartesianAdequacy.gradesOf act.InActFormallyOrVirtually moreEminent
    causes false

/-- Statements about these two interpretations only. With the formal
comparative: the formal possession gap holds; inclusive distinct-cause possession
(formal or virtual) and the four reception premises hold; "what is more such has
the perfection" holds with formal act; the exceeding step read with inclusive act
fails, "more such" fails and formal possession fails. With the eminent
comparative on the same causes, acts and reception: inclusive possession, the
reception premises, the inclusive exceeding step, "more such" and the inclusive
more-such bearer all hold, while the formal more-such bearer fails. -/
def Controls : Prop :=
  FormalPossessionGap formalGrades act ∧
  DistinctCauseHasWhatItGives formalGrades.CausesIn act.InActFormallyOrVirtually ∧
  CausedPerfectionIsReceivedInEffect formalGrades.CausesIn received ∧
  ReceivedPerfectionIsLimitedByRecipient received limited ∧
  PerfectionLimitedOnlyThroughReception received limited ∧
  CauseHasPerfectionNotAsReceivedInEffect formalGrades.CausesIn received ∧
  MoreSuchHasThePerfectionReading act.InActFormally formalGrades.MoreIn ∧
  ¬ UnlimitedPossessionExceedsLimited act.InActFormallyOrVirtually limited
      formalGrades.MoreIn ∧
  ¬ CauseOfQualityInAnotherIsMoreSuchReading formalGrades.CausesIn formalGrades.MoreIn ∧
  ¬ FormalDistinctCausePossession formalGrades act ∧
  DistinctCauseHasWhatItGives eminentGrades.CausesIn act.InActFormallyOrVirtually ∧
  CausedPerfectionIsReceivedInEffect eminentGrades.CausesIn received ∧
  CauseHasPerfectionNotAsReceivedInEffect eminentGrades.CausesIn received ∧
  UnlimitedPossessionExceedsLimited act.InActFormallyOrVirtually limited
      eminentGrades.MoreIn ∧
  CauseOfQualityInAnotherIsMoreSuchReading eminentGrades.CausesIn eminentGrades.MoreIn ∧
  MoreSuchHasThePerfectionReading act.InActFormallyOrVirtually eminentGrades.MoreIn ∧
  ¬ MoreSuchHasThePerfectionReading act.InActFormally eminentGrades.MoreIn

end Control

end TruthCore.Causality.MoreSuchSenseCollapse
