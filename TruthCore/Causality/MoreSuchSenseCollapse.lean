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

/-! ## Two determinations of the comparative

`G.MoreIn` (MORE_1) is primitive. The two declarations below are candidate
determinations of it for the "more such" premise; neither is its definition, and
no statement identifies either with it. -/

/-- MORE_3, the ordinary comparative: `x` is more `r` than `y` when both have `r`
formally and `x`'s measured degree of `r` is strictly higher, as one body is
hotter than another by temperature. It is the represented-degree comparative
(MORE_2) restricted to formal possessors of `r`; the degree `deg` is a supplied
measure with a strict order `<` (a preorder's, for MORE_2). -/
def OrdinaryComparative {D : Type} [instD : LT D] (A : ActFrame B R) (deg : R → B → D)
    (r : R) (x y : B) : Prop :=
  A.InActFormally x r ∧ A.InActFormally y r ∧ deg r y < deg r x

/-- MORE_4, the eminent comparative: `x` is more `r` than `y` by eminence when `x`
has `r` virtually (IN_ACT_2) and surpasses `y` in the mode of having `r`.
`Surpasses r x y` is an explicitly **primitive** parameter: "`x`'s way of having
`r` is higher than `y`'s". No record specifies it at arbitrary `r`; its only
recorded instance is the order by approach to a primary at being
(DISAMB-ORDER-OF-BEING). It is declared here so that the ordinary and eminent
readings of "more such" are distinct types; it settles nothing about eminence. -/
def EminentComparative (A : ActFrame B R) (Surpasses : R → B → B → Prop)
    (r : R) (x y : B) : Prop :=
  A.InActVirtually x r ∧ Surpasses r x y

/-- "More such" read with the ordinary comparative (the MORE_3 reading of
d5a94eb1): every distinct cause of `x`'s being `r` is more `r` than `x` by
measured degree, both having `r` formally. -/
def OrdinaryMoreSuch {D : Type} [instD : LT D] (G : GradesFrame W B T R) (A : ActFrame B R)
    (deg : R → B → D) : Prop :=
  CauseOfQualityInAnotherIsMoreSuchReading G.CausesIn (OrdinaryComparative A deg)

/-- The exact negation of `OrdinaryMoreSuch`: some `c`, distinct from `x`, causes
`x`'s being `r` and is not more `r` than `x` on the ordinary comparative. -/
def OrdinaryComparativeGap {D : Type} [instD : LT D] (G : GradesFrame W B T R)
    (A : ActFrame B R) (deg : R → B → D) : Prop :=
  ∃ c x r, c ≠ x ∧ G.CausesIn c x r ∧ ¬ OrdinaryComparative A deg r c x

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

/-! ### Respects fixed by degree

Beings as above (`false` the coil, `true` the workpiece). Respects: `0` being,
`1` having some heat, `2` having heat at or above the workpiece's degree. The
coil causes the workpiece's respects `1` and `2`. Degrees of heat, read as
temperatures in °C: coil 40, workpiece 1000. -/

/-- The coil causes the workpiece's heat in both heat respects. -/
def causes3 (c x : Bool) (r : Fin 3) : Prop := c = false ∧ x = true ∧ r ≠ 0

/-- Both have being and some heat formally; only the workpiece has heat at its
own degree formally. -/
def formal3 (b : Bool) (r : Fin 3) : Prop := r ≠ 2 ∨ b = true

/-- The coil has both heat respects virtually. -/
def virtual3 (b : Bool) (r : Fin 3) : Prop := b = false ∧ r ≠ 0

/-- Measured degree of heat (respect `1`): coil 40, workpiece 1000. -/
def temp (r : Fin 3) (b : Bool) : Nat := if r = 1 then (if b then 1000 else 40) else 0

/-- The eminent surpassing relation, stipulated: the coil surpasses the
workpiece in both heat respects. -/
def surpasses (r : Fin 3) (x y : Bool) : Prop := r ≠ 0 ∧ x = false ∧ y = true

/-- The coil also moves the workpiece in both heat respects: it reduces the
workpiece from cold to hot. -/
def act3 : ActFrame Bool (Fin 3) where
  InActFormally := formal3
  InActVirtually := virtual3
  InPotency := fun _ _ => False
  MovedIn := fun _ _ => False
  MovesIn := causes3

def grades3 : GradesFrame Unit Bool Unit (Fin 3) :=
  TruthCore.Causality.CartesianAdequacy.gradesOf act3.InActFormallyOrVirtually
    (OrdinaryComparative (instD := instLTNat) act3 temp) causes3 0

/-- Statements about this interpretation only. The coil has some heat formally
(respect `1`) but not heat at the workpiece's degree (respect `2`); so the formal
possession gap is witnessed only at the degree-indexed respect. On the ordinary
comparative the coil is not hotter: the ordinary-comparative gap holds and the
ordinary reading of "more such" fails. Read with the stipulated eminent
comparative, "more such" holds. The coil moves the workpiece in the heat
respects: "nothing moves except as in act" fails read with formal act and holds
read with inclusive act. -/
def OrdinaryControls : Prop :=
  act3.InActFormally false 1 ∧
  ¬ act3.InActFormally false 2 ∧
  FormalPossessionGap grades3 act3 ∧
  (∀ c x, c ≠ x → grades3.CausesIn c x 1 → act3.InActFormally c 1) ∧
  OrdinaryComparativeGap (instD := instLTNat) grades3 act3 temp ∧
  ¬ OrdinaryMoreSuch (instD := instLTNat) grades3 act3 temp ∧
  CauseOfQualityInAnotherIsMoreSuchReading grades3.CausesIn
    (EminentComparative act3 surpasses) ∧
  ¬ TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading act3.MovesIn
      act3.InActFormally ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading act3.MovesIn
      act3.InActFormallyOrVirtually

end Control

end TruthCore.Causality.MoreSuchSenseCollapse
