module

public import TruthCore.Causality.Frame
public import TruthCore.Causality.EsseCausePriority
public import TruthCore.Causality.NecessaryFirstBeing
public import TruthCore.Causality.ReflexiveDependenceScope
public import TruthCore.Causality.ExistenceActuality
public import TruthCore.Causality.NecessaryBeingInAct
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.FirstMoverAttributes
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
public import TruthCore.Latin.Aquinas.InMetaphysicam.BookIX
public import TruthCore.Logic.ExcludedMiddle

/-!
# Does the First Way's first mover exist necessarily? (owner lead 2026-11-22)

Analyst formulations, attribution deferred (logic first). The question is
whether the SAME individual that the *prima via* delivers, a first mover moved
by none (`IsFirstUnmovedMover`, already shown pure act by the existing
`FirstUnmovedMoverIsPureAct` derivations), exists at every world accessible
from the reading world `w` (`NecessaryAt`, NECESSARY_2 box-existence), without
first assuming it necessary or identifying it with an independently derived
necessary root.

Everything is stated over one shared `CausalityFrame` (#1784): its
world-relative existence `F.history.ontic` carries the modality, its
`F.MovesIn` is the *prima via*'s moving (CAUSE_1), its `F.CausesIn … F.esse`
is causing being (CAUSE_2 at esse) and its `F.PriorSimply` is SIMPLY_PRIOR_1.
`MovedIn`, `InPotency` (POTENCY_1), `InAct`, concreteness and the selected
grounding relation are not frame fields and stay parameters. The case's
motion vocabulary is not world-indexed; it is read at `w`.

Four conditional routes to the same witness, each with its modal bridge stated
as an explicit OPEN premise:

* **Route A (causal, esse-cause):** every being contingent at `w` has a
  distinct cause of its esse (`ContingentHasDistinctEsseCause`, B2); a distinct
  cause of esse is simply prior (existing `DistinctEsseCausePriority`, B3); the
  first mover is first in being (existing `FirstUnmovedMoverIsFirstBeing`, B1).
  So the first mover is not contingent; it exists at `w`
  (`MoversExistAt`, B0), so with excluded middle it is necessary. Pure act is
  carried for the same witness, not used for necessity.
* **Route A (grounding):** the same with the existing selected-grounding
  premises (`EveryContingentGroundedAt`, `ActualGroundingIsSimplePriority`) and
  irreflexive actual grounding in place of B2 and B3. It also gives actual
  rootness, so the First Way's mover itself witnesses the existing endpoint
  `NecessaryActualFirstPureActAt` without any identification bridge B7.
* **Route C (essence–esse):** whatever is contingent at `w` has esse distinct
  from essence (`ContingentHasDistinctEsse`, the contrapositive form of B6);
  the existing simplicity reading gives the first mover esse not distinct from
  essence. B6 also derives B2 through the q.3 a.4 reading
  `DistinctEsseRequiresExternalCauseReading`, so routes A and C share B6 when
  B2 is supported that way.
* **Route B (potency):** whatever is contingent at `w` is in POTENCY_1 in some
  respect (`PossibleNonexistenceIsPotency`, B4). Pure act then excludes
  contingency directly. B4 is the converse of both existing potency/modality
  bridges (`PotencyIsOfContradictionReading`, `CanFailToBeIsPossiblyNot`), which
  therefore do not supply it (`Model.Laws`, `Model.bruteFirst`). On the
  adopted POTENCY_1, B4 concerns potency in the subject only
  (DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER, MUTABLE_1).
* **Route A ∨ B (pure act and firstness together):** whatever is contingent at
  `w` has either a potency or a distinct cause of its esse
  (`ContingentHasPotencyOrEsseCause`), the weakest of the three bridges: each of
  B2 and B4 implies it. Pure act excludes the first disjunct, firstness and B3
  the second. This is the only route on which pure actuality does work toward
  necessity together with the causal premises.

Models are finite typed interpretations (logical boundaries), not claims of
metaphysical possibility.
-/

@[expose] public section

namespace TruthCore.Causality.FirstMoverNecessity

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct IsFirstBeing)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover)

variable {W B T R : Type}

/-! ## Shared profiles built from one frame -/

/-- The selected-grounding profile on the frame's own world-relative existence.
`concrete` and `grounds` are not frame fields. -/
def groundProfile (F : CausalityFrame W B T R) (concrete : B → Prop)
    (grounds : W → B → B → Prop) : Profile W B :=
  ⟨F.history.ontic, concrete, grounds⟩

/-- The ST I q.3 a.4 profile on the frame's `CausesIn` and `esse`. `InAct`, the
represented essence and esse, and the essential-principles predicate are
parameters. -/
def esseProfile {P : Type} (F : CausalityFrame W B T R) (InAct : B → R → Prop)
    (essenceOf esseOf : B → P) (suffice : B → Prop) :
    TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R :=
  ⟨InAct, F.CausesIn, essenceOf, esseOf, suffice, F.esse⟩

/-! ## Open bridges (analyst formulations, attribution deferred) -/

/-- B0, OPEN interface: whatever moves something exists at the reading world
`w`. The motion vocabulary is read at `w`; a mover exercising its moving there
exists there. It says nothing about any other world. -/
def MoversExistAt (F : CausalityFrame W B T R) (w : W) : Prop :=
  ∀ y x r, F.MovesIn y x r → F.history.ontic.ExistsAt w y

/-- B0', OPEN interface: whatever moves something is concrete in the
selected-grounding profile. Needed only by the grounding route. -/
def MoversConcrete (F : CausalityFrame W B T R) (concrete : B → Prop) : Prop :=
  ∀ y x r, F.MovesIn y x r → concrete y

/-- B2, OPEN: every being contingent at `w` (existing at `w` and absent at some
accessible world) has a distinct cause of its esse (CAUSE_2 at esse). The cause
is not required to exist at `w`, to be concrete, or to be efficient; that is the
weakest form the causal route uses. -/
def ContingentHasDistinctEsseCause (F : CausalityFrame W B T R) (w : W) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x → ∃ c, c ≠ x ∧ F.CausesIn c x F.esse

/-- B6 in contrapositive form, OPEN modal bridge: whatever is contingent at `w`
has a represented esse distinct from its represented essence. With excluded
middle it is equivalent to: whatever exists at `w` with esse not distinct from
essence exists at every world accessible from `w` (`Model.Laws`). It does not
follow from essence–esse identity alone (`Model.bruteFirst`). -/
def ContingentHasDistinctEsse {P : Type} (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x → esseOf x ≠ essenceOf x

/-- The B6 form: whatever exists at `w` with esse not distinct from essence
exists at every world accessible from `w`. Used only in `Model.Laws`. -/
def EsseIdentityGivesNecessity {P : Type} (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) : Prop :=
  ∀ x, F.history.ontic.ExistsAt w x → ¬ esseOf x ≠ essenceOf x →
    NecessaryAt F.history.ontic w x

/-- B4, OPEN and sense-sensitive: whatever is contingent at `w` is in POTENCY_1
in some respect. On the adopted POTENCY_1 (a capacity of the bearer itself),
this says that possible nonexistence is grounded in an intrinsic potency of the
bearer, not merely in the power of another not to conserve it. -/
def PossibleNonexistenceIsPotency (F : CausalityFrame W B T R)
    (InPotency : B → R → Prop) (w : W) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x → ∃ r, InPotency x r

/-- B2 ∨ B4, OPEN: whatever is contingent at `w` is either in POTENCY_1 in some
respect (possible non-being through a potency in the subject, MUTABLE_1) or has
a distinct cause of its esse (the channel of possible non-being through
another's power over its esse, MUTABLE_2, read as being caused in esse by
another). Each of B2 and B4 implies it (`Model.Laws`); it is the weakest of the
three that the pure-act-and-firstness route uses. -/
def ContingentHasPotencyOrEsseCause (F : CausalityFrame W B T R)
    (InPotency : B → R → Prop) (w : W) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    (∃ r, InPotency x r) ∨ ∃ c, c ≠ x ∧ F.CausesIn c x F.esse

/-- B4a, decomposition of B4, OPEN: whatever is contingent at `w` can fail to be
in substance (`CanFailToBe … esse`). The converse direction of the existing
`CanFailToBeIsPossiblyNot`. Used only in `Model.Laws`. -/
def ContingentCanFailToBe (F : CausalityFrame W B T R)
    (CanFailToBe : B → R → Prop) (w : W) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x → CanFailToBe x F.esse

/-- B4b, decomposition of B4, OPEN: whatever can fail to be in substance is in
POTENCY_1 as to esse. The converse, at esse, of the existing
`PotencyIsOfContradictionReading`. Used only in `Model.Laws`. -/
def CanFailToBeIsPotencyAtEsse (F : CausalityFrame W B T R)
    (InPotency CanFailToBe : B → R → Prop) : Prop :=
  ∀ x, CanFailToBe x F.esse → InPotency x F.esse

/-! ## Same-witness endpoints -/

/-- ONE first mover moved by none is pure act, exists at `w` and exists at
every world accessible from `w`. No firstness, uniqueness, root status or God
is asserted. -/
def FirstMoverNecessaryPureActAt (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (w : W) : Prop :=
  ∃ f, IsFirstUnmovedMover MovedIn F.MovesIn f ∧ PureAct InPotency f ∧
    F.history.ontic.ExistsAt w f ∧ NecessaryAt F.history.ontic w f

/-- ONE first mover moved by none is an actual root of the selected grounding at
`w`, exists at every accessible world, is a first being in SIMPLY_PRIOR_1 and is
pure act: the existing `NecessaryActualFirstPureActAt` body together with being
a first mover. No uniqueness or God is asserted. -/
def FirstMoverNecessaryFirstRootAt (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W) : Prop :=
  ∃ f, IsFirstUnmovedMover MovedIn F.MovesIn f ∧
    ActualRoot (groundProfile F concrete grounds) w f ∧
    NecessaryAt F.history.ontic w f ∧ IsFirstBeing F.PriorSimply f ∧
    PureAct InPotency f

/-! ## Laws and finite models -/

namespace Model

open TruthCore.Causality.EsseCausePriority (DistinctEsseCausePriority)
open TruthCore.Causality.Round2Grounding (ActualGroundingIsSimplePriority)
open TruthCore.Causality.ReflexiveDependenceScope (ActualGroundingIrreflexive)
open TruthCore.Causality.NecessaryFirstBeing (NecessaryActualFirstPureActAt)
open TruthCore.Causality.NecessaryBeingInAct (CanFailToBeIsPossiblyNot)
open TruthCore.Causality.NecessaryConcreteRouteBridge (modalPossible modalIsAt)
open TruthCore.Latin.Aquinas.InMetaphysicam (PotencyIsOfContradictionReading)
open TruthCore.Latin.Aquinas.SummaTheologiae (FirstUnmovedMoverIsSimpleReading)
open TruthCore.Case.Catholicism (ThereIsAFirstUnmovedMover FirstUnmovedMoverIsFirstBeing
  FirstUnmovedMoverIsPureAct)

/-- Finite frames: worlds and beings `Bool`, one moment and one respect (`()`,
which is also `esse`), universal access. Being `true` is the mover `f`, being
`false` the moved thing `x`; world `true` is the reading world. -/
def mk (ex : Bool → Bool → Prop) (causes : Bool → Bool → Unit → Prop)
    (prior : Bool → Bool → Prop) : CausalityFrame Bool Bool Unit Unit where
  history := ⟨⟨⟨fun _ _ => True⟩, ex, fun _ _ _ => False⟩, fun _ _ _ => False, ()⟩
  GivesAt := fun _ _ _ _ => False
  CausesIn := causes
  MovesIn := fun y x _ => y = true ∧ x = false
  DependsForBeing := fun _ _ => False
  PriorSimply := prior
  esse := ()

/-- Only `x` is moved. -/
def movedIn (x : Bool) (_ : Unit) : Prop := x = false

/-- No potency anywhere. -/
def noPotency (_ : Bool) (_ : Unit) : Prop := False

/-- `f` is in potency. -/
def fPotency (x : Bool) (_ : Unit) : Prop := x = true

/-- `x` is in potency. -/
def xPotency (x : Bool) (_ : Unit) : Prop := x = false

/-- `f` exists at the reading world only; `x` at both worlds. -/
def fContingent (v x : Bool) : Prop := x = false ∨ v = true

/-- Both exist at both worlds. -/
def allNecessary (_ _ : Bool) : Prop := True

/-- `f` exists nowhere; `x` everywhere. -/
def fAbsent (_ x : Bool) : Prop := x = false

/-- `x` causes `f`'s esse. -/
def xCausesF (c y : Bool) (_ : Unit) : Prop := c = false ∧ y = true

/-- `x` is simply prior to `f`. -/
def xPriorF (c y : Bool) : Prop := c = false ∧ y = true

/-- No cause, no priority. -/
def noCause (_ _ : Bool) (_ : Unit) : Prop := False
def noPrior (_ _ : Bool) : Prop := False

/-- `f` exists at both worlds, `x` at the reading world only. -/
def xContingent (v x : Bool) : Prop := x = true ∨ v = true

/-- `f` causes `x`'s esse and is simply prior to it. -/
def fCausesX (c y : Bool) (_ : Unit) : Prop := c = true ∧ y = false
def fPriorX (c y : Bool) : Prop := c = true ∧ y = false

/-- Everything concrete; nothing concrete. -/
def allConcrete (_ : Bool) : Prop := True
def noneConcrete (_ : Bool) : Prop := False

/-- Grounding relations. -/
def noGround (_ _ _ : Bool) : Prop := False
def fGroundsF (_ y x : Bool) : Prop := y = true ∧ x = true
def xGroundsF (_ y x : Bool) : Prop := y = false ∧ x = true
def fSelfPrior (c y : Bool) : Prop := c = true ∧ y = true
def fGroundsX (_ y x : Bool) : Prop := y = true ∧ x = false

/-- Essence and esse: identical (`Unit`) or distinct (`Bool`, esse `true`,
essence `false`). -/
def unitOf (_ : Bool) : Unit := ()
def esseTrue (_ : Bool) : Bool := true
def essenceFalse (_ : Bool) : Bool := false

/-- Body, matter–form and composition: none. -/
def noneHolds (_ : Bool) : Prop := False

/-- **bruteFirst** (lead models M1, M2, M4): `f` moves `x`, is moved by none, is
the first being, is pure act, has esse not distinct from essence, exists at
the reading world, and is absent at the other, accessible world; nothing
causes or grounds it. -/
def bruteFirst : CausalityFrame Bool Bool Unit Unit := mk fContingent noCause noPrior

/-- **conserved** (M3): as `bruteFirst`, but `x` (present at both worlds)
causes `f`'s esse and is simply prior to it. `f` is pure act in POTENCY_1 yet
receives its esse from another and could fail to exist. -/
def conserved : CausalityFrame Bool Bool Unit Unit := mk fContingent xCausesF xPriorF

/-- **unprioritized**: as `conserved` without the priority. -/
def unprioritized : CausalityFrame Bool Bool Unit Unit := mk fContingent xCausesF noPrior

/-- **absentMover**: `f` exists at no world. -/
def absentMover : CausalityFrame Bool Bool Unit Unit := mk fAbsent noCause noPrior

/-- **necessaryMover**: both beings exist at both worlds. -/
def necessaryMover : CausalityFrame Bool Bool Unit Unit := mk allNecessary noCause noPrior

/-- **still**: as `necessaryMover`, but nothing moves anything. -/
def still : CausalityFrame Bool Bool Unit Unit :=
  { necessaryMover with MovesIn := fun _ _ _ => False }

/-- **witness** (nonvacuity): `f` exists at both worlds; `x` exists at the
reading world only and is caused and preceded by `f`. -/
def witness : CausalityFrame Bool Bool Unit Unit := mk xContingent fCausesX fPriorX

/-- **selfGround**: `f` grounds itself and is simply prior to itself. -/
def selfGround : CausalityFrame Bool Bool Unit Unit := mk fContingent noCause fSelfPrior

/-- General laws:
1. B6 in its contrapositive form is equivalent, given excluded middle, to the
   B6 form "existence at `w` with esse not distinct from essence gives
   existence at every accessible world";
2. B4 follows from its two converse-direction halves B4a and B4b;
3. route B: with excluded middle, B4 makes every pure-act being that exists at
   `w` necessary at `w`;
4. B2 implies the disjunctive bridge B2 ∨ B4;
5. B4 implies it. -/
def Laws : Prop :=
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (essenceOf esseOf : B → P),
    TruthCore.Logic.ExcludedMiddle →
    (ContingentHasDistinctEsse F w essenceOf esseOf ↔
      EsseIdentityGivesNecessity F w essenceOf esseOf)) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W)
    (InPotency CanFailToBe : B → R → Prop),
    ContingentCanFailToBe F CanFailToBe w → CanFailToBeIsPotencyAtEsse F InPotency CanFailToBe →
      PossibleNonexistenceIsPotency F InPotency w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (InPotency : B → R → Prop),
    TruthCore.Logic.ExcludedMiddle → PossibleNonexistenceIsPotency F InPotency w →
      ∀ x, PureAct InPotency x → F.history.ontic.ExistsAt w x →
        NecessaryAt F.history.ontic w x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (InPotency : B → R → Prop),
    ContingentHasDistinctEsseCause F w → ContingentHasPotencyOrEsseCause F InPotency w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (InPotency : B → R → Prop),
    PossibleNonexistenceIsPotency F InPotency w → ContingentHasPotencyOrEsseCause F InPotency w)

/-- Models, each at the reading world `true`:
1. `bruteFirst`: the *prima via* conclusion, B0, B0', B1, pure act, B3,
   simplicity with esse not distinct from essence, act's two existing
   potency/modality bridges (`PotencyIsOfContradictionReading`,
   `CanFailToBeIsPossiblyNot` with no being able to fail to be), selected-
   grounding priority and irreflexivity all hold; B2, B4, B2 ∨ B4, B6 and
   `EveryContingentGroundedAt` fail; so do both endpoints. It is the omission
   model of B2 (route A), B6 (route C), B4 (route B), B2 ∨ B4 (route A ∨ B)
   and the grounding closure (grounding route).
2. `conserved`: everything of routes A and A ∨ B but B1 holds (B2 holds: `x`
   causes `f`'s esse); the first mover is pure act yet contingent and caused.
3. `unprioritized`: everything of routes A and A ∨ B but B3 holds.
4. `absentMover`: everything of routes A, B and C but B0 holds.
5. A model with no moving: everything of routes A, A ∨ B, B and C but the
   *prima via* conclusion.
6. `necessaryMover` with `f` in potency: everything of routes A, B and C but
   pure act holds (B4 holds because nothing is contingent).
7. `conserved` with distinct esse and essence: everything of route C but
   simplicity holds.
8. `selfGround`: everything of the grounding route but irreflexivity holds.
9. `bruteFirst` with `x` grounding `f`: everything of the grounding route but
   grounding-priority holds.
10. `bruteFirst` with nothing concrete: everything of the grounding route but
    B0' holds.
11. `witness`: every premise of routes A, A ∨ B, C and the grounding route,
    and both endpoints, hold, with B2, B3 and B6 applied nonvacuously to the
    contingent `x`; with `x` in potency instead (`xPotency`), B4 and pure act
    of the mover hold too, and so does route B's endpoint.
12. `necessaryMover` (M5, distinct roots): the grounding endpoint holds for
    `f`, and the moved thing `x ≠ f` is also an actual root, necessary, first
    in being and pure act, so `NecessaryActualFirstPureActAt` has two
    witnesses. Neither endpoint identifies the first mover with every
    necessary root. -/
def Models : Prop :=
  -- 1. bruteFirst
  (ThereIsAFirstUnmovedMover movedIn bruteFirst.MovesIn ∧
    MoversExistAt bruteFirst true ∧ MoversConcrete bruteFirst allConcrete ∧
    FirstUnmovedMoverIsFirstBeing movedIn bruteFirst.MovesIn bruteFirst.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn bruteFirst.MovesIn (PureAct noPotency) ∧
    DistinctEsseCausePriority bruteFirst.CausesIn bruteFirst.esse bruteFirst.PriorSimply ∧
    FirstUnmovedMoverIsSimpleReading movedIn bruteFirst.MovesIn noneHolds noneHolds noneHolds
      unitOf unitOf ∧
    PotencyIsOfContradictionReading noPotency noPotency ∧
    CanFailToBeIsPossiblyNot (modalPossible (groundProfile bruteFirst allConcrete noGround) true)
      (modalIsAt (groundProfile bruteFirst allConcrete noGround)) noPotency bruteFirst.esse ∧
    ActualGroundingIsSimplePriority (groundProfile bruteFirst allConcrete noGround) true
      bruteFirst.PriorSimply ∧
    ActualGroundingIrreflexive (groundProfile bruteFirst allConcrete noGround) true ∧
    ¬ ContingentHasDistinctEsseCause bruteFirst true ∧
    ¬ PossibleNonexistenceIsPotency bruteFirst noPotency true ∧
    ¬ ContingentHasPotencyOrEsseCause bruteFirst noPotency true ∧
    ¬ ContingentHasDistinctEsse bruteFirst true unitOf unitOf ∧
    ¬ EveryContingentGroundedAt (groundProfile bruteFirst allConcrete noGround) true ∧
    ¬ FirstMoverNecessaryPureActAt bruteFirst movedIn noPotency true ∧
    ¬ FirstMoverNecessaryFirstRootAt bruteFirst movedIn noPotency allConcrete noGround true) ∧
  -- 2. conserved
  (ThereIsAFirstUnmovedMover movedIn conserved.MovesIn ∧ MoversExistAt conserved true ∧
    FirstUnmovedMoverIsPureAct movedIn conserved.MovesIn (PureAct noPotency) ∧
    ContingentHasDistinctEsseCause conserved true ∧
    ContingentHasPotencyOrEsseCause conserved noPotency true ∧
    DistinctEsseCausePriority conserved.CausesIn conserved.esse conserved.PriorSimply ∧
    ¬ FirstUnmovedMoverIsFirstBeing movedIn conserved.MovesIn conserved.PriorSimply ∧
    ¬ FirstMoverNecessaryPureActAt conserved movedIn noPotency true) ∧
  -- 3. unprioritized
  (ThereIsAFirstUnmovedMover movedIn unprioritized.MovesIn ∧ MoversExistAt unprioritized true ∧
    FirstUnmovedMoverIsFirstBeing movedIn unprioritized.MovesIn unprioritized.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn unprioritized.MovesIn (PureAct noPotency) ∧
    ContingentHasDistinctEsseCause unprioritized true ∧
    ContingentHasPotencyOrEsseCause unprioritized noPotency true ∧
    ¬ DistinctEsseCausePriority unprioritized.CausesIn unprioritized.esse
      unprioritized.PriorSimply ∧
    ¬ FirstMoverNecessaryPureActAt unprioritized movedIn noPotency true) ∧
  -- 4. absentMover
  (ThereIsAFirstUnmovedMover movedIn absentMover.MovesIn ∧
    FirstUnmovedMoverIsFirstBeing movedIn absentMover.MovesIn absentMover.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn absentMover.MovesIn (PureAct noPotency) ∧
    ContingentHasDistinctEsseCause absentMover true ∧
    DistinctEsseCausePriority absentMover.CausesIn absentMover.esse absentMover.PriorSimply ∧
    PossibleNonexistenceIsPotency absentMover noPotency true ∧
    ContingentHasPotencyOrEsseCause absentMover noPotency true ∧
    ContingentHasDistinctEsse absentMover true unitOf unitOf ∧
    FirstUnmovedMoverIsSimpleReading movedIn absentMover.MovesIn noneHolds noneHolds noneHolds
      unitOf unitOf ∧
    ¬ MoversExistAt absentMover true ∧
    ¬ FirstMoverNecessaryPureActAt absentMover movedIn noPotency true) ∧
  -- 5. no moving
  (MoversExistAt still true ∧ MoversConcrete still allConcrete ∧
    FirstUnmovedMoverIsFirstBeing movedIn still.MovesIn still.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn still.MovesIn (PureAct noPotency) ∧
    ContingentHasDistinctEsseCause still true ∧
    DistinctEsseCausePriority still.CausesIn still.esse still.PriorSimply ∧
    PossibleNonexistenceIsPotency still noPotency true ∧
    ContingentHasPotencyOrEsseCause still noPotency true ∧
    ContingentHasDistinctEsse still true unitOf unitOf ∧
    FirstUnmovedMoverIsSimpleReading movedIn still.MovesIn noneHolds noneHolds noneHolds
      unitOf unitOf ∧
    ¬ ThereIsAFirstUnmovedMover movedIn still.MovesIn ∧
    ¬ FirstMoverNecessaryPureActAt still movedIn noPotency true) ∧
  -- 6. necessaryMover with potency
  (ThereIsAFirstUnmovedMover movedIn necessaryMover.MovesIn ∧
    MoversExistAt necessaryMover true ∧
    FirstUnmovedMoverIsFirstBeing movedIn necessaryMover.MovesIn necessaryMover.PriorSimply ∧
    ContingentHasDistinctEsseCause necessaryMover true ∧
    DistinctEsseCausePriority necessaryMover.CausesIn necessaryMover.esse
      necessaryMover.PriorSimply ∧
    PossibleNonexistenceIsPotency necessaryMover fPotency true ∧
    ContingentHasPotencyOrEsseCause necessaryMover fPotency true ∧
    ContingentHasDistinctEsse necessaryMover true unitOf unitOf ∧
    FirstUnmovedMoverIsSimpleReading movedIn necessaryMover.MovesIn noneHolds noneHolds
      noneHolds unitOf unitOf ∧
    ¬ FirstUnmovedMoverIsPureAct movedIn necessaryMover.MovesIn (PureAct fPotency) ∧
    ¬ FirstMoverNecessaryPureActAt necessaryMover movedIn fPotency true) ∧
  -- 7. conserved with distinct esse and essence
  (ThereIsAFirstUnmovedMover movedIn conserved.MovesIn ∧ MoversExistAt conserved true ∧
    FirstUnmovedMoverIsPureAct movedIn conserved.MovesIn (PureAct noPotency) ∧
    ContingentHasDistinctEsse conserved true essenceFalse esseTrue ∧
    ¬ FirstUnmovedMoverIsSimpleReading movedIn conserved.MovesIn noneHolds noneHolds noneHolds
      essenceFalse esseTrue ∧
    ¬ FirstMoverNecessaryPureActAt conserved movedIn noPotency true) ∧
  -- 8. selfGround
  (ThereIsAFirstUnmovedMover movedIn selfGround.MovesIn ∧ MoversExistAt selfGround true ∧
    MoversConcrete selfGround allConcrete ∧
    FirstUnmovedMoverIsFirstBeing movedIn selfGround.MovesIn selfGround.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn selfGround.MovesIn (PureAct noPotency) ∧
    EveryContingentGroundedAt (groundProfile selfGround allConcrete fGroundsF) true ∧
    ActualGroundingIsSimplePriority (groundProfile selfGround allConcrete fGroundsF) true
      selfGround.PriorSimply ∧
    ¬ ActualGroundingIrreflexive (groundProfile selfGround allConcrete fGroundsF) true ∧
    ¬ FirstMoverNecessaryFirstRootAt selfGround movedIn noPotency allConcrete fGroundsF true) ∧
  -- 9. bruteFirst with x grounding f
  (EveryContingentGroundedAt (groundProfile bruteFirst allConcrete xGroundsF) true ∧
    ActualGroundingIrreflexive (groundProfile bruteFirst allConcrete xGroundsF) true ∧
    ¬ ActualGroundingIsSimplePriority (groundProfile bruteFirst allConcrete xGroundsF) true
      bruteFirst.PriorSimply ∧
    ¬ FirstMoverNecessaryFirstRootAt bruteFirst movedIn noPotency allConcrete xGroundsF true) ∧
  -- 10. bruteFirst with nothing concrete
  (EveryContingentGroundedAt (groundProfile bruteFirst noneConcrete noGround) true ∧
    ActualGroundingIsSimplePriority (groundProfile bruteFirst noneConcrete noGround) true
      bruteFirst.PriorSimply ∧
    ActualGroundingIrreflexive (groundProfile bruteFirst noneConcrete noGround) true ∧
    ¬ MoversConcrete bruteFirst noneConcrete ∧
    ¬ FirstMoverNecessaryFirstRootAt bruteFirst movedIn noPotency noneConcrete noGround true) ∧
  -- 11. witness
  (ThereIsAFirstUnmovedMover movedIn witness.MovesIn ∧ MoversExistAt witness true ∧
    MoversConcrete witness allConcrete ∧
    FirstUnmovedMoverIsFirstBeing movedIn witness.MovesIn witness.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn witness.MovesIn (PureAct noPotency) ∧
    ContingentHasDistinctEsseCause witness true ∧
    ContingentHasPotencyOrEsseCause witness noPotency true ∧
    DistinctEsseCausePriority witness.CausesIn witness.esse witness.PriorSimply ∧
    FirstUnmovedMoverIsSimpleReading movedIn witness.MovesIn noneHolds noneHolds noneHolds
      (fun b => b) (fun _ => true) ∧
    ContingentHasDistinctEsse witness true (fun b => b) (fun _ => true) ∧
    EveryContingentGroundedAt (groundProfile witness allConcrete fGroundsX) true ∧
    ActualGroundingIsSimplePriority (groundProfile witness allConcrete fGroundsX) true
      witness.PriorSimply ∧
    ActualGroundingIrreflexive (groundProfile witness allConcrete fGroundsX) true ∧
    (∃ x, ContingentAt witness.history.ontic true x) ∧
    FirstMoverNecessaryPureActAt witness movedIn noPotency true ∧
    FirstMoverNecessaryFirstRootAt witness movedIn noPotency allConcrete fGroundsX true ∧
    PossibleNonexistenceIsPotency witness xPotency true ∧
    FirstUnmovedMoverIsPureAct movedIn witness.MovesIn (PureAct xPotency) ∧
    FirstMoverNecessaryPureActAt witness movedIn xPotency true) ∧
  -- 12. necessaryMover, distinct roots
  (FirstMoverNecessaryFirstRootAt necessaryMover movedIn noPotency allConcrete noGround true ∧
    ActualRoot (groundProfile necessaryMover allConcrete noGround) true false ∧
    NecessaryAt necessaryMover.history.ontic true false ∧
    IsFirstBeing necessaryMover.PriorSimply false ∧ PureAct noPotency false ∧
    ¬ IsFirstUnmovedMover movedIn necessaryMover.MovesIn false ∧
    NecessaryActualFirstPureActAt (groundProfile necessaryMover allConcrete noGround) true
      necessaryMover.PriorSimply noPotency)

/-- The laws and the models. -/
def Controls : Prop := Laws ∧ Models

end Model

end TruthCore.Causality.FirstMoverNecessity
