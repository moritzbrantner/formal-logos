module

public import TruthCore.Causality.Frame
public import TruthCore.Causality.EsseCausePriority
public import TruthCore.Causality.NecessaryFirstBeing
public import TruthCore.Causality.ReflexiveDependenceScope
public import TruthCore.Causality.EsseReception
public import TruthCore.Latin.Aquinas.DeEnte.EsseReception
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency
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
* **Route B (potency):** whatever is contingent at `w` is in POTENCY_1 in at
  least one (any) respect (`PossibleNonexistenceIsPotency`, B4). Pure act then
  excludes contingency directly. With excluded middle, B4 is equivalent to
  "every pure-act being existing at `w` is necessary at `w`" (`Model.Laws`, 3),
  so this route relocates the lead's question into B4. The esse-tied
  converses of the two existing potency/modality bridges
  (`PotencyIsOfContradictionReading`, `CanFailToBeIsPossiblyNot`) give B4
  (`Model.Laws`, 2); the existing bridges themselves do not
  (`Model.bruteFirst`).
* **Route A ∨ B (pure act and firstness together):** whatever is contingent at
  `w` is in POTENCY_1 in some respect or has a distinct cause of its esse
  (`ContingentHasPotencyOrEsseCause`), the weakest of the three bridges as
  typed: each of B2 and B4 implies it. Pure act excludes the first disjunct,
  firstness and B3 the second. This is the only route on which pure actuality
  does work toward necessity together with the causal premises.

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
`w`. `MovesIn` (the frame's CAUSE_1 moving, DEF-MOTION-AS-REDUCTION) is not
world-indexed: it is read at `w`, and a mover exercising its moving there
exists there. B0 is warranted only at the world at which `MovesIn` is read; at
any other world it would itself assert that the movers exist there (at every
accessible world it would make every mover necessary). -/
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

/-- B4, OPEN: whatever is contingent at `w` is in POTENCY_1 (the adopted
potency in the subject) in at least one respect, any respect. It states no
grounding or explanatory relation and does not tie the respect to esse or to
non-being: a contingent thing that can merely become hot satisfies it. The
esse-tied version is B4a ∧ B4b (`Model.Laws`, 2), which is stronger. With
excluded middle B4 is equivalent to "every pure-act being existing at `w` is
necessary at `w`" (`Model.Laws`, 3), so the potency route relocates the lead's
question into B4 rather than answering it. -/
def PossibleNonexistenceIsPotency (F : CausalityFrame W B T R)
    (InPotency : B → R → Prop) (w : W) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x → ∃ r, InPotency x r

/-- B2 ∨ B4, OPEN: whatever is contingent at `w` is either in POTENCY_1 in at
least one (any) respect or has a distinct CAUSE_2 of its esse. Each of B2 and
B4 implies it (`Model.Laws`, 4–5), so it is the weakest of the three as typed.
It is not the q.9 a.2 pair of channels (mutable in the subject, MUTABLE_1;
mutable through another's power, MUTABLE_2 `MutableThroughAnother`): reading
it as exhausting those channels would need two unrecorded OPEN bridges,
contingency at `w` → mutable in some way (MUTABLE_3), and another's power over
a thing's esse → a distinct cause of its esse. -/
def ContingentHasPotencyOrEsseCause (F : CausalityFrame W B T R)
    (InPotency : B → R → Prop) (w : W) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    (∃ r, InPotency x r) ∨ ∃ c, c ≠ x ∧ F.CausesIn c x F.esse

/-- The lead's target restricted to `w`: every pure-act being that exists at
`w` exists at every world accessible from `w`. Used only in `Model.Laws`. -/
def PureActBeingsNecessaryAt (F : CausalityFrame W B T R) (InPotency : B → R → Prop)
    (w : W) : Prop :=
  ∀ x, PureAct InPotency x → F.history.ontic.ExistsAt w x → NecessaryAt F.history.ontic w x

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


/-! ## Reception of esse and the selected POTENCY_1 -/

/-- R1, OPEN: every actual being that can be absent at an accessible world
receives its act of being in some principle. Modal contingency by itself does
not definitionally establish reception, an external giver, or grounding. -/
def ContingentReceivesEsse {P : Type} (F : CausalityFrame W B T R)
    (w : W) (Received : B → P → Prop) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x → ∃ p, Received x p

/-- R3, OPEN: where esse *is* essence, receipt of esse can only be in that
essence. A scoped instance of the already studied own-essence reception law,
weaker than applying it to all beings, including nonidentity recipients. -/
def IdentityScopedEsseReception {P : Type}
    (essenceOf esseOf : B → P) (Received : B → P → Prop) : Prop :=
  ∀ x p, esseOf x = essenceOf x → Received x p → p = essenceOf x

/-- R2, diagnostic OPEN transfer: a contingent bearer receiving esse in a
principle is in unactualized subject POTENCY_1 at esse. De ente states only
the receiving PRINCIPLE'S receptive potency. With adopted POTENCY_1 and
actual existing-in-esse, R2 excludes all contingent actual beings; it does
not provide a viable positive argument for B4 (see ReceptionControls). -/
def ContingentReceptionIsSubjectPotency {P : Type}
    (F : CausalityFrame W B T R) (InPotency : B → R → Prop)
    (w : W) (Received : B → P → Prop) : Prop :=
  ∀ x p, ContingentAt F.history.ontic w x → Received x p → InPotency x F.esse

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

/-- Finite frames: worlds and beings `Bool`, one moment, two respects (`true`
is `esse`, `false` the respect of motion, say heat), universal access. Being
`true` is the mover `f`, being `false` the moved thing `x`; world `true` is the
reading world. `f` moves `x` in the respect of motion only. -/
def mk (ex : Bool → Bool → Prop) (causes : Bool → Bool → Bool → Prop)
    (prior : Bool → Bool → Prop) : CausalityFrame Bool Bool Unit Bool where
  history := ⟨⟨⟨fun _ _ => True⟩, ex, fun _ _ _ => False⟩, fun _ _ _ => False, ()⟩
  GivesAt := fun _ _ _ _ => False
  CausesIn := causes
  MovesIn := fun y x r => y = true ∧ x = false ∧ r = false
  DependsForBeing := fun _ _ => False
  PriorSimply := prior
  esse := true

/-- Only `x` is moved, in the respect of motion. -/
def movedIn (x r : Bool) : Prop := x = false ∧ r = false

/-- The moved thing is in POTENCY_1 in the respect in which it is moved (as
motion-as-reduction requires); nothing else is in potency. -/
def movedPotency (x r : Bool) : Prop := x = false ∧ r = false

/-- `f` is in potency in every respect, and `x` in the respect of motion. -/
def fPotency (x r : Bool) : Prop := x = true ∨ (x = false ∧ r = false)

/-- What can fail to be so: `x` in the respect of motion (it can fail to be
hot), `f` in substance (it can fail to be). -/
def canFail (x r : Bool) : Prop := (x = false ∧ r = false) ∨ (x = true ∧ r = true)

/-- `f` exists at the reading world only; `x` at both worlds. -/
def fContingent (v x : Bool) : Prop := x = false ∨ v = true

/-- Both exist at both worlds. -/
def allNecessary (_ _ : Bool) : Prop := True

/-- `f` exists nowhere; `x` everywhere. -/
def fAbsent (_ x : Bool) : Prop := x = false

/-- `x` causes `f`'s esse. -/
def xCausesF (c y r : Bool) : Prop := c = false ∧ y = true ∧ r = true

/-- `x` is simply prior to `f`. -/
def xPriorF (c y : Bool) : Prop := c = false ∧ y = true

/-- No cause, no priority. -/
def noCause (_ _ _ : Bool) : Prop := False
def noPrior (_ _ : Bool) : Prop := False

/-- `f` exists at both worlds, `x` at the reading world only. -/
def xContingent (v x : Bool) : Prop := x = true ∨ v = true

/-- `f` causes `x`'s esse and is simply prior to it. -/
def fCausesX (c y r : Bool) : Prop := c = true ∧ y = false ∧ r = true
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


/-- Receipt is in the thing's essence in the nonvacuous witness. -/
def receivedByMoved (x p : Bool) : Prop := x = false ∧ p = false
def receivedByMover (x p : Bool) : Prop := x = true ∧ p = false
def receivedNone (_ _ : Bool) : Prop := False
def receptivePotency (p act : Bool) : Prop := p = false ∧ act = true
def essenceByBeing (x : Bool) : Bool := x

/-- This free subject-potency interpretation is NOT the adopted potency in
a respect where the bearer is actually in act. -/
def subjectPotencyAtEsse (x _ : Bool) : Prop := x = false
def actAtEsse (_ r : Bool) : Prop := r = true
def canBeAny (_ _ : Bool) : Prop := True

/-- x supports f's esse exactly at the reading world: the world-relative
support relation supplements the frame's world-free CausesIn, read at w. -/
def supportsEsseAt (v c x : Bool) : Prop :=
  v = true ∧ c = false ∧ x = true

/-- **bruteFirst** (lead models M1, M2, M4): `f` moves `x`, is moved by none, is
the first being, is pure act, has esse not distinct from essence, exists at
the reading world, and is absent at the other, accessible world; nothing
causes or grounds it. -/
def bruteFirst : CausalityFrame Bool Bool Unit Bool := mk fContingent noCause noPrior

/-- **conserved** (M3): as `bruteFirst`, but `x` (present at both worlds)
causes `f`'s esse and is simply prior to it. `f` is pure act in POTENCY_1 yet
receives its esse from another and could fail to exist. -/
def conserved : CausalityFrame Bool Bool Unit Bool := mk fContingent xCausesF xPriorF

/-- **unprioritized**: as `conserved` without the priority. -/
def unprioritized : CausalityFrame Bool Bool Unit Bool := mk fContingent xCausesF noPrior

/-- **absentMover**: `f` exists at no world. -/
def absentMover : CausalityFrame Bool Bool Unit Bool := mk fAbsent noCause noPrior

/-- **necessaryMover**: both beings exist at both worlds. -/
def necessaryMover : CausalityFrame Bool Bool Unit Bool := mk allNecessary noCause noPrior

/-- **still**: as `necessaryMover`, but nothing moves anything. -/
def still : CausalityFrame Bool Bool Unit Bool :=
  { necessaryMover with MovesIn := fun _ _ _ => False }

/-- **witness** (nonvacuity): `f` exists at both worlds; `x` exists at the
reading world only and is caused and preceded by `f`. -/
def witness : CausalityFrame Bool Bool Unit Bool := mk xContingent fCausesX fPriorX

/-- **selfGround**: `f` grounds itself and is simply prior to itself. -/
def selfGround : CausalityFrame Bool Bool Unit Bool := mk fContingent noCause fSelfPrior

/-- Three beings for the distinct-roots model: the mover, the moved thing and
an idle being that neither moves nor is moved. -/
inductive Trio
  | mover
  | moved
  | idle
  deriving DecidableEq

theorem Trio.forall_iff {p : Trio → Prop} :
    (∀ t, p t) ↔ p .mover ∧ p .moved ∧ p .idle :=
  ⟨fun h => ⟨h _, h _, h _⟩, fun ⟨a, b, c⟩ t => by cases t <;> assumption⟩

theorem Trio.exists_iff {p : Trio → Prop} :
    (∃ t, p t) ↔ p .mover ∨ p .moved ∨ p .idle :=
  ⟨fun ⟨t, h⟩ => by cases t <;> simp_all, fun h => by
    rcases h with h | h | h <;> exact ⟨_, h⟩⟩

/-- **twoRoots** (M5): all three beings exist at both worlds; the mover moves
the moved thing in the respect of motion; nothing causes, grounds or is
simply prior to anything. -/
def twoRoots : CausalityFrame Bool Trio Unit Bool where
  history := ⟨⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩,
    fun _ _ _ => False, ()⟩
  GivesAt := fun _ _ _ _ => False
  CausesIn := fun _ _ _ => False
  MovesIn := fun y x r => y = .mover ∧ x = .moved ∧ r = false
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := true

/-- In `twoRoots`, only the moved thing is moved, and it is in potency in that
respect. -/
def trioMovedIn (x : Trio) (r : Bool) : Prop := x = .moved ∧ r = false
def trioPotency (x : Trio) (r : Bool) : Prop := x = .moved ∧ r = false
def trioConcrete (_ : Trio) : Prop := True
def trioNoGround (_ : Bool) (_ _ : Trio) : Prop := False

/-- General laws:
1. B6 in its contrapositive form is equivalent, given excluded middle, to the
   B6 form "existence at `w` with esse not distinct from essence gives
   existence at every accessible world";
2. B4 follows from its two converse-direction halves B4a and B4b;
3. route B relocates the question: with excluded middle, B4 is equivalent to
   the lead's target at `w`, "every pure-act being that exists at `w` is
   necessary at `w`";
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
    TruthCore.Logic.ExcludedMiddle →
      (PossibleNonexistenceIsPotency F InPotency w ↔ PureActBeingsNecessaryAt F InPotency w)) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (InPotency : B → R → Prop),
    ContingentHasDistinctEsseCause F w → ContingentHasPotencyOrEsseCause F InPotency w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (InPotency : B → R → Prop),
    PossibleNonexistenceIsPotency F InPotency w → ContingentHasPotencyOrEsseCause F InPotency w)

/-- Models, each at the reading world `true`. In every model the moved thing is
in POTENCY_1 in the respect in which it is moved (motion-as-reduction); the
first mover is pure act unless stated otherwise.
1. `bruteFirst`: the *prima via* conclusion, B0, B0', B1, pure act, B3,
   simplicity with esse not distinct from essence, the two existing
   potency/modality bridges, both nonvacuously (`x` is in potency to heat and
   can fail to be hot; `f` can fail to be in substance and possibly is not),
   B4a, selected-grounding priority and irreflexivity all hold; B4b, B2, B4,
   B2 ∨ B4, B6 and `EveryContingentGroundedAt` fail; so do both endpoints. It
   is the omission model of B2 (route A), B6 (route C), B4 (route B), B2 ∨ B4
   (route A ∨ B) and the grounding closure (grounding route).
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
11. `witness`: every premise of every route, and both endpoints, hold, with
    B2, B3, B4 and B6 applied nonvacuously to the contingent moved thing `x`
    (caused and preceded by `f`, in potency to heat, esse distinct from
    essence).
12. `twoRoots` (M5, distinct roots, three beings): the grounding endpoint holds
    for the mover, and an idle being, neither moving nor moved, is also an
    actual root, necessary, first in being and pure act, so
    `NecessaryActualFirstPureActAt` has two witnesses (the moved thing, in
    potency, is not one). Neither endpoint identifies the first mover with
    every necessary root. -/
def Models : Prop :=
  -- 1. bruteFirst
  (ThereIsAFirstUnmovedMover movedIn bruteFirst.MovesIn ∧
    MoversExistAt bruteFirst true ∧ MoversConcrete bruteFirst allConcrete ∧
    FirstUnmovedMoverIsFirstBeing movedIn bruteFirst.MovesIn bruteFirst.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn bruteFirst.MovesIn (PureAct movedPotency) ∧
    DistinctEsseCausePriority bruteFirst.CausesIn bruteFirst.esse bruteFirst.PriorSimply ∧
    FirstUnmovedMoverIsSimpleReading movedIn bruteFirst.MovesIn noneHolds noneHolds noneHolds
      unitOf unitOf ∧
    PotencyIsOfContradictionReading movedPotency canFail ∧
    CanFailToBeIsPossiblyNot (modalPossible (groundProfile bruteFirst allConcrete noGround) true)
      (modalIsAt (groundProfile bruteFirst allConcrete noGround)) canFail bruteFirst.esse ∧
    canFail false false ∧ canFail true bruteFirst.esse ∧
    ContingentCanFailToBe bruteFirst canFail true ∧
    ¬ CanFailToBeIsPotencyAtEsse bruteFirst movedPotency canFail ∧
    ActualGroundingIsSimplePriority (groundProfile bruteFirst allConcrete noGround) true
      bruteFirst.PriorSimply ∧
    ActualGroundingIrreflexive (groundProfile bruteFirst allConcrete noGround) true ∧
    ¬ ContingentHasDistinctEsseCause bruteFirst true ∧
    ¬ PossibleNonexistenceIsPotency bruteFirst movedPotency true ∧
    ¬ ContingentHasPotencyOrEsseCause bruteFirst movedPotency true ∧
    ¬ ContingentHasDistinctEsse bruteFirst true unitOf unitOf ∧
    ¬ EveryContingentGroundedAt (groundProfile bruteFirst allConcrete noGround) true ∧
    ¬ FirstMoverNecessaryPureActAt bruteFirst movedIn movedPotency true ∧
    ¬ FirstMoverNecessaryFirstRootAt bruteFirst movedIn movedPotency allConcrete noGround true) ∧
  -- 2. conserved
  (ThereIsAFirstUnmovedMover movedIn conserved.MovesIn ∧ MoversExistAt conserved true ∧
    FirstUnmovedMoverIsPureAct movedIn conserved.MovesIn (PureAct movedPotency) ∧
    ContingentHasDistinctEsseCause conserved true ∧
    ContingentHasPotencyOrEsseCause conserved movedPotency true ∧
    DistinctEsseCausePriority conserved.CausesIn conserved.esse conserved.PriorSimply ∧
    ¬ FirstUnmovedMoverIsFirstBeing movedIn conserved.MovesIn conserved.PriorSimply ∧
    ¬ FirstMoverNecessaryPureActAt conserved movedIn movedPotency true) ∧
  -- 3. unprioritized
  (ThereIsAFirstUnmovedMover movedIn unprioritized.MovesIn ∧ MoversExistAt unprioritized true ∧
    FirstUnmovedMoverIsFirstBeing movedIn unprioritized.MovesIn unprioritized.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn unprioritized.MovesIn (PureAct movedPotency) ∧
    ContingentHasDistinctEsseCause unprioritized true ∧
    ContingentHasPotencyOrEsseCause unprioritized movedPotency true ∧
    ¬ DistinctEsseCausePriority unprioritized.CausesIn unprioritized.esse
      unprioritized.PriorSimply ∧
    ¬ FirstMoverNecessaryPureActAt unprioritized movedIn movedPotency true) ∧
  -- 4. absentMover
  (ThereIsAFirstUnmovedMover movedIn absentMover.MovesIn ∧
    FirstUnmovedMoverIsFirstBeing movedIn absentMover.MovesIn absentMover.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn absentMover.MovesIn (PureAct movedPotency) ∧
    ContingentHasDistinctEsseCause absentMover true ∧
    DistinctEsseCausePriority absentMover.CausesIn absentMover.esse absentMover.PriorSimply ∧
    PossibleNonexistenceIsPotency absentMover movedPotency true ∧
    ContingentHasPotencyOrEsseCause absentMover movedPotency true ∧
    ContingentHasDistinctEsse absentMover true unitOf unitOf ∧
    FirstUnmovedMoverIsSimpleReading movedIn absentMover.MovesIn noneHolds noneHolds noneHolds
      unitOf unitOf ∧
    ¬ MoversExistAt absentMover true ∧
    ¬ FirstMoverNecessaryPureActAt absentMover movedIn movedPotency true) ∧
  -- 5. no moving
  (MoversExistAt still true ∧ MoversConcrete still allConcrete ∧
    FirstUnmovedMoverIsFirstBeing movedIn still.MovesIn still.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn still.MovesIn (PureAct movedPotency) ∧
    ContingentHasDistinctEsseCause still true ∧
    DistinctEsseCausePriority still.CausesIn still.esse still.PriorSimply ∧
    PossibleNonexistenceIsPotency still movedPotency true ∧
    ContingentHasPotencyOrEsseCause still movedPotency true ∧
    ContingentHasDistinctEsse still true unitOf unitOf ∧
    FirstUnmovedMoverIsSimpleReading movedIn still.MovesIn noneHolds noneHolds noneHolds
      unitOf unitOf ∧
    ¬ ThereIsAFirstUnmovedMover movedIn still.MovesIn ∧
    ¬ FirstMoverNecessaryPureActAt still movedIn movedPotency true) ∧
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
    FirstUnmovedMoverIsPureAct movedIn conserved.MovesIn (PureAct movedPotency) ∧
    ContingentHasDistinctEsse conserved true essenceFalse esseTrue ∧
    ¬ FirstUnmovedMoverIsSimpleReading movedIn conserved.MovesIn noneHolds noneHolds noneHolds
      essenceFalse esseTrue ∧
    ¬ FirstMoverNecessaryPureActAt conserved movedIn movedPotency true) ∧
  -- 8. selfGround
  (ThereIsAFirstUnmovedMover movedIn selfGround.MovesIn ∧ MoversExistAt selfGround true ∧
    MoversConcrete selfGround allConcrete ∧
    FirstUnmovedMoverIsFirstBeing movedIn selfGround.MovesIn selfGround.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn selfGround.MovesIn (PureAct movedPotency) ∧
    EveryContingentGroundedAt (groundProfile selfGround allConcrete fGroundsF) true ∧
    ActualGroundingIsSimplePriority (groundProfile selfGround allConcrete fGroundsF) true
      selfGround.PriorSimply ∧
    ¬ ActualGroundingIrreflexive (groundProfile selfGround allConcrete fGroundsF) true ∧
    ¬ FirstMoverNecessaryFirstRootAt selfGround movedIn movedPotency allConcrete fGroundsF true) ∧
  -- 9. bruteFirst with x grounding f
  (EveryContingentGroundedAt (groundProfile bruteFirst allConcrete xGroundsF) true ∧
    ActualGroundingIrreflexive (groundProfile bruteFirst allConcrete xGroundsF) true ∧
    ¬ ActualGroundingIsSimplePriority (groundProfile bruteFirst allConcrete xGroundsF) true
      bruteFirst.PriorSimply ∧
    ¬ FirstMoverNecessaryFirstRootAt bruteFirst movedIn movedPotency allConcrete xGroundsF true) ∧
  -- 10. bruteFirst with nothing concrete
  (EveryContingentGroundedAt (groundProfile bruteFirst noneConcrete noGround) true ∧
    ActualGroundingIsSimplePriority (groundProfile bruteFirst noneConcrete noGround) true
      bruteFirst.PriorSimply ∧
    ActualGroundingIrreflexive (groundProfile bruteFirst noneConcrete noGround) true ∧
    ¬ MoversConcrete bruteFirst noneConcrete ∧
    ¬ FirstMoverNecessaryFirstRootAt bruteFirst movedIn movedPotency noneConcrete noGround true) ∧
  -- 11. witness
  (ThereIsAFirstUnmovedMover movedIn witness.MovesIn ∧ MoversExistAt witness true ∧
    MoversConcrete witness allConcrete ∧
    FirstUnmovedMoverIsFirstBeing movedIn witness.MovesIn witness.PriorSimply ∧
    FirstUnmovedMoverIsPureAct movedIn witness.MovesIn (PureAct movedPotency) ∧
    ContingentHasDistinctEsseCause witness true ∧
    ContingentHasPotencyOrEsseCause witness movedPotency true ∧
    DistinctEsseCausePriority witness.CausesIn witness.esse witness.PriorSimply ∧
    FirstUnmovedMoverIsSimpleReading movedIn witness.MovesIn noneHolds noneHolds noneHolds
      (fun b => b) (fun _ => true) ∧
    ContingentHasDistinctEsse witness true (fun b => b) (fun _ => true) ∧
    EveryContingentGroundedAt (groundProfile witness allConcrete fGroundsX) true ∧
    ActualGroundingIsSimplePriority (groundProfile witness allConcrete fGroundsX) true
      witness.PriorSimply ∧
    ActualGroundingIrreflexive (groundProfile witness allConcrete fGroundsX) true ∧
    (∃ x, ContingentAt witness.history.ontic true x) ∧
    FirstMoverNecessaryPureActAt witness movedIn movedPotency true ∧
    FirstMoverNecessaryFirstRootAt witness movedIn movedPotency allConcrete fGroundsX true ∧
    PossibleNonexistenceIsPotency witness movedPotency true) ∧
  -- 12. twoRoots, distinct roots
  (FirstMoverNecessaryFirstRootAt twoRoots trioMovedIn trioPotency trioConcrete trioNoGround
      true ∧
    ActualRoot (groundProfile twoRoots trioConcrete trioNoGround) true .idle ∧
    NecessaryAt twoRoots.history.ontic true .idle ∧
    IsFirstBeing twoRoots.PriorSimply .idle ∧ PureAct trioPotency .idle ∧
    ¬ IsFirstUnmovedMover trioMovedIn twoRoots.MovesIn .idle ∧
    ¬ PureAct trioPotency .moved ∧ Trio.idle ≠ Trio.mover ∧
    NecessaryActualFirstPureActAt (groundProfile twoRoots trioConcrete trioNoGround) true
      twoRoots.PriorSimply trioPotency)

/-- The laws and the models. -/
def Controls : Prop := Laws ∧ Models


/-- Universal same-respect incompatibility and three finite interpretation
tests. These are structural surrogates, NOT genuine metaphysical possibility
certificates. (1) R1+R2+actuality of esse excludes all contingent existents
when POTENCY_1 is the adopted unactualized-capacity sense. (2) A contingent
moved being receives its esse in a principle that already has its act, and
the subject-level adopted transfer fails. (3) A contingent POTENCY_1-pure-act
mover has an actual external esse supporter at exactly its existence worlds;
it is NOT first in being. Identity-scoped own-essence reception can fail when
a purported identical act is received in a different principle. (4) A brute
first pure-act contingent mover has distinct represented essence/esse and no
receipt, showing that R1 contributes new metaphysical content. -/
def ReceptionControls : Prop :=
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W)
      (InAct CanBe : B → R → Prop) (Received : B → P → Prop),
      TruthCore.Causality.ExistenceActuality.ExistingInActAt
        F.history.ontic InAct F.esse w →
      ContingentReceivesEsse F w Received →
      ContingentReceptionIsSubjectPotency F
        (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)
        w Received →
      ∀ x, ¬ ContingentAt F.history.ontic w x) ∧
  (ContingentAt witness.history.ontic true false ∧
    ContingentReceivesEsse witness true receivedByMoved ∧
    IdentityScopedEsseReception essenceByBeing esseTrue receivedByMoved ∧
    TruthCore.Causality.EsseReception.EsseReceivedOnlyInOwnEssence
      essenceFalse receivedByMoved ∧
    TruthCore.Latin.Aquinas.DeEnte.ReceiverInPotencyToReceivedEsseReading
      esseTrue receivedByMoved receptivePotency ∧
    TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself
      receptivePotency ∧
    ContingentHasDistinctEsse witness true essenceByBeing esseTrue ∧
    ContingentReceptionIsSubjectPotency witness subjectPotencyAtEsse
      true receivedByMoved ∧
    TruthCore.Causality.ExistenceActuality.ExistingInActAt
      witness.history.ontic actAtEsse witness.esse true ∧
    ¬ ContingentReceptionIsSubjectPotency witness
      (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency
        actAtEsse canBeAny) true receivedByMoved) ∧
  (ContingentAt conserved.history.ontic true true ∧
    ContingentReceivesEsse conserved true receivedByMover ∧
    IdentityScopedEsseReception essenceFalse esseTrue receivedByMover ∧
    TruthCore.Causality.EsseReception.EsseReceivedOnlyInOwnEssence
      essenceFalse receivedByMover ∧
    TruthCore.Latin.Aquinas.DeEnte.ReceiverInPotencyToReceivedEsseReading
      esseTrue receivedByMover receptivePotency ∧
    TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself
      receptivePotency ∧
    conserved.CausesIn false true conserved.esse ∧
    conserved.PriorSimply false true ∧
    (∀ v, conserved.history.ontic.ExistsAt v true ↔
      ∃ c, conserved.history.ontic.ExistsAt v c ∧ supportsEsseAt v c true ∧
        conserved.CausesIn c true conserved.esse) ∧
    PureAct movedPotency true ∧
    ¬ IsFirstBeing conserved.PriorSimply true ∧
    ¬ ContingentReceptionIsSubjectPotency conserved movedPotency
      true receivedByMover ∧
    ¬ PossibleNonexistenceIsPotency conserved movedPotency true ∧
    ¬ IdentityScopedEsseReception essenceByBeing esseTrue receivedByMover ∧
    ¬ ContingentHasDistinctEsse conserved true essenceByBeing esseTrue) ∧
  (ContingentAt bruteFirst.history.ontic true true ∧
    IsFirstUnmovedMover movedIn bruteFirst.MovesIn true ∧
    IsFirstBeing bruteFirst.PriorSimply true ∧
    PureAct movedPotency true ∧
    ContingentHasDistinctEsse bruteFirst true essenceFalse esseTrue ∧
    ¬ ContingentReceivesEsse bruteFirst true receivedNone)

end Model

end TruthCore.Causality.FirstMoverNecessity
