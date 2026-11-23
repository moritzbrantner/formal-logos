module

public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Causality.TermSenseForks2
public import TruthCore.Causality.TermSenseForks4
public import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
public import TruthCore.Logic.StrengthComparison

/-!
# C2: what grounds the contingency of an actual being? (follow-up to #1870)

Analyst formulations, attribution deferred (logic first). Navigation only, no
source claim: Met. Θ.1 1046a (a passive potency correlates with an active
power), Θ.8 1050b (what can not-be is perishable, through matter); ST I q.9
a.2 (mutable through a potency in itself or through a power in another), q.50
a.5 (angels have no potency to non-being), q.104 a.1 and a.3 (conservation as
continued giving of esse; annihilation as ceasing to give being, not an action
on a patient), q.44 a.1, q.2 a.3; *De ente* c.3–c.4 (receiver and received
act).

**C2** (`ContingentReceptiveOrReceivedFromPrior`): every being contingent at the
reading world `w` (`ContingentAt` on `F.history.ontic`, existing at `w` and
absent at some accessible world) either is existentially receptive
(`ExistentiallyReceptive`: its esse is received in some principle in receptive
potency to it, RECEPTIVE_POTENCY_1 of *De ente* c.3, or it is composed of
matter and form) or has a distinct CAUSE_2 of its esse that is SIMPLY_PRIOR_1
to it. "Relevant" receptivity is typed no further: any such recipient, or any
matter–form composition, satisfies it. "Receptive" is **not** POTENCY_1 at
esse: by the R2 law of `FirstMoverNecessity.Model.ReceptionControls`,
unactualized POTENCY_1 at esse is incompatible with actual existence, whereas a
receiving principle may already have its act. The matter–form disjunct keeps
C2 faithful for views without a real essence–esse distinction (Suárez).

**PGP** (`ContingencyPowerGrounded`): every being contingent at `w` can fail to
be in substance (`CanFailToBe x F.esse`, the existing DEF-CAN-FAIL-TO-BE
primitive at the respect of being, read as the in-subject channel,
*corruptibile simpliciter*; POSSIBLE_NOT_TO_BE_1) or some being has power over
its esse (`PowerOverEsse`, POWER_OVER_ESSE_1, the broad power to unmake `x`'s
being; possibility of non-being through another, POSSIBLE_NOT_TO_BE_2). `y = x`
is allowed. PGP is a material disjunction: it is weaker than the explanatory
"grounding" of the powers theory of modality whose warrant it borrows. It
concerns only the possible absence of an *actual individual*.

**Correlation** (`PowerOverEsseCorrelation`): whenever `y` has power over `x`'s
esse (sense POWER_OVER_ESSE_1), `x` can fail to be in substance or `y` is a
CAUSE_2 of `x`'s esse (`CausesIn y x F.esse`, tenseless: "conserving now" and
"having originated" are not distinguished). A co-occurrence disjunction; it
does not state that the power works through either. Under the narrower giving
sense POWER_OVER_ESSE_2 (`GivingPowerOverEsse`) it is trivial (`Model.Laws`,
11), so the batch uses the broad sense.

**Passive → receptive** (`CorruptibleIsExistentiallyReceptive`): what can fail
to be in substance is composed of matter and form (a principle open to being
and non-being) or has its esse received in a principle in receptive potency to
it.

Results (in `TruthCore.Results.Causality.ContingencyGrounding`): C2 from PGP,
correlation, passive→receptive, no self-esse-cause and B3 (`ee74c678`); the
First Way's mover is necessary from C2, firstness, and the new intermediate
`FirstUnmovedMoverUnreceived` (itself from simplicity, R3, *De ente* and
receptive irreflexivity, with no excluded middle); C2 from R1 with *De ente*,
and from B2 with B3 (both existing bridges are stronger than C2); C2 ⇒ C2⁻,
C2⁻ with B3 ⇒ C2, and the certified difference of C2 over C2⁻; and #1870's
B2 ∨ B4 (`3c9d683b`) from PGP, correlation, no self-esse-cause and a
corruptible-has-POTENCY_1 bridge.

Models are finite typed interpretations: structural satisfiability of a stated
formal reading, never a certificate of metaphysical possibility.
-/

@[expose] public section

namespace TruthCore.Causality.ContingencyGrounding

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct IsFirstBeing)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover)
open TruthCore.Logic.StrengthComparison (ComparisonSpec)

variable {W B T R P : Type}

/-! ## Existential receptivity and C2 -/

/-- EXISTENTIAL RECEPTIVITY (defined predicate): either the esse of `x` is
received in some principle that is in receptive potency to that esse
(`Received`, `ReceptivePotencyTo`: RECEPTIVE_POTENCY_1 of *De ente* c.3,
compatible with actually having the act), or `x` is composed of matter and form
(the same `ComposedOfMatterAndForm` parameter as the existing simplicity
reading). Any such recipient satisfies it. It is not POTENCY_1 (`InPotency`,
able to be and not in act) at esse, and it says nothing about a cause. -/
def ExistentiallyReceptive (esseOf : B → P) (Received : B → P → Prop)
    (ReceptivePotencyTo : P → P → Prop) (ComposedOfMatterAndForm : B → Prop) (x : B) :
    Prop :=
  (∃ p, Received x p ∧ ReceptivePotencyTo p (esseOf x)) ∨ ComposedOfMatterAndForm x

/-- **C2**, OPEN: every being contingent at `w` is existentially receptive or
has a distinct CAUSE_2 of its esse that is SIMPLY_PRIOR_1 to it. -/
def ContingentReceptiveOrReceivedFromPrior (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    ExistentiallyReceptive esseOf Received ReceptivePotencyTo ComposedOfMatterAndForm x ∨
      ∃ c, c ≠ x ∧ F.CausesIn c x F.esse ∧ F.PriorSimply c x

/-- **C2⁻**, OPEN weak form of C2 without the priority conjunct: every being
contingent at `w` is existentially receptive or has a distinct CAUSE_2 of its
esse. C2 implies it; with B3 it implies C2 (`Model.Laws`, 1–2). -/
def ContingentReceptiveOrReceived (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    ExistentiallyReceptive esseOf Received ReceptivePotencyTo ComposedOfMatterAndForm x ∨
      ∃ c, c ≠ x ∧ F.CausesIn c x F.esse

/-- Difference of C2 over C2⁻ (#1598), OPEN: every being contingent at `w` that
has a distinct CAUSE_2 of its esse is existentially receptive or has a distinct
CAUSE_2 of its esse that is SIMPLY_PRIOR_1 to it. -/
def ContingentEsseCauseIsPriorOrReceptive (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x → (∃ c, c ≠ x ∧ F.CausesIn c x F.esse) →
    ExistentiallyReceptive esseOf Received ReceptivePotencyTo ComposedOfMatterAndForm x ∨
      ∃ c, c ≠ x ∧ F.CausesIn c x F.esse ∧ F.PriorSimply c x

/-- The strength comparison of C2 over C2⁻ with its difference. -/
def c2OverWeak (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) : ComparisonSpec where
  stronger := ContingentReceptiveOrReceivedFromPrior F w esseOf Received ReceptivePotencyTo
    ComposedOfMatterAndForm
  weaker := ContingentReceptiveOrReceived F w esseOf Received ReceptivePotencyTo
    ComposedOfMatterAndForm
  delta := ContingentEsseCauseIsPriorOrReceptive F w esseOf Received ReceptivePotencyTo
    ComposedOfMatterAndForm

/-- Premise-free equivalence: C2 holds exactly when C2⁻ and the difference hold. -/
def C2OverWeakExact : Prop :=
  ∀ {W B T R P : Type} (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop),
    ContingentReceptiveOrReceivedFromPrior F w esseOf Received ReceptivePotencyTo
        ComposedOfMatterAndForm ↔
      ContingentReceptiveOrReceived F w esseOf Received ReceptivePotencyTo
          ComposedOfMatterAndForm ∧
        ContingentEsseCauseIsPriorOrReceptive F w esseOf Received ReceptivePotencyTo
          ComposedOfMatterAndForm

/-! ## Power over esse: two senses -/

/-- POWER_OVER_ESSE_1 (broad): `y` has a power whose exercise would make or
unmake `x`'s being, by giving or withholding its esse or by corrupting it. The
relation `PowerOver` of MUTABLE_2's `MutableThroughAnother`, applied at the
frame's respect of being; `y = x` is not excluded. -/
def PowerOverEsse (F : CausalityFrame W B T R) (PowerOver : B → B → R → Prop) (y x : B) :
    Prop :=
  PowerOver y x F.esse

/-- POWER_OVER_ESSE_2 (giving): the conjunction of a power over `x`'s esse
(`PowerOverEsse`) and being a CAUSE_2 of `x`'s esse. Nothing more is typed: it
is not a primitive "power as giver". It represents, as a conjunction, the
creator reading of q.9 a.2 in DEF-MUTABILITY-IN-ANOTHER. -/
def GivingPowerOverEsse (F : CausalityFrame W B T R) (PowerOver : B → B → R → Prop)
    (y x : B) : Prop :=
  PowerOver y x F.esse ∧ F.CausesIn y x F.esse

/-! ## Power grounding of possible non-existence -/

/-- **PGP**, OPEN: every being contingent at `w` can fail to be in substance
(`CanFailToBe x F.esse`, the in-subject channel POSSIBLE_NOT_TO_BE_1) or some
being, possibly `x` itself, has power over its esse in the broad sense
(POWER_OVER_ESSE_1). A material disjunction, weaker than explanatory grounding.
Concerns the possible absence of an actual individual only. -/
def ContingencyPowerGrounded (F : CausalityFrame W B T R) (w : W)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    CanFailToBe x F.esse ∨ ∃ y, PowerOverEsse F PowerOver y x

/-- **Correlation**, OPEN (navigation: Met. Θ.1's correlation of active power
with passive potency, with the creation exception): whenever `y` has power over
`x`'s esse (POWER_OVER_ESSE_1), `x` can fail to be in substance or `y` is a
CAUSE_2 of `x`'s esse (`CausesIn y x esse`, tenseless). A co-occurrence
disjunction; it says nothing about how the power operates. -/
def PowerOverEsseCorrelation (F : CausalityFrame W B T R) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop) : Prop :=
  ∀ y x, PowerOverEsse F PowerOver y x → CanFailToBe x F.esse ∨ F.CausesIn y x F.esse

/-- **Passive → receptive**, OPEN: whatever can fail to be in substance is
existentially receptive: it is composed of matter and form (a principle open to
being and non-being), or its esse is received in a principle in receptive
potency to it. -/
def CorruptibleIsExistentiallyReceptive (F : CausalityFrame W B T R)
    (CanFailToBe : B → R → Prop) (esseOf : B → P) (Received : B → P → Prop)
    (ReceptivePotencyTo : P → P → Prop) (ComposedOfMatterAndForm : B → Prop) : Prop :=
  ∀ x, CanFailToBe x F.esse →
    ExistentiallyReceptive esseOf Received ReceptivePotencyTo ComposedOfMatterAndForm x

/-- OPEN bridge: whatever is corruptible simply is in POTENCY_1 (the adopted
potency in the subject) in some respect, any respect. Not at esse in
particular: by the R2 law POTENCY_1 at esse would exclude actual existence. The
existing B4b (`CanFailToBeIsPotencyAtEsse`) implies it (`Model.Laws`, 8). -/
def CorruptibleIsInSomePotency (F : CausalityFrame W B T R)
    (CanFailToBe InPotency : B → R → Prop) : Prop :=
  ∀ x, CanFailToBe x F.esse → ∃ r, InPotency x r

/-! ## Unreceivedness of the first mover -/

/-- Every first mover moved by none receives its esse in no principle and is not
composed of matter and form. No modality, cause or POTENCY_1 is asserted. -/
def FirstUnmovedMoverUnreceived {Respect : Type} (MovedIn : B → Respect → Prop)
    (MovesIn : B → B → Respect → Prop) (Received : B → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f →
    (∀ p, ¬ Received f p) ∧ ¬ ComposedOfMatterAndForm f

/-! ## #1870's gap-1 bridge (ii), used only in `Model.Laws` -/

/-- #1870's unrecorded bridge (ii) at esse, unrestricted: another's power over a
thing's esse (POWER_OVER_ESSE_1) gives a distinct CAUSE_2 of its esse. It is not
derived here; its countermodel `Model.CorruptorModel` is an uncaused
corruptible composite. -/
def AnothersPowerOverEsseGivesEsseCause (F : CausalityFrame W B T R)
    (PowerOver : B → B → R → Prop) : Prop :=
  ∀ y x, y ≠ x → PowerOverEsse F PowerOver y x → ∃ c, c ≠ x ∧ F.CausesIn c x F.esse

/-- Bridge (ii) restricted to beings incorruptible simply. The correlation
premise implies it (`Model.Laws`, 5). -/
def IncorruptibleUnderAnothersPowerHasEsseCause (F : CausalityFrame W B T R)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) : Prop :=
  ∀ y x, TruthCore.Latin.Aquinas.InMetaphysicam.IncorruptibleSimply CanFailToBe F.esse x →
    y ≠ x → PowerOverEsse F PowerOver y x → ∃ c, c ≠ x ∧ F.CausesIn c x F.esse


/-! ## Laws and finite models -/

namespace Model

open TruthCore.Causality.FirstMoverNecessity
open TruthCore.Causality.FirstMoverNecessity.Model (mk bruteFirst conserved unprioritized
  witness movedIn movedPotency fContingent xContingent noCause noPrior receivedByMoved
  receivedByMover receivedNone receptivePotency essenceByBeing esseTrue essenceFalse noneHolds
  actAtEsse)
open TruthCore.Causality.EsseCausePriority (DistinctEsseCausePriority)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing MutableInSomeWay)
open TruthCore.Latin.Aquinas.DeEnte (ReceiverInPotencyToReceivedEsseReading ActualEsseCause)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (ClosedActualEsseCollectionsRooted)
open TruthCore.Latin.Aquinas.SummaTheologiae (FirstUnmovedMoverIsSimpleReading)
open TruthCore.Case.Catholicism (ThereIsAFirstUnmovedMover FirstUnmovedMoverIsFirstBeing
  FirstUnmovedMoverIsPureAct)

/-- General laws.
1. C2 implies C2⁻.
2. C2⁻ with B3 implies C2.
3. R1 with *De ente* c.3 implies C2 (through its receptive disjunct).
4. B2 with B3 implies C2 (through its prior-cause disjunct).
5. Correlation implies #1870's bridge (ii) restricted to incorruptibles.
6. Bridge (i) correspondence: PGP, no power of anything over its own esse, and
   corruptible-has-POTENCY_1 give q.9 a.2's MUTABLE_3 for every contingent
   being.
7. Composition: the PGP route reaches the First Way endpoint.
8. B4b implies corruptible-has-POTENCY_1.
9. B4a implies PGP (through its corruptibility disjunct).
10. With the adopted POTENCY_1 (able to be and not in act) and the existing
    selected-world existence-to-act interface, B4b excludes every actual being
    corruptible simply at `w`: like R2, it reads a capacity for non-being as
    unactualized potency at esse, which actual existence contradicts. So the
    corruptibility disjunct of PGP is not POTENCY_1 at esse.
11. Under the giving sense POWER_OVER_ESSE_2 the correlation is trivial, by
    definition of that sense as a conjunction containing CAUSE_2; this does not
    show that a primitive creator's-power reading would trivialize it. Here a
    giving power over `x`'s esse is a CAUSE_2 of it. -/
def Laws : Prop :=
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (esseOf : B → P)
    (Received : B → P → Prop) (RP : P → P → Prop) (MF : B → Prop),
    ContingentReceptiveOrReceivedFromPrior F w esseOf Received RP MF →
      ContingentReceptiveOrReceived F w esseOf Received RP MF) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (esseOf : B → P)
    (Received : B → P → Prop) (RP : P → P → Prop) (MF : B → Prop),
    ContingentReceptiveOrReceived F w esseOf Received RP MF →
    DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply →
      ContingentReceptiveOrReceivedFromPrior F w esseOf Received RP MF) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (esseOf : B → P)
    (Received : B → P → Prop) (RP : P → P → Prop) (MF : B → Prop),
    ContingentReceivesEsse F w Received →
    ReceiverInPotencyToReceivedEsseReading esseOf Received RP →
      ContingentReceptiveOrReceivedFromPrior F w esseOf Received RP MF) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (esseOf : B → P)
    (Received : B → P → Prop) (RP : P → P → Prop) (MF : B → Prop),
    ContingentHasDistinctEsseCause F w →
    DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply →
      ContingentReceptiveOrReceivedFromPrior F w esseOf Received RP MF) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop),
    PowerOverEsseCorrelation F CanFailToBe PowerOver →
      IncorruptibleUnderAnothersPowerHasEsseCause F CanFailToBe PowerOver) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W)
    (InPotency CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop),
    ContingencyPowerGrounded F w CanFailToBe PowerOver →
    (∀ x, ¬ PowerOver x x F.esse) →
    CorruptibleIsInSomePotency F CanFailToBe InPotency →
      ∀ x, ContingentAt F.history.ontic w x → MutableInSomeWay InPotency PowerOver x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W)
    (MovedIn InPotency CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop)
    (Body MF Composite : B → Prop) (essenceOf esseOf : B → P)
    (Received : B → P → Prop) (RP : P → P → Prop),
    TruthCore.Logic.ExcludedMiddle →
    ThereIsAFirstUnmovedMover MovedIn F.MovesIn →
    MoversExistAt F w →
    FirstUnmovedMoverIsFirstBeing MovedIn F.MovesIn F.PriorSimply →
    FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency) →
    FirstUnmovedMoverIsSimpleReading MovedIn F.MovesIn Body MF Composite essenceOf esseOf →
    IdentityScopedEsseReception essenceOf esseOf Received →
    ReceiverInPotencyToReceivedEsseReading esseOf Received RP →
    NothingInReceptivePotencyToItself RP →
    ContingencyPowerGrounded F w CanFailToBe PowerOver →
    PowerOverEsseCorrelation F CanFailToBe PowerOver →
    CorruptibleIsExistentiallyReceptive F CanFailToBe esseOf Received RP MF →
    NothingCausesItsOwnBeing F.CausesIn F.esse →
    DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply →
      FirstMoverNecessaryPureActAt F MovedIn InPotency w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (InPotency CanFailToBe : B → R → Prop),
    CanFailToBeIsPotencyAtEsse F InPotency CanFailToBe →
      CorruptibleIsInSomePotency F CanFailToBe InPotency) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop),
    ContingentCanFailToBe F CanFailToBe w → ContingencyPowerGrounded F w CanFailToBe PowerOver) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W)
    (InAct CanBe CanFailToBe : B → R → Prop),
    TruthCore.Causality.ExistenceActuality.ExistingInActAt F.history.ontic InAct F.esse w →
    CanFailToBeIsPotencyAtEsse F
      (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)
      CanFailToBe →
      ∀ x, F.history.ontic.ExistsAt w x → ¬ CanFailToBe x F.esse) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop),
    ∀ y x, GivingPowerOverEsse F PowerOver y x → CanFailToBe x F.esse ∨ F.CausesIn y x F.esse)

/-! ### Model ingredients

Frames reuse `FirstMoverNecessity.Model.mk`: worlds and beings `Bool`, one
moment, respects `Bool` with `true` the respect of being (`esse`) and `false`
a respect of motion (heat), universal access, reading world `true`. Being
`true` (`f`) moves being `false` (`x`) in heat; `x` is in POTENCY_1 in heat
only (`movedPotency`), so `f` is POTENCY_1-pure act in every model.
Principles are `Bool`: `esseTrue` gives every being the esse-principle `true`. -/

/-- `x` exists at the reading world only; `f` at both; nothing causes or is
prior to anything. -/
def uncausedX : CausalityFrame Bool Bool Unit Bool := mk xContingent noCause noPrior

/-- `f` causes its own esse. -/
def fSelfCausesEsse (c y r : Bool) : Prop := c = true ∧ y = true ∧ r = true

/-- As `bruteFirst` (`f` contingent), but `f` causes its own esse. -/
def selfCauser : CausalityFrame Bool Bool Unit Bool := mk fContingent fSelfCausesEsse noPrior

/-- Only `x` can fail to be hot; nothing is corruptible simply. -/
def heatFail (x r : Bool) : Prop := x = false ∧ r = false

/-- `x` can fail to be hot and can fail to be simply (corruptible). -/
def xCorruptible (x _ : Bool) : Prop := x = false

/-- Power relations at esse. -/
def noPower (_ _ _ : Bool) : Prop := False
def selfPower (y x r : Bool) : Prop := y = true ∧ x = true ∧ r = true
def xPowerF (y x r : Bool) : Prop := y = false ∧ x = true ∧ r = true
def fPowerX (y x r : Bool) : Prop := y = true ∧ x = false ∧ r = true

/-- `x` is composed of matter and form. -/
def xComposite (b : Bool) : Prop := b = false

/-- **bruteSimple** (rivals 6.1/6.3; frame `bruteFirst`). `f` moves `x`, is
moved by none, is first in being, POTENCY_1-pure act, simple with esse equal to
essence, unreceived, not composed of matter and form, uncaused, incorruptible
simply, and no being has power over its esse; it exists at the reading world
and is absent at the other. Every premise of the PGP argument and of the
unreceivedness and C2 routes to the endpoint holds except PGP and C2, which
fail at `f`: ¬C2 here needs ¬PGP (it does not follow from ¬PGP alone:
`UncausedCompositeModel`). The closed-collection premise CCR (`20babef7`, C1)
holds on the q.3 a.4 profile of the same frame, with `f` an actual esse bearer
that has no distinct actual esse-cause; that check is degenerate (the adapter's
one-world `Unit` frame reads existence as act of esse and this frame has no
esse-causes, so every bearer is trivially a root and CCR is modally silent by
construction). Structural satisfiability only. The relevant admissible reading
is a hybrid: it accepts the First Way's act and potency for change while using
a non-power modality for existence (modal primitivism, combinatorial
recombination, Lewisian counterpart absence, or essence-based modality with
existence-conditional essences, Fine/Lowe). Pure Humeans reject the model's act,
potency and motion premises. -/
def BruteSimpleModel : Prop :=
  ContingentAt bruteFirst.history.ontic true true ∧
  ThereIsAFirstUnmovedMover movedIn bruteFirst.MovesIn ∧
  MoversExistAt bruteFirst true ∧
  FirstUnmovedMoverIsFirstBeing movedIn bruteFirst.MovesIn bruteFirst.PriorSimply ∧
  FirstUnmovedMoverIsPureAct movedIn bruteFirst.MovesIn (PureAct movedPotency) ∧
  FirstUnmovedMoverIsSimpleReading movedIn bruteFirst.MovesIn noneHolds noneHolds noneHolds
    essenceByBeing esseTrue ∧
  IdentityScopedEsseReception essenceByBeing esseTrue receivedNone ∧
  ReceiverInPotencyToReceivedEsseReading esseTrue receivedNone receptivePotency ∧
  NothingInReceptivePotencyToItself receptivePotency ∧
  FirstUnmovedMoverUnreceived movedIn bruteFirst.MovesIn receivedNone noneHolds ∧
  PowerOverEsseCorrelation bruteFirst heatFail noPower ∧
  CorruptibleIsExistentiallyReceptive bruteFirst heatFail esseTrue receivedNone receptivePotency
    noneHolds ∧
  NothingCausesItsOwnBeing bruteFirst.CausesIn bruteFirst.esse ∧
  DistinctEsseCausePriority bruteFirst.CausesIn bruteFirst.esse bruteFirst.PriorSimply ∧
  CorruptibleIsInSomePotency bruteFirst heatFail movedPotency ∧
  ¬ ContingencyPowerGrounded bruteFirst true heatFail noPower ∧
  ¬ ContingentReceptiveOrReceivedFromPrior bruteFirst true esseTrue receivedNone receptivePotency
    noneHolds ∧
  ¬ FirstMoverNecessaryPureActAt bruteFirst movedIn movedPotency true ∧
  ClosedActualEsseCollectionsRooted (esseProfile bruteFirst actAtEsse essenceByBeing esseTrue
    noneHolds) ∧
  (esseProfile bruteFirst actAtEsse essenceByBeing esseTrue noneHolds).InAct true
    bruteFirst.esse ∧
  (∀ c, ¬ ActualEsseCause (esseProfile bruteFirst actAtEsse essenceByBeing esseTrue noneHolds)
    c true)

/-- **selfAnnihilator**, two variants, both with the simple, uncaused,
incorruptible contingent `f` having power over its own esse. Variant 1 (frame
`bruteFirst`): PGP holds, correlation fails (the power works on no potency of
`f` and is no causing of its esse). Variant 2 (frame `selfCauser`, `f` causes
its own esse): PGP and correlation hold, no-self-esse-cause fails. B3 and
passive→receptive hold in both; C2 fails in both. Structural only; variant 2
is admissible only on a metaphysics allowing self-causation of esse. -/
def SelfAnnihilatorModel : Prop :=
  (ContingencyPowerGrounded bruteFirst true heatFail selfPower ∧
    ¬ PowerOverEsseCorrelation bruteFirst heatFail selfPower ∧
    CorruptibleIsExistentiallyReceptive bruteFirst heatFail esseTrue receivedNone
      receptivePotency noneHolds ∧
    NothingCausesItsOwnBeing bruteFirst.CausesIn bruteFirst.esse ∧
    DistinctEsseCausePriority bruteFirst.CausesIn bruteFirst.esse bruteFirst.PriorSimply ∧
    ¬ ContingentReceptiveOrReceivedFromPrior bruteFirst true esseTrue receivedNone
      receptivePotency noneHolds) ∧
  (ContingentAt selfCauser.history.ontic true true ∧
    ContingencyPowerGrounded selfCauser true heatFail selfPower ∧
    PowerOverEsseCorrelation selfCauser heatFail selfPower ∧
    CorruptibleIsExistentiallyReceptive selfCauser heatFail esseTrue receivedNone
      receptivePotency noneHolds ∧
    ¬ NothingCausesItsOwnBeing selfCauser.CausesIn selfCauser.esse ∧
    DistinctEsseCausePriority selfCauser.CausesIn selfCauser.esse selfCauser.PriorSimply ∧
    ¬ ContingentReceptiveOrReceivedFromPrior selfCauser true esseTrue receivedNone
      receptivePotency noneHolds)

/-- **uncausedComposite** (rival 6.2; frame `uncausedX`): the contingent `x`
receives its esse in its essence, a principle in receptive potency to it, and
nothing causes or has power over it. C2 holds by its receptive disjunct while
PGP, B2 and C2's prior-cause disjunct fail; R1 and *De ente* hold. So C2 does
not entail PGP, and C2 is strictly weaker than B2 with B3. Structural only;
admissible on a metaphysics allowing an uncaused composite (it contradicts the
q.3 a.4 reading, not C2). -/
def UncausedCompositeModel : Prop :=
  ContingentAt uncausedX.history.ontic true false ∧
  ContingentReceivesEsse uncausedX true receivedByMoved ∧
  ReceiverInPotencyToReceivedEsseReading esseTrue receivedByMoved receptivePotency ∧
  NothingInReceptivePotencyToItself receptivePotency ∧
  PowerOverEsseCorrelation uncausedX heatFail noPower ∧
  CorruptibleIsExistentiallyReceptive uncausedX heatFail esseTrue receivedByMoved
    receptivePotency noneHolds ∧
  NothingCausesItsOwnBeing uncausedX.CausesIn uncausedX.esse ∧
  DistinctEsseCausePriority uncausedX.CausesIn uncausedX.esse uncausedX.PriorSimply ∧
  ContingentReceptiveOrReceivedFromPrior uncausedX true esseTrue receivedByMoved
    receptivePotency noneHolds ∧
  ¬ ContingencyPowerGrounded uncausedX true heatFail noPower ∧
  ¬ ContingentHasDistinctEsseCause uncausedX true ∧
  ¬ (∃ c, c ≠ false ∧ uncausedX.CausesIn c false uncausedX.esse ∧
    uncausedX.PriorSimply c false)

/-- **angelic** (frame `conserved`): the contingent `f` is incorruptible simply
(no intrinsic potency to non-being), receives its esse in a principle in
receptive potency to it, and the necessary `x` has power over `f`'s esse,
causes it and is simply prior to it. Every premise of the PGP argument holds
and C2 holds by both disjuncts. Admissible on the Thomist account of a created
intelligence for exactly this part: contingent, incorruptible simply, C2 by
both disjuncts, contingency grounded extrinsically (being able not to exist is
not having a potency to non-being). STRUCTURAL ONLY: `f` is POTENCY_1-pure act
only relative to the frame's two respects, so the failures of B4 and of the
pure-act target at `w` are not Thomist-admissible (Aquinas's angels have
potencies of intellect, will and place, q.9 a.2, which make B4 true and the
target vacuous for them). -/
def AngelicModel : Prop :=
  ContingentAt conserved.history.ontic true true ∧
  PureAct movedPotency true ∧
  TruthCore.Latin.Aquinas.InMetaphysicam.IncorruptibleSimply heatFail conserved.esse true ∧
  ContingentReceivesEsse conserved true receivedByMover ∧
  ReceiverInPotencyToReceivedEsseReading esseTrue receivedByMover receptivePotency ∧
  ContingencyPowerGrounded conserved true heatFail xPowerF ∧
  PowerOverEsseCorrelation conserved heatFail xPowerF ∧
  CorruptibleIsExistentiallyReceptive conserved heatFail esseTrue receivedByMover
    receptivePotency noneHolds ∧
  NothingCausesItsOwnBeing conserved.CausesIn conserved.esse ∧
  DistinctEsseCausePriority conserved.CausesIn conserved.esse conserved.PriorSimply ∧
  ContingentReceptiveOrReceivedFromPrior conserved true esseTrue receivedByMover
    receptivePotency noneHolds ∧
  ¬ PossibleNonexistenceIsPotency conserved movedPotency true ∧
  ¬ PureActBeingsNecessaryAt conserved movedPotency true

/-- **inertPowerHolder** (omission model of correlation; frame `bruteFirst`):
the necessary `x` has power over the contingent `f`'s esse but plays no causal
role (it is no CAUSE_2 of `f`'s esse), and `f` is not corruptible simply; `f`
receives its esse in a principle in receptive potency to it. PGP holds,
correlation fails, C2 holds by its receptive disjunct, its prior-cause disjunct
and B2 fail. This is the inert power over being named in the revision
conditions, not a deist creator: with the tenseless `CausesIn`, a deist
originator is a CAUSE_2 of `f`'s esse and satisfies the typed correlation and
C2's prior-cause disjunct given B3 or an independent priority fact; the deist
rival bears only on a tensed (conserving)
strengthening. Since `f` is POTENCY_1-pure act, B2 ∨ B4 fails too: C2 does not
entail B2 ∨ B4. Structural only. -/
def InertPowerHolderModel : Prop :=
  ContingentAt bruteFirst.history.ontic true true ∧
  ContingencyPowerGrounded bruteFirst true heatFail xPowerF ∧
  ¬ PowerOverEsseCorrelation bruteFirst heatFail xPowerF ∧
  CorruptibleIsExistentiallyReceptive bruteFirst heatFail esseTrue receivedByMover
    receptivePotency noneHolds ∧
  NothingCausesItsOwnBeing bruteFirst.CausesIn bruteFirst.esse ∧
  DistinctEsseCausePriority bruteFirst.CausesIn bruteFirst.esse bruteFirst.PriorSimply ∧
  ContingentReceptiveOrReceivedFromPrior bruteFirst true esseTrue receivedByMover
    receptivePotency noneHolds ∧
  ¬ ContingentHasDistinctEsseCause bruteFirst true ∧
  ¬ ContingentHasPotencyOrEsseCause bruteFirst movedPotency true ∧
  ¬ (∃ c, c ≠ true ∧ bruteFirst.CausesIn c true bruteFirst.esse ∧
    bruteFirst.PriorSimply c true)

/-- **bareCorruptible** (omission of passive→receptive; frame `uncausedX`): the
contingent `x` is corruptible simply but has neither matter nor a receiving
principle; nothing has power over it. PGP, correlation, no-self-esse-cause and
B3 hold; passive→receptive and C2 fail. Structural only. -/
def BareCorruptibleModel : Prop :=
  ContingencyPowerGrounded uncausedX true xCorruptible noPower ∧
  PowerOverEsseCorrelation uncausedX xCorruptible noPower ∧
  ¬ CorruptibleIsExistentiallyReceptive uncausedX xCorruptible esseTrue receivedNone
    receptivePotency noneHolds ∧
  NothingCausesItsOwnBeing uncausedX.CausesIn uncausedX.esse ∧
  DistinctEsseCausePriority uncausedX.CausesIn uncausedX.esse uncausedX.PriorSimply ∧
  ¬ ContingentReceptiveOrReceivedFromPrior uncausedX true esseTrue receivedNone
    receptivePotency noneHolds

/-- **unprioritizedSource** (omission of B3; frame `unprioritized`): the
necessary `x` has power over and causes the contingent `f`'s esse but is not
simply prior to it; `f` is unreceived and simple. PGP, correlation,
passive→receptive and no-self-esse-cause hold; B3 and C2 fail while C2⁻ holds,
so C2 strictly strengthens C2⁻. -/
def UnprioritizedSourceModel : Prop :=
  ContingentReceptiveOrReceived unprioritized true esseTrue receivedNone receptivePotency
    noneHolds ∧
  ContingencyPowerGrounded unprioritized true heatFail xPowerF ∧
  PowerOverEsseCorrelation unprioritized heatFail xPowerF ∧
  CorruptibleIsExistentiallyReceptive unprioritized heatFail esseTrue receivedNone
    receptivePotency noneHolds ∧
  NothingCausesItsOwnBeing unprioritized.CausesIn unprioritized.esse ∧
  ¬ DistinctEsseCausePriority unprioritized.CausesIn unprioritized.esse
    unprioritized.PriorSimply ∧
  ¬ ContingentReceptiveOrReceivedFromPrior unprioritized true esseTrue receivedNone
    receptivePotency noneHolds

/-- The separating setting of C2 over C2⁻ (#1598): the `unprioritized` frame,
with nothing received and no matter–form composition. -/
def unprioritizedSetting : ComparisonSpec :=
  c2OverWeak unprioritized true esseTrue receivedNone receptivePotency noneHolds

/-- In `unprioritizedSetting` C2⁻ holds and C2 fails. -/
def UnprioritizedSeparates : Prop :=
  TruthCore.Logic.StrengthComparison.Separation unprioritizedSetting

/-- **witness** (nonvacuity; frame `witness`): the first mover `f` is necessary,
first, pure act, simple and unreceived; the contingent moved thing `x` is
corruptible simply, composed of matter and form, receives its esse in its
essence, and `f` has power over, causes and is simply prior to `x`'s esse.
Every premise of every new argument holds, and PGP, correlation,
passive→receptive and corruptible-has-POTENCY_1 are applied nonvacuously to `x`;
C2, B2 ∨ B4 and the endpoint hold. -/
def WitnessModel : Prop :=
  ThereIsAFirstUnmovedMover movedIn witness.MovesIn ∧
  MoversExistAt witness true ∧
  FirstUnmovedMoverIsFirstBeing movedIn witness.MovesIn witness.PriorSimply ∧
  FirstUnmovedMoverIsPureAct movedIn witness.MovesIn (PureAct movedPotency) ∧
  FirstUnmovedMoverIsSimpleReading movedIn witness.MovesIn noneHolds xComposite noneHolds
    essenceByBeing esseTrue ∧
  IdentityScopedEsseReception essenceByBeing esseTrue receivedByMoved ∧
  ReceiverInPotencyToReceivedEsseReading esseTrue receivedByMoved receptivePotency ∧
  NothingInReceptivePotencyToItself receptivePotency ∧
  FirstUnmovedMoverUnreceived movedIn witness.MovesIn receivedByMoved xComposite ∧
  ContingencyPowerGrounded witness true xCorruptible fPowerX ∧
  PowerOverEsseCorrelation witness xCorruptible fPowerX ∧
  CorruptibleIsExistentiallyReceptive witness xCorruptible esseTrue receivedByMoved
    receptivePotency xComposite ∧
  NothingCausesItsOwnBeing witness.CausesIn witness.esse ∧
  DistinctEsseCausePriority witness.CausesIn witness.esse witness.PriorSimply ∧
  CorruptibleIsInSomePotency witness xCorruptible movedPotency ∧
  ContingentAt witness.history.ontic true false ∧
  xCorruptible false witness.esse ∧ fPowerX true false witness.esse ∧
  witness.CausesIn true false witness.esse ∧
  ExistentiallyReceptive esseTrue receivedByMoved receptivePotency xComposite false ∧
  ContingentReceptiveOrReceivedFromPrior witness true esseTrue receivedByMoved
    receptivePotency xComposite ∧
  ContingentHasPotencyOrEsseCause witness movedPotency true ∧
  FirstMoverNecessaryPureActAt witness movedIn movedPotency true

/-- **potencyOnly** (non-equivalence, direction 9; frame `uncausedX`): the
contingent `x` is in POTENCY_1 in heat (so not pure act), incorruptible simply,
unreceived, uncaused and under no power. The pure-act target at `w` (every
pure-act being existing at `w` is necessary there) holds and so does B4, while
PGP and C2 fail. With `AngelicModel` (PGP and C2 hold, the target fails), PGP
and C2 are each logically independent of the target, unlike B4, which with
excluded middle is equivalent to it (`FirstMoverNecessity.Model.Laws`, 3). B2 ∨ B4
holds here while C2 fails, so B2 ∨ B4 does not entail C2 either (with
`InertPowerHolderModel`, the two bridges are independent). -/
def PotencyOnlyModel : Prop :=
  PureActBeingsNecessaryAt uncausedX movedPotency true ∧
  PossibleNonexistenceIsPotency uncausedX movedPotency true ∧
  ContingentHasPotencyOrEsseCause uncausedX movedPotency true ∧
  ¬ ContingencyPowerGrounded uncausedX true heatFail noPower ∧
  ¬ ContingentReceptiveOrReceivedFromPrior uncausedX true esseTrue receivedNone
    receptivePotency noneHolds

/-- **corruptor** (#1870 bridge (ii); frame `uncausedX`): `f` has power over the
esse of the uncaused corruptible composite `x` without causing its esse.
Correlation, PGP, passive→receptive and C2 hold; the unrestricted bridge (ii)
fails and its restriction to incorruptibles holds. The countermodel depends on
`x` being uncaused: under the tenseless CAUSE_2 an ordinary corruptible has a
distinct esse-cause (its generator), so this model does not show the
unrestricted bridge false of ordinary corruption. No being receives esse, so R1
fails while C2 holds through matter and form: C2 does not require R1. -/
def CorruptorModel : Prop :=
  ContingencyPowerGrounded uncausedX true xCorruptible fPowerX ∧
  PowerOverEsseCorrelation uncausedX xCorruptible fPowerX ∧
  CorruptibleIsExistentiallyReceptive uncausedX xCorruptible esseTrue receivedNone
    receptivePotency xComposite ∧
  ContingentReceptiveOrReceivedFromPrior uncausedX true esseTrue receivedNone
    receptivePotency xComposite ∧
  ¬ ContingentReceivesEsse uncausedX true receivedNone ∧
  ¬ AnothersPowerOverEsseGivesEsseCause uncausedX fPowerX ∧
  IncorruptibleUnderAnothersPowerHasEsseCause uncausedX xCorruptible fPowerX

/-- The models, each at the reading world `true`. -/
def Models : Prop :=
  BruteSimpleModel ∧ SelfAnnihilatorModel ∧ UncausedCompositeModel ∧ AngelicModel ∧
  InertPowerHolderModel ∧ BareCorruptibleModel ∧ UnprioritizedSourceModel ∧ WitnessModel ∧
  PotencyOnlyModel ∧ CorruptorModel

/-- The laws and the models. -/
def Controls : Prop := Laws ∧ Models

end Model

end TruthCore.Causality.ContingencyGrounding
