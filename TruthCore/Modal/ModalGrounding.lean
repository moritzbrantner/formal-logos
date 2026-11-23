module

public import TruthCore.Causality.ContingencyGrounding
public import TruthCore.Causality.SubtractionArgument
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Modern.Hume.Conceivability

/-!
# What grounds the possible absence of a foundational being? (#1887, tests 4–5)

Analyst formulations, attribution deferred (logic first). Navigation only, no
source claim and nothing materialized: B. Vetter, *Potentiality* (2015);
A. Pruss, *Actuality, Possibility, and Worlds* (2011); D. Armstrong, *A
Combinatorial Theory of Possibility* (1989); K. Fine, "Essence and Modality"
(1994); E. J. Lowe, "Two Notions of Being" (2008) and *More Kinds of Being*
(2009); ST I q.45 a.2 ad 2 (creation is not a change).

All accounts are stated on one shared `CausalityFrame` (#1784): world-relative
existence `F.history.ontic.ExistsAt`, its accessibility frame, `CausesIn` at
`F.esse` (CAUSE_2 at esse), `PriorSimply` (SIMPLY_PRIOR_1) and `MovesIn`
(CAUSE_1). Every relation introduced below that is not a frame field is a
stated primitive parameter with its meaning, examples and non-examples in its
doc comment and definition record; no relation between primitives is assumed.

**The foundational case** (`FoundationalAt`): a being actual at `w`, simple
(esse equal to essence as represented, not composed of matter and form),
receiving its esse in no principle, first in SIMPLY_PRIOR_1, with no CAUSE_2 of
its esse, incorruptible simply (no in-subject potency to non-being,
POSSIBLE_NOT_TO_BE_1) and under no being's power over its esse
(POWER_OVER_ESSE_1).

**Accounts of de re possibility of absence**, each an explicit framework
input on that frame:

* *Power-grounded (PGP, Aristotelian)*: `ContingencyPowerGrounded` of
  `TruthCore.Causality.ContingencyGrounding` (statement `20d5fecd`), reused.
* *Combinatorial (Humean)*: `UnrestrictedRecombinationAt` of
  `TruthCore.Causality.SubtractionArgument`, reused on the frame's own profile
  (`groundProfile`).
* *Primitivist*: no grounding requirement at all. It is not a predicate: its
  formal content is that the foundational profile fixes no modal verdict
  (`Model.PrimitivistSilence`).
* *Essentialist*: a primitive `Essential x φ` ("it lies in the nature of `x`
  that `φ`", Fine's `□ₓ`), with `φ` a world-proposition. Essence grounds
  necessity (`EssenceGroundsNecessity`); possibility of absence is the absence
  of an essential exclusion (`EssentialExclusionAccount`). *Existence-
  conditional* essentialism (`ExistenceConditionalEssences`): every essential
  truth about `x` holds wherever `x` is absent ("necessarily, if `x` exists,
  …"). *Unconditional* essentialism lets existence itself belong to an essence;
  its reading of esse = essence is `EsseEssenceIsEssentialExistence`.
* *Hybrid*: powers ground possibilities of change (`MovedOnlyAsInPotencyReading`
  of ST I q.2 a.3, reused), while possibilities of existence are combinatorial
  or primitive (`Model.HybridFirstWayModel`).

**Pruss's Aristotelian-modality argument** (analyst reconstruction): a
primitive `PowerFor w y p` (at `w`, `y` has a power whose exercise would
initiate a causal chain issuing in `p`), the Aristotelian grounding of a
non-actual possibility in an actual being's power, initiator presence, and the
tenseless global possibility that no contingent concrete being exists.

Models are finite typed interpretations: structural satisfiability of the
stated formal reading, never a certificate of metaphysical possibility.
-/

@[expose] public section

namespace TruthCore.Modal.ModalGrounding

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Causality.ContingencyGrounding (PowerOverEsse ContingencyPowerGrounded)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing)
open TruthCore.Latin.Aquinas.InMetaphysicam (IncorruptibleSimply)

variable {W B T R P : Type}

/-! ## The foundational case -/

/-- The foundational case for `f` at `w`: `f` exists at `w`; its represented
esse equals its represented essence; it is not composed of matter and form; its
esse is received in no principle; it is first in SIMPLY_PRIOR_1 (whatever is
simply prior to it is itself); nothing (itself included) is a CAUSE_2 of its
esse; it is incorruptible simply (no in-subject potency to non-being,
POSSIBLE_NOT_TO_BE_1); and no being (itself included) has power over its esse
(POWER_OVER_ESSE_1). Every conjunct is non-modal: nothing here says whether
`f` exists at another world. -/
def FoundationalAt (F : CausalityFrame W B T R) (w : W) (essenceOf esseOf : B → P)
    (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) (f : B) : Prop :=
  F.history.ontic.ExistsAt w f ∧ esseOf f = essenceOf f ∧ ¬ ComposedOfMatterAndForm f ∧
    (∀ p, ¬ Received f p) ∧ IsFirstBeing F.PriorSimply f ∧
    (∀ c, ¬ F.CausesIn c f F.esse) ∧ IncorruptibleSimply CanFailToBe F.esse f ∧
    ∀ y, ¬ PowerOverEsse F PowerOver y f

/-- Verdict "necessary": every being foundational at `w` exists at every world
accessible from `w`. -/
def FoundationalBeingsNecessaryAt (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) : Prop :=
  ∀ f, FoundationalAt F w essenceOf esseOf Received ComposedOfMatterAndForm CanFailToBe
    PowerOver f → NecessaryAt F.history.ontic w f

/-- Verdict "possibly absent": every being foundational at `w` is contingent at
`w` (exists there and is absent at some accessible world). -/
def FoundationalBeingsContingentAt (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) : Prop :=
  ∀ f, FoundationalAt F w essenceOf esseOf Received ComposedOfMatterAndForm CanFailToBe
    PowerOver f → ContingentAt F.history.ontic w f

/-- Some concrete being is foundational at `w`. Common ground between the
theist and the brute-first rival (`Model.BruteFoundationalModel`); a pure
Humean who rejects simplicity or act need not accept it. -/
def SomeConcreteFoundationalAt (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) (concrete : B → Prop) :
    Prop :=
  ∃ f, concrete f ∧ FoundationalAt F w essenceOf esseOf Received ComposedOfMatterAndForm
    CanFailToBe PowerOver f

/-! ## Essentialist accounts

`Essential : B → (W → Prop) → Prop` is a stated primitive: `Essential x φ`
says that it lies in the nature of `x` that `φ` (Fine's `□ₓ φ`), for a
world-proposition `φ` over the frame's points. Examples: it lies in the nature
of a singleton that it has its member; of water that it is H₂O. Non-examples:
that Socrates is a member of his singleton is necessary but does not lie in
Socrates' nature (Fine's point against the modal analysis of essence); that a
contingent being happens to exist at `w`. Distinct from necessity (the
converse fails), from CAUSE_2 and from power. Structural properties assumed:
none. The existing `EssenceReasonSeparation.Profile.InEssence` represents only
existence facts in essences; it cannot state an existence-conditional essence,
which is why this parameter takes world-propositions. -/

/-- `φ` entails `x`'s existence over every point of the frame's world type (not
only the accessible ones): wherever `φ` holds, `x` exists. -/
def EntailsExistence (F : CausalityFrame W B T R) (φ : W → Prop) (x : B) : Prop :=
  ∀ v, φ v → F.history.ontic.ExistsAt v x

/-- OPEN (essence grounds necessity): whatever lies in a being's nature holds at
every world accessible from `w`. Accepted by conditional and unconditional
essentialists alike. -/
def EssenceGroundsNecessity (F : CausalityFrame W B T R) (w : W)
    (Essential : B → (W → Prop) → Prop) : Prop :=
  ∀ x φ, Essential x φ → ∀ v, F.history.ontic.frame.access w v → φ v

/-- OPEN (unconditional essentialism's reading of esse = essence): whatever has
its represented esse equal to its represented essence has its own existence in
its nature (Lowe-style necessary existents; navigation only). The bridge of
the essentialist B6 route; existence-conditional essentialism cannot accept it
when the being's absence is representable (`Model.Laws`, 3). -/
def EsseEssenceIsEssentialExistence (F : CausalityFrame W B T R) (essenceOf esseOf : B → P)
    (Essential : B → (W → Prop) → Prop) : Prop :=
  ∀ x, esseOf x = essenceOf x → Essential x (fun v => F.history.ontic.ExistsAt v x)

/-- OPEN (existence-conditional essentialism, Fine/Lowe reading): every
essential truth about `x` holds at every point where `x` is absent, that is, it
has the form "if `x` exists, …". -/
def ExistenceConditionalEssences (F : CausalityFrame W B T R)
    (Essential : B → (W → Prop) → Prop) : Prop :=
  ∀ x φ, Essential x φ → ∀ v, ¬ F.history.ontic.ExistsAt v x → φ v

/-- OPEN (essentialist account of possibility of absence): a being existing at
`w` whose existence is entailed by no being's essential truth is absent at some
world accessible from `w`. The non-power ground of de re possibility (ACT-06 of
`docs/modal-ontology-120.md`). -/
def EssentialExclusionAccount (F : CausalityFrame W B T R) (w : W)
    (Essential : B → (W → Prop) → Prop) : Prop :=
  ∀ x, F.history.ontic.ExistsAt w x → (∀ y φ, Essential y φ → ¬ EntailsExistence F φ x) →
    ∃ v, F.history.ontic.frame.access w v ∧ ¬ F.history.ontic.ExistsAt v x

/-- OPEN: no other being's essential truth entails the existence of a being
foundational at `w`. The foundational being has nothing prior to it; this
clause states the corresponding essentialist fact separately, since firstness
in SIMPLY_PRIOR_1 does not by itself say anything about essences. -/
def FoundationalExistenceUnrequiredByOthers (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop)
    (Essential : B → (W → Prop) → Prop) : Prop :=
  ∀ f, FoundationalAt F w essenceOf esseOf Received ComposedOfMatterAndForm CanFailToBe
    PowerOver f → ∀ y φ, y ≠ f → Essential y φ → ¬ EntailsExistence F φ f

/-- OPEN: for each being foundational at `w`, some point of the frame's world
type lacks it (its absence is representable in the logical space, whether or
not that point is accessible). -/
def FoundationalAbsenceRepresentable (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) : Prop :=
  ∀ f, FoundationalAt F w essenceOf esseOf Received ComposedOfMatterAndForm CanFailToBe
    PowerOver f → ∃ v, ¬ F.history.ontic.ExistsAt v f

/-! ## Pruss's Aristotelian-modality argument (analyst reconstruction)

`PowerFor : W → B → (W → Prop) → Prop` is a stated primitive: `PowerFor w y p`
says that at `w`, `y` has a power whose exercise would initiate a causal chain
issuing in `p` obtaining. Examples: a match's power to start a fire; a
sculptor's power to bring it about that a statue exists. Non-examples: the bare
logical possibility of `p`; a power whose exercise could not issue in `p` (a
match's power to make it the case that two plus two is five). Distinct from
POWER_OVER_ESSE_1 (power over one individual's being: `PowerFor` targets a
proposition, possibly a global one) and from CAUSE_2 (no exercise is implied).
Structural properties assumed: none. -/

/-- No concrete being is contingent at `v`. The meaning of the existing
DEF-NO-CONTINGENT-CONCRETE-AT (`EmptyHistoryCausalAvailability.NoContingentConcreteAt`),
restated on the shared frame's own `Ontic`, because that definition is typed on
a fact `Arena` that this frame does not carry. It permits an empty world and
necessary concreta. -/
def NoContingentConcreteIn (F : CausalityFrame W B T R) (concrete : B → Prop) (v : W) :
    Prop :=
  ∀ x, concrete x → ¬ ContingentAt F.history.ontic v x

/-- Aristotelian grounding for `p` at `w`: if `p` holds at some accessible world
and not at `w`, some being existing at `w` has, at `w`, a power for `p`. -/
def AristotelianGroundingFor (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (w : W) (p : W → Prop) : Prop :=
  (∃ v, F.history.ontic.frame.access w v ∧ p v) → ¬ p w →
    ∃ y, F.history.ontic.ExistsAt w y ∧ PowerFor w y p

/-- Initiator presence for `p` at `w`: a power at `w` for `p` can be exercised so
that `p` obtains at some accessible world at which its holder exists. With the
frame's tenseless world-relative existence, the initiator of a chain exists in
the world of that chain. -/
def InitiatorPresentFor (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (w : W) (p : W → Prop) : Prop :=
  ∀ y, PowerFor w y p →
    ∃ v, F.history.ontic.frame.access w v ∧ p v ∧ F.history.ontic.ExistsAt v y

/-- Holders of a power at `w` for `p` are concrete. -/
def PowerHoldersConcreteFor (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop)
    (w : W) (p : W → Prop) : Prop :=
  ∀ y, PowerFor w y p → concrete y

/-- OPEN (P1, Aristotelian grounding of the global possibility): if possibly no
concrete being is contingent, and some concrete being is contingent at `w`,
then some being existing at `w` has a power for there being no contingent
concrete being. -/
def GlobalAbsenceGrounded (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (concrete : B → Prop) (w : W) : Prop :=
  AristotelianGroundingFor F PowerFor w (NoContingentConcreteIn F concrete)

/-- OPEN (P2, initiator presence for the global possibility). -/
def GlobalAbsenceInitiatorPresent (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  InitiatorPresentFor F PowerFor w (NoContingentConcreteIn F concrete)

/-- OPEN (P3): holders of a power for the global possibility are concrete. -/
def GlobalAbsencePowerHoldersConcrete (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  PowerHoldersConcreteFor PowerFor concrete w (NoContingentConcreteIn F concrete)

/-- OPEN (P4, the global possibility premise): some world accessible from `w`
has no contingent concrete being. -/
def PossiblyNoContingentConcrete (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W) :
    Prop :=
  ∃ v, F.history.ontic.frame.access w v ∧ NoContingentConcreteIn F concrete v

/-- OPEN (P5): some concrete being is contingent at `w`. -/
def SomeContingentConcreteAt (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W) :
    Prop :=
  ∃ x, concrete x ∧ ContingentAt F.history.ontic w x

/-- Conclusion: some concrete being exists at `w`, exists at every world
accessible from `w`, and has at `w` a power for there being no contingent
concrete being. No uniqueness, simplicity, firstness or God is asserted. -/
def NecessaryConcreteGlobalAbsencePowerAt (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∃ y, concrete y ∧ F.history.ontic.ExistsAt w y ∧ NecessaryAt F.history.ontic w y ∧
    PowerFor w y (NoContingentConcreteIn F concrete)

/-- OPEN transfer bridge, used only in `Model.Laws`: a power at `w` for the
global possibility is a power over the esse (POWER_OVER_ESSE_1) of every
concrete being absent at every accessible world where that possibility holds. -/
def GlobalAbsencePowerIsPowerOverEsse (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (PowerOver : B → B → R → Prop)
    (concrete : B → Prop) (w : W) : Prop :=
  ∀ y x, PowerFor w y (NoContingentConcreteIn F concrete) → concrete x →
    (∀ v, F.history.ontic.frame.access w v → NoContingentConcreteIn F concrete v →
      ¬ F.history.ontic.ExistsAt v x) →
    PowerOverEsse F PowerOver y x

/-! ## The hybrid's restriction of PGP

The hybrid keeps power-grounding where there is a subject for the power to
work on (matter, or a principle receiving esse: `ExistentiallyReceptive` of
the C2 batch) and drops it for subjectless beings. With excluded middle PGP is
exactly the conjunction of the two halves (`Model.Laws`, 11). -/

/-- OPEN (the hybrid's half of PGP): every being contingent at `w` that is
existentially receptive (received esse in a receptive principle, or matter and
form) is corruptible simply or under some being's power over its esse. -/
def PowerGroundedForSubjects (F : CausalityFrame W B T R) (w : W) (esseOf : B → P)
    (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    TruthCore.Causality.ContingencyGrounding.ExistentiallyReceptive esseOf Received
      ReceptivePotencyTo ComposedOfMatterAndForm x →
    CanFailToBe x F.esse ∨ ∃ y, PowerOverEsse F PowerOver y x

/-- OPEN (the half the hybrid rejects): every being contingent at `w` that is
not existentially receptive is corruptible simply or under some being's power
over its esse. -/
def PowerGroundedForSubjectless (F : CausalityFrame W B T R) (w : W) (esseOf : B → P)
    (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    ¬ TruthCore.Causality.ContingencyGrounding.ExistentiallyReceptive esseOf Received
      ReceptivePotencyTo ComposedOfMatterAndForm x →
    CanFailToBe x F.esse ∨ ∃ y, PowerOverEsse F PowerOver y x

/-! ## Laws and finite models -/

namespace Model

open TruthCore.Causality.FirstMoverNecessity (groundProfile MoversExistAt ContingentHasDistinctEsse
  PossibleNonexistenceIsPotency)
open TruthCore.Causality.FirstMoverNecessity.Model (mk bruteFirst movedIn movedPotency noCause
  noPrior receivedNone esseTrue essenceByBeing noneHolds fContingent receptivePotency)
open TruthCore.Causality.ContingencyGrounding (PowerOverEsseCorrelation
  ContingentReceptiveOrReceivedFromPrior FirstUnmovedMoverUnreceived
  CorruptibleIsExistentiallyReceptive)
open TruthCore.Causality.ContingencyGrounding.Model (heatFail noPower fPowerX xCorruptible
  xComposite)
open TruthCore.Causality.EsseCausePriority (DistinctEsseCausePriority)
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing)
open TruthCore.Modern.Hume.Conceivability (Conception StrongBridge)
open TruthCore.Isabelle.AFP.GoedelGod (Box)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover)
open TruthCore.Causality.SubtractionArgument (UnrestrictedRecombinationAt ConcreteCompanionsAt
  PossiblyNoConcrete EachConcreteCouldFailAt)
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt InhabitedAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct MovedOnlyAsInPotencyReading)
open TruthCore.Case.Catholicism (ThereIsAFirstUnmovedMover FirstUnmovedMoverIsFirstBeing
  FirstUnmovedMoverIsPureAct)

/-- General laws.
1. Correlation, an uncaused esse and simple incorruptibility exclude any power
   over a being's esse: under correlation the profile's no-power clause is
   redundant.
2. PGP, unrestricted recombination and companions at `w` exclude any concrete
   foundational being at `w` (constructive: recombination itself supplies the
   foundational being's possible absence).
3. Existence-conditional essentialism excludes unconditional essentialism's
   reading of esse = essence for any being with esse = essence whose absence is
   representable.
4. Under existence-conditional essentialism, no essential truth of `x` entails
   `x`'s existence once its absence is representable: `x`'s own nature cannot
   make it necessary, whatever its esse and essence.
5. Pruss's premises P1 and P4, with a Euclidean frame and the transfer bridge,
   put every concrete being contingent at `w` under some being's power over its
   esse (PGP's power channel, for concreta). Constructive.
6. With the same premises every concrete foundational being at `w` is
   necessary: Pruss's grounding with the transfer bridge reproduces PGP's
   verdict at the foundational case.
7. Aristotelian grounding of the possibility that nothing concrete exists, with
   initiator presence and concrete power-holders, excludes that possibility
   wherever something concrete actually exists: it contradicts the subtraction
   conclusion.
8. The subtraction conclusion gives Pruss's possibility premise P4.
9. Conceivability parity (#1887 F1): on a Euclidean frame, #248's unrestricted
   `StrongBridge` cannot take both the conceived necessary existence of `n` and
   its conceived absence: the first gives an accessible world where `n` is
   necessary, the second an accessible world lacking `n`, and Euclidean access
   joins them.
10. PGP's "lack of power" at the first mover (#1887 F3): unreceivedness,
    firstness, correlation, passive→receptive, no self-esse-cause and B3 make
    the first unmoved mover incorruptible simply and put it under no being's
    power over its esse (constructively); with PGP and excluded middle it is
    then necessary if it exists at `w`. The neededness of correlation and of
    no self-esse-cause is shown by the C2 batch's `selfAnnihilator` variants.
11. The hybrid's restriction (#1887 F2): with excluded middle, PGP is exactly
    its subject half together with its subjectless half. -/
def Laws : Prop :=
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop) (f : B),
    PowerOverEsseCorrelation F CanFailToBe PowerOver → (∀ c, ¬ F.CausesIn c f F.esse) →
    IncorruptibleSimply CanFailToBe F.esse f → ∀ y, ¬ PowerOverEsse F PowerOver y f) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (essenceOf esseOf : B → P)
    (Received : B → P → Prop) (MF : B → Prop) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop),
    ContingencyPowerGrounded F w CanFailToBe PowerOver →
    UnrestrictedRecombinationAt (groundProfile F concrete grounds) w →
    ConcreteCompanionsAt (groundProfile F concrete grounds) w →
    ¬ SomeConcreteFoundationalAt F w essenceOf esseOf Received MF CanFailToBe PowerOver
      concrete) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (essenceOf esseOf : B → P)
    (Essential : B → (W → Prop) → Prop) (x : B),
    ExistenceConditionalEssences F Essential →
    EsseEssenceIsEssentialExistence F essenceOf esseOf Essential →
    esseOf x = essenceOf x → (∃ v, ¬ F.history.ontic.ExistsAt v x) → False) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (Essential : B → (W → Prop) → Prop) (x : B),
    ExistenceConditionalEssences F Essential → (∃ v, ¬ F.history.ontic.ExistsAt v x) →
    ∀ φ, Essential x φ → ¬ EntailsExistence F φ x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W)
    (PowerFor : W → B → (W → Prop) → Prop) (PowerOver : B → B → R → Prop)
    (concrete : B → Prop),
    TruthCore.Modal.Euclidean F.history.ontic.frame →
    GlobalAbsenceGrounded F PowerFor concrete w → PossiblyNoContingentConcrete F concrete w →
    GlobalAbsencePowerIsPowerOverEsse F PowerFor PowerOver concrete w →
    ∀ x, concrete x → ContingentAt F.history.ontic w x → ∃ y, PowerOverEsse F PowerOver y x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (essenceOf esseOf : B → P)
    (Received : B → P → Prop) (MF : B → Prop) (CanFailToBe : B → R → Prop)
    (PowerFor : W → B → (W → Prop) → Prop) (PowerOver : B → B → R → Prop)
    (concrete : B → Prop),
    TruthCore.Logic.ExcludedMiddle → TruthCore.Modal.Euclidean F.history.ontic.frame →
    GlobalAbsenceGrounded F PowerFor concrete w → PossiblyNoContingentConcrete F concrete w →
    GlobalAbsencePowerIsPowerOverEsse F PowerFor PowerOver concrete w →
    ∀ f, concrete f → FoundationalAt F w essenceOf esseOf Received MF CanFailToBe PowerOver f →
      NecessaryAt F.history.ontic w f) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop),
    AristotelianGroundingFor F PowerFor w
      (fun v => ¬ ∃ x, concrete x ∧ F.history.ontic.ExistsAt v x) →
    InitiatorPresentFor F PowerFor w
      (fun v => ¬ ∃ x, concrete x ∧ F.history.ontic.ExistsAt v x) →
    PowerHoldersConcreteFor PowerFor concrete w
      (fun v => ¬ ∃ x, concrete x ∧ F.history.ontic.ExistsAt v x) →
    InhabitedAt (groundProfile F concrete grounds) w →
    ¬ PossiblyNoConcrete (groundProfile F concrete grounds) w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (concrete : B → Prop)
    (grounds : W → B → B → Prop),
    PossiblyNoConcrete (groundProfile F concrete grounds) w →
    PossiblyNoContingentConcrete F concrete w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (C : Conception W) (w : W) (n : B),
    TruthCore.Modal.Euclidean F.history.ontic.frame →
    StrongBridge F.history.ontic.frame C w →
    C (Box F.history.ontic.frame (fun v => F.history.ontic.ExistsAt v n)) w →
    C (fun v => ¬ F.history.ontic.ExistsAt v n) w → False) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (MovedIn : B → R → Prop)
    (esseOf : B → P) (Received : B → P → Prop) (RP : P → P → Prop) (MF : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) (f : B),
    TruthCore.Logic.ExcludedMiddle →
    IsFirstUnmovedMover MovedIn F.MovesIn f →
    FirstUnmovedMoverUnreceived MovedIn F.MovesIn Received MF →
    FirstUnmovedMoverIsFirstBeing MovedIn F.MovesIn F.PriorSimply →
    ContingencyPowerGrounded F w CanFailToBe PowerOver →
    PowerOverEsseCorrelation F CanFailToBe PowerOver →
    CorruptibleIsExistentiallyReceptive F CanFailToBe esseOf Received RP MF →
    NothingCausesItsOwnBeing F.CausesIn F.esse →
    DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply →
    IncorruptibleSimply CanFailToBe F.esse f ∧ (∀ y, ¬ PowerOverEsse F PowerOver y f) ∧
      (F.history.ontic.ExistsAt w f → NecessaryAt F.history.ontic w f)) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (w : W) (esseOf : B → P)
    (Received : B → P → Prop) (RP : P → P → Prop) (MF : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop),
    TruthCore.Logic.ExcludedMiddle →
    (ContingencyPowerGrounded F w CanFailToBe PowerOver ↔
      PowerGroundedForSubjects F w esseOf Received RP MF CanFailToBe PowerOver ∧
        PowerGroundedForSubjectless F w esseOf Received RP MF CanFailToBe PowerOver))

/-! ### Model ingredients

Beings are `Bool`: `true` is the foundational candidate (the First Way's mover
`f`, or God `g`), `false` a second being (the moved thing `x`, or a creature
`c`). Respects are `Bool` with `true` the respect of being. `true` moves
`false` in the respect of motion, as in `FirstMoverNecessity.Model.mk`, but the
world type and accessibility are free. -/

/-- A finite frame on any world type, with stated accessibility and existence;
otherwise as `FirstMoverNecessity.Model.mk`. -/
def frameOn {W : Type} (acc : W → W → Prop) (ex : W → Bool → Prop)
    (causes : Bool → Bool → Bool → Prop) (prior : Bool → Bool → Prop) :
    CausalityFrame W Bool Unit Bool where
  history := ⟨⟨⟨acc⟩, ex, fun _ _ _ => False⟩, fun _ _ _ => False, ()⟩
  GivesAt := fun _ _ _ _ => False
  CausesIn := causes
  MovesIn := fun y x r => y = true ∧ x = false ∧ r = false
  DependsForBeing := fun _ _ => False
  PriorSimply := prior
  esse := true

/-- Every candidate counts as concrete. -/
def allConcrete (_ : Bool) : Prop := True

/-- Only `false` (the creature) is concrete: `true` is a non-concrete holder. -/
def onlyFalseConcrete (b : Bool) : Prop := b = false

/-- Every relation and world of the selected-grounding profile, unused. -/
def noGrounds {W : Type} (_ : W) (_ _ : Bool) : Prop := False

/-- Access to `true` only, from every world. -/
def toTrue (_ v : Bool) : Prop := v = true

/-- Universal access on `Bool`. -/
def univ (_ _ : Bool) : Prop := True

/-- `true` exists only at world `true`; `false` exists nowhere. -/
def onlyFHere (v b : Bool) : Prop := b = true ∧ v = true

/-- Both candidates exist only at world `true`. -/
def bothHere (v _ : Bool) : Prop := v = true

/-- `true` exists everywhere; `false` nowhere. -/
def onlyFEverywhere (_ b : Bool) : Prop := b = true

/-- God `true` exists at both worlds; the creature `false` at world `true` only. -/
def theistEx (v b : Bool) : Prop := b = true ∨ v = true

/-- `false` exists at world `true` only; `true` exists nowhere. -/
def creatureOnly (v b : Bool) : Prop := b = false ∧ v = true

/-- Each world has a different contingent being: `false` at `true`, `true` at
`false`. -/
def swapped (v b : Bool) : Prop := (b = false ∧ v = true) ∨ (b = true ∧ v = false)

/-- Nothing exists anywhere. -/
def nothing (_ _ : Bool) : Prop := False

/-- `true` causes the esse of `false`. -/
def gCausesC (c y r : Bool) : Prop := c = true ∧ y = false ∧ r = true

/-- `true` is simply prior to `false`. -/
def gPriorC (c y : Bool) : Prop := c = true ∧ y = false

/-- `holder` has, at every world, a power for every proposition (a structural
surrogate: the models below only use the global proposition). -/
def powerBy (holder : Bool) {W : Type} (_ : W) (y : Bool) (_ : W → Prop) : Prop := y = holder

/-- No power for anything. -/
def noPowerFor {W : Type} (_ : W) (_ : Bool) (_ : W → Prop) : Prop := False

/-- No essential truths. -/
def noEssence {W : Type} (_ : Bool) (_ : W → Prop) : Prop := False

/-- `true`'s nature includes its existence, unconditionally: its one essential
truth is the proposition true exactly where `true` exists. -/
def fEssentialExistence {W : Type} (F : CausalityFrame W Bool Unit Bool) (x : Bool)
    (φ : W → Prop) : Prop :=
  x = true ∧ φ = fun v => F.history.ontic.ExistsAt v true

/-- `true`'s nature includes its existence only conditionally ("if it exists,
it exists"). -/
def fConditionalExistence {W : Type} (F : CausalityFrame W Bool Unit Bool) (x : Bool)
    (φ : W → Prop) : Prop :=
  x = true ∧ φ = fun v => F.history.ontic.ExistsAt v true → F.history.ontic.ExistsAt v true

/-- `false`'s nature requires `true`'s existence, conditionally on its own:
"if `false` exists, `true` exists". -/
def otherRequiresF {W : Type} (F : CausalityFrame W Bool Unit Bool) (x : Bool)
    (φ : W → Prop) : Prop :=
  x = false ∧ φ = fun v => F.history.ontic.ExistsAt v false → F.history.ontic.ExistsAt v true

/-- The foundational profile of `true` on a frame of this family: identity
essence map, one esse-principle, nothing received, no matter and form, `true`
not corruptible simply. -/
abbrev FoundationalF {W : Type} (F : CausalityFrame W Bool Unit Bool) (w : W)
    (PowerOver : Bool → Bool → Bool → Prop) : Prop :=
  FoundationalAt F w essenceByBeing esseTrue receivedNone noneHolds heatFail PowerOver true

/-! ### Frames -/

/-- God necessary, one contingent creature, God causes and is prior to the
creature's esse; universal access. -/
def theistFrame : CausalityFrame Bool Bool Unit Bool := frameOn univ theistEx gCausesC gPriorC

/-- God necessary and the creature contingent, with no esse-causation. -/
def theistNoCauseFrame : CausalityFrame Bool Bool Unit Bool := frameOn univ theistEx noCause noPrior

/-- Access only to `true`; `true` exists only there. -/
def lockedF : CausalityFrame Bool Bool Unit Bool := frameOn toTrue onlyFHere noCause noPrior

/-- Universal access; both beings exist only at world `true`. -/
def bothContingent : CausalityFrame Bool Bool Unit Bool := frameOn univ bothHere noCause noPrior

/-- Universal access; `true` everywhere, `false` nowhere. -/
def fEverywhere : CausalityFrame Bool Bool Unit Bool := frameOn univ onlyFEverywhere noCause noPrior

/-- Access only to `true`; `false` everywhere, `true` only at world `true`
(`fContingent`'s existence pattern). -/
def lockedRequired : CausalityFrame Bool Bool Unit Bool := frameOn toTrue fContingent noCause noPrior

/-- `true` necessary, `false` absent everywhere: `fEverywhere` with both
candidates' existence fixed by world; used as the primitivist "necessary" twin. -/
def primitivistNecessary : CausalityFrame Bool Bool Unit Bool := fEverywhere

/-- `true` contingent: the primitivist "contingent" twin (`true` exists only at
world `true`; `false` nowhere). -/
def primitivistContingent : CausalityFrame Bool Bool Unit Bool := frameOn univ onlyFHere noCause noPrior

/-- Only the creature, contingent; universal access. -/
def creatureFrame : CausalityFrame Bool Bool Unit Bool := frameOn univ creatureOnly noCause noPrior

/-- Two contingent beings, one at each world; universal access. -/
def swappedFrame : CausalityFrame Bool Bool Unit Bool := frameOn univ swapped noCause noPrior

/-- Nothing exists; universal access. -/
def emptyFrame : CausalityFrame Bool Bool Unit Bool := frameOn univ nothing noCause noPrior

/-- Three worlds for the Euclidean omission. -/
inductive Pt where
  | a
  | b
  | c
  deriving DecidableEq

/-- `a → b`, `a → c`, `b → b`: not Euclidean (`b` does not reach `c`). -/
def ptAccess (u v : Pt) : Prop := (u = .a ∧ v = .b) ∨ (u = .a ∧ v = .c) ∨ (u = .b ∧ v = .b)

/-- `true` exists at `a` and `b`; `false` exists at `a` only. -/
def ptEx (v : Pt) (x : Bool) : Prop := (x = true ∧ v ≠ .c) ∨ (x = false ∧ v = .a)

/-- The Euclidean-omission frame. -/
def nonEuclidean : CausalityFrame Pt Bool Unit Bool := frameOn ptAccess ptEx noCause noPrior

/-- Full combinatorial worlds: a world is a pair (does `true` exist, does
`false` exist). -/
def comboEx (v : Bool × Bool) (x : Bool) : Prop :=
  (x = true ∧ v.1 = true) ∨ (x = false ∧ v.2 = true)

/-- The hybrid frame: every combination of the two beings' existence is a
world, all mutually accessible; reading world `(true, true)`. -/
def comboFrame : CausalityFrame (Bool × Bool) Bool Unit Bool :=
  frameOn (fun _ _ => True) comboEx noCause noPrior

/-! ### Models -/

/-- **theist** (nonvacuity; frame `theistFrame`): God `true` is foundational at
`true`, necessary, has its existence in its nature, power over and causes the
creature's esse and has a power for the global possibility; the creature
`false` is contingent. PGP, correlation, both essentialist premises, B6,
every Pruss premise, the transfer bridge, both verdict-level conclusions and
the stage-one node hold. Admissible on classical theism. -/
def TheistModel : Prop :=
  FoundationalF theistFrame true fPowerX ∧
  SomeConcreteFoundationalAt theistFrame true essenceByBeing esseTrue receivedNone noneHolds
    heatFail fPowerX allConcrete ∧
  ContingencyPowerGrounded theistFrame true heatFail fPowerX ∧
  PowerOverEsseCorrelation theistFrame heatFail fPowerX ∧
  FoundationalBeingsNecessaryAt theistFrame true essenceByBeing esseTrue receivedNone noneHolds
    heatFail fPowerX ∧
  EssenceGroundsNecessity theistFrame true (fEssentialExistence theistFrame) ∧
  EsseEssenceIsEssentialExistence theistFrame essenceByBeing esseTrue
    (fEssentialExistence theistFrame) ∧
  ContingentHasDistinctEsse theistFrame true essenceByBeing esseTrue ∧
  TruthCore.Modal.Euclidean theistFrame.history.ontic.frame ∧
  GlobalAbsenceGrounded theistFrame (powerBy true) allConcrete true ∧
  GlobalAbsenceInitiatorPresent theistFrame (powerBy true) allConcrete true ∧
  GlobalAbsencePowerHoldersConcrete theistFrame (powerBy true) allConcrete true ∧
  PossiblyNoContingentConcrete theistFrame allConcrete true ∧
  SomeContingentConcreteAt theistFrame allConcrete true ∧
  GlobalAbsencePowerIsPowerOverEsse theistFrame (powerBy true) fPowerX allConcrete true ∧
  NecessaryConcreteGlobalAbsencePowerAt theistFrame (powerBy true) allConcrete true ∧
  NecessaryConcreteAt (groundProfile theistFrame allConcrete noGrounds) true

/-- **prussWithoutPGP** (test 5 independence; frame `theistNoCauseFrame`): God
`true` is necessary and has a power for the global possibility, but no being
has power over the creature's esse, nothing causes it and it is incorruptible
simply. Every Pruss premise and the Pruss conclusion hold while PGP, C2 (no
receptivity, no prior esse-cause) and the transfer bridge fail. So the Pruss
route needs neither PGP nor C2. Structural: on classical theism the creature
would be under God's power over its esse (the transfer bridge), so this model
separates the premise sets, it does not exhibit a theist-admissible world. -/
def PrussWithoutPGPModel : Prop :=
  TruthCore.Modal.Euclidean theistNoCauseFrame.history.ontic.frame ∧
  GlobalAbsenceGrounded theistNoCauseFrame (powerBy true) allConcrete true ∧
  GlobalAbsenceInitiatorPresent theistNoCauseFrame (powerBy true) allConcrete true ∧
  GlobalAbsencePowerHoldersConcrete theistNoCauseFrame (powerBy true) allConcrete true ∧
  PossiblyNoContingentConcrete theistNoCauseFrame allConcrete true ∧
  SomeContingentConcreteAt theistNoCauseFrame allConcrete true ∧
  NecessaryConcreteGlobalAbsencePowerAt theistNoCauseFrame (powerBy true) allConcrete true ∧
  ¬ ContingencyPowerGrounded theistNoCauseFrame true heatFail noPower ∧
  ¬ ContingentReceptiveOrReceivedFromPrior theistNoCauseFrame true esseTrue receivedNone
    (fun _ _ => False) noneHolds ∧
  ¬ GlobalAbsencePowerIsPowerOverEsse theistNoCauseFrame (powerBy true) noPower allConcrete true

/-- **bruteFoundational** (frame `bruteFirst`): the First Way's mover `true` is
foundational at `true` and contingent; every concrete candidate counts. PGP,
B6 and the necessity verdict fail while the existence premise holds: the
omission model of PGP in the PGP argument and of B6 in the esse-identity
argument. With `fEssentialExistence` the unconditional bridge holds and
essence-grounds-necessity fails; with no essences the converse. Admissible on
a hybrid, primitivist, combinatorial or existence-conditional essentialist
modal metaphysics (the C2 note's `bruteSimple`). -/
def BruteFoundationalModel : Prop :=
  FoundationalF bruteFirst true noPower ∧
  ContingentAt bruteFirst.history.ontic true true ∧
  SomeConcreteFoundationalAt bruteFirst true essenceByBeing esseTrue receivedNone noneHolds
    heatFail noPower allConcrete ∧
  ¬ ContingencyPowerGrounded bruteFirst true heatFail noPower ∧
  ¬ ContingentHasDistinctEsse bruteFirst true essenceByBeing esseTrue ∧
  ¬ FoundationalBeingsNecessaryAt bruteFirst true essenceByBeing esseTrue receivedNone noneHolds
    heatFail noPower ∧
  (EsseEssenceIsEssentialExistence bruteFirst essenceByBeing esseTrue
      (fEssentialExistence bruteFirst) ∧
    ¬ EssenceGroundsNecessity bruteFirst true (fEssentialExistence bruteFirst)) ∧
  (EssenceGroundsNecessity bruteFirst true noEssence ∧
    ¬ EsseEssenceIsEssentialExistence bruteFirst essenceByBeing esseTrue noEssence)

/-- **conditionalEssence** (nonvacuity of the existence-conditional verdict;
frame `bothContingent`): `true` is foundational at `true` with esse equal to
essence, its nature includes its existence only conditionally, and it is
contingent. Existence-conditional essences, the essentialist account of
possibility, the two foundational essence clauses and the "possibly absent"
verdict hold; unconditional essentialism's bridge fails. Admissible on a
Fine/Lowe existence-conditional essentialism with a contingent simple first
being. -/
def ConditionalEssenceModel : Prop :=
  FoundationalF bothContingent true noPower ∧
  ExistenceConditionalEssences bothContingent (fConditionalExistence bothContingent) ∧
  EssentialExclusionAccount bothContingent true (fConditionalExistence bothContingent) ∧
  FoundationalExistenceUnrequiredByOthers bothContingent true essenceByBeing esseTrue
    receivedNone noneHolds heatFail noPower (fConditionalExistence bothContingent) ∧
  FoundationalAbsenceRepresentable bothContingent true essenceByBeing esseTrue receivedNone
    noneHolds heatFail noPower ∧
  FoundationalBeingsContingentAt bothContingent true essenceByBeing esseTrue receivedNone
    noneHolds heatFail noPower ∧
  ¬ EsseEssenceIsEssentialExistence bothContingent essenceByBeing esseTrue
    (fConditionalExistence bothContingent)

/-- Omission models of the existence-conditional argument, each with `true`
foundational at `true` and the "possibly absent" verdict failing:
1. conditional essences omitted (frame `lockedF`, `true`'s nature includes its
   existence unconditionally);
2. the essentialist account omitted (frame `lockedF`, no essences: `true` is
   necessary with no essential ground);
3. unrequired-by-others omitted (frame `lockedRequired`, `false`'s nature
   requires `true`'s existence conditionally on its own);
4. representability omitted (frame `fEverywhere`, unconditional essence, no
   point lacks `true`). -/
def ConditionalEssenceOmissions : Prop :=
  (FoundationalF lockedF true noPower ∧
    ¬ ExistenceConditionalEssences lockedF (fEssentialExistence lockedF) ∧
    EssentialExclusionAccount lockedF true (fEssentialExistence lockedF) ∧
    FoundationalExistenceUnrequiredByOthers lockedF true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower (fEssentialExistence lockedF) ∧
    FoundationalAbsenceRepresentable lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower ∧
    ¬ FoundationalBeingsContingentAt lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower) ∧
  (FoundationalF lockedF true noPower ∧
    ExistenceConditionalEssences lockedF noEssence ∧
    ¬ EssentialExclusionAccount lockedF true noEssence ∧
    FoundationalExistenceUnrequiredByOthers lockedF true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower noEssence ∧
    FoundationalAbsenceRepresentable lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower ∧
    ¬ FoundationalBeingsContingentAt lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower) ∧
  (FoundationalF lockedRequired true noPower ∧
    ExistenceConditionalEssences lockedRequired (otherRequiresF lockedRequired) ∧
    EssentialExclusionAccount lockedRequired true (otherRequiresF lockedRequired) ∧
    ¬ FoundationalExistenceUnrequiredByOthers lockedRequired true essenceByBeing esseTrue
      receivedNone noneHolds heatFail noPower (otherRequiresF lockedRequired) ∧
    FoundationalAbsenceRepresentable lockedRequired true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower ∧
    ¬ FoundationalBeingsContingentAt lockedRequired true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower) ∧
  (FoundationalF fEverywhere true noPower ∧
    ExistenceConditionalEssences fEverywhere (fEssentialExistence fEverywhere) ∧
    EssentialExclusionAccount fEverywhere true (fEssentialExistence fEverywhere) ∧
    FoundationalExistenceUnrequiredByOthers fEverywhere true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower (fEssentialExistence fEverywhere) ∧
    ¬ FoundationalAbsenceRepresentable fEverywhere true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower ∧
    ¬ FoundationalBeingsContingentAt fEverywhere true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower)

/-- **primitivistSilence**: two frames with the same accessibility, the same
non-modal facts at the reading world `true` (`true` foundational, moving
`false`, first, pure act) and no grounding constraint. In
`primitivistNecessary` `true` is necessary; in `primitivistContingent` it is
contingent. So the foundational profile, with no grounding principle, fixes
neither verdict: the primitivist's modal status of the foundational being is a
further primitive fact. In the contingent twin PGP fails; in the necessary twin
PGP holds (vacuously at `true`). -/
def PrimitivistSilence : Prop :=
  (FoundationalF primitivistNecessary true noPower ∧
    FoundationalBeingsNecessaryAt primitivistNecessary true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower ∧
    ContingencyPowerGrounded primitivistNecessary true heatFail noPower) ∧
  (FoundationalF primitivistContingent true noPower ∧
    FoundationalBeingsContingentAt primitivistContingent true essenceByBeing esseTrue
      receivedNone noneHolds heatFail noPower ∧
    ¬ ContingencyPowerGrounded primitivistContingent true heatFail noPower) ∧
  (PureAct movedPotency true ∧
    ThereIsAFirstUnmovedMover movedIn primitivistNecessary.MovesIn ∧
    ThereIsAFirstUnmovedMover movedIn primitivistContingent.MovesIn)

/-- **hybridFirstWay** (frame `comboFrame`, reading world `(true, true)`): the
First Way's act and potency premises (a first unmoved mover, B0, firstness,
pure act, and ST I q.2 a.3's "nothing is moved except as in potency": powers
and potency ground the possibilities of change) hold together with unrestricted
recombination and companions (existence-possibilities combinatorial), while the
first mover is foundational and contingent. The moved thing `false` is a
corruptible matter–form composite, so PGP's subject half holds nonvacuously;
its subjectless half, PGP itself, B4 and the necessity verdict fail. This
extends the C2 note's `bruteSimple` to a combinatorial hybrid and separates
the two halves of PGP (`Model.Laws`, 11). Admissible on the hybrid: powers for
change and for subjects, combinatorial modality for subjectless existence. -/
def HybridFirstWayModel : Prop :=
  ThereIsAFirstUnmovedMover movedIn comboFrame.MovesIn ∧
  MoversExistAt comboFrame (true, true) ∧
  FirstUnmovedMoverIsFirstBeing movedIn comboFrame.MovesIn comboFrame.PriorSimply ∧
  FirstUnmovedMoverIsPureAct movedIn comboFrame.MovesIn (PureAct movedPotency) ∧
  MovedOnlyAsInPotencyReading movedIn movedPotency ∧
  UnrestrictedRecombinationAt (groundProfile comboFrame allConcrete noGrounds) (true, true) ∧
  ConcreteCompanionsAt (groundProfile comboFrame allConcrete noGrounds) (true, true) ∧
  FoundationalAt comboFrame (true, true) essenceByBeing esseTrue receivedNone xComposite
    xCorruptible noPower true ∧
  ContingentAt comboFrame.history.ontic (true, true) true ∧
  PowerGroundedForSubjects comboFrame (true, true) esseTrue receivedNone receptivePotency
    xComposite xCorruptible noPower ∧
  ContingentAt comboFrame.history.ontic (true, true) false ∧ xCorruptible false comboFrame.esse ∧
  ¬ PowerGroundedForSubjectless comboFrame (true, true) esseTrue receivedNone receptivePotency
    xComposite xCorruptible noPower ∧
  ¬ ContingencyPowerGrounded comboFrame (true, true) xCorruptible noPower ∧
  ¬ PossibleNonexistenceIsPotency comboFrame movedPotency (true, true) ∧
  ¬ FoundationalBeingsNecessaryAt comboFrame (true, true) essenceByBeing esseTrue receivedNone
    xComposite xCorruptible noPower

/-- Conceiving exactly the absence of `n` (extensionally). -/
def conceiveAbsence {W : Type} (F : CausalityFrame W Bool Unit Bool) (n : Bool) :
    Conception W :=
  fun P _ => ∀ v, P v ↔ ¬ F.history.ontic.ExistsAt v n

/-- Conceiving exactly the necessary existence of `n` (extensionally). -/
def conceiveNecessity {W : Type} (F : CausalityFrame W Bool Unit Bool) (n : Bool) :
    Conception W :=
  fun P _ => ∀ v, P v ↔ Box F.history.ontic.frame (fun u => F.history.ontic.ExistsAt u n) v

/-- **conceivabilityOneSided** (#1887 F1): the unrestricted bridge with only
one of the two conceivings is satisfiable either way. On `primitivistContingent`
(universal, hence Euclidean) the bridge holds for a conceiver of `true`'s
absence only, and `true` is contingent; on `fEverywhere` the bridge holds for
a conceiver of `true`'s necessary existence only, and `true` is necessary. So
law 9's inconsistency needs both conceivings. -/
def ConceivabilityOneSided : Prop :=
  (TruthCore.Modal.Euclidean primitivistContingent.history.ontic.frame ∧
    StrongBridge primitivistContingent.history.ontic.frame
      (conceiveAbsence primitivistContingent true) true ∧
    conceiveAbsence primitivistContingent true
      (fun v => ¬ primitivistContingent.history.ontic.ExistsAt v true) true ∧
    ¬ conceiveAbsence primitivistContingent true
      (Box primitivistContingent.history.ontic.frame
        (fun v => primitivistContingent.history.ontic.ExistsAt v true)) true ∧
    ContingentAt primitivistContingent.history.ontic true true) ∧
  (TruthCore.Modal.Euclidean fEverywhere.history.ontic.frame ∧
    StrongBridge fEverywhere.history.ontic.frame (conceiveNecessity fEverywhere true) true ∧
    conceiveNecessity fEverywhere true
      (Box fEverywhere.history.ontic.frame (fun v => fEverywhere.history.ontic.ExistsAt v true))
      true ∧
    ¬ conceiveNecessity fEverywhere true
      (fun v => ¬ fEverywhere.history.ontic.ExistsAt v true) true ∧
    NecessaryAt fEverywhere.history.ontic true true)

/-- Omission models of the Pruss argument, each falsifying its conclusion while
the other premises hold (reading world `true`, or `Pt.a`):
1. grounding P1 omitted (frame `creatureFrame`, no powers);
2. initiator presence P2 omitted (frame `creatureFrame`, the contingent
   creature has the power: an all-annihilating contingent power-holder);
3. concrete holders P3 omitted (frame `theistFrame` with only the creature
   concrete: the necessary holder is not concrete);
4. possibility P4 omitted (frame `swappedFrame`, every world has a contingent
   being); here every actual concretum could fail to exist (S2 at `true`) while
   P4 fails: "each possibly absent" does not give "possibly all absent" (Van
   Cleve's point, navigation only), so P4 is an independent premise, not a
   consequence of the contingency of each actual concretum;
5. an actual contingent concretum P5 omitted (frame `emptyFrame`);
6. Euclidean access omitted (frame `nonEuclidean` at `Pt.a`: the holder is
   necessary at the contingent-free world `b` but absent at `c`).
Excluded middle is not omitted: every model is built in Lean, which is
consistent with it. -/
def PrussOmissions : Prop :=
  (TruthCore.Modal.Euclidean creatureFrame.history.ontic.frame ∧
    ¬ GlobalAbsenceGrounded creatureFrame noPowerFor allConcrete true ∧
    GlobalAbsenceInitiatorPresent creatureFrame noPowerFor allConcrete true ∧
    GlobalAbsencePowerHoldersConcrete creatureFrame noPowerFor allConcrete true ∧
    PossiblyNoContingentConcrete creatureFrame allConcrete true ∧
    SomeContingentConcreteAt creatureFrame allConcrete true ∧
    ¬ NecessaryConcreteGlobalAbsencePowerAt creatureFrame noPowerFor allConcrete true) ∧
  (TruthCore.Modal.Euclidean creatureFrame.history.ontic.frame ∧
    GlobalAbsenceGrounded creatureFrame (powerBy false) allConcrete true ∧
    ¬ GlobalAbsenceInitiatorPresent creatureFrame (powerBy false) allConcrete true ∧
    GlobalAbsencePowerHoldersConcrete creatureFrame (powerBy false) allConcrete true ∧
    PossiblyNoContingentConcrete creatureFrame allConcrete true ∧
    SomeContingentConcreteAt creatureFrame allConcrete true ∧
    ¬ NecessaryConcreteGlobalAbsencePowerAt creatureFrame (powerBy false) allConcrete true) ∧
  (TruthCore.Modal.Euclidean theistFrame.history.ontic.frame ∧
    GlobalAbsenceGrounded theistFrame (powerBy true) onlyFalseConcrete true ∧
    GlobalAbsenceInitiatorPresent theistFrame (powerBy true) onlyFalseConcrete true ∧
    ¬ GlobalAbsencePowerHoldersConcrete theistFrame (powerBy true) onlyFalseConcrete true ∧
    PossiblyNoContingentConcrete theistFrame onlyFalseConcrete true ∧
    SomeContingentConcreteAt theistFrame onlyFalseConcrete true ∧
    ¬ NecessaryConcreteGlobalAbsencePowerAt theistFrame (powerBy true) onlyFalseConcrete true) ∧
  (TruthCore.Modal.Euclidean swappedFrame.history.ontic.frame ∧
    GlobalAbsenceGrounded swappedFrame noPowerFor allConcrete true ∧
    GlobalAbsenceInitiatorPresent swappedFrame noPowerFor allConcrete true ∧
    GlobalAbsencePowerHoldersConcrete swappedFrame noPowerFor allConcrete true ∧
    ¬ PossiblyNoContingentConcrete swappedFrame allConcrete true ∧
    EachConcreteCouldFailAt (groundProfile swappedFrame allConcrete noGrounds) true ∧
    SomeContingentConcreteAt swappedFrame allConcrete true ∧
    ¬ NecessaryConcreteGlobalAbsencePowerAt swappedFrame noPowerFor allConcrete true) ∧
  (TruthCore.Modal.Euclidean emptyFrame.history.ontic.frame ∧
    GlobalAbsenceGrounded emptyFrame noPowerFor allConcrete true ∧
    GlobalAbsenceInitiatorPresent emptyFrame noPowerFor allConcrete true ∧
    GlobalAbsencePowerHoldersConcrete emptyFrame noPowerFor allConcrete true ∧
    PossiblyNoContingentConcrete emptyFrame allConcrete true ∧
    ¬ SomeContingentConcreteAt emptyFrame allConcrete true ∧
    ¬ NecessaryConcreteGlobalAbsencePowerAt emptyFrame noPowerFor allConcrete true) ∧
  (¬ TruthCore.Modal.Euclidean nonEuclidean.history.ontic.frame ∧
    GlobalAbsenceGrounded nonEuclidean (powerBy true) allConcrete .a ∧
    GlobalAbsenceInitiatorPresent nonEuclidean (powerBy true) allConcrete .a ∧
    GlobalAbsencePowerHoldersConcrete nonEuclidean (powerBy true) allConcrete .a ∧
    PossiblyNoContingentConcrete nonEuclidean allConcrete .a ∧
    SomeContingentConcreteAt nonEuclidean allConcrete .a ∧
    ¬ NecessaryConcreteGlobalAbsencePowerAt nonEuclidean (powerBy true) allConcrete .a)

/-- The models. -/
def Models : Prop :=
  TheistModel ∧ PrussWithoutPGPModel ∧ BruteFoundationalModel ∧ ConditionalEssenceModel ∧
    ConditionalEssenceOmissions ∧ PrimitivistSilence ∧ HybridFirstWayModel ∧ PrussOmissions ∧
    ConceivabilityOneSided

/-- The laws and the models. -/
def Controls : Prop := Laws ∧ Models

end Model

end TruthCore.Modal.ModalGrounding
