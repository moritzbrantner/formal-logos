import TruthCore.Causality.ContingencyGrounding

/-! C2, the receptivity-or-prior-cause grounding of contingency: C2 from power
grounding (PGP), correlation, passive→receptive, no self-esse-cause and B3;
unreceivedness of the First Way's mover from simplicity and the reception
premises; the First Way's mover necessary from C2; C2 from R1 and from B2;
C2 and its weak form; B2 ∨ B4 from power grounding; laws and models. Analyst
formulations; attribution deferred. Excluded middle enters only as the
explicit premise `TruthCore.Logic.ExcludedMiddle`, and only where necessity is
concluded. -/

namespace TruthCore.Results.Causality.ContingencyGrounding
open TruthCore.Causality.ContingencyGrounding
open TruthCore.Causality.ContingencyGrounding.Model
open TruthCore.Causality.FirstMoverNecessity
open TruthCore.Causality.FirstMoverNecessity.Model (mk bruteFirst conserved unprioritized
  witness movedIn movedPotency fContingent xContingent noCause noPrior receivedByMoved
  receivedByMover receivedNone receptivePotency essenceByBeing esseTrue essenceFalse noneHolds
  actAtEsse xCausesF xPriorF fCausesX fPriorX)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.EsseCausePriority (DistinctEsseCausePriority)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing MutableInSomeWay)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.DeEnte (ReceiverInPotencyToReceivedEsseReading ActualEsseCause)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct IsFirstBeing
  FirstUnmovedMoverIsSimpleReading)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover ThereIsAFirstUnmovedMover
  FirstUnmovedMoverIsFirstBeing FirstUnmovedMoverIsPureAct)

/-- Argument 1, C2 from power grounding. A contingent `x` is corruptible simply
or under some power over its esse (PGP). If corruptible, it is existentially
receptive (passive→receptive). If `y` has power over its esse, correlation
makes `x` corruptible (receptive again) or makes `y` a CAUSE_2 of `x`'s esse;
`y = x` would make `x` cause its own being, against no-self-esse-cause, so `y`
is distinct and, by B3, simply prior. Constructive: no excluded middle. -/
theorem c2FromPowerGrounding {W B T R P : Type} (F : CausalityFrame W B T R) (w : W)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop)
    (hPGP : ContingencyPowerGrounded F w CanFailToBe PowerOver)
    (hCorr : PowerOverEsseCorrelation F CanFailToBe PowerOver)
    (hRec : CorruptibleIsExistentiallyReceptive F CanFailToBe esseOf Received
      ReceptivePotencyTo ComposedOfMatterAndForm)
    (hSelf : NothingCausesItsOwnBeing F.CausesIn F.esse)
    (hPrior : DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply) :
    ContingentReceptiveOrReceivedFromPrior F w esseOf Received ReceptivePotencyTo
      ComposedOfMatterAndForm := by
  sorry

/-- Argument 2a, unreceivedness of the first mover. By the simplicity reading
the first mover `f` is not composed of matter and form and its esse is not
distinct from its essence. Were its esse received in a principle `p`, the
identity hypothesis would make `p` its essence (R3) and *De ente* would put
`p` in receptive potency to `f`'s esse, that is, to itself, against
irreflexivity; so its esse is distinct from its essence, against simplicity.
Constructive: no excluded middle. -/
theorem firstMoverUnreceivedFromSimplicity {B R P : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (Body ComposedOfMatterAndForm Composite : B → Prop)
    (essenceOf esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (hSimple : FirstUnmovedMoverIsSimpleReading MovedIn MovesIn Body ComposedOfMatterAndForm
      Composite essenceOf esseOf)
    (hOwn : IdentityScopedEsseReception essenceOf esseOf Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading esseOf Received ReceptivePotencyTo)
    (hIrrefl : NothingInReceptivePotencyToItself ReceptivePotencyTo) :
    FirstUnmovedMoverUnreceived MovedIn MovesIn Received ComposedOfMatterAndForm := by
  sorry

/-- Argument 2b, the First Way's mover is necessary from C2. It exists at `w`
(B0). Were it absent at some accessible world, C2 would make it existentially
receptive, against unreceivedness, or give it a distinct, simply prior CAUSE_2
of its esse, against firstness. Excluded middle gives presence at every
accessible world. Pure act (POTENCY_1) is carried for the endpoint and does no
work toward necessity. -/
theorem firstMoverNecessaryByReceptivityOrPriorCause {W B T R P : Type}
    (F : CausalityFrame W B T R) (MovedIn InPotency : B → R → Prop)
    (ComposedOfMatterAndForm : B → Prop) (esseOf : B → P) (Received : B → P → Prop)
    (ReceptivePotencyTo : P → P → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hThere : ThereIsAFirstUnmovedMover MovedIn F.MovesIn)
    (hExist : MoversExistAt F w)
    (hFirst : FirstUnmovedMoverIsFirstBeing MovedIn F.MovesIn F.PriorSimply)
    (hPure : FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency))
    (hUnrec : FirstUnmovedMoverUnreceived MovedIn F.MovesIn Received ComposedOfMatterAndForm)
    (hC2 : ContingentReceptiveOrReceivedFromPrior F w esseOf Received ReceptivePotencyTo
      ComposedOfMatterAndForm) :
    FirstMoverNecessaryPureActAt F MovedIn InPotency w := by
  sorry

/-- Argument 3a, C2 from R1 and *De ente* c.3: a contingent being receives its
esse in some principle (R1), which is in receptive potency to that esse. -/
theorem c2FromReception {W B T R P : Type} (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop)
    (hR1 : ContingentReceivesEsse F w Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading esseOf Received ReceptivePotencyTo) :
    ContingentReceptiveOrReceivedFromPrior F w esseOf Received ReceptivePotencyTo
      ComposedOfMatterAndForm := by
  sorry

/-- Argument 3b, C2 from B2 and B3: a contingent being has a distinct CAUSE_2 of
its esse (B2), which is simply prior to it (B3). -/
theorem c2FromEsseCause {W B T R P : Type} (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop)
    (hB2 : ContingentHasDistinctEsseCause F w)
    (hPrior : DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply) :
    ContingentReceptiveOrReceivedFromPrior F w esseOf Received ReceptivePotencyTo
      ComposedOfMatterAndForm := by
  sorry

/-- Argument 3c, strength order: C2 implies C2⁻ (drop the priority conjunct). -/
theorem c2ImpliesWeak {W B T R P : Type} (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop)
    (hC2 : ContingentReceptiveOrReceivedFromPrior F w esseOf Received ReceptivePotencyTo
      ComposedOfMatterAndForm) :
    ContingentReceptiveOrReceived F w esseOf Received ReceptivePotencyTo
      ComposedOfMatterAndForm := by
  sorry

/-- Argument 3d, C2⁻ with B3 gives C2. -/
theorem c2FromWeakAndPriority {W B T R P : Type} (F : CausalityFrame W B T R) (w : W)
    (esseOf : B → P) (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (ComposedOfMatterAndForm : B → Prop)
    (hWeak : ContingentReceptiveOrReceived F w esseOf Received ReceptivePotencyTo
      ComposedOfMatterAndForm)
    (hPrior : DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply) :
    ContingentReceptiveOrReceivedFromPrior F w esseOf Received ReceptivePotencyTo
      ComposedOfMatterAndForm := by
  sorry

/-- Argument 4, #1870's B2 ∨ B4 from power grounding. A contingent `x` is
corruptible simply, hence in POTENCY_1 in some respect, or under a power `y`
over its esse; correlation makes it corruptible or makes `y` a CAUSE_2 of its
esse, distinct from `x` by no-self-esse-cause. Constructive. -/
theorem potencyOrEsseCauseFromPowerGrounding {W B T R : Type} (F : CausalityFrame W B T R)
    (w : W) (InPotency CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop)
    (hPGP : ContingencyPowerGrounded F w CanFailToBe PowerOver)
    (hCorr : PowerOverEsseCorrelation F CanFailToBe PowerOver)
    (hSelf : NothingCausesItsOwnBeing F.CausesIn F.esse)
    (hPot : CorruptibleIsInSomePotency F CanFailToBe InPotency) :
    ContingentHasPotencyOrEsseCause F InPotency w := by
  sorry

/-! ## Laws and models -/

/-- The unfolding set for the finite checks. -/
macro "c2_unfold" : tactic => `(tactic|
  simp only [ContingentReceptiveOrReceivedFromPrior, ContingentReceptiveOrReceived,
    ExistentiallyReceptive, ContingencyPowerGrounded, PowerOverEsseCorrelation,
    CorruptibleIsExistentiallyReceptive, CorruptibleIsInSomePotency,
    FirstUnmovedMoverUnreceived, AnothersPowerOverEsseGivesEsseCause,
    IncorruptibleUnderAnothersPowerHasEsseCause, PowerOverEsse, GivingPowerOverEsse,
    TruthCore.Latin.Aquinas.InMetaphysicam.IncorruptibleSimply,
    ThereIsAFirstUnmovedMover, MoversExistAt, FirstUnmovedMoverIsFirstBeing,
    FirstUnmovedMoverIsPureAct, DistinctEsseCausePriority, FirstUnmovedMoverIsSimpleReading,
    IdentityScopedEsseReception, ReceiverInPotencyToReceivedEsseReading,
    NothingInReceptivePotencyToItself, NothingCausesItsOwnBeing, ContingentReceivesEsse,
    ContingentHasDistinctEsseCause, ContingentHasPotencyOrEsseCause,
    PossibleNonexistenceIsPotency, PureActBeingsNecessaryAt, FirstMoverNecessaryPureActAt,
    IsFirstUnmovedMover, PureAct, IsFirstBeing, NecessaryAt, ContingentAt,
    TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource.ClosedActualEsseCollectionsRooted,
    TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource.esseCauseGraph,
    TruthCore.Causality.ClosedGroundingRoots.ClosedGroundingCollectionsRooted,
    TruthCore.Causality.ClosedGroundingRoots.GroundClosedActual,
    TruthCore.Causality.NecessaryRootFork.ActualRoot,
    TruthCore.Causality.NecessaryRootFork.ActualConcrete,
    TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround,
    ActualEsseCause, esseProfile,
    uncausedX, selfCauser, fSelfCausesEsse, heatFail, xCorruptible, noPower, selfPower,
    xPowerF, fPowerX, xComposite,
    mk, bruteFirst, conserved, unprioritized, witness, movedIn, movedPotency, fContingent,
    xContingent, noCause, noPrior, receivedByMoved, receivedByMover, receivedNone,
    receptivePotency, essenceByBeing, esseTrue, essenceFalse, noneHolds, actAtEsse,
    xCausesF, xPriorF, fCausesX, fPriorX])

theorem controls : Controls := by
  sorry

/-- Certified difference of C2 over C2⁻ (#1598): C2 holds exactly when C2⁻ and
the difference hold. Premise-free and constructive. -/
theorem c2OverWeakExact : C2OverWeakExact := by
  sorry

/-- Strictness of C2 over C2⁻: the `unprioritized` setting separates them. -/
theorem unprioritizedSeparates : UnprioritizedSeparates := by
  sorry

end TruthCore.Results.Causality.ContingencyGrounding
