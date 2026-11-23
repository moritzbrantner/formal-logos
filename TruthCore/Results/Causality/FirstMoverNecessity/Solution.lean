module

public import TruthCore.Causality.FirstMoverNecessity

/-! Necessary existence of the First Way's own first mover: route A (esse-cause
and grounding forms), route C (essence–esse), route B (potency), B2 from the
q.3 a.4 reading and B6, the projection to the existing necessary-first-being
endpoint, and laws and models. Analyst formulations; attribution deferred.
Excluded middle enters only as the explicit premise
`TruthCore.Logic.ExcludedMiddle`. -/

@[expose] public section

namespace TruthCore.Results.Causality.FirstMoverNecessity
open TruthCore.Causality.FirstMoverNecessity
open TruthCore.Causality.FirstMoverNecessity.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt NecessaryConcreteAt)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.EsseCausePriority (DistinctEsseCausePriority)
open TruthCore.Causality.Round2Grounding (ActualGroundingIsSimplePriority)
open TruthCore.Causality.ReflexiveDependenceScope (ActualGroundingIrreflexive)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryFirstBeing (NecessaryActualFirstPureActAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct IsFirstBeing
  FirstUnmovedMoverIsSimpleReading)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseRequiresExternalCauseReading)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover ThereIsAFirstUnmovedMover
  FirstUnmovedMoverIsFirstBeing FirstUnmovedMoverIsPureAct)

/-- Route A, esse-cause form: the First Way's first mover `f` exists at `w`
(B0). Were it absent at some accessible world, it would be contingent, so B2
gives a distinct cause of its esse, which B3 makes simply prior to it; B1 makes
`f` the first being, so that cause would be `f` itself, contradicting
distinctness. Excluded middle turns "not absent" into "present" at each
accessible world. Pure act is carried for the same witness. -/
theorem firstMoverNecessaryByEsseCause {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hThere : ThereIsAFirstUnmovedMover MovedIn F.MovesIn)
    (hExist : MoversExistAt F w)
    (hFirst : FirstUnmovedMoverIsFirstBeing MovedIn F.MovesIn F.PriorSimply)
    (hPure : FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency))
    (hCause : ContingentHasDistinctEsseCause F w)
    (hPrior : DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply) :
    FirstMoverNecessaryPureActAt F MovedIn InPotency w := by
  obtain ⟨f, hf⟩ := hThere
  obtain ⟨x, r, hm⟩ := hf.1
  have hfw : F.history.ontic.ExistsAt w f := hExist f x r hm
  refine ⟨f, hf, hPure f hf, hfw, fun v hv => ?_⟩
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · obtain ⟨c, hne, hc⟩ := hCause f ⟨hfw, v, hv, h⟩
    exact (hne (hFirst f hf c (hPrior c f hne hc))).elim

/-- B2 from B6 and the q.3 a.4 reading: a being contingent at `w` exists at `w`,
so it is in act of esse (`ExistingInActAt`); by B6 its esse is distinct from its
essence; the q.3 a.4 reading then gives another being, in act of esse, that
causes its esse. -/
theorem contingentEsseCauseFromDistinctEsse {W B T R P : Type} (F : CausalityFrame W B T R)
    (InAct : B → R → Prop) (essenceOf esseOf : B → P) (suffice : B → Prop) (w : W)
    (hDistinct : ContingentHasDistinctEsse F w essenceOf esseOf)
    (hInAct : ExistingInActAt F.history.ontic InAct F.esse w)
    (hQ3 : DistinctEsseRequiresExternalCauseReading
      (esseProfile F InAct essenceOf esseOf suffice)) :
    ContingentHasDistinctEsseCause F w := by
  intro x hx
  obtain ⟨y, hne, -, hc⟩ := hQ3 x ⟨hInAct x hx.1, hDistinct x hx⟩
  exact ⟨y, hne, hc⟩



/-- A strength-fork law: the unrestricted reception-in-own-essence principle
implies the identity-scoped principle. The only premise is the stronger
existing statement, so the frontier retains the option to assume the weaker
R3 directly without promoting the stronger law to an established fact. -/
theorem unrestrictedReceptionImpliesIdentityScoped {B P : Type}
    (essenceOf esseOf : B → P) (Received : B → P → Prop)
    (hFull : TruthCore.Causality.EsseReception.EsseReceivedOnlyInOwnEssence
      essenceOf Received) :
    IdentityScopedEsseReception essenceOf esseOf Received := by
  intro x p _ hRec
  exact hFull x p hRec

/-- Substantive support for B6 from reception. A contingent identity-being
would receive esse (R1). Under identity (and only then), R3 locates the
recipient in its essence. De ente puts that recipient in receptive potency to
the act which, under identity, would be itself, violating irreflexivity. The
hypothesis does NOT assert B6 or necessary existence. -/
theorem contingentDistinctEsseFromReception {W B T R P : Type}
    (F : CausalityFrame W B T R) (essenceOf esseOf : B → P)
    (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop) (w : W)
    (hReceived : ContingentReceivesEsse F w Received)
    (hOwn : IdentityScopedEsseReception essenceOf esseOf Received)
    (hPotency : TruthCore.Latin.Aquinas.DeEnte.ReceiverInPotencyToReceivedEsseReading
      esseOf Received ReceptivePotencyTo)
    (hIrrefl : TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself
      ReceptivePotencyTo) :
    ContingentHasDistinctEsse F w essenceOf esseOf := by
  intro x hx hEq
  obtain ⟨p, hp⟩ := hReceived x hx
  have hOwnP : p = essenceOf x := hOwn x p hEq hp
  have hRec : ReceptivePotencyTo p (esseOf x) := hPotency x p hp
  rw [hOwnP, ← hEq] at hRec
  exact hIrrefl (esseOf x) hRec

/-- Route C, essence–esse: the First Way's first mover exists at `w` (B0) and,
by the existing simplicity reading, has esse not distinct from essence. Were it
absent at some accessible world, B6 would make its esse distinct from its
essence. Excluded middle gives presence at every accessible world. Neither
firstness nor any esse-cause is used. -/
theorem firstMoverNecessaryByEsseIdentity {W B T R P : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (Body ComposedOfMatterAndForm Composite : B → Prop)
    (essenceOf esseOf : B → P) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hThere : ThereIsAFirstUnmovedMover MovedIn F.MovesIn)
    (hExist : MoversExistAt F w)
    (hSimple : FirstUnmovedMoverIsSimpleReading MovedIn F.MovesIn Body ComposedOfMatterAndForm
      Composite essenceOf esseOf)
    (hPure : FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency))
    (hDistinct : ContingentHasDistinctEsse F w essenceOf esseOf) :
    FirstMoverNecessaryPureActAt F MovedIn InPotency w := by
  obtain ⟨f, hf⟩ := hThere
  obtain ⟨x, r, hm⟩ := hf.1
  have hfw : F.history.ontic.ExistsAt w f := hExist f x r hm
  refine ⟨f, hf, hPure f hf, hfw, fun v hv => ?_⟩
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · exact ((hSimple f hf).2.2.1 (hDistinct f ⟨hfw, v, hv, h⟩)).elim

/-- Route B, potency: the First Way's first mover exists at `w` (B0) and is
pure act. Were it absent at some accessible world, B4 would put it in POTENCY_1
in some respect, against pure act. Neither firstness nor any cause is used. -/
theorem firstMoverNecessaryByPotency {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hThere : ThereIsAFirstUnmovedMover MovedIn F.MovesIn)
    (hExist : MoversExistAt F w)
    (hPure : FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency))
    (hPotency : PossibleNonexistenceIsPotency F InPotency w) :
    FirstMoverNecessaryPureActAt F MovedIn InPotency w := by
  obtain ⟨f, hf⟩ := hThere
  obtain ⟨x, r, hm⟩ := hf.1
  have hfw : F.history.ontic.ExistsAt w f := hExist f x r hm
  refine ⟨f, hf, hPure f hf, hfw, fun v hv => ?_⟩
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · obtain ⟨s, hs⟩ := hPotency f ⟨hfw, v, hv, h⟩
    exact (hPure f hf s hs).elim

/-- Route A ∨ B: the First Way's first mover exists at `w` (B0). Were it absent
at some accessible world, the disjunctive bridge would give it either a potency,
against pure act, or a distinct cause of its esse, which B3 makes simply prior
to it and B1 then identifies with it, against distinctness. Pure act and
firstness each close one disjunct. -/
theorem firstMoverNecessaryByPotencyOrCause {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hThere : ThereIsAFirstUnmovedMover MovedIn F.MovesIn)
    (hExist : MoversExistAt F w)
    (hFirst : FirstUnmovedMoverIsFirstBeing MovedIn F.MovesIn F.PriorSimply)
    (hPure : FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency))
    (hEither : ContingentHasPotencyOrEsseCause F InPotency w)
    (hPrior : DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply) :
    FirstMoverNecessaryPureActAt F MovedIn InPotency w := by
  obtain ⟨f, hf⟩ := hThere
  obtain ⟨x, r, hm⟩ := hf.1
  have hfw : F.history.ontic.ExistsAt w f := hExist f x r hm
  refine ⟨f, hf, hPure f hf, hfw, fun v hv => ?_⟩
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · rcases hEither f ⟨hfw, v, hv, h⟩ with ⟨s, hs⟩ | ⟨c, hne, hc⟩
    · exact (hPure f hf s hs).elim
    · exact (hne (hFirst f hf c (hPrior c f hne hc))).elim

/-- Route A, grounding form: the First Way's first mover is an actual concretum
at `w` (B0, B0'). Any actual concrete ground of it is simply prior to it
(grounding-priority), hence is it (B1), hence it grounds itself, against
irreflexivity: so it is an actual root. Were it absent at some accessible
world, the grounding closure would give it such a ground. Excluded middle gives
presence at every accessible world. -/
theorem firstMoverNecessaryFirstRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hThere : ThereIsAFirstUnmovedMover MovedIn F.MovesIn)
    (hExist : MoversExistAt F w)
    (hConcrete : MoversConcrete F concrete)
    (hFirst : FirstUnmovedMoverIsFirstBeing MovedIn F.MovesIn F.PriorSimply)
    (hPure : FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency))
    (hDep : EveryContingentGroundedAt (groundProfile F concrete grounds) w)
    (hGroundPrior : ActualGroundingIsSimplePriority (groundProfile F concrete grounds) w
      F.PriorSimply)
    (hIrr : ActualGroundingIrreflexive (groundProfile F concrete grounds) w) :
    FirstMoverNecessaryFirstRootAt F MovedIn InPotency concrete grounds w := by
  obtain ⟨f, hf⟩ := hThere
  obtain ⟨x, r, hm⟩ := hf.1
  have hfw : F.history.ontic.ExistsAt w f := hExist f x r hm
  have hfa : ActualConcrete (groundProfile F concrete grounds) w f :=
    ⟨hConcrete f x r hm, hfw⟩
  have noGround : ∀ y, ¬ (concrete y ∧ F.history.ontic.ExistsAt w y ∧ grounds w y f) := by
    rintro y ⟨hyc, hyw, hg⟩
    have hy : y = f := hFirst f hf y (hGroundPrior y f ⟨hyc, hyw⟩ hfa hg)
    subst hy
    exact hIrr y hfa hg
  refine ⟨f, hf, ⟨hfa, noGround⟩, fun v hv => ?_, hFirst f hf, hPure f hf⟩
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · obtain ⟨y, hy⟩ := hDep f hfa.1 hfw ⟨hfw, v, hv, h⟩
    exact (noGround y hy).elim

/-- The grounding endpoint for the first mover witnesses the existing
necessary-first-being endpoint on the same profile: forget that the witness
moves. -/
theorem firstMoverRootIsNecessaryFirstPureAct {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W)
    (h : FirstMoverNecessaryFirstRootAt F MovedIn InPotency concrete grounds w) :
    NecessaryActualFirstPureActAt (groundProfile F concrete grounds) w F.PriorSimply
      InPotency := by
  obtain ⟨f, -, hr, hn, hfb, hp⟩ := h
  exact ⟨f, hr, hn, hfb, hp⟩

/-- The grounding endpoint for the first mover witnesses the stage-one
necessary-being node on the same profile: the first mover is a concrete
individual existing at `w` and at every accessible world. -/
theorem firstMoverRootIsNecessaryConcrete {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W)
    (h : FirstMoverNecessaryFirstRootAt F MovedIn InPotency concrete grounds w) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  obtain ⟨f, -, ⟨⟨hc, hw⟩, -⟩, hn, -⟩ := h
  exact ⟨f, hc, hw, hn⟩

/-- The pure-act necessity endpoint, with movers concrete (B0'), witnesses the
stage-one necessary-being node on any grounding profile over the frame's
existence: the necessary first mover is concrete because it moves something. -/
theorem firstMoverNecessaryIsNecessaryConcrete {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W)
    (h : FirstMoverNecessaryPureActAt F MovedIn InPotency w)
    (hConcrete : MoversConcrete F concrete) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  obtain ⟨f, hf, -, hw, hn⟩ := h
  obtain ⟨x, r, hm⟩ := hf.1
  exact ⟨f, hConcrete f x r hm, hw, hn⟩

/-! ## Laws and models -/

theorem laws : Laws := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro W B T R P F w essenceOf esseOf hEM
    constructor
    · intro h x hx hid v hv
      rcases hEM (F.history.ontic.ExistsAt v x) with he | he
      · exact he
      · exact (hid (h x ⟨hx, v, hv, he⟩)).elim
    · rintro h x ⟨hx, v, hv, he⟩ hid
      exact he (h x hx (fun hne => hne hid) v hv)
  · intro W B T R F w InPotency CanFailToBe ha hb x hx
    exact ⟨F.esse, hb x (ha x hx)⟩
  · intro W B T R F w InPotency hEM
    constructor
    · intro hPot x hpure hx v hv
      rcases hEM (F.history.ontic.ExistsAt v x) with he | he
      · exact he
      · obtain ⟨s, hs⟩ := hPot x ⟨hx, v, hv, he⟩
        exact (hpure s hs).elim
    · rintro h x ⟨hx, v, hv, he⟩
      rcases hEM (∃ r, InPotency x r) with hp | hp
      · exact hp
      · exact (he (h x (fun r hr => hp ⟨r, hr⟩) hx v hv)).elim
  · intro W B T R F w InPotency h x hx
    exact Or.inr (h x hx)
  · intro W B T R F w InPotency h x hx
    exact Or.inl (h x hx)

theorem models : Models := by
  unfold Models
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [ThereIsAFirstUnmovedMover, MoversExistAt, MoversConcrete,
    FirstUnmovedMoverIsFirstBeing, FirstUnmovedMoverIsPureAct, DistinctEsseCausePriority,
    FirstUnmovedMoverIsSimpleReading, TruthCore.Latin.Aquinas.InMetaphysicam.PotencyIsOfContradictionReading,
    TruthCore.Causality.NecessaryBeingInAct.CanFailToBeIsPossiblyNot,
    TruthCore.Latin.Aquinas.SummaTheologiae.PossibleNotToBe,
    TruthCore.Causality.NecessaryConcreteRouteBridge.modalPossible,
    TruthCore.Causality.NecessaryConcreteRouteBridge.modalIsAt,
    ActualGroundingIsSimplePriority, ActualGroundingIrreflexive, ContingentHasDistinctEsseCause,
    PossibleNonexistenceIsPotency, ContingentHasPotencyOrEsseCause, ContingentHasDistinctEsse,
    EveryContingentGroundedAt,
    FirstMoverNecessaryPureActAt, FirstMoverNecessaryFirstRootAt, NecessaryActualFirstPureActAt,
    IsFirstUnmovedMover, PureAct, IsFirstBeing, ActualRoot, ActualConcrete,
    TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround, NecessaryAt, ContingentAt,
    groundProfile, bruteFirst, conserved, unprioritized, absentMover, necessaryMover, still,
    witness, selfGround, mk, movedIn, movedPotency, fPotency, canFail, fContingent, allNecessary,
    ContingentCanFailToBe, CanFailToBeIsPotencyAtEsse, twoRoots, trioMovedIn, trioPotency,
    trioConcrete, trioNoGround, Trio.forall_iff, Trio.exists_iff,
    fAbsent,
    xCausesF, xPriorF, noCause, noPrior, xContingent, fCausesX, fPriorX, allConcrete,
    noneConcrete, noGround, fGroundsF, xGroundsF, fSelfPrior, fGroundsX, unitOf, esseTrue,
    essenceFalse, noneHolds] <;>
  simp [Bool.forall_bool]

theorem controls : Controls := ⟨laws, models⟩


/-- Reception controls: proof of the general mismatch uses the definition
of adopted potency in the SAME esse respect; the rest are finite checks. -/
theorem receptionControls : ReceptionControls := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W B T R P F w InAct CanBe Received hAct hReceived hTransfer x hx
    obtain ⟨p, hp⟩ := hReceived x hx
    have hPot := hTransfer x p hx hp
    exact hPot.2 (hAct x hx.1)
  all_goals
    simp only [ThereIsAFirstUnmovedMover, MoversExistAt, MoversConcrete,
      FirstUnmovedMoverIsFirstBeing, FirstUnmovedMoverIsPureAct, DistinctEsseCausePriority,
      FirstUnmovedMoverIsSimpleReading, TruthCore.Latin.Aquinas.InMetaphysicam.PotencyIsOfContradictionReading,
      TruthCore.Causality.NecessaryBeingInAct.CanFailToBeIsPossiblyNot,
      TruthCore.Latin.Aquinas.SummaTheologiae.PossibleNotToBe,
      TruthCore.Causality.NecessaryConcreteRouteBridge.modalPossible,
      TruthCore.Causality.NecessaryConcreteRouteBridge.modalIsAt,
      ActualGroundingIsSimplePriority, ActualGroundingIrreflexive, ContingentHasDistinctEsseCause,
      PossibleNonexistenceIsPotency, ContingentHasPotencyOrEsseCause, ContingentHasDistinctEsse,
      EveryContingentGroundedAt,
      FirstMoverNecessaryPureActAt, FirstMoverNecessaryFirstRootAt, NecessaryActualFirstPureActAt,
      IsFirstUnmovedMover, PureAct, IsFirstBeing, ActualRoot, ActualConcrete,
      TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround, NecessaryAt, ContingentAt,
      groundProfile, bruteFirst, conserved, unprioritized, absentMover, necessaryMover, still,
      witness, selfGround, mk, movedIn, movedPotency, fPotency, canFail, fContingent, allNecessary,
      ContingentCanFailToBe, CanFailToBeIsPotencyAtEsse, twoRoots, trioMovedIn, trioPotency,
      trioConcrete, trioNoGround, Trio.forall_iff, Trio.exists_iff,
      fAbsent,
      xCausesF, xPriorF, noCause, noPrior, xContingent, fCausesX, fPriorX, allConcrete,
      noneConcrete, noGround, fGroundsF, xGroundsF, fSelfPrior, fGroundsX, unitOf, esseTrue,
      essenceFalse, noneHolds,
      ContingentReceivesEsse, IdentityScopedEsseReception,
      ContingentReceptionIsSubjectPotency,
      TruthCore.Causality.EsseReception.EsseReceivedOnlyInOwnEssence,
      TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself,
      TruthCore.Latin.Aquinas.DeEnte.ReceiverInPotencyToReceivedEsseReading,
      TruthCore.Causality.ExistenceActuality.ExistingInActAt,
      TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency,
      receivedByMoved, receivedByMover, receivedNone, receptivePotency, essenceByBeing,
      subjectPotencyAtEsse, actAtEsse, canBeAny, supportsEsseAt] <;>
    simp [Bool.forall_bool]

end TruthCore.Results.Causality.FirstMoverNecessity
