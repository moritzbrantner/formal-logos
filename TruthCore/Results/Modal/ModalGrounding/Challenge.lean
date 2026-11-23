import TruthCore.Modal.ModalGrounding

/-! Accounts of de re possibility of absence at the foundational case (#1887,
test 4) and Pruss's Aristotelian-modality argument (test 5): verdicts of the
power-grounded and essentialist accounts, the existence-conditional verdict,
the Pruss reconstruction and its projection onto the stage-one node, laws and
models. Analyst formulations; attribution deferred. Excluded middle enters
only as the explicit premise `TruthCore.Logic.ExcludedMiddle`, and only where
necessity is concluded. -/

namespace TruthCore.Results.Modal.ModalGrounding
open TruthCore.Modal.ModalGrounding
open TruthCore.Modal.ModalGrounding.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Causality.ContingencyGrounding (PowerOverEsse ContingencyPowerGrounded
  PowerOverEsseCorrelation ContingentReceptiveOrReceivedFromPrior ExistentiallyReceptive)
open TruthCore.Causality.ContingencyGrounding.Model (heatFail noPower fPowerX)
open TruthCore.Causality.FirstMoverNecessity (groundProfile ContingentHasDistinctEsse MoversExistAt
  PossibleNonexistenceIsPotency)
open TruthCore.Causality.FirstMoverNecessity.Model (mk bruteFirst movedIn movedPotency noCause
  noPrior receivedNone esseTrue essenceByBeing noneHolds fContingent)
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt InhabitedAt)
open TruthCore.Causality.SubtractionArgument (UnrestrictedRecombinationAt ConcreteCompanionsAt
  PossiblyNoConcrete ConcretePresence)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct IsFirstBeing MovedOnlyAsInPotencyReading)
open TruthCore.Latin.Aquinas.InMetaphysicam (IncorruptibleSimply)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover ThereIsAFirstUnmovedMover
  FirstUnmovedMoverIsFirstBeing FirstUnmovedMoverIsPureAct)
open TruthCore.Causality.ContingencyGrounding.Model (xCorruptible xComposite)
open TruthCore.Causality.FirstMoverNecessity.Model (receptivePotency)
open TruthCore.Causality.SubtractionArgument (EachConcreteCouldFailAt)
open TruthCore.Isabelle.AFP.GoedelGod (Box)

/-- Argument 1, PGP's verdict. A foundational `f` exists at `w`. At an accessible
world `v`, excluded middle decides its existence; were it absent, `f` would be
contingent at `w`, and PGP would make it corruptible simply or put it under some
being's power over its esse, which the foundational profile excludes. Only the
profile's actuality, incorruptibility and no-power clauses are used. -/
theorem pgpFoundationalNecessary {W B T R P : Type} (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hPGP : ContingencyPowerGrounded F w CanFailToBe PowerOver) :
    FoundationalBeingsNecessaryAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver := by
  sorry

/-- Argument 2, B6's verdict. A foundational `f` exists at `w` with esse equal to
essence. Were it absent at an accessible world, it would be contingent and B6
would make its esse distinct from its essence. Only actuality and esse =
essence are used. -/
theorem esseIdentityFoundationalNecessary {W B T R P : Type} (F : CausalityFrame W B T R)
    (w : W) (essenceOf esseOf : B → P) (Received : B → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hB6 : ContingentHasDistinctEsse F w essenceOf esseOf) :
    FoundationalBeingsNecessaryAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver := by
  sorry

/-- Argument 3, unconditional essentialism gives B6. If a contingent `x` had
esse equal to essence, its own existence would lie in its nature (the
unconditional bridge), so it would exist at every accessible world (essence
grounds necessity), against its contingency. Constructive. -/
theorem essentialExistenceGivesDistinctEsse {W B T R P : Type} (F : CausalityFrame W B T R)
    (w : W) (essenceOf esseOf : B → P) (Essential : B → (W → Prop) → Prop)
    (hEss : EssenceGroundsNecessity F w Essential)
    (hBridge : EsseEssenceIsEssentialExistence F essenceOf esseOf Essential) :
    ContingentHasDistinctEsse F w essenceOf esseOf := by
  sorry

/-- Argument 4, projection onto the stage-one node: a concrete foundational
being, necessary by the verdict, witnesses STMT-NECESSARY-CONCRETE-AT on the
frame's own profile. An instantiation. -/
theorem foundationalNecessaryConcrete {W B T R P : Type} (F : CausalityFrame W B T R) (w : W)
    (essenceOf esseOf : B → P) (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop) (PowerOver : B → B → R → Prop) (concrete : B → Prop)
    (grounds : W → B → B → Prop)
    (hNec : FoundationalBeingsNecessaryAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver)
    (hSome : SomeConcreteFoundationalAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver concrete) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  sorry

/-- Argument 5, the existence-conditional verdict. For a foundational `f`, no
essential truth entails its existence: one of `f`'s own would hold at a point
lacking `f` (conditional essences, representability), and no other being's does
(unrequired by others). So the essentialist account makes `f` absent at some
accessible world. Esse = essence plays no role. Constructive. -/
theorem conditionalEssencesFoundationalContingent {W B T R P : Type}
    (F : CausalityFrame W B T R) (w : W) (essenceOf esseOf : B → P) (Received : B → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop) (Essential : B → (W → Prop) → Prop)
    (hECE : ExistenceConditionalEssences F Essential)
    (hEPP : EssentialExclusionAccount F w Essential)
    (hOthers : FoundationalExistenceUnrequiredByOthers F w essenceOf esseOf Received
      ComposedOfMatterAndForm CanFailToBe PowerOver Essential)
    (hRep : FoundationalAbsenceRepresentable F w essenceOf esseOf Received
      ComposedOfMatterAndForm CanFailToBe PowerOver) :
    FoundationalBeingsContingentAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver := by
  sorry

/-- Argument 6, Pruss's argument (analyst reconstruction). Some concrete `x` is
contingent at `w`, so the global possibility (no contingent concretum) fails at
`w`; it holds at some accessible world (P4). Aristotelian grounding (P1) gives a
being `y` existing at `w` with a power for it; initiator presence (P2) gives an
accessible world `v` where it obtains and `y` exists; `y` is concrete (P3), so
`y` is not contingent at `v`. Excluded middle and Euclidean access transfer
this to every world accessible from `w`. -/
theorem prussNecessaryPowerHolder {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hEuc : TruthCore.Modal.Euclidean F.history.ontic.frame)
    (hGround : GlobalAbsenceGrounded F PowerFor concrete w)
    (hInit : GlobalAbsenceInitiatorPresent F PowerFor concrete w)
    (hConcrete : GlobalAbsencePowerHoldersConcrete F PowerFor concrete w)
    (hPoss : PossiblyNoContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w) :
    NecessaryConcreteGlobalAbsencePowerAt F PowerFor concrete w := by
  sorry

/-- Argument 7, projection of Pruss's conclusion onto the stage-one node:
forget the power. An assembly. -/
theorem prussNecessaryConcrete {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W)
    (h : NecessaryConcreteGlobalAbsencePowerAt F PowerFor concrete w) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  sorry

/-! ## Laws -/

/-! ## Models -/

macro "mg_unfold" : tactic => `(tactic|
  simp only [FoundationalAt, FoundationalBeingsNecessaryAt, FoundationalBeingsContingentAt,
    SomeConcreteFoundationalAt, EntailsExistence, EssenceGroundsNecessity,
    EsseEssenceIsEssentialExistence, ExistenceConditionalEssences, EssentialExclusionAccount,
    FoundationalExistenceUnrequiredByOthers, FoundationalAbsenceRepresentable,
    NoContingentConcreteIn, AristotelianGroundingFor, InitiatorPresentFor,
    PowerHoldersConcreteFor, GlobalAbsenceGrounded, GlobalAbsenceInitiatorPresent,
    GlobalAbsencePowerHoldersConcrete, PossiblyNoContingentConcrete, SomeContingentConcreteAt,
    NecessaryConcreteGlobalAbsencePowerAt, GlobalAbsencePowerIsPowerOverEsse,
    PowerOverEsse, ContingencyPowerGrounded, PowerOverEsseCorrelation,
    ContingentReceptiveOrReceivedFromPrior, ExistentiallyReceptive, ContingentHasDistinctEsse,
    PossibleNonexistenceIsPotency, MoversExistAt, NecessaryConcreteAt, groundProfile,
    UnrestrictedRecombinationAt, ConcreteCompanionsAt, TruthCore.Isabelle.AFP.GoedelGod.Dia,
    TruthCore.Modal.Euclidean, IsFirstBeing, IncorruptibleSimply, PureAct,
    MovedOnlyAsInPotencyReading, ThereIsAFirstUnmovedMover, IsFirstUnmovedMover,
    FirstUnmovedMoverIsFirstBeing, FirstUnmovedMoverIsPureAct, NecessaryAt, ContingentAt,
    theistFrame, theistNoCauseFrame, lockedF, bothContingent, fEverywhere, lockedRequired,
    primitivistNecessary, primitivistContingent, creatureFrame, swappedFrame, emptyFrame,
    nonEuclidean, comboFrame, bruteFirst, frameOn, mk, allConcrete, onlyFalseConcrete,
    noGrounds, toTrue, univ, onlyFHere, bothHere, onlyFEverywhere, theistEx, creatureOnly,
    swapped, nothing, gCausesC, gPriorC, powerBy, noPowerFor, noEssence, fEssentialExistence,
    fConditionalExistence, otherRequiresF, ptAccess, ptEx, comboEx, heatFail, noPower,
    fPowerX, movedIn, movedPotency, noCause, noPrior, receivedNone, esseTrue, essenceByBeing,
    noneHolds, fContingent, PowerGroundedForSubjects, PowerGroundedForSubjectless, xComposite,
    xCorruptible, receptivePotency, EachConcreteCouldFailAt, ConcretePresence])

/-- Closes the goals `simp` leaves over predicates `φ : Bool → Prop` (from the
extensional essence relations): universal ones by `simp_all`, existential ones
with the witness "true exactly at world `true`". -/
macro "mg_finish" : tactic => `(tactic| first
  | done
  | (intros; simp_all; done)
  | (intro h; have h' := congrFun h false; simp at h'; done)
  | (intro h; have h' := congrFun h true; simp at h'; done)
  | (exact ⟨fun v => v = true, by simp⟩)
  | (exact ⟨⟨fun v => v = true, by simp⟩, ⟨fun v => v = true, by simp⟩⟩))

macro "mg_bool" : tactic => `(tactic|
  (mg_unfold <;> simp [Bool.forall_bool, Bool.exists_bool] <;> mg_finish))

theorem controls : Controls := by
  sorry

end TruthCore.Results.Modal.ModalGrounding
