module

public import TruthCore.Modal.ModalGrounding

/-! Accounts of de re possibility of absence at the foundational case (#1887,
test 4) and Pruss's Aristotelian-modality argument (test 5): verdicts of the
power-grounded and essentialist accounts, the existence-conditional verdict,
the Pruss reconstruction and its projection onto the stage-one node, laws and
models. Analyst formulations; attribution deferred. Excluded middle enters
only as the explicit premise `TruthCore.Logic.ExcludedMiddle`, and only where
necessity is concluded. -/

@[expose] public section

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
  intro f hf v hv
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · exfalso
    rcases hPGP f ⟨hf.1, v, hv, h⟩ with hc | ⟨y, hy⟩
    · exact hf.2.2.2.2.2.2.1 hc
    · exact hf.2.2.2.2.2.2.2 y hy

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
  intro f hf v hv
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · exact (hB6 f ⟨hf.1, v, hv, h⟩ hf.2.1).elim

/-- Argument 3, unconditional essentialism gives B6. If a contingent `x` had
esse equal to essence, its own existence would lie in its nature (the
unconditional bridge), so it would exist at every accessible world (essence
grounds necessity), against its contingency. Constructive. -/
theorem essentialExistenceGivesDistinctEsse {W B T R P : Type} (F : CausalityFrame W B T R)
    (w : W) (essenceOf esseOf : B → P) (Essential : B → (W → Prop) → Prop)
    (hEss : EssenceGroundsNecessity F w Essential)
    (hBridge : EsseEssenceIsEssentialExistence F essenceOf esseOf Essential) :
    ContingentHasDistinctEsse F w essenceOf esseOf := by
  rintro x ⟨_, v, hv, hAbs⟩ hEq
  exact hAbs (hEss x _ (hBridge x hEq) v hv)

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
  obtain ⟨f, hc, hf⟩ := hSome
  exact ⟨f, hc, hf.1, hNec f hf⟩

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
  intro f hf
  refine ⟨hf.1, hEPP f hf.1 fun y φ hE hEnt => ?_⟩
  refine hOthers f hf y φ (fun hyf => ?_) hE hEnt
  subst hyf
  obtain ⟨v, hv⟩ := hRep y hf
  exact hv (hEnt v (hECE y φ hE v hv))

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
  obtain ⟨x, hxc, hx⟩ := hSome
  obtain ⟨y, hyw, hpow⟩ := hGround hPoss (fun h => h x hxc hx)
  obtain ⟨v, hwv, hpv, hyv⟩ := hInit y hpow
  have hyc := hConcrete y hpow
  refine ⟨y, hyc, hyw, fun u hwu => ?_, hpow⟩
  rcases hEM (F.history.ontic.ExistsAt u y) with h | h
  · exact h
  · exact (hpv y hyc ⟨hyv, u, hEuc w v u hwv hwu, h⟩).elim

/-- Argument 7, projection of Pruss's conclusion onto the stage-one node:
forget the power. An assembly. -/
theorem prussNecessaryConcrete {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W)
    (h : NecessaryConcreteGlobalAbsencePowerAt F PowerFor concrete w) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  obtain ⟨y, hc, he, hn, _⟩ := h
  exact ⟨y, hc, he, hn⟩

/-! ## Laws -/

/-- Pruss's grounding with the transfer bridge gives power over the esse of each
concrete contingent being (law 5). -/
theorem globalGroundingPowerOverEsse {W B T R : Type} (F : CausalityFrame W B T R) (w : W)
    (PowerFor : W → B → (W → Prop) → Prop) (PowerOver : B → B → R → Prop)
    (concrete : B → Prop)
    (hEuc : TruthCore.Modal.Euclidean F.history.ontic.frame)
    (hGround : GlobalAbsenceGrounded F PowerFor concrete w)
    (hPoss : PossiblyNoContingentConcrete F concrete w)
    (hTransfer : GlobalAbsencePowerIsPowerOverEsse F PowerFor PowerOver concrete w) :
    ∀ x, concrete x → ContingentAt F.history.ontic w x → ∃ y, PowerOverEsse F PowerOver y x := by
  intro x hxc hx
  obtain ⟨y, _, hpow⟩ := hGround hPoss (fun h => h x hxc hx)
  refine ⟨y, hTransfer y x hpow hxc fun v hwv hpv hxv => ?_⟩
  obtain ⟨_, u, hwu, hxu⟩ := hx
  apply hpv x hxc ⟨hxv, u, hEuc w v u hwv hwu, hxu⟩

theorem laws : Laws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B T R F CanFailToBe PowerOver f hCorr hUncaused hInc y hy
    rcases hCorr y f hy with hc | hc
    · exact hInc hc
    · exact hUncaused y hc
  · intro W B T R P F w essenceOf esseOf Received MF CanFailToBe PowerOver concrete grounds
      hPGP hRec hComp ⟨f, hfc, hf⟩
    obtain ⟨x, hxf, hxc, hxPoss⟩ := hComp f hfc
    obtain ⟨v, hwv, _, hfv⟩ := hRec x f hxc hfc hxf hxPoss
    rcases hPGP f ⟨hf.1, v, hwv, hfv⟩ with hc | ⟨y, hy⟩
    · exact hf.2.2.2.2.2.2.1 hc
    · exact hf.2.2.2.2.2.2.2 y hy
  · intro W B T R P F essenceOf esseOf Essential x hECE hBridge hEq ⟨v, hv⟩
    exact hv (hECE x _ (hBridge x hEq) v hv)
  · intro W B T R F Essential x hECE ⟨v, hv⟩ φ hE hEnt
    exact hv (hEnt v (hECE x φ hE v hv))
  · intro W B T R F w PowerFor PowerOver concrete hEuc hGround hPoss hTransfer
    exact globalGroundingPowerOverEsse F w PowerFor PowerOver concrete hEuc hGround hPoss
      hTransfer
  · intro W B T R P F w essenceOf esseOf Received MF CanFailToBe PowerFor PowerOver concrete
      hEM hEuc hGround hPoss hTransfer f hfc hf v hv
    rcases hEM (F.history.ontic.ExistsAt v f) with h | h
    · exact h
    · obtain ⟨y, hy⟩ := globalGroundingPowerOverEsse F w PowerFor PowerOver concrete hEuc
        hGround hPoss hTransfer f hfc ⟨hf.1, v, hv, h⟩
      exact (hf.2.2.2.2.2.2.2 y hy).elim
  · intro W B T R F w PowerFor concrete grounds hGround hInit hConcrete ⟨x, hxc, hxw⟩ hPoss
    obtain ⟨y, _, hpow⟩ := hGround hPoss (fun h => h ⟨x, hxc, hxw⟩)
    obtain ⟨v, _, hpv, hyv⟩ := hInit y hpow
    exact hpv ⟨y, hConcrete y hpow, hyv⟩
  · intro W B T R F w concrete grounds ⟨v, hwv, hv⟩
    exact ⟨v, hwv, fun x hxc hx => hv ⟨x, hxc, hx.1⟩⟩
  · intro W B T R F C w n hEuc hBridge hNec hAbs
    obtain ⟨v, hwv, hBox⟩ := hBridge _ hNec
    obtain ⟨u, hwu, hu⟩ := hBridge _ hAbs
    exact hu (hBox u (hEuc w v u hwv hwu))
  · intro W B T R P F w MovedIn esseOf Received RP MF CanFailToBe PowerOver f hEM hf hUnrec
      hFirst hPGP hCorr hRec hSelf hPrior
    have hInc : IncorruptibleSimply CanFailToBe F.esse f := fun hc => by
      rcases hRec f hc with ⟨p, hp, _⟩ | hm
      · exact (hUnrec f hf).1 p hp
      · exact (hUnrec f hf).2 hm
    have hNo : ∀ y, ¬ PowerOverEsse F PowerOver y f := fun y hy => by
      rcases hCorr y f hy with hc | hc
      · exact hInc hc
      · have hne : y ≠ f := fun h => by subst h; exact hSelf y hc
        exact hne (hFirst f hf y (hPrior y f hne hc))
    refine ⟨hInc, hNo, fun hw v hv => ?_⟩
    rcases hEM (F.history.ontic.ExistsAt v f) with h | h
    · exact h
    · rcases hPGP f ⟨hw, v, hv, h⟩ with hc | ⟨y, hy⟩
      · exact (hInc hc).elim
      · exact (hNo y hy).elim
  · intro W B T R P F w esseOf Received RP MF CanFailToBe PowerOver hEM
    constructor
    · intro h
      exact ⟨fun x hx _ => h x hx, fun x hx _ => h x hx⟩
    · rintro ⟨hS, hN⟩ x hx
      rcases hEM (ExistentiallyReceptive esseOf Received RP MF x) with hr | hr
      · exact hS x hx hr
      · exact hN x hx hr

/-! ## Models -/

theorem Pt.forall_iff (p : Pt → Prop) : (∀ v, p v) ↔ p .a ∧ p .b ∧ p .c :=
  ⟨fun h => ⟨h _, h _, h _⟩, fun ⟨ha, hb, hc⟩ v => by cases v <;> assumption⟩

theorem Pt.exists_iff (p : Pt → Prop) : (∃ v, p v) ↔ p .a ∨ p .b ∨ p .c :=
  ⟨fun ⟨v, h⟩ => by cases v <;> simp_all, fun h => by
    rcases h with h | h | h <;> exact ⟨_, h⟩⟩

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

theorem theistModel : TheistModel := by
  unfold TheistModel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> mg_bool

theorem prussWithoutPGPModel : PrussWithoutPGPModel := by
  unfold PrussWithoutPGPModel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> mg_bool

theorem bruteFoundationalModel : BruteFoundationalModel := by
  unfold BruteFoundationalModel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> mg_bool

theorem conditionalEssenceModel : ConditionalEssenceModel := by
  unfold ConditionalEssenceModel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> mg_bool

theorem conditionalEssenceOmissions : ConditionalEssenceOmissions := by
  unfold ConditionalEssenceOmissions
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> mg_bool

theorem primitivistSilence : PrimitivistSilence := by
  unfold PrimitivistSilence
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> mg_bool

theorem hybridFirstWayModel : HybridFirstWayModel := by
  unfold HybridFirstWayModel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  mg_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Prod.forall, Prod.exists]

theorem prussOmissions : PrussOmissions := by
  unfold PrussOmissions
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  mg_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Pt.forall_iff, Pt.exists_iff]

theorem conceivabilityOneSided : ConceivabilityOneSided := by
  unfold ConceivabilityOneSided
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · mg_unfold; simp
  · intro P hP
    exact ⟨false, trivial, (hP false).2 (by mg_unfold; simp)⟩
  · intro v; exact Iff.rfl
  · intro h
    have := (h false).2
    simp only [primitivistContingent, frameOn, onlyFHere, univ, Box] at this
    simp at this
  · mg_unfold; simp
  · mg_unfold; simp
  · intro P hP
    exact ⟨true, trivial, (hP true).2 (by mg_unfold; simp [Box])⟩
  · intro v; exact Iff.rfl
  · intro h
    have := (h true).2
    simp only [fEverywhere, frameOn, onlyFEverywhere, univ, Box] at this
    simp at this
  · mg_unfold; simp

theorem models : Models :=
  ⟨theistModel, prussWithoutPGPModel, bruteFoundationalModel, conditionalEssenceModel,
    conditionalEssenceOmissions, primitivistSilence, hybridFirstWayModel, prussOmissions,
    conceivabilityOneSided⟩

theorem controls : Controls := ⟨laws, models⟩

end TruthCore.Results.Modal.ModalGrounding
