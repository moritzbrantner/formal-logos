module

public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Results.Causality.RootPurity.Solution
public import TruthCore.Results.Causality.PureActThisness.Solution

@[expose] public section

namespace TruthCore.Results.Causality.WholePowerPerfection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActThisness
open TruthCore.Causality.PureIndiscernibility (PurelyDeterminedIndiscerniblesIdentical)
open TruthCore.Causality.PureActRoot (ActualRootHasEveryPureDetermination)
open TruthCore.Causality.WholePowerPerfection
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)
open TruthCore.Logic (ExcludedMiddle)

/-- Unrestricted perfection for first movers: simplicity and firstness remove
every represented limiting principle; the open bridge makes an unlimited first
mover its own being; SCG I.28 gives it every perfection of being; q.4 a.2 makes
every pure perfection such a perfection. -/
theorem firstMoverPerfectionFromWholePower {B R P D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (Body ComposedOfMatterAndForm Composite : B → Prop) (essenceOf esseOf : B → P)
    (OwnBeing : B → Prop) (Has : B → D → Prop) (Pure OfBeing : D → Prop)
    (hSimple : FirstUnmovedMoverIsSimpleReading Moved Moves Body ComposedOfMatterAndForm
      Composite essenceOf esseOf)
    (hFirst : FirstUnmovedMoverIsFirstBeing Moved Moves PriorSimply)
    (hOwn : UnlimitedIsOwnBeing Composite PriorSimply essenceOf esseOf OwnBeing)
    (hWhole : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (hPertain : PurePerfectionsPertainToBeing Pure OfBeing) :
    FirstMoverHasEveryPureDetermination Moved Moves Has Pure := by
  intro f hf d hd
  have hs := hSimple f hf
  have hUnlimited : ¬ TruthCore.Causality.RootMultiplication.HasLimitingPrinciple
      Composite PriorSimply essenceOf esseOf f := by
    intro hLimited
    rcases hLimited with hComposite | hDistinctEsse | ⟨y, hDistinct, hPriorY⟩
    · exact hs.2.2.2 hComposite
    · exact hs.2.2.1 hDistinctEsse
    · exact hDistinct (hFirst f hf y hPriorY)
  exact hWhole f (hOwn f hUnlimited) d (hPertain d hd)

/-- Unrestricted perfection at the actual roots, from the eight inputs that make
every actual root unlimited and the same three premises. -/
theorem rootPerfectionFromWholePower {W B P R D : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (OwnBeing : B → Prop) (Has : B → D → Prop) (Pure OfBeing : D → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hOwn : UnlimitedIsOwnBeing Composite PriorSimply p.essenceOf p.esseOf OwnBeing)
    (hWhole : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (hPertain : PurePerfectionsPertainToBeing Pure OfBeing) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  intro r hr d hd
  exact hWhole r (hOwn r (TruthCore.Results.Causality.RootPurity.rootsWithoutLimitingPrinciple
    m w p PriorSimply ComponentOf Composite hEM hExisting hEsse hExhaustive hNoSelfCause
    hPrior hPosterior hOther r hr)) d (hPertain d hd)

/-- Unrestricted perfection for first movers through infinity: simplicity and
excluded middle give esse equal to essence, the existing q.7 reading
(`STMT-SUBSISTENT-BEING-IS-INFINITE`, a premise of the designated root route) makes
the first mover infinite, and the bridge gives it every pure perfection. -/
theorem firstMoverPerfectionFromInfinity {B R P D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body ComposedOfMatterAndForm Composite : B → Prop) (essenceOf esseOf : B → P)
    (Infinite : B → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (hEM : ExcludedMiddle)
    (hSimple : FirstUnmovedMoverIsSimpleReading Moved Moves Body ComposedOfMatterAndForm
      Composite essenceOf esseOf)
    (hInfinite : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hBridge : InfiniteHasEveryPurePerfection Infinite Has Pure) :
    FirstMoverHasEveryPureDetermination Moved Moves Has Pure := by
  intro f hf d hd
  have hEq : esseOf f = essenceOf f := by
    rcases hEM (esseOf f = essenceOf f) with h | h
    · exact h
    · exact ((hSimple f hf).2.2.1 h).elim
  exact hBridge f (hInfinite f hEq) d hd

/-- Unrestricted perfection at the actual roots through infinity: the existing
per-root essence/esse identity, the q.7 reading and the bridge. -/
theorem rootPerfectionFromInfinity {W B P R D : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (Infinite : B → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hInfinite : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hBridge : InfiniteHasEveryPurePerfection Infinite Has Pure) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  intro r hr d hd
  exact hBridge r (hInfinite r (TruthCore.Causality.RootEssenceIdentity.identityOfActualRoot
    m w p r hr hEM hExisting hEsse hExhaustive hNoSelfCause)) d hd

/-- SCG I.42 with unrestricted perfection and strict pure actuality: at most one
first mover. Conditional on three OPEN premises. -/
theorem uniqueFromPerfectBeings {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hPerfect : PerfectBeingsNotSeveral Has Pure) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  intro f g hf hg
  exact hPerfect f g (hEvery f hf) (hPure f hf) (hEvery g hg) (hPure g hg)

/-- The narrower bridge entails SCG I.42. -/
theorem perfectBeingsOfPureIndiscernibility {B D : Type} (Has : B → D → Prop)
    (Pure : D → Prop) (hBridge : PurelyDeterminedIndiscerniblesIdentical Has Pure) :
    PerfectBeingsNotSeveral Has Pure := by
  intro x y hx hxPure hy hyPure
  exact hBridge x y hxPure (fun d => ⟨fun h => hy d (hxPure d h), fun h => hx d (hyPure d h)⟩)


/-! ## Intrinsic self-knowledge from whole-being perfection

These are conditional applications to the SAME subsistent source, actual root,
or GOD_4 bearer. The genuinely substantive self-capacity, immanent exercise,
cognitive-grounding and HAS_INTELLECT_1 recognition inputs remain OPEN. In
particular, a productive-power meaning of virtual possession supplies none of
them, and these proofs do not import the q.14 self-understanding claim as a
conclusion-shaped premise. -/
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding

/-- Whole power of being supplies wisdom at the very same OwnBeing bearer;
the separate self-directed capacity, exercise/potency, and cognitive-grounding
bridges supply an actual, true, cognitively grounded self-directed apprehension.
'PureAct' is read with `InPotency` as POTENCY_2 (`DEF-INDEPENDENT-POTENCY`):
it excludes that primitive potency in every respect, and the proof uses only
its instance at the designated understanding respect. Under POTENCY_1 (capable
and not actually), pure act would forbid every unexercised capacity, including
productive powers if those count as `CanBe` respects (the fork recorded in
`DeiFiliusOperationFromIntellect`). Compare the existing generic-respect result
`intellectualPureActOperatesFromCapacity` (c55e2ce2), which takes the same
exercise-or-potency step at the respect of understanding; this variant is
content-indexed so that the subject, the aboutness target and the grounding
relation stay the same `g`, which the generic respect does not express. -/
theorem intrinsicSelfKnowledgeFromWisdom {B D C R : Type}
    (OwnBeing : B → Prop) (Has : B → D → Prop) (Pure OfBeing : D → Prop)
    (wisdom : D) (About Correct : C → B → Prop)
    (CanApprehend Apprehends CognitivelyGrounded : B → C → Prop)
    (InPotency : B → R → Prop) (understanding : R)
    (hWhole : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (hPertain : PurePerfectionsPertainToBeing Pure OfBeing)
    (hPureWisdom : Pure wisdom)
    (hSelfCapacity : WisdomSelfCapacity OwnBeing Has wisdom About Correct CanApprehend)
    (hExercise : SelfCapacityExercisedOrPotent OwnBeing About CanApprehend Apprehends
      InPotency understanding)
    (hGrounding : TrueSelfApprehensionGrounded OwnBeing About Correct Apprehends CognitivelyGrounded)
    (g : B) (hOwn : OwnBeing g)
    (hPureAct : PureAct InPotency g) :
    IntrinsicSelfKnowledge About Correct Apprehends CognitivelyGrounded g := by
  have hPossesses : Has g wisdom := hWhole g hOwn wisdom (hPertain wisdom hPureWisdom)
  obtain ⟨content, hAbout, hCorrect, hCan⟩ :=
    hSelfCapacity g hOwn hPossesses
  rcases hExercise g content hOwn hAbout hCan with hApprehension | hPotency
  · exact ⟨content, hAbout, hCorrect, hApprehension,
      hGrounding g content hOwn hAbout hCorrect hApprehension⟩
  · exact False.elim (hPureAct understanding hPotency)

/-- Actual-root specialization consuming the UNCHANGED,
already supported `ActualRootHasEveryPureDetermination` interface, e.g. its
`rootPerfectionFromWholePower` producer. The root-without-limitation and
UnlimitedIsOwnBeing premises supply subsistent esse for this *same* root.
No actuality-to-being, root existence or pure act is manufactured here. -/
theorem actualRootSelfKnowledgeFromWisdom {W B P D C R : Type}
    (m : Profile W B) (w : W)
    (Composite : B → Prop) (PriorSimply : B → B → Prop)
    (essenceOf esseOf : B → P)
    (OwnBeing : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) (wisdom : D)
    (About Correct : C → B → Prop)
    (CanApprehend Apprehends CognitivelyGrounded : B → C → Prop)
    (InPotency : B → R → Prop) (understanding : R)
    (hNoLimits : TruthCore.Causality.RootPurity.ActualRootsWithoutLimitingPrinciple
      m w Composite PriorSimply essenceOf esseOf)
    (hOwn : UnlimitedIsOwnBeing Composite PriorSimply essenceOf esseOf OwnBeing)
    (hEvery : ActualRootHasEveryPureDetermination m w Has Pure)
    (hPureWisdom : Pure wisdom)
    (hSelfCapacity : WisdomSelfCapacity OwnBeing Has wisdom About Correct CanApprehend)
    (hExercise : SelfCapacityExercisedOrPotent OwnBeing About CanApprehend Apprehends
      InPotency understanding)
    (hGrounding : TrueSelfApprehensionGrounded OwnBeing About Correct Apprehends CognitivelyGrounded)
    (g : B) (hRoot : TruthCore.Causality.NecessaryRootFork.ActualRoot m w g)
    (hPureAct : PureAct InPotency g) :
    IntrinsicSelfKnowledge About Correct Apprehends CognitivelyGrounded g := by
  have hOwnG : OwnBeing g := hOwn g (hNoLimits g hRoot)
  have hWisdom : Has g wisdom := hEvery g hRoot wisdom hPureWisdom
  obtain ⟨content, hAbout, hCorrect, hCan⟩ :=
    hSelfCapacity g hOwnG hWisdom
  rcases hExercise g content hOwnG hAbout hCan with hApprehension | hPotency
  · exact ⟨content, hAbout, hCorrect, hApprehension,
      hGrounding g content hOwnG hAbout hCorrect hApprehension⟩
  · exact False.elim (hPureAct understanding hPotency)

/-- Weaker endpoint for HAS_INTELLECT_1 *as capacity*: whole-being perfection
and its substantive wisdom→self-directed-power bridge suffice if that power
is recognized as intrinsic intellectual aptitude. No pure-act exercise,
actual apprehension, or cognitive-grounding premise is required for this
capacity-level conditional. GOD_4 itself still needs a real witness.
Reading HAS_INTELLECT_1 as a capacity is a reading choice: its definition
says "intellectual cognition" without deciding capacity versus exercise. The
existing open premise `IntellectIsCapacityToUnderstand`
(`DeiFiliusOperationFromIntellect`) takes the same capacity reading. If
HAS_INTELLECT_1 meant actual cognition, this would not be the weaker endpoint. -/
theorem godHasIntellectFromWisdomCapacity {B D C : Type}
    (IsGod HasIntellect OwnBeing : B → Prop)
    (Has : B → D → Prop) (Pure OfBeing : D → Prop) (wisdom : D)
    (About Correct : C → B → Prop) (CanApprehend : B → C → Prop)
    (hGodOwn : ∀ g, IsGod g → OwnBeing g)
    (hWhole : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (hPertain : PurePerfectionsPertainToBeing Pure OfBeing)
    (hPureWisdom : Pure wisdom)
    (hSelfCapacity : WisdomSelfCapacity OwnBeing Has wisdom About Correct CanApprehend)
    (hRecognition : ∀ g, IsGod g →
      (∃ content, About content g ∧ Correct content g ∧
        CanApprehend g content) → HasIntellect g) :
    GodHasIntellect IsGod HasIntellect := by
  intro g hg
  have hOwn : OwnBeing g := hGodOwn g hg
  have hWisdom : Has g wisdom := hWhole g hOwn wisdom (hPertain wisdom hPureWisdom)
  exact hRecognition g hg (hSelfCapacity g hOwn hWisdom)

/-- Conditional GOD_4 attachment to the unchanged HAS_INTELLECT_1 consumer:
first obtain *intrinsic* source-borne, true and cognitively grounded self-apprehension
before applying the explicitly OPEN recognition bridge. GOD_4 existence,
source identity, and the philosophical truth of the bridge are not proved. -/
theorem godHasIntellectFromWholePowerWisdom {B D C R : Type}
    (IsGod HasIntellect OwnBeing : B → Prop)
    (Has : B → D → Prop) (Pure OfBeing : D → Prop) (wisdom : D)
    (About Correct : C → B → Prop)
    (CanApprehend Apprehends CognitivelyGrounded : B → C → Prop)
    (InPotency : B → R → Prop) (understanding : R)
    (hGodOwn : ∀ g, IsGod g → OwnBeing g)
    (hGodPure : ∀ g, IsGod g → PureAct InPotency g)
    (hWhole : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (hPertain : PurePerfectionsPertainToBeing Pure OfBeing)
    (hPureWisdom : Pure wisdom)
    (hSelfCapacity : WisdomSelfCapacity OwnBeing Has wisdom About Correct CanApprehend)
    (hExercise : SelfCapacityExercisedOrPotent OwnBeing About CanApprehend Apprehends
      InPotency understanding)
    (hGrounding : TrueSelfApprehensionGrounded OwnBeing About Correct Apprehends CognitivelyGrounded)
    (hRecognition : ∀ g, IsGod g →
      IntrinsicSelfKnowledge About Correct Apprehends CognitivelyGrounded g → HasIntellect g) :
    GodHasIntellect IsGod HasIntellect := by
  intro g hg
  exact hRecognition g hg
    (intrinsicSelfKnowledgeFromWisdom OwnBeing Has Pure OfBeing wisdom
      About Correct CanApprehend Apprehends CognitivelyGrounded InPotency understanding
      hWhole hPertain hPureWisdom hSelfCapacity hExercise hGrounding g
      (hGodOwn g hg) (hGodPure g hg))

/-- Same fixed, nonempty source/effect background, with three missing-premise
controls and one successful joint assignment. This is a kernel-checkable
structural interpretation, not a metaphysical rival's proven possibility. -/
theorem wisdomSelfUnderstandingControls :
    WisdomSelfUnderstanding.Control.Controls := by
  simp [WisdomSelfUnderstanding.Control.Controls,
    WisdomSelfUnderstanding.Control.Background,
    WisdomSelfCapacity, SelfCapacityExercisedOrPotent,
    TrueSelfApprehensionGrounded, IntrinsicSelfKnowledge,
    OwnBeingLacksNoPerfectionOfBeing, PurePerfectionsPertainToBeing,
    PureAct, WisdomSelfUnderstanding.Control.own, WisdomSelfUnderstanding.Control.has,
    WisdomSelfUnderstanding.Control.pure, WisdomSelfUnderstanding.Control.ofBeing,
    WisdomSelfUnderstanding.Control.about, WisdomSelfUnderstanding.Control.correct,
    WisdomSelfUnderstanding.Control.canApprehend, WisdomSelfUnderstanding.Control.apprehends,
    WisdomSelfUnderstanding.Control.cognitivelyGrounded,
    WisdomSelfUnderstanding.Control.none, WisdomSelfUnderstanding.Control.noPotency,
    WisdomSelfUnderstanding.Control.causesIn, WisdomSelfUnderstanding.Control.hasIntellect,
    Bool.forall_bool, Bool.exists_bool]

section Controls
open TruthCore.Causality.WholePowerPerfection.Control
open TruthCore.Causality.RootPurity.Control (fmMoved fmMoves)
open TruthCore.Results.Causality.RootPurity (unlimited)
open TruthCore.Results.Causality.PartFreePlurality (leftFirst rightFirst perfect notUnique)

theorem fmFirst : IsFirstUnmovedMover fmMoved fmMoves true := ⟨⟨true, (), rfl⟩, fun _ h => h⟩

theorem fmSimple : FirstUnmovedMoverIsSimpleReading fmMoved fmMoves
    TruthCore.Causality.RootPurity.Control.none1 TruthCore.Causality.RootPurity.Control.none1
    TruthCore.Causality.RootPurity.Control.none1
    TruthCore.Causality.RootPurity.Control.flat.essenceOf
    TruthCore.Causality.RootPurity.Control.flat.esseOf :=
  fun _ _ => ⟨fun h => h, fun h => h, fun h => h rfl, fun h => h⟩

theorem fmFirstBeing : FirstUnmovedMoverIsFirstBeing fmMoved fmMoves
    TruthCore.Causality.RootPurity.Control.none2 := fun _ _ _ h => h.elim

theorem noPerfection : ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas
    (fun _ => True) := fun h => h true fmFirst () trivial

theorem controls : TruthCore.Causality.WholePowerPerfection.Control.Certificate :=
  ⟨⟨fun _ _ hx _ _ _ => (hx () trivial).elim,
      fun h => Bool.noConfusion (h true false (fun _ h => h.elim) (fun _ => Iff.rfl))⟩,
    ⟨fun x hx r _ => perfect x hx r, fun _ _ _ _ => trivial,
      fun h => TruthCore.Causality.PartFreePlurality.Being.noConfusion
        (h .left .right (fun r _ => perfect .left leftFirst r) (fun _ _ => trivial)
          (fun r _ => perfect .right rightFirst r) (fun _ _ => trivial)),
      notUnique⟩,
    ⟨fmSimple, fmFirstBeing, fun h => h true (unlimited true), fun _ h => h.elim,
      fun _ _ => trivial, noPerfection⟩,
    ⟨fun _ _ => trivial, fun h => h true trivial () trivial, fun _ _ => trivial, noPerfection⟩,
    ⟨fun _ _ => trivial, fun _ _ _ h => h.elim, fun h => h () trivial, noPerfection⟩,
    ⟨fun _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ => trivial, fun _ _ _ _ => trivial,
      fmFirst⟩,
    ⟨fun _ _ => trivial, fun h => h true trivial () trivial, noPerfection,
      fun _ _ _ _ => trivial⟩⟩

end Controls

end TruthCore.Results.Causality.WholePowerPerfection
