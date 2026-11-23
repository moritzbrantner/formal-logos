module

public import TruthCore.Causality.IntentionalExemplarExtension
public import TruthCore.Results.Causality.PossessionSensitiveAppetite.Solution
public import TruthCore.Results.Causality.DeiFiliusOperationFromIntellect.Solution
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill

@[expose] public section
namespace TruthCore.Results.Causality.IntentionalExemplarExtension

open TruthCore.Causality.IntentionalExemplarExtension
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding
open TruthCore.Causality.PossessionSensitiveAppetite
open TruthCore.Causality.WholePowerPerfection
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)


/-! ## The immanent intellectual-act alternative to wisdom-to-capacity

This is an additional, explicit positive support option for the SAME source.
Unlike the productive/eminent-containment route, its first positive premise is
q.14 a.1's immateriality-to-intellect reading, already used by GodHasIntellect.
The POTENCY_3 capacity / POTENCY_2 exercise-or-potency fork from
DeiFiliusOperationFromIntellect and pure actuality give actual understanding.
The NEW philosophical question is then what this existing intellectual act
immediately understands: q.14 a.2/a.4 motivate an immanent species identical
to subsistent essence, without an acquired token. A source-form's objective
primary aboutness and an actual cognitive act must BOTH hold; mere structural
truth, reflexivity or causing an intelligent effect cannot replace the latter.

The model of content is here B itself (the knower's being as its primary
intelligible object). This is a selected non-representational interpretation,
not an assertion that all cognition lacks representations. A further OPEN
grounding-recognition step is needed to apply the result to an independent
Grounded parameter; exemplary cognition of effects still needs #1873's
content-sensitive coverage and uptake. -/
open TruthCore.Causality.IntentionalExemplarExtension.ImmanentSelfPresence
open TruthCore.Causality.DeiFiliusOperationFromIntellect
open TruthCore.Latin.Aquinas.SummaTheologiae
  (PureAct ImmaterialIsIntellectualReading)

/-- Positive same-bearer reconstruction: im/material composition and component
freedom give intellect by the existing q.14 a.1 premise. An independently
specified POTENCY_3 ability to understand must either be actual or leave
POTENCY_2 unactualized; pure act excludes the latter. The immediate species
of THAT actual act, if identical with subsistent essence and primarily about
its source, is intentionally apprehended by that same g. This is more than
a productive-power implication and uses none of #1866's WisdomSelfCapacity,
SelfCapacityExercisedOrPotent or TrueSelfApprehensionGrounded.

All four primary-object commitments and the existing immateriality/capacity
premises remain OPEN; the theorem does not prove their metaphysical truth.
The chosen GroundedInOwnForm is a concrete, potentially nonrepresentational
reading, not equality with arbitrary CognitiveGrounding primitives. -/
theorem intrinsicSelfKnowledgeFromImmanentPrimaryForm {B R S : Type}
    (OwnBeing Composite HasIntellect : B → Prop)
    (ComponentOf : B → B → Prop)
    (InAct InPotency CanBe : B → R → Prop) (understanding : R)
    (ownForm : B → S) (ImmediateSpecies : B → S → Prop)
    (PrimaryAbout : S → B → Prop) (Apprehends : B → B → Prop)
    (hImmaterial : ImmaterialIsIntellectualReading Composite HasIntellect ComponentOf)
    (hCapacity : IntellectIsCapacityToUnderstand HasIntellect CanBe understanding)
    (hExercise : UnderstandingCapacityExercisedOrInPotency
      InAct InPotency CanBe understanding)
    (hSpecies : ImmanentActHasSpecies InAct understanding ImmediateSpecies)
    (hOwnSpecies : SubsistentActHasOnlyOwnSpecies OwnBeing ownForm ImmediateSpecies)
    (hSelfObject : OwnFormPresentsSelf OwnBeing ownForm PrimaryAbout)
    (hApprehends : ActApprehendsPrimaryObject
      InAct understanding ImmediateSpecies PrimaryAbout Apprehends)
    (g : B) (hOwn : OwnBeing g)
    (hNonmaterial : ¬ Composite g) (hNoComponent : ∀ y, ¬ ComponentOf g y)
    (hPure : PureAct InPotency g) :
    IntrinsicSelfKnowledge (fun c x : B => c = x) (fun c x : B => c = x)
      Apprehends (GroundedInOwnForm OwnBeing ownForm ImmediateSpecies PrimaryAbout
        Apprehends) g := by
  have hIntellect : HasIntellect g := hImmaterial g hNonmaterial hNoComponent
  have hAct : InAct g understanding := by
    rcases hExercise g (hCapacity g hIntellect) with hActual | hPotent
    · exact hActual
    · exact False.elim (hPure understanding hPotent)
  obtain ⟨s, hs⟩ := hSpecies g hAct
  have hEq : s = ownForm g := hOwnSpecies g s hOwn hs
  have hsOwn : ImmediateSpecies g (ownForm g) := by simpa [hEq] using hs
  have hAbout : PrimaryAbout (ownForm g) g := hSelfObject g hOwn
  have hKnows : Apprehends g g :=
    hApprehends g (ownForm g) g hAct hsOwn hAbout
  refine ⟨g, rfl, rfl, hKnows, ?_⟩
  exact ⟨hOwn, hKnows, ownForm g, hsOwn, rfl, hAbout⟩

namespace ImmanentSelfPresence.Control

def own (g : Bool) : Prop := g = true
def none (_ : Bool) : Prop := False
def noComponent (_ _ : Bool) : Prop := False
def noPotency (_ : Bool) (_ : Unit) : Prop := False
def ownForm (g : Bool) : Bool := g
def inActEffect (g : Bool) (_ : Unit) : Prop := g = false
def canEffect (g : Bool) (_ : Unit) : Prop := g = false
def intellectEffect (g : Bool) : Prop := g = false
def immediateEffect (g s : Bool) : Prop := g = false ∧ s = false
def selfSpecies (g s : Bool) : Prop := s = g
def primarySelf (s x : Bool) : Prop := s = x
def primaryAlien (_ : Bool) (x : Bool) : Prop := x = false
def effectApp (g x : Bool) : Prop := g = false ∧ x = false
def alienApp (_ : Bool) (x : Bool) : Prop := x = false
def selfApp (g x : Bool) : Prop := g = x
def allIntellect (_ : Bool) : Prop := True
def allAct (_ : Bool) (_ : Unit) : Prop := True

/-- Existing source/effect frame, with real secondary apprehension but no
source-level intellectual act: all the *primary-object* principles are
satisfied, yet the q.14 a.1 immaterial-to-intellect application is false.
The model is a formal counterassignment, not a metaphysically possible
incorporeal but noncognitive substance. -/
def impersonal : Prop :=
  own true ∧ PureAct noPotency true ∧
  TruthCore.Causality.IntentionalExemplarExtension.Control.frame.CausesIn
    true false () ∧
  IntrinsicSelfKnowledge (fun c x : Bool => c = x) (fun c x : Bool => c = x)
    effectApp effectApp false ∧
  IntellectIsCapacityToUnderstand intellectEffect canEffect () ∧
  UnderstandingCapacityExercisedOrInPotency inActEffect noPotency canEffect () ∧
  ImmanentActHasSpecies inActEffect () immediateEffect ∧
  SubsistentActHasOnlyOwnSpecies own ownForm immediateEffect ∧
  OwnFormPresentsSelf own ownForm primarySelf ∧
  ActApprehendsPrimaryObject inActEffect () immediateEffect primarySelf effectApp ∧
  ¬ ImmaterialIsIntellectualReading none intellectEffect noComponent ∧
  ¬ IntrinsicSelfKnowledge (fun c x : Bool => c = x)
    (fun c x : Bool => c = x) effectApp
    (GroundedInOwnForm own ownForm immediateEffect primarySelf effectApp) true

/-- The source has actual intellect and an immediate species identical with
its own form, but that form is assigned only the *other* object's primary
aboutness. Omission of self-object aboutness is material to the deduction,
not evidence that this is a tenable metaphysics of subsistent form. -/
def alienPrimaryObject : Prop :=
  ImmaterialIsIntellectualReading none allIntellect noComponent ∧
  IntellectIsCapacityToUnderstand allIntellect allAct () ∧
  UnderstandingCapacityExercisedOrInPotency allAct noPotency allAct () ∧
  PureAct noPotency true ∧
  ImmanentActHasSpecies allAct () selfSpecies ∧
  SubsistentActHasOnlyOwnSpecies own ownForm selfSpecies ∧
  ActApprehendsPrimaryObject allAct () selfSpecies primaryAlien alienApp ∧
  ¬ OwnFormPresentsSelf own ownForm primaryAlien ∧
  ¬ IntrinsicSelfKnowledge (fun c x : Bool => c = x)
    (fun c x : Bool => c = x) alienApp
    (GroundedInOwnForm own ownForm selfSpecies primaryAlien alienApp) true

/-- Joint nonvacuity: with the distinct positive principles, the actual
source has its own form as an intrinsically apprehended primary object.
No distinct mental representation or effect-level cognition is required. -/
def positive : Prop :=
  ImmaterialIsIntellectualReading none allIntellect noComponent ∧
  IntellectIsCapacityToUnderstand allIntellect allAct () ∧
  UnderstandingCapacityExercisedOrInPotency allAct noPotency allAct () ∧
  PureAct noPotency true ∧ own true ∧
  ImmanentActHasSpecies allAct () selfSpecies ∧
  SubsistentActHasOnlyOwnSpecies own ownForm selfSpecies ∧
  OwnFormPresentsSelf own ownForm primarySelf ∧
  ActApprehendsPrimaryObject allAct () selfSpecies primarySelf selfApp ∧
  IntrinsicSelfKnowledge (fun c x : Bool => c = x)
    (fun c x : Bool => c = x) selfApp
    (GroundedInOwnForm own ownForm selfSpecies primarySelf selfApp) true

def Controls : Prop := impersonal ∧ alienPrimaryObject ∧ positive
end ImmanentSelfPresence.Control

/-- Kernel-checkable finite structural controls. Each interpretation uses
two actual beings and a genuine secondary cognitive subject in the
impersonal configuration. No metaphysical-possibility claim is made. -/
theorem immanentSelfPresenceControls :
    ImmanentSelfPresence.Control.Controls := by
  simp [ImmanentSelfPresence.Control.Controls,
    ImmanentSelfPresence.Control.impersonal,
    ImmanentSelfPresence.Control.alienPrimaryObject,
    ImmanentSelfPresence.Control.positive,
    ImmanentActHasSpecies, SubsistentActHasOnlyOwnSpecies, OwnFormPresentsSelf,
    ActApprehendsPrimaryObject, GroundedInOwnForm, IntrinsicSelfKnowledge,
    IntellectIsCapacityToUnderstand, UnderstandingCapacityExercisedOrInPotency,
    TruthCore.Causality.TermSenseForks.CapacityPotency,
    ImmaterialIsIntellectualReading, PureAct,
    ImmanentSelfPresence.Control.own, ImmanentSelfPresence.Control.none,
    ImmanentSelfPresence.Control.noComponent,
    ImmanentSelfPresence.Control.noPotency,
    ImmanentSelfPresence.Control.ownForm,
    ImmanentSelfPresence.Control.inActEffect,
    ImmanentSelfPresence.Control.canEffect,
    ImmanentSelfPresence.Control.intellectEffect,
    ImmanentSelfPresence.Control.immediateEffect,
    ImmanentSelfPresence.Control.selfSpecies,
    ImmanentSelfPresence.Control.primarySelf,
    ImmanentSelfPresence.Control.primaryAlien,
    ImmanentSelfPresence.Control.effectApp,
    ImmanentSelfPresence.Control.alienApp,
    ImmanentSelfPresence.Control.selfApp,
    ImmanentSelfPresence.Control.allIntellect,
    ImmanentSelfPresence.Control.allAct,
    TruthCore.Causality.IntentionalExemplarExtension.Control.frame,
    TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.causesIn,
    Bool.forall_bool, Bool.exists_bool]


/-- #1866's self-directed understanding remains at the very same g, and
the two distinct OPEN exemplar premises add true, intrinsically grounded
apprehension of contents about each actual caused effect x. Does not infer
knowledge of uncaused beings, contingent choices or omniscience. -/
theorem understandsCausedEffectsFromSelfAndExemplars {W B T R C : Type}
    (F : CausalityFrame W B T R) (w : W)
    (About Correct : C → B → Prop) (Apprehends Grounded : B → C → Prop)
    (Specifies : B → C → B → C → Prop)
    (hCoverage : EffectExemplarCoverage F w About Correct Specifies)
    (hUptake : CognitivelyTakesUpExemplar Apprehends Grounded Specifies)
    (g : B) (hSelf : IntrinsicSelfKnowledge About Correct Apprehends Grounded g) :
    UnderstandsActualEffects F w About Correct Apprehends Grounded g := by
  obtain ⟨self, hAboutSelf, hCorrectSelf, hAppSelf, hGroundSelf⟩ := hSelf
  intro x hActual hCause
  obtain ⟨other, hSpecified, hAboutOther, hCorrectOther⟩ :=
    hCoverage g self x hActual hCause hAboutSelf hCorrectSelf
  obtain ⟨hAppOther, hGroundOther⟩ :=
    hUptake g self x other hAppSelf hGroundSelf hSpecified
  exact ⟨other, hAboutOther, hCorrectOther, hAppOther, hGroundOther⟩

/-- Preserve the exact necessary actual root, at the same world and selected
grounding relation, in an effect-knowledge consumer. The independent OPEN
RootToEsseCauseAt adapter supplies any missing selected-ground to
CAUSE_2/esse mapping. This theorem does not manufacture a root or its necessity. -/
theorem necessaryRootUnderstandsGroundedEffects {W B T R C : Type}
    (F : CausalityFrame W B T R)
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (About Correct : C → B → Prop) (Apprehends Grounded : B → C → Prop)
    (Specifies : B → C → B → C → Prop)
    (hAdapter : RootToEsseCauseAt F m w)
    (hCoverage : EffectExemplarCoverage F w About Correct Specifies)
    (hUptake : CognitivelyTakesUpExemplar Apprehends Grounded Specifies)
    (g : B) (hRoot : ActualRoot m w g) (hNecessary : NecessaryAt m.ontic w g)
    (hSelf : IntrinsicSelfKnowledge About Correct Apprehends Grounded g) :
    ActualRoot m w g ∧ NecessaryAt m.ontic w g ∧
    ∀ x, ActualConcrete m w x → m.grounds w g x →
      ∃ content, About content x ∧ Correct content x ∧
        Apprehends g content ∧ Grounded g content := by
  have hEffects := understandsCausedEffectsFromSelfAndExemplars F w About Correct
    Apprehends Grounded Specifies hCoverage hUptake g hSelf
  refine ⟨hRoot, hNecessary, ?_⟩
  intro x hActual hGround
  exact hEffects x (hAdapter.1 x hActual)
    (hAdapter.2 g x hRoot.1 hActual hGround)

/-- If About denotes a *single* referent per content, knowledge of a genuinely
other being requires a distinct content. A single self-content cannot be
silently recycled as an effect-content under that interpretation. -/
theorem otherBeingNeedsOtherContent {B C : Type}
    (About : C → B → Prop)
    (hSingle : AboutHasSingleReferent About)
    (g x : B) (hDistinct : g ≠ x) (self other : C)
    (hSelf : About self g) (hOther : About other x) : self ≠ other := by
  intro heq
  cases heq
  exact hDistinct (hSingle self g x hSelf hOther)

/-- Specializes the existing possession-sensitive appetite semantics to the
known, already-possessed good of this very same source. 'retain' is rest in
possessed good, not seeking an absent object. This is an oriented AVAILABLE
response, not its selection, performance, HasWill recognition or free creation.
All four philosophical application inputs remain explicit. -/
theorem possessedGoodRestFromSameSource {B C : Type}
    (OwnGood : B → Prop)
    (About Correct : C → B → Prop) (Apprehends Grounded : B → C → Prop)
    (profiles : B → Profile)
    (hRecognize : SelfKnownGoodIsRepresented OwnGood About Correct
      Apprehends Grounded profiles)
    (g : B) (hSelf : IntrinsicSelfKnowledge About Correct Apprehends Grounded g)
    (hGood : OwnGood g)
    (hCalibration : Calibration (profiles g))
    (hAvailability : Availability (profiles g)) :
    (profiles g).available true .retain ∧
    (profiles g).rank true .ignore < (profiles g).rank true .retain ∧
    serves true .retain ∧ next true .retain = true := by
  have hRepresented : (profiles g).representedGood true :=
    hRecognize g hSelf hGood
  exact ⟨hAvailability true hRepresented, hCalibration true hRepresented,
    Or.inr ⟨rfl, rfl⟩, rfl⟩

/-- Kernel evaluation of finite, nonempty omission and joint assignments. -/
theorem controls : TruthCore.Causality.IntentionalExemplarExtension.Control.Controls := by
  simp [TruthCore.Causality.IntentionalExemplarExtension.Control.Controls,
    AboutHasSingleReferent, RootToEsseCauseAt,
    ActualConcrete, ActualRoot, NecessaryAt,
    TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround,
    TruthCore.Modal.TemporalHistory.CoherentAtNow,
    EffectExemplarCoverage,
    CognitivelyTakesUpExemplar, UnderstandsActualEffects, SelfKnownGoodIsRepresented,
    IntrinsicSelfKnowledge, WisdomSelfCapacity,
    WisdomSelfUnderstanding.Control.Background,
    OwnBeingLacksNoPerfectionOfBeing, PurePerfectionsPertainToBeing, PureAct,
    WisdomSelfUnderstanding.Control.own, WisdomSelfUnderstanding.Control.has,
    WisdomSelfUnderstanding.Control.pure, WisdomSelfUnderstanding.Control.ofBeing,
    WisdomSelfUnderstanding.Control.noPotency, WisdomSelfUnderstanding.Control.causesIn,
    WisdomSelfUnderstanding.Control.hasIntellect,
    TruthCore.Causality.IntentionalExemplarExtension.Control.frame, TruthCore.Causality.IntentionalExemplarExtension.Control.rootProfile, TruthCore.Causality.IntentionalExemplarExtension.Control.about, TruthCore.Causality.IntentionalExemplarExtension.Control.correct,
    TruthCore.Causality.IntentionalExemplarExtension.Control.none, TruthCore.Causality.IntentionalExemplarExtension.Control.specifies, TruthCore.Causality.IntentionalExemplarExtension.Control.effectOnly, TruthCore.Causality.IntentionalExemplarExtension.Control.selfOnly,
    TruthCore.Causality.IntentionalExemplarExtension.Control.sourceTakesUp, TruthCore.Causality.IntentionalExemplarExtension.Control.goodOwn, TruthCore.Causality.IntentionalExemplarExtension.Control.noWill, TruthCore.Causality.IntentionalExemplarExtension.Control.reading,
    TruthCore.Causality.IntentionalExemplarExtension.Control.guidedResponse,
    Calibration, Availability, responsive, response,
    Bool.forall_bool, Bool.exists_bool]

end TruthCore.Results.Causality.IntentionalExemplarExtension
/-! ## C4: intrinsic objective eminence, actual noesis and simplicity

Lean-only interpretation controls, not registered premise discharges. All
interpretations share the EXISTING actual necessary root, a pure-act source
and a genuinely apprehending distinct effect. The strong impersonal model
also has an intrinsic self-intelligible source form and an objective norm for
the effect's correct apprehension. It lacks any source-level apprehension.
This does not establish that objective exemplarity exhausts intellectual
perfection; that is the OPEN metaphysical dispute.

The positive model shares the very same first source and model of normative
exemplarity, but includes actual self-apprehension with only one real intrinsic
constituent. That shows the *constitutive plurality* bridge is additional;
it does not defeat a more general Plotinian theory of noetic articulation. -/
namespace TruthCore.Results.Causality.IntentionalExemplarExtension.ObjectiveEminence

open TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

/-- Objective exemplar eminence has a genuinely cognitive, distinct effect;
this direction is logical projection, not an argument from production to
eminent containment. -/
theorem exemplarEminenceProducesKnower {B C Form : Type}
    (OwnBeing : B → Prop) (ownForm : B → Form)
    (HasOwnForm : B → Form → Prop)
    (ObjectivelyAbout : Form → B → Prop)
    (Norms : B → Form → B → C → Prop)
    (CausesEsse : B → B → Prop) (About Correct : C → B → Prop)
    (Apprehends Grounded : B → C → Prop) (g : B)
    (hEminent : IntrinsicExemplarEminence OwnBeing ownForm HasOwnForm
      ObjectivelyAbout Norms CausesEsse About Correct Apprehends Grounded g) :
    ProducesActualKnower CausesEsse About Correct Apprehends Grounded g :=
  hEminent.2.2.2.2

/-- If real constitutive plurality is essential to source-level noesis, a
source with at most one such constituent cannot genuinely understand itself.
The disputed REAL-PLURALITY premise does all the work of crossing from
intentional aboutness to ontological division. -/
theorem strictUnityExcludesNoesisUnderRealDuality {B C Aspect : Type}
    (OwnBeing : B → Prop) (About Correct : C → B → Prop)
    (Apprehends Grounded : B → C → Prop)
    (RealConstituent : B → Aspect → Prop) (g : B)
    (hSimple : ConstitutivelySimple RealConstituent g)
    (hRealDuality : SourceNoesisRequiresRealPlurality OwnBeing About Correct
      Apprehends Grounded RealConstituent)
    (hOwn : OwnBeing g) :
    ¬ IntrinsicSelfKnowledge About Correct Apprehends Grounded g := by
  intro hKnows
  obtain ⟨a, b, ha, hb, hNe⟩ := hRealDuality g hOwn hKnows
  exact hNe (hSimple a b ha hb)

namespace Control

/-- One SOURCE, not merely some being with a cognitive effect. The rootProfile
is the existing selected actual-root grounding dictionary, not a fresh source.
The source exists necessarily at true; false is a concrete caused effect.
The constituent carrier admits exactly one intrinsic form at the source. -/
def FirstSourceFrame : Prop :=
  ActualRoot TruthCore.Causality.IntentionalExemplarExtension.Control.rootProfile true true ∧
  NecessaryAt TruthCore.Causality.IntentionalExemplarExtension.Control.rootProfile.ontic
    true true ∧
  PureAct
    TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.noPotency
    true ∧
  TruthCore.Causality.IntentionalExemplarExtension.Control.frame.CausesIn
    true false () ∧
  TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.own true ∧
  ConstitutivelySimple
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.realConstituent
    true

/-- ¬C4 for the deliberately *strong objective/exemplary* eminence reading:
the source is actually necessary, pure act, a single-form first, the genuine
intrinsic intelligible and normative standard for an actual intelligent effect,
yet does not itself intentionally apprehend any content. Contrast the earlier
productive-only model, where no source-level excellence is represented. -/
def ImpersonalEminence : Prop :=
  FirstSourceFrame ∧
  IntrinsicExemplarEminence
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.own
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.formOf
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.hasOwnForm
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.objectAbout
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.norms
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.causesEsse
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    true ∧
  IntrinsicSelfKnowledge
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    false ∧
  ¬ IntrinsicSelfKnowledge
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    true ∧
  SourceNoesisRequiresRealPlurality
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.own
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.realConstituent

/-- The same source and same objective norm, but a single immanent actual
understanding rather than two real constituents. Pure act and the intellectual
effect are still populated. The real-duality rule fails under this selected
non-constitutive account of intentional distinction. -/
def SimpleIntentionalEminence : Prop :=
  FirstSourceFrame ∧
  IntrinsicExemplarEminence
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.own
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.formOf
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.hasOwnForm
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.objectAbout
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.norms
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.causesEsse
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.bothKnowOwn
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.bothKnowOwn
    true ∧
  IntrinsicSelfKnowledge
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.bothKnowOwn
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.bothKnowOwn
    true ∧
  ¬ SourceNoesisRequiresRealPlurality
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.own
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.bothKnowOwn
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.bothKnowOwn
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.realConstituent

/-- Mere ability to cause real knowledge cannot imply source-level OBJECTIVE
normative/formal containment, even before the further C4 question about
subjective apprehension arises. -/
def ProductiveWithoutExemplarity : Prop :=
  ProducesActualKnower
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.causesEsse
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    true ∧
  ¬ IntrinsicExemplarEminence
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.own
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.formOf
    (fun _ _ => False)
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.objectAbout
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.norms
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.causesEsse
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly
    true

def Controls : Prop :=
  ImpersonalEminence ∧ SimpleIntentionalEminence ∧ ProductiveWithoutExemplarity

end Control

/-- Nonvacuous two-being, two-world structural interpretations of both C4
and ¬C4 under one explicit, stronger objective-eminence interpretation, plus
the additional constitutive-duality fork. The models do NOT certify that
objective/intelligible exemplarity is the whole subjective perfection of
understanding, nor that either picture is metaphysically admissible. -/
theorem controls : Control.Controls := by
  simp [Control.Controls, Control.ImpersonalEminence,
    Control.SimpleIntentionalEminence, Control.ProductiveWithoutExemplarity,
    Control.FirstSourceFrame,
    IntrinsicExemplarEminence, ProducesActualKnower,
    ConstitutivelySimple, SourceNoesisRequiresRealPlurality,
    IntrinsicSelfKnowledge, ActualRoot, ActualConcrete, NecessaryAt,
    TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround,
    PureAct,
    TruthCore.Causality.IntentionalExemplarExtension.Control.frame,
    TruthCore.Causality.IntentionalExemplarExtension.Control.rootProfile,
    TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.noPotency,
    TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.causesIn,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.own,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.formOf,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.hasOwnForm,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.objectAbout,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.norms,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.realConstituent,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.causesEsse,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.about,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.correct,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.effectOnly,
    TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control.bothKnowOwn,
    Bool.forall_bool, Bool.exists_bool]

end TruthCore.Results.Causality.IntentionalExemplarExtension.ObjectiveEminence

