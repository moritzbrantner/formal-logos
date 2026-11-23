module

public import TruthCore.Causality.Frame
public import TruthCore.Causality.NecessaryRootFork
public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Causality.PossessionSensitiveAppetite

/-!
# Intentional cognition: source, exemplary content, and possessed good

Analyst conditional continuation of #1731 / stacked on draft #1866.
The source's understanding of itself is the *content-indexed* result from
WholePowerPerfection, not a new definition of intellectual capacity.
Knowledge of another being must use another appropriately specified content;
bare causation, output accuracy, and even genuine cognition in a produced
secondary being do not assert cognition in the source.

The causal/actuality parameters use one CausalityFrame: world-relative existence, and CausesIn at the distinguished esse respect. Passage from the selected ActualRoot grounding relation requires the distinct OPEN RootToEsseCauseAt adapter.

The two following premises are OPEN:
* A correctly described actual effect of the source has a determinate, true intelligible
  specification accessible from that source's self-content. The specification
  can fail even if the source really causes the effect.
* The source's actual, intrinsically grounded apprehension takes up that
  specification as its own further act of understanding. A physical mapping
  of signs to effects alone does not establish such uptake.

They are not definitions of knowledge or of causation. The conditional result
is restricted to effects actually caused by this same bearer, not to every
possible creature, all truths, or its free selection among creations. -/

@[expose] public section
namespace TruthCore.Causality.IntentionalExemplarExtension

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding

variable {B C : Type}

/-- OPEN exemplar *content* bridge. A source's correct self-content plus
actual causation specifies a separate true content about each actual effect.
'Specifies' is not 'Apprehends', and it presupposes neither cognition of the
effect nor an efficacious choice of this effect from alternatives. -/
def EffectExemplarCoverage {W T R : Type} (F : CausalityFrame W B T R) (w : W)
    (About Correct : C → B → Prop)
    (Specifies : B → C → B → C → Prop) : Prop :=
  ∀ g self x, F.history.ontic.ExistsAt w x → F.CausesIn g x F.esse →
    About self g → Correct self g →
    ∃ other, Specifies g self x other ∧ About other x ∧ Correct other x

/-- OPEN immanent, content-sensitive *uptake* of a specified exemplar. This is
additional to knowing one's own content: an uninterpreted computation that
produces a true specification cannot by itself count as cognitive uptake.
Grounded here retains the #1866 source-intrinsic intentional-norm reading. -/
def CognitivelyTakesUpExemplar (Apprehends Grounded : B → C → Prop)
    (Specifies : B → C → B → C → Prop) : Prop :=
  ∀ g self x other, Apprehends g self → Grounded g self →
    Specifies g self x other → Apprehends g other ∧ Grounded g other

/-- Actual cognitively grounded knowledge of caused effects, not omniscience.
The knower is the same g throughout; the known content concerns x. -/
def UnderstandsActualEffects {W T R : Type} (F : CausalityFrame W B T R) (w : W)
    (About Correct : C → B → Prop) (Apprehends Grounded : B → C → Prop)
    (g : B) : Prop :=
  ∀ x, F.history.ontic.ExistsAt w x → F.CausesIn g x F.esse →
    ∃ content, About content x ∧ Correct content x ∧
      Apprehends g content ∧ Grounded g content

/-- OPEN world-scoped bridge from the selected actual root profile's
grounding relation to the CAUSE_2 cause of esse in the common CausalityFrame.
Every selected actual concretum exists in the frame's world, and actual
grounding is sufficient for CAUSE_2 at esse. Neither converse is assumed. -/
def RootToEsseCauseAt {W T R : Type} (F : CausalityFrame W B T R)
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W) : Prop :=
  (∀ x, ActualConcrete m w x → F.history.ontic.ExistsAt w x) ∧
  (∀ g x, ActualConcrete m w g → ActualConcrete m w x →
    m.grounds w g x → F.CausesIn g x F.esse)

/-- A selected single-referent interpretation of About; multipurpose
contents are possible under other readings but cannot be presumed. -/
def AboutHasSingleReferent (About : C → B → Prop) : Prop :=
  ∀ c x y, About c x → About c y → x = y

/-- OPEN recognition of the source's possessed goodness as good. It does not
follow from bare true self-knowledge, whose content need not be evaluative.
The response profile is a separate intellectual-appetite model: no current
desire, movement, decision or creation is inferred from its availability. -/
def SelfKnownGoodIsRepresented (OwnGood : B → Prop)
    (About Correct : C → B → Prop) (Apprehends Grounded : B → C → Prop)
    (profiles : B → TruthCore.Causality.PossessionSensitiveAppetite.Profile) : Prop :=
  ∀ g, IntrinsicSelfKnowledge About Correct Apprehends Grounded g →
    OwnGood g → (profiles g).representedGood true


/-! ## The primary intelligible object of a subsistent intellectual act

Analyst reconstruction of the *distinct* q.14 a.1/a.2/a.4 route, not an
interpretation of productive InActVirtually. An actual intellectual operation
has a primary intelligible form; a subsistent intellect admits no distinct
primary species inhering in it; its own form presents the source as the
immediate object. The operation apprehends that primary object. These are
separate OPEN philosophical commitments, not consequences of correct output.

A form here is the immediate formal specification of an immanent intellectual
act, NOT a copied image, passive reception event or separate mental token.
It need not have the same type as a being; no injectivity or unique referring
relation is assumed. Secondary knowledge of effects has the different
CognitivelyTakesUpExemplar obligation above. -/
namespace ImmanentSelfPresence

/-- OPEN act/object principle: an actual immanent intellectual operation has
an immediate intelligible form. This strengthens the previously registered
`Round5Worklist.UnderstandingIsThroughIntelligibleForm`, which takes an
`Understands` relation and finds *some* intelligible form held by the
understanding bearer. That result does not select the form *immediately*
actualizing the very act, nor translate formal `InAct` to `Understands`;
those interpretations require further bridges rather than a silent reuse.
InAct is ACT of understanding, not merely
virtual possession or productive power; identifying those readings is OPEN. -/
def ImmanentActHasSpecies {B R S : Type}
    (InAct : B → R → Prop) (understanding : R)
    (ImmediateSpecies : B → S → Prop) : Prop :=
  ∀ g, InAct g understanding → ∃ s, ImmediateSpecies g s

/-- OPEN simplicity/identity principle: for a source that is its own esse,
an immediately informing intellectual species is not an additional intrinsic
form distinct from that source's own intelligible essence. This is stronger
than being an efficient producer of mental representations elsewhere. -/
def SubsistentActHasOnlyOwnSpecies {B S : Type}
    (OwnBeing : B → Prop) (ownForm : B → S)
    (ImmediateSpecies : B → S → Prop) : Prop :=
  ∀ g s, OwnBeing g → ImmediateSpecies g s → s = ownForm g

/-- OPEN self-intelligibility of essence: the source's own intelligible form
has the source as its *primary* object. This is objective aboutness, not yet
a subject's act of knowing. Aboutness of created effects is a separate relation. -/
def OwnFormPresentsSelf {B S : Type}
    (OwnBeing : B → Prop) (ownForm : B → S)
    (PrimaryAbout : S → B → Prop) : Prop :=
  ∀ g, OwnBeing g → PrimaryAbout (ownForm g) g

/-- OPEN intrinsic-intentional exercise rule. A formally actual intellectual
act apprehends the primary object of its immediate form. This is not a rule
that accurate production or an effect's cognition gives cognition to its cause;
the source must already actually be understanding in the selected ACT sense. -/
def ActApprehendsPrimaryObject {B R S : Type}
    (InAct : B → R → Prop) (understanding : R)
    (ImmediateSpecies : B → S → Prop) (PrimaryAbout : S → B → Prop)
    (Apprehends : B → B → Prop) : Prop :=
  ∀ g s x, InAct g understanding → ImmediateSpecies g s →
    PrimaryAbout s x → Apprehends g x

/-- Selected stronger interpretation of intrinsic cognitive grounding.
An actually apprehended object is grounded in the very source's immediate
intelligible form, not in a distinct secondary producer's true signal.
This profile can be used as the Grounded parameter of IntrinsicSelfKnowledge,
but does NOT establish an arbitrary prior Grounded primitive by definition. -/
def GroundedInOwnForm {B S : Type}
    (OwnBeing : B → Prop) (ownForm : B → S)
    (ImmediateSpecies : B → S → Prop) (PrimaryAbout : S → B → Prop)
    (Apprehends : B → B → Prop) (g x : B) : Prop :=
  OwnBeing g ∧ Apprehends g x ∧
    ∃ s, ImmediateSpecies g s ∧ s = ownForm g ∧ PrimaryAbout s x

end ImmanentSelfPresence


namespace Control

/-- One world-relative frame: the true source exists at both worlds,
the false effect at world true; the sole temporal presence agrees with
existence. The CAUSE_2 relation is literally the one in the upstream
wisdom source/effect control, not a new causes predicate. -/
def frame : CausalityFrame Bool Bool Unit Unit where
  history := {
    ontic := {
      frame := ⟨fun _ _ => True⟩
      ExistsAt := fun w x => x = true ∨ w = true
      Causes := fun _ _ _ => False
    }
    IsAt := fun w x _ => x = true ∨ w = true
    now := ()
  }
  GivesAt := fun _ _ _ _ => False
  CausesIn := TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.causesIn
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := ()

/-- The source true is a necessary, actual, ungrounded concretum; its
actual effect false is grounded by it at world true. Selected grounding
and CAUSE_2 remain different fields, related only by the OPEN adapter. -/
def rootProfile : TruthCore.Causality.BruteFoundationBoundary.Profile Bool Bool where
  ontic := frame.history.ontic
  concrete := fun _ => True
  grounds := fun w g x => w = true ∧ g = true ∧ x = false
def about (content x : Bool) : Prop := content = x
def correct (content x : Bool) : Prop := content = x
def none (_ _ _ _ : Bool) : Prop := False
def specifies (g self x other : Bool) : Prop :=
  g = true ∧ self = true ∧ x = false ∧ other = false

/-- A produced cognitive subject really apprehends its own true content,
while the productive source itself apprehends none. -/
def effectOnly (g content : Bool) : Prop := g = false ∧ content = false

/-- Both beings understand their own respective content, but the source does
not yet apprehend the *distinct* effect-directed content. -/
def selfOnly (g content : Bool) : Prop := g = content

/-- The source apprehends both contents; the effect still apprehends its own. -/
def sourceTakesUp (g content : Bool) : Prop :=
  g = true ∨ (g = false ∧ content = false)

def goodOwn (g : Bool) : Prop := g = true
def noWill (_ : Bool) : Prop := False

/-- A content-guided secondary response is correct without interference and
can be wrong with interference. This is a functional surrogate of a
producer/consumer system, not a reduction of cognitive norms to Boolean I/O. -/
def reading (state interference : Bool) : Bool :=
  if interference then !state else state

def guidedResponse (state interference : Bool) : Bool := reading state interference

/-- Three independently varying gaps on one fixed source/effect dictionary.
The first repairs #1866's effect-only *label* control with an effect that
actually apprehends and is cognitively grounded. Cases 2-4 test additional
exemplar specification and uptake while holding the source's true
self-understanding fixed. The fourth keeps actual-source knowledge separate
from the old, still-unrecognized unary HasWill interface. All are structural
surrogates; they do not certify metaphysical possibility of a rival. -/
def Controls : Prop :=
  AboutHasSingleReferent about ∧
  RootToEsseCauseAt frame rootProfile true ∧
  TruthCore.Causality.NecessaryRootFork.ActualRoot rootProfile true true ∧
  TruthCore.German.Kant.CosmologicalInference.NecessaryAt rootProfile.ontic true true ∧
  ActualConcrete rootProfile true false ∧
  TruthCore.Modal.TemporalHistory.CoherentAtNow frame.history ∧
  frame.CausesIn true false frame.esse ∧
  (TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.Background ∧
    IntrinsicSelfKnowledge about correct effectOnly effectOnly false ∧
    ¬ IntrinsicSelfKnowledge about correct effectOnly effectOnly true ∧
    ¬ WisdomSelfCapacity
      TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.own
      TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.has
      () about correct effectOnly ∧
    reading true false = true ∧ reading true true = false ∧
    reading false false = false ∧ reading false true = true ∧
    (∀ state interference, guidedResponse state interference = reading state interference)) ∧
  (IntrinsicSelfKnowledge about correct selfOnly selfOnly true ∧
    ¬ EffectExemplarCoverage frame true about correct none ∧
    CognitivelyTakesUpExemplar selfOnly selfOnly none ∧
    ¬ UnderstandsActualEffects frame true about correct selfOnly selfOnly true) ∧
  (EffectExemplarCoverage frame true about correct specifies ∧
    ¬ CognitivelyTakesUpExemplar selfOnly selfOnly specifies ∧
    ¬ UnderstandsActualEffects frame true about correct selfOnly selfOnly true) ∧
  (EffectExemplarCoverage frame true about correct specifies ∧
    CognitivelyTakesUpExemplar sourceTakesUp sourceTakesUp specifies ∧
    UnderstandsActualEffects frame true about correct
      sourceTakesUp sourceTakesUp true) ∧
  (SelfKnownGoodIsRepresented goodOwn about correct selfOnly selfOnly
      (fun _ => TruthCore.Causality.PossessionSensitiveAppetite.responsive) ∧
    TruthCore.Causality.PossessionSensitiveAppetite.Calibration
      TruthCore.Causality.PossessionSensitiveAppetite.responsive ∧
    TruthCore.Causality.PossessionSensitiveAppetite.Availability
      TruthCore.Causality.PossessionSensitiveAppetite.responsive ∧
    ¬ (∀ g, goodOwn g → noWill g))

end Control
end TruthCore.Causality.IntentionalExemplarExtension
/-! ## Objective eminent intelligibility and actual source-level noesis

C4 analyst fork. This is not another definition of HAS_INTELLECT_1 or the
q.14 source's intentional act. Objective exemplary and normative sufficiency is
stronger than mere power to produce an intelligent creature: the first source
itself is assigned an intelligible own form and a primitive Norms relation to
a real, apprehending secondary knower's correct content. Norms is
*interpreted* as a truth/correctness standard, but nothing here defines
Correct from Norms or otherwise constrains it. Nothing in that object-side
structure yet makes the source an apprehending subject. Whether this counts as
the *full pure perfection* of intellectual understanding is exactly the
substantive question, not something decided by these definitions.

A second fork isolates real constitutive plurality from distinct intentional
descriptions. It is one selected constituent sub-reading of the Plotinian
challenge, deliberately transposed onto OwnBeing bearers; it is not a faithful
definition of every Plotinian theory of noesis or of Thomistic simplicity.
These are analyst interpretations; source attribution is deferred.
-/
namespace TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence

open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding

/-- A nonvacuous intellectual effect of g: a distinct being actually and
intrinsically apprehends a correct self-directed content. Mere HAS_INTELLECT_1
labelling does not suffice. -/
def ProducesActualKnower {B C : Type}
    (CausesEsse : B → B → Prop) (About Correct : C → B → Prop)
    (Apprehends Grounded : B → C → Prop) (g : B) : Prop :=
  ∃ x, x ≠ g ∧ CausesEsse g x ∧
    IntrinsicSelfKnowledge About Correct Apprehends Grounded x

/-- A stronger OBJECTIVE reading of eminent intellectual containment.
The source has its own intelligible form, that form is primarily about the
source, and the source bears a norm-setting relation to each correct
self-directed content that an actual caused being apprehends (the clause
covers only contents about that caused being itself). Norms is an OPEN
constitutive/epistemic explanation, not just a causal edge or a successful
Boolean response; HasOwnForm, PrimaryAbout and Norms are otherwise
unconstrained primitives here. A real cognitive effect is required.
The reading does not assert that g itself exercises understanding.

The PrimaryAbout clause is deliberately the g-instance of #1879's
ImmanentSelfPresence.OwnFormPresentsSelf with the same PrimaryAbout relation,
not a fresh aboutness primitive, so that the same form witness can be fed to
ActApprehendsPrimaryObject (see eminentFormApprehendedIfActual).

Accepting this as *genuine higher-mode possession of intellectual perfection*
rather than intelligibility without intellection requires philosophical warrant.
It is NOT substituted for the old IN_ACT_4 or InActVirtually primitives. -/
def IntrinsicExemplarEminence {B C Form : Type}
    (OwnBeing : B → Prop) (ownForm : B → Form)
    (HasOwnForm : B → Form → Prop)
    (PrimaryAbout : Form → B → Prop)
    (Norms : B → Form → B → C → Prop)
    (CausesEsse : B → B → Prop) (About Correct : C → B → Prop)
    (Apprehends Grounded : B → C → Prop) (g : B) : Prop :=
  OwnBeing g ∧ HasOwnForm g (ownForm g) ∧
  PrimaryAbout (ownForm g) g ∧
  (∀ x c, CausesEsse g x → Apprehends x c →
    About c x → Correct c x → Norms g (ownForm g) x c) ∧
  ProducesActualKnower CausesEsse About Correct Apprehends Grounded g

/-- At most one real intrinsic constituent/aspect of the selected source,
not a denial of multiple descriptions or intentional relata. The real
constituent carrier Aspect is a separate type parameter, not identified with
the content or being carriers. -/
def ConstitutivelySimple {B Aspect : Type}
    (RealConstituent : B → Aspect → Prop) (g : B) : Prop :=
  ∀ a b, RealConstituent g a → RealConstituent g b → a = b

/-- OPEN *constitutive duality* reading of noesis: a subsistent subject's
actual self-understanding needs two genuinely distinct real constituents.
An intentional distinction that does not divide the source denies this
principle. This is a deliberate transposition of one constituent sub-reading
of the Plotinian objection onto OwnBeing bearers. Plotinus's more general claim
about intelligible articulation may not reduce to it (the strongest Plotinian
objection "survives merely removing two numerically different relata",
docs/immaterial-intellect-reception.md); that semantic question stays open.
RealConstituent occurs only here and in ConstitutivelySimple: it is linked to
no act, subject/object identity or intentional-distinction relation. -/
def SourceNoesisRequiresRealPlurality {B C Aspect : Type}
    (OwnBeing : B → Prop) (About Correct : C → B → Prop)
    (Apprehends Grounded : B → C → Prop)
    (RealConstituent : B → Aspect → Prop) : Prop :=
  ∀ g, OwnBeing g →
    IntrinsicSelfKnowledge About Correct Apprehends Grounded g →
      ∃ a b, RealConstituent g a ∧ RealConstituent g b ∧ a ≠ b

end TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence
