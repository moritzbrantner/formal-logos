module

public import TruthCore.Causality.IntentionalExemplarExtension
public import TruthCore.Results.Causality.PossessionSensitiveAppetite.Solution

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
