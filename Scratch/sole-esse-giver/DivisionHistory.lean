import TruthCore.Results.Causality.IntentionalExemplarExtension.Solution
import TruthCore.Causality.ComprehensionByMeasure

/-! Matched interventions on the right inlet in the division control.
The trigger that reroutes the inlet can come from either of two agents. The
physical gate retains its routing, without storing the identity of the sender.
The audit below reconstructs that identity from the events, not from the gate. -/
namespace DivisionHistory

open TruthCore.Causality.IntentionalExemplarExtension
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding (IntrinsicSelfKnowledge)

inductive Sender | parent | neighbor deriving DecidableEq
structure PulsePair where
  atCut : Option Sender
  afterCut : Option Sender

/-- The first pulse opens the inlet; any later pulse leaves the open gate alone. -/
def gate (openAlready : Bool) (pulse : Option Sender) : Bool :=
  openAlready || pulse.isSome

def agentAtOnset (p : PulsePair) := p.atCut
def routing (p : PulsePair) : Bool × Bool :=
  let atCut := gate false p.atCut
  (atCut, gate atCut p.afterCut)

def parentFirst : PulsePair := ⟨some .parent, some .neighbor⟩
def neighborFirst : PulsePair := ⟨some .neighbor, some .parent⟩

theorem onsetTest :
    routing parentFirst = (true, true) ∧ routing neighborFirst = (true, true) ∧
    routing ⟨none, parentFirst.afterCut⟩ = (false, true) ∧
    routing ⟨parentFirst.atCut, none⟩ = (true, true) ∧
    routing ⟨none, neighborFirst.afterCut⟩ = (false, true) ∧
    routing ⟨neighborFirst.atCut, none⟩ = (true, true) := by decide

theorem noOnsetAttributionFromRouting :
    ¬ ∃ identify : Bool × Bool → Option Sender,
        identify (routing parentFirst) = agentAtOnset parentFirst ∧
        identify (routing neighborFirst) = agentAtOnset neighborFirst := by
  rintro ⟨_, a, b⟩
  have same : agentAtOnset parentFirst = agentAtOnset neighborFirst := a.symm.trans b
  cases same

inductive Content | gives | orders (sender : Sender) | localAtCut | openedBy (sender : Sender)
  deriving DecidableEq

def about : Content → Bool → Prop
  | .gives, x | .orders _, x => x = true
  | _, x => x = false

def correct (order : Option Sender) (p : PulsePair) : Content → Bool → Prop
  | .gives, x => x = true
  | .orders a, x => x = true ∧ order = some a
  | .localAtCut, x => x = false ∧ (routing p).1 = true
  | .openedBy a, x => x = false ∧ agentAtOnset p = some a

/-- The source apprehends its giving and the recipient's actual local supply.
The signature makes these two actual, grounded contents explicit premises of
the example. It does not define intellectual grounding as a physical signal. -/
def common (s : Bool) (c : Content) : Prop :=
  s = true ∧ (c = .gives ∨ c = .localAtCut)
def exemplar (s : Bool) (self : Content) (x : Bool) (other : Content) : Prop :=
  s = true ∧ self = .gives ∧ x = false ∧ other = .localAtCut

/-- On the established source/effect frame, even effect exemplar coverage and
actual grounded uptake can be held fixed across the two production histories. -/
theorem commonKnowledge (p : PulsePair) (atCut : (routing p).1 = true) :
    IntrinsicSelfKnowledge about (correct none p) common common true ∧
    EffectExemplarCoverage Control.frame true about (correct none p) exemplar ∧
    CognitivelyTakesUpExemplar common common exemplar ∧
    UnderstandsActualEffects Control.frame true about (correct none p) common common true ∧
    (∀ a, ¬ common true (.openedBy a)) := by
  have self : IntrinsicSelfKnowledge about (correct none p) common common true :=
    ⟨.gives, rfl, rfl, ⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inl rfl⟩⟩
  have coverage : EffectExemplarCoverage Control.frame true about (correct none p) exemplar := by
    intro g c x _ cause ab truth
    obtain ⟨rfl, rfl⟩ := cause
    have hc : c = .gives := by cases c <;> simp_all [about, correct]
    exact ⟨.localAtCut, ⟨rfl, hc, rfl, rfl⟩, rfl, rfl, atCut⟩
  have uptake : CognitivelyTakesUpExemplar common common exemplar := by
    rintro _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨⟨rfl, Or.inr rfl⟩, ⟨rfl, Or.inr rfl⟩⟩
  exact ⟨self, coverage, uptake,
    TruthCore.Results.Causality.IntentionalExemplarExtension.understandsCausedEffectsFromSelfAndExemplars
      _ _ _ _ _ _ _ coverage uptake _ self, by simp [common]⟩

/-- An addressed effective order: the selected channel alone receives the
release at the cut. The other receives it afterward. -/
def releaseAtCut : Sender → PulsePair
  | .parent => parentFirst
  | .neighbor => neighborFirst

/-- A true order-content survives a swap of the arrivals. The diagnosis
of the effective sender then changes despite the unchanged final routing. -/
theorem reorderedDelivery :
    correct (some .parent) neighborFirst (.orders .parent) true ∧
    ¬ correct (some .parent) neighborFirst (.openedBy .parent) false ∧
    correct (some .parent) neighborFirst (.openedBy .neighbor) false := by
  refine ⟨⟨rfl, rfl⟩, ?_, ⟨rfl, rfl⟩⟩
  intro h
  cases h.2

theorem knowledgeFromEffectiveOrder (channel : Sender)
    (takes grounds : Bool → Content → Prop)
    (hUptake : CognitivelyTakesUpExemplar takes grounds
      (fun g self x other => g = true ∧ self = .orders channel ∧ x = false ∧ other = .openedBy channel))
    (hSelf : takes true (.orders channel) ∧ grounds true (.orders channel)) :
    about (.openedBy channel) false ∧ correct (some channel) (releaseAtCut channel) (.openedBy channel) false ∧
    takes true (.openedBy channel) ∧ grounds true (.openedBy channel) := by
  refine ⟨rfl, ⟨rfl, ?_⟩, hUptake _ _ _ _ hSelf.1 hSelf.2 ⟨rfl, rfl, rfl, rfl⟩⟩
  cases channel <;> rfl

/-- Calibrating an exhaustive intrinsic profile is a separate requirement.
Only the inequality from knowability to every upper bound is needed; the
converse condition that knowability bounds each grade is unused. One *realized*
knowing must cover the profile at a single degree. A different knowing for
each aspect would require a further integration argument. -/
theorem comprehendsCalibratedProfile {B D Aspect : Type} [Preorder D]
    (M : TruthCore.Causality.ComprehensionByMeasure.Measures B D)
    (s x : B) (grade : Aspect → D) (d : D)
    (hLeast : ∀ bound, (∀ a, grade a ≤ bound) → M.knowability x ≤ bound)
    (hKnows : M.KnowsAt s x d) (hReaches : ∀ a, grade a ≤ d) :
    TruthCore.Causality.ComprehensionByMeasure.ComprehendsByMeasure M s x :=
  ⟨d, hKnows, hLeast d hReaches⟩

#print axioms onsetTest
#print axioms noOnsetAttributionFromRouting
#print axioms commonKnowledge
#print axioms reorderedDelivery
#print axioms knowledgeFromEffectiveOrder
#print axioms comprehendsCalibratedProfile
end DivisionHistory
