module

public import TruthCore.Causality.Q44EssentialSource
public import TruthCore.Causality.TermSenseForks2
public import TruthCore.Causality.ReceptionLimitation

/-! Analyst common-ancestor application to q44 source supply. All causation is
at the same profile's esse respect. Composition is a substantive premise, not
the definition of causation; identity is not the definition of OwnBeing. -/

@[expose] public section
namespace TruthCore.Causality.Q44SourceSupply
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause)

/-- OPEN composition premise: an actual a causally responsible for b's esse is
also responsible for c's esse when b is an actual distinct cause of c's esse.
This propagates one causal-responsibility edge along an actual esse-cause link;
it says nothing about causes of becoming, different respects or modal frames. -/
def ActualEsseCauseComposes {B P R : Type} (f : Profile B P R) : Prop :=
  ∀ a b c, f.InAct a f.esse → f.CausesIn a b f.esse → ActualEsseCause f b c →
    f.CausesIn a c f.esse

/-- The selected p supplies each participant's esse as a distinct actual
OwnBeing cause. This concludes a particular witness for source supply, not
identity of every possible own-being cause with p or GOD_4 identification. -/
def SelectedEssentialSourceSupply {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (p : B) : Prop :=
  ∀ x, Participated x → p ≠ x ∧ f.InAct p f.esse ∧ OwnBeing p ∧ f.CausesIn p x f.esse

namespace Control
abbrev Being := TruthCore.Causality.Q44EssentialSource.Control.Three
open TruthCore.Causality.Q44EssentialSource.Control.Three
open TruthCore.Causality.TermSenseForks (BecomingBeingFrame ParticipatedHasDistinctEsse)
open TruthCore.Latin.Aquinas.DeEnte
  (CommonEsseIsEssenceSource AtMostOneEsseIsEssence ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Causality.EsseReception
  (EsseReceivedOnlyInOwnEssence NothingInReceptivePotencyToItself)
open TruthCore.Causality.ReceptionLimitation (UnreceivedEsseIsOwnBeing)
open TruthCore.Causality.Q44EssentialSource (SelectedActualIdentity ParticipatedHasEssentialSource)

def profile (actual : Being → Prop) (identity : Being → Bool)
    (cause : Being → Being → Prop) : Profile Being Bool Unit where
  InAct := fun x _ => actual x
  CausesIn := fun c x _ => cause c x
  essenceOf := fun _ => false
  esseOf := identity
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

def oneIdentity (c : Being) : Bool := if c = primary then false else true
def twoIdentity (c : Being) : Bool := if c = effect then true else false
def starCause (c x : Being) : Prop := c = primary ∧ x ≠ primary
def chainCause (c x : Being) : Prop :=
  (c = primary ∧ x = source) ∨ (c = source ∧ x = effect)
def fullCause (c x : Being) : Prop := starCause c x ∨ (c = source ∧ x = effect)

def star := profile (fun _ => True) oneIdentity starCause
def chain := profile (fun _ => True) oneIdentity chainCause
def full := profile (fun _ => True) oneIdentity fullCause
def two := profile (fun _ => True) twoIdentity starCause
def absent := profile (fun x => x ≠ effect) oneIdentity (fun c x => c = primary ∧ x = source)

def frame (f : Profile Being Bool Unit) (participated : Being → Prop) :
    BecomingBeingFrame Being Bool Unit := ⟨f, fun _ _ => False, participated⟩
def justEffect (x : Being) : Prop := x = effect
def justPrimary (x : Being) : Prop := x = primary
def other (x : Being) : Prop := x ≠ primary

/-- Assignments in finite controls only, not a definition of OwnBeing. -/
def own (f : Profile Being Bool Unit) (x : Being) : Prop := f.esseOf x = f.essenceOf x
def received (f : Profile Being Bool Unit) (x : Being) (r : Bool) : Prop :=
  f.esseOf x ≠ f.essenceOf x ∧ r = false
def potency (r a : Bool) : Prop := r = false ∧ a = true

/-- Only a grouping of the four unchanged reception premises in closed
control certificates; no argument takes this as an opaque open premise. -/
def ReceptionInputs (f : Profile Being Bool Unit) (Own : Being → Prop) : Prop :=
  EsseReceivedOnlyInOwnEssence f.essenceOf (received f) ∧
  ReceiverInPotencyToReceivedEsseReading f.esseOf (received f) potency ∧
  NothingInReceptivePotencyToItself potency ∧ UnreceivedEsseIsOwnBeing (received f) Own

/-- Participant actuality and distinction are tested separately; then causal
composition, the unreceived-to-own-being interpretation, selected identity and
numerical uniqueness are omitted in turn. The positive interpretation exercises
composition along primary → source → effect as well as primary → effect. -/
def Certificate : Prop :=
  (CommonEsseIsEssenceSource absent ∧ ActualEsseCauseComposes absent ∧
    ReceptionInputs absent (own absent) ∧
    (∀ x, justEffect x → absent.esseOf x ≠ absent.essenceOf x) ∧
    ¬ (∀ x, justEffect x → absent.InAct x absent.esse) ∧
    ¬ ParticipatedHasEssentialSource absent justEffect (own absent)) ∧
  (CommonEsseIsEssenceSource star ∧ ActualEsseCauseComposes star ∧
    ReceptionInputs star (own star) ∧
    (∀ x, justPrimary x → star.InAct x star.esse) ∧
    ¬ (∀ x, justPrimary x → star.esseOf x ≠ star.essenceOf x) ∧
    ¬ ParticipatedHasEssentialSource star justPrimary (own star)) ∧
  (CommonEsseIsEssenceSource chain ∧
    ParticipatedHasDistinctEsse (frame chain justEffect) ∧ ReceptionInputs chain (own chain) ∧
    ¬ ActualEsseCauseComposes chain ∧
    ¬ ParticipatedHasEssentialSource chain justEffect (own chain)) ∧
  (CommonEsseIsEssenceSource star ∧
    ParticipatedHasDistinctEsse (frame star justEffect) ∧ ActualEsseCauseComposes star ∧
    EsseReceivedOnlyInOwnEssence star.essenceOf (received star) ∧
    ReceiverInPotencyToReceivedEsseReading star.esseOf (received star) potency ∧
    NothingInReceptivePotencyToItself potency ∧
    ¬ UnreceivedEsseIsOwnBeing (received star) (fun _ => False) ∧
    ¬ ParticipatedHasEssentialSource star justEffect (fun _ => False)) ∧
  (CommonEsseIsEssenceSource star ∧
    ParticipatedHasDistinctEsse (frame star justEffect) ∧ ActualEsseCauseComposes star ∧
    ReceptionInputs star (own star) ∧ AtMostOneEsseIsEssence star ∧
    ¬ SelectedActualIdentity star source ∧
    ¬ SelectedEssentialSourceSupply star justEffect (own star) source) ∧
  (CommonEsseIsEssenceSource two ∧
    ParticipatedHasDistinctEsse (frame two justEffect) ∧ ActualEsseCauseComposes two ∧
    ReceptionInputs two (own two) ∧ SelectedActualIdentity two source ∧
    ¬ AtMostOneEsseIsEssence two ∧
    ¬ SelectedEssentialSourceSupply two justEffect (own two) source) ∧
  (CommonEsseIsEssenceSource full ∧ ParticipatedHasDistinctEsse (frame full other) ∧
    ActualEsseCauseComposes full ∧ ReceptionInputs full (own full) ∧
    AtMostOneEsseIsEssence full ∧ SelectedActualIdentity full primary ∧
    SelectedEssentialSourceSupply full other (own full) primary ∧
    ParticipatedHasEssentialSource full other (own full) ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
      (TruthCore.Causality.CreatureSenses.IsCreatureOfUniversalCause
        full.InAct full.CausesIn full.esse) primary)
end Control
end TruthCore.Causality.Q44SourceSupply
