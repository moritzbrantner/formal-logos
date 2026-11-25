module

public import TruthCore.Epistemology.InitialHistoryAuthenticity
public import TruthCore.Causality.DivineVeracityContent1410

/-! # From a truthful source to an observed record

Analyst channel reconstruction. `History.ontic` supplies the unchanged existence
and causal relations; `Attitudes` and `Semantics` supply individuated assertions,
assents and world-relative truth. No new causal or cognitive truth predicate is
introduced. The channel's code, receipt and decoding are different maps.

The causal-token condition is deliberately weaker than intentional assertion.
A cause of a token need not assert the content a recipient reads from it.
Successful realization, assertoric scope, provenance and transmission therefore
remain explicit. Their applicability to actual historical evidence is OPEN.
The comparison controls have existing, necessarily present sources and nonempty
causal relations. They are structural interpretations, not complete theistic or
impersonal metaphysics, and supply no probabilities or epistemic entitlement.
-/

@[expose] public section

namespace TruthCore.Epistemology.SourceEvidenceAdequacy

open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Case.Catholicism
open TruthCore.Causality.DivineVeracityContent1410
open TruthCore.Logic.ReflectiveCoherence (Semantics)
open TruthCore.Epistemology.InitialHistoryAuthenticity (RecordsSound)

/-- A specified token code, observation channel and interpretation. `bearer`
locates a token in the existing ontology. These maps alone assert no correctness,
causation, actual occurrence, injectivity or availability to an inquirer.
`Message` can be individuated contents, or values in an exact-value report. -/
structure Channel (Being Message Token Observation : Type) where
  bearer : Token → Being
  encode : Message → Token
  receive : Token → Observation
  decode : Observation → Message

/-- Primitive plans to produce a sign expressing this very content. Planning a
fictional sign is permitted by this meaning; putting its content forward as true
requires the separate `AssertoricPlans` condition. Neither successful execution
nor the truth of the planned content is built in. -/
structure Intentions (World Being Content : Type) where
  Plans : World → Being → Content → Prop

/-- The same source and token bearer both exist, and the existing ordinary
causal relation links them in this history. This is not by definition an
assertion, an intention, immediate emission, or an account of divine causation. -/
def CausedToken (h : History I B T) (K : Channel B C R O)
    (i : I) (g : B) (r : R) : Prop :=
  h.ontic.ExistsAt i g ∧ h.ontic.ExistsAt i (K.bearer r) ∧
    h.ontic.Causes i g (K.bearer r)

/-- Every selected positive observation is actually received from a token
caused by this SAME source. Merely observing a convincing token does not prove
this provenance; a token from another producer does not satisfy it. -/
def Covered (h : History I B T) (K : Channel B C R O) (g : B)
    (allowed : I → Prop) (observe : I → O) (positive : O → Prop) : Prop :=
  ∀ i, allowed i → positive (observe i) →
    ∃ r, CausedToken h K i g r ∧ K.receive r = observe i

/-- All tokens caused by this source on the selected channel realize a planned
content in D by its specified code. This includes intentional coverage and
effective encoding; a mere intention to make truthful records is weaker. -/
def RealizesPlans (h : History I B T) (K : Channel B C R O)
    (P : Intentions I B C) (g : B) (allowed : I → Prop) (D : C → Prop) : Prop :=
  ∀ i, allowed i → ∀ r, CausedToken h K i g r →
    ∃ c, D c ∧ P.Plans i g c ∧ K.encode c = r

/-- Every selected plan is a genuine assertion by the same source of the
identical individuated content. This is an OPEN scope bridge; no lie prohibition
extends itself to every permitted causal trace. -/
def AssertoricPlans (σ : Signature) (P : Intentions I σ.Being C)
    (V : I → Attitudes σ C) (g : σ.Being) (allowed : I → Prop) : Prop :=
  ∀ i, allowed i → ∀ c, P.Plans i g c → (V i).Asserts g c

/-- Strong transmission condition on the named domain only: decoding a
received code recovers the very same message, not just a co-true content. -/
def ExactTransport (K : Channel B C R O) (D : C → Prop) : Prop :=
  ∀ c, D c → K.decode (K.receive (K.encode c)) = c

/-- Weaker transmission condition sufficient for truth: for admitted histories
and messages in D, true encoded content remains true after receipt/decoding.
It neither asserts original content truth nor preserves content identity. -/
def TruthTransport (S : Semantics I C) (K : Channel B C R O)
    (allowed : I → Prop) (D : C → Prop) : Prop :=
  ∀ i, allowed i → ∀ c, D c → S.trueAt i c →
    S.trueAt i (K.decode (K.receive (K.encode c)))

/-- Actual source tokens copy the supplied target value through the code.
This is a process constraint on the independently given target, not a definition
of record truth. Actual historical access to that target is an OPEN burden. -/
def CopiesTarget (h : History I B T) (K : Channel B C R O) (g : B)
    (allowed : I → Prop) (target : I → C) : Prop :=
  ∀ i, allowed i → ∀ r, CausedToken h K i g r → r = K.encode (target i)

/-- Conditional source-to-record assembly. Every premise uses the same history,
source, intended content, token and channel. The source truth premise is the
existing individuated-content target, required at each admitted history; its
truth at one actual history alone does not imply this uniform premise. -/
def SourceGuarantee : Prop :=
  ∀ (I C R O T : Type) (σ : Signature) (h : History I σ.Being T)
      (K : Channel σ.Being C R O) (P : Intentions I σ.Being C)
      (V : I → Attitudes σ C) (S : Semantics I C) (g : σ.Being)
      (allowed : I → Prop) (observe : I → O) (positive : O → Prop) (D : C → Prop),
    σ.IsGod g → σ.HasClassicalAttributes g →
    (∀ i, allowed i → ContentAssertionTruth σ S i (V i)) →
    AssertoricPlans σ P V g allowed → RealizesPlans h K P g allowed D →
    Covered h K g allowed observe positive → TruthTransport S K allowed D →
    RecordsSound allowed observe positive (fun o i => S.trueAt i (K.decode o))

/-- A nonmental sufficient mechanism for exact-value records. All selected
records come from the source; its actual tokens copy the target; encoding,
receipt and decoding recover that target on its actual range. No mental
predicate or God classification is a premise. It does not infer their negations. -/
def CopyGuarantee : Prop :=
  ∀ (I B C R O T : Type) (h : History I B T) (K : Channel B C R O) (g : B)
      (allowed : I → Prop) (observe : I → O) (positive : O → Prop)
      (target : I → C) (D : C → Prop),
    CopiesTarget h K g allowed target →
    (∀ i, allowed i → D (target i)) → ExactTransport K D →
    Covered h K g allowed observe positive →
    RecordsSound allowed observe positive (fun o i => K.decode o = target i)

namespace Control

abbrev Content := Bool × Bool
abbrev Being := Sum Bool Content
def source : Being := .inl true
def otherSource : Being := .inl false
def report (i : Bool) : Content := (i, false)
def contrary (i : Bool) : Content := (!i, false)
def all (_ : α) : Prop := True

/-- An independent tag preserves distinct co-true contents. -/
def semantics : Semantics Bool Content where
  trueAt i c := c.1 = i
  neg c := (!c.1, c.2)
  neg_true_iff := by
    intro i ⟨b, tag⟩
    cases i <;> cases b <;> cases tag <;> decide

/-- Every bearer is present in both admitted histories, and each source causes
an actual token. The designated source's output can vary while its identity and
presence remain fixed. This is no complete model of necessity or causation. -/
def history (output : Bool → Content) : History Bool Being Unit where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => True
    Causes := fun i g b =>
      (g = source ∧ b = .inr (output i)) ∨
      (g = otherSource ∧ b = .inr (contrary i))
  }
  IsAt := fun _ _ _ => True
  now := ()

/-- A skeleton classifier, not an interpretation of every classical attribute.
The cognitive/assertoric conjuncts below do the work separately. -/
def signature : Signature where
  Being := Being
  IsGod := fun g => g = source
  HasClassicalAttributes := fun g => g = source
  RevealsRecognizably := fun _ => False
  jesus := source
  ClaimedDivineAuthority := fun _ => False
  RoseFromTheDead := fun _ => False
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => False
  VisibleWithAuthority := fun _ => False
  FoundedAsTeachingAuthority := fun _ _ => False
  DefinitivelyProposesAsRevealed := fun _ _ => False
  creedOneGodFatherAlmightyCreator := True
  creedOneLordJesusChristOnlyBegottenConsubstantial := True
  creedIncarnateOfSpiritAndVirginMary := True
  creedCrucifiedUnderPilateSufferedBuried := True
  creedRoseOnTheThirdDay := True
  creedAscendedSeatedAtRightHand := True
  creedWillComeToJudgeKingdomWithoutEnd := True
  creedHolySpiritLordGiverOfLife := True
  creedOneHolyCatholicApostolicChurch := True
  creedOneBaptismForForgiveness := True
  creedResurrectionOfTheDead := True
  creedLifeOfTheWorldToCome := True

def attitudes (i : Bool) : Attitudes signature Content where
  Asserts g c := g = source ∧ c = report i
  Assents g c := g = source ∧ semantics.trueAt i c

def noAttitudes (_ : Bool) : Attitudes signature Content where
  Asserts := fun _ _ => False
  Assents := fun _ _ => False

def plans (intended : Bool → Content) : Intentions Bool Being Content where
  Plans i g c := g = source ∧ c = intended i

def noPlans : Intentions Bool Being Content where
  Plans := fun _ _ _ => False

def channel (transfer : Content → Content) : Channel Being Content Content Content where
  bearer := Sum.inr
  encode := id
  receive := transfer
  decode := id

def corrupt (c : Content) : Content := (!c.1, c.2)
def retag (c : Content) : Content := (c.1, !c.2)

def Sound (transfer : Content → Content) (observe : Bool → Content) : Prop :=
  RecordsSound all observe all (fun o i => semantics.trueAt i ((channel transfer).decode o))

/-- The same source actually asserts in every history, is sincere, complete
and accurate on all represented contents, and never asserts a counter-belief.
These are explicit finite assignments, not a divine-cognition mechanism. -/
def InformedSource : Prop :=
  signature.IsGod source ∧ signature.HasClassicalAttributes source ∧
  ∀ i, (attitudes i).Asserts source (report i) ∧
    ContentSincere signature (attitudes i) ∧
    ScopedAccuracy signature semantics i (attitudes i) all ∧
    DomainComplete signature semantics i (attitudes i) all ∧
    CounterComplete signature semantics i (attitudes i) ∧
    NoContraryAssertion signature semantics (attitudes i) ∧
    ContentAssertionTruth signature semantics i (attitudes i)

/-- Joint positive control with actual, distinct readouts and causal tokens.
The source is necessarily present relative to the stipulated universal frame. -/
def PositiveControl : Prop :=
  InformedSource ∧
  (∀ i, NecessaryAt (history report).ontic i source ∧
    CausedToken (history report) (channel id) i source (report i)) ∧
  AssertoricPlans signature (plans report) attitudes source all ∧
  RealizesPlans (history report) (channel id) (plans report) source all all ∧
  Covered (history report) (channel id) source all report all ∧
  ExactTransport (channel id) all ∧ Sound id report ∧ report false ≠ report true

/-- Planned but nonassertoric false signs, ineffective truthful plans, corrupted
transmission, and a token from another source. Each control retains the same
truthful, informed asserting source and a populated causal history. -/
def OmissionControls : Prop :=
  InformedSource ∧
  (RealizesPlans (history contrary) (channel id) (plans contrary) source all all ∧
    Covered (history contrary) (channel id) source all contrary all ∧
    TruthTransport semantics (channel id) all all ∧
    ¬ AssertoricPlans signature (plans contrary) attitudes source all ∧
    ¬ Sound id contrary) ∧
  (AssertoricPlans signature (plans report) attitudes source all ∧
    Covered (history contrary) (channel id) source all contrary all ∧
    TruthTransport semantics (channel id) all all ∧
    ¬ RealizesPlans (history contrary) (channel id) (plans report) source all all ∧
    ¬ Sound id contrary) ∧
  (AssertoricPlans signature (plans report) attitudes source all ∧
    RealizesPlans (history report) (channel corrupt) (plans report) source all all ∧
    Covered (history report) (channel corrupt) source all
      (fun i => corrupt (report i)) all ∧
    ¬ TruthTransport semantics (channel corrupt) all all ∧
    ¬ Sound corrupt (fun i => corrupt (report i))) ∧
  (AssertoricPlans signature (plans report) attitudes source all ∧
    RealizesPlans (history report) (channel id) (plans report) source all all ∧
    TruthTransport semantics (channel id) all all ∧
    Covered (history report) (channel id) otherSource all contrary all ∧
    ¬ Covered (history report) (channel id) source all contrary all ∧
    ¬ Sound id contrary)

/-- Truth preservation does not require identical content. The transfer flips
only an independent tag, keeping both actual source tokens and varying readouts. -/
def SemanticTransportControl : Prop :=
  TruthTransport semantics (channel retag) all all ∧
  ¬ ExactTransport (channel retag) all ∧
  (∀ i, report i ≠ retag (report i) ∧
    (semantics.trueAt i (report i) ↔ semantics.trueAt i (retag (report i)))) ∧
  Covered (history report) (channel retag) source all (fun i => retag (report i)) all ∧
  Sound retag (fun i => retag (report i))

/-- The very same source, causal tokens and exact transport also instantiate
the copying guarantee when all represented plans and attitudes are absent.
This tests functional parity; absence of these attitudes is not a complete
analysis of mindlessness, and existence necessity alone explains no truth. -/
def NonmentalControl : Prop :=
  (∀ i, NecessaryAt (history report).ontic i source ∧
    CausedToken (history report) (channel id) i source (report i)) ∧
  (∀ i c, ¬ noPlans.Plans i source c ∧
    ¬ (noAttitudes i).Asserts source c ∧ ¬ (noAttitudes i).Assents source c) ∧
  CopiesTarget (history report) (channel id) source all report ∧
  Covered (history report) (channel id) source all report all ∧
  ExactTransport (channel id) all ∧
  RecordsSound all report all (fun o i => (channel id).decode o = report i) ∧
  Sound id report

end Control
end TruthCore.Epistemology.SourceEvidenceAdequacy
