module

public import TruthCore.Epistemology.SourceEvidenceAdequacy
public import TruthCore.Results.Causality.DivineVeracityContent1410.Solution

@[expose] public section

namespace TruthCore.Results.Epistemology.SourceEvidenceAdequacy
open TruthCore.Epistemology.SourceEvidenceAdequacy
open TruthCore.Logic.ReflectiveCoherence (Semantics)
open TruthCore.Causality.DivineVeracityContent1410
  (ContentSincere ScopedAccuracy AssertionsInDomain ContentAssertionTruth
    DomainComplete NegationClosed CounterComplete NoContraryAssertion)

theorem transportWeakens {I B C R O : Type} (S : Semantics I C)
    (K : Channel B C R O) (allowed : I → Prop) (D : C → Prop)
    (h0 : ExactTransport K D) : TruthTransport S K allowed D := by
  intro i _ c inDomain trueContent
  rw [h0 c inDomain]
  exact trueContent

theorem sourceGuarantee : SourceGuarantee := by
  intro I C R O T σ h K P V S g allowed observe positive D
    isGod attributes truthful assertoric realizes covered transport i admitted selected
  obtain ⟨r, caused, received⟩ := covered i admitted selected
  obtain ⟨c, inDomain, planned, encoded⟩ := realizes i admitted r caused
  have trueContent := truthful i admitted g isGod attributes c
    (assertoric i admitted c planned)
  have trueReceipt := transport i admitted c inDomain trueContent
  rw [encoded, received] at trueReceipt
  exact trueReceipt

theorem copyGuarantee : CopyGuarantee := by
  intro I B C R O T h K g allowed observe positive target D
    copying inDomain exactTransport covered i admitted selected
  obtain ⟨r, caused, received⟩ := covered i admitted selected
  have copied := copying i admitted r caused
  have recovered := exactTransport (target i) (inDomain i admitted)
  rw [← copied, received] at recovered
  exact recovered

open TruthCore.Epistemology.SourceEvidenceAdequacy.Control

private theorem causedSource (output : Bool → Content)
    (transfer : Content → Content) (i : Bool) :
    CausedToken (history output) (channel transfer) i source (output i) := by
  exact ⟨True.intro, True.intro, Or.inl ⟨rfl, rfl⟩⟩

private theorem sourceTokenEq (output : Bool → Content)
    (transfer : Content → Content) (i : Bool) (r : Content)
    (caused : CausedToken (history output) (channel transfer) i source r) :
    r = output i := by
  rcases caused.2.2 with ⟨_, token⟩ | ⟨wrongSource, _⟩
  · exact Sum.inr.inj token
  · have impossible : true = false := Sum.inl.inj wrongSource
    cases impossible

private theorem sourceCovered (output : Bool → Content)
    (transfer : Content → Content) :
    Covered (history output) (channel transfer) source all
      (fun i => transfer (output i)) all := by
  intro i _ _
  exact ⟨output i, causedSource output transfer i, rfl⟩

private theorem realizes (output : Bool → Content)
    (transfer : Content → Content) :
    RealizesPlans (history output) (channel transfer) (plans output) source all all := by
  intro i _ r caused
  exact ⟨output i, True.intro, ⟨rfl, rfl⟩,
    (sourceTokenEq output transfer i r caused).symm⟩

private theorem truthfulPlans :
    AssertoricPlans signature (plans report) attitudes source all := by
  intro i _ c planned
  exact planned

private theorem exactIdentity : ExactTransport (channel id) all := by
  intro c _
  rfl

private theorem truthIdentity : TruthTransport semantics (channel id) all all :=
  transportWeakens semantics (channel id) all all exactIdentity

private theorem informed : InformedSource := by
  refine ⟨rfl, rfl, ?_⟩
  intro i
  have sincere : ContentSincere signature (attitudes i) := by
    intro g _ _ c asserted
    refine ⟨asserted.1, ?_⟩
    change c.1 = i
    rw [asserted.2]
    rfl
  have accurate : ScopedAccuracy signature semantics i (attitudes i) all := by
    intro g _ _ c _ assented
    exact assented.2
  have coverage : AssertionsInDomain signature (attitudes i) all := by
    intro g _ _ c _
    trivial
  have trueAssertions : ContentAssertionTruth signature semantics i (attitudes i) :=
    TruthCore.Results.Causality.DivineVeracityContent1410.contentRouteA
      signature semantics i (attitudes i) all sincere accurate coverage
  have complete : DomainComplete signature semantics i (attitudes i) all := by
    intro g isGod _ c _ trueContent
    exact ⟨isGod, trueContent⟩
  have negClosed : NegationClosed semantics all := by
    intro c _
    trivial
  have counterComplete : CounterComplete signature semantics i (attitudes i) :=
    TruthCore.Results.Causality.DivineVeracityContent1410.counterCompleteFromDomain
      signature semantics i (attitudes i) all complete coverage negClosed
  have noContrary : NoContraryAssertion signature semantics (attitudes i) := by
    intro g isGod attributes c asserted contraryAssent
    exact (semantics.neg_true_iff i c).mp contraryAssent.2
      (trueAssertions g isGod attributes c asserted)
  exact ⟨⟨rfl, rfl⟩, sincere, accurate, complete, counterComplete, noContrary, trueAssertions⟩

private theorem necessaryAndCaused (i : Bool) :
    TruthCore.German.Kant.CosmologicalInference.NecessaryAt
      (history report).ontic i source ∧
    CausedToken (history report) (channel id) i source (report i) := by
  refine ⟨?_, causedSource report id i⟩
  intro v _
  trivial

private theorem soundIdentity : Sound id report := by
  intro i _ _
  rfl

private theorem contraryUnsound : ¬ Sound id contrary := by
  intro sound
  have impossible : true = false := sound false True.intro True.intro
  cases impossible

theorem positiveControl : Control.PositiveControl := by
  refine ⟨informed, necessaryAndCaused, truthfulPlans, realizes report id,
    sourceCovered report id, exactIdentity, soundIdentity, ?_⟩
  intro same
  have impossible : false = true := congrArg Prod.fst same
  cases impossible

theorem omissionControls : Control.OmissionControls := by
  refine ⟨informed, ?_, ?_, ?_, ?_⟩
  · refine ⟨realizes contrary id, sourceCovered contrary id, truthIdentity,
      ?_, contraryUnsound⟩
    intro assertoric
    have asserted := assertoric false True.intro (contrary false) ⟨rfl, rfl⟩
    have impossible : true = false := congrArg Prod.fst asserted.2
    cases impossible
  · refine ⟨truthfulPlans, sourceCovered contrary id, truthIdentity,
      ?_, contraryUnsound⟩
    intro realized
    obtain ⟨c, _, planned, encoded⟩ :=
      realized false True.intro (contrary false) (causedSource contrary id false)
    have same : report false = contrary false := planned.2.symm.trans encoded
    have impossible : false = true := congrArg Prod.fst same
    cases impossible
  · refine ⟨truthfulPlans, realizes report corrupt, sourceCovered report corrupt,
      ?_, ?_⟩
    · intro faithful
      have impossible : true = false :=
        faithful false True.intro (report false) True.intro rfl
      cases impossible
    · intro sound
      have impossible : true = false := sound false True.intro True.intro
      cases impossible
  · refine ⟨truthfulPlans, realizes report id, truthIdentity, ?_, ?_, contraryUnsound⟩
    · intro i _ _
      exact ⟨contrary i, ⟨True.intro, True.intro, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩
    · intro covered
      obtain ⟨r, caused, received⟩ := covered false True.intro True.intro
      have same : report false = contrary false :=
        (sourceTokenEq report id false r caused).symm.trans received
      have impossible : false = true := congrArg Prod.fst same
      cases impossible

theorem semanticTransportControl : Control.SemanticTransportControl := by
  refine ⟨?_, ?_, ?_, sourceCovered report retag, ?_⟩
  · intro i _ c _ trueContent
    exact trueContent
  · intro faithful
    have same := faithful (report false) True.intro
    have impossible : true = false := congrArg Prod.snd same
    cases impossible
  · intro i
    constructor
    · intro same
      have impossible : false = true := congrArg Prod.snd same
      cases impossible
    · exact Iff.rfl
  · intro i _ _
    rfl

theorem nonmentalControl : Control.NonmentalControl := by
  refine ⟨necessaryAndCaused, ?_, ?_, sourceCovered report id, exactIdentity, ?_, soundIdentity⟩
  · intro i c
    exact ⟨False.elim, False.elim, False.elim⟩
  · intro i _ r caused
    exact sourceTokenEq report id i r caused
  · intro i _ _
    rfl

end TruthCore.Results.Epistemology.SourceEvidenceAdequacy
