module

public import TruthCore.Logic.FirstPersonWitness

@[expose] public section

namespace TruthCore.Results.Logic.FirstPersonWitness

open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.Round2ExistenceAct
  (AgentOfEpisodeBearsIt BearerExistsWhereEpisodeOccurs OccurringThoughtOccursAt)
open TruthCore.Causality.Round3CogitoBase (DoubtIsPerformed PerformedDoubtIsThought)
open TruthCore.German.Kant.CosmologicalInference (Ontic ContingentAt)
open TruthCore.Logic.AssertionRetorsion (AssertionMade AssertionRealized SomeExistent)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Logic.FirstPersonWitness
open TruthCore.Ontology.ConcreteAbstract (HasEsseInRe)

/-- Local witness transfer. The two existence and classification inputs are
pointwise sufficient for the very candidate bearing the local episode. -/
theorem bearingHere {W B Episode : Type} (m : Ontic W B) (w : W)
    (OccursAt : W → Episode → Prop) (Bears : B → Episode → Prop)
    (concrete : B → Prop) (b : B) (e : Episode)
    (here : OccursAt w e) (borne : Bears b e)
    (presence : OccursAt w e → Bears b e → m.ExistsAt w b)
    (classify : m.ExistsAt w b → concrete b) :
    Bears b e ∧ m.ExistsAt w b ∧ concrete b :=
  let existsHere := presence here borne
  ⟨borne, existsHere, classify existsHere⟩

/-- The asserter, realizer and bearer are retained together. The hypothesis
on agency imposes bearing by that asserter for the matching local episode. -/
theorem assertionWitness {W B R Content Episode : Type} (m : Ontic W B) (w : W)
    (InAct : B → R → Prop) (esse : R) (OccursAt : W → Episode → Prop)
    (Bears : B → Episode → Prop) (Asserts : B → Content → Prop) (claim : Content)
    (Realizes : B → Content → Episode → Prop)
    (made : AssertionMade Asserts claim)
    (realized : AssertionRealized Asserts claim (OccursAt w) Realizes)
    (alignment : AgentOfEpisodeBearsIt (AssertionAgency Asserts claim (OccursAt w) Realizes) Bears)
    (presence : BearerExistsWhereEpisodeOccurs m OccursAt Bears)
    (classify : ExistingInActAt m InAct esse w) :
    ∃ b e, AssertionAgency Asserts claim (OccursAt w) Realizes b e ∧
      Bears b e ∧ m.ExistsAt w b ∧ HasEsseInRe InAct esse b := by
  obtain ⟨b, asserted⟩ := made
  obtain ⟨e, here, realizes⟩ := realized b asserted
  have agency : AssertionAgency Asserts claim (OccursAt w) Realizes b e :=
    ⟨asserted, here, realizes⟩
  exact ⟨b, e, agency, bearingHere m w OccursAt Bears _ b e here (alignment b e agency)
    (presence w b e) (classify b)⟩

/-- The realized act and its assigned performer occur in the same witness
chain. Bearing and selected-world existence enter as separate hypotheses. -/
theorem doubtWitness {W B R Act Episode : Type} (m : Ontic W B) (w : W)
    (InAct : B → R → Prop) (esse : R) (OccursAt : W → Episode → Prop)
    (Bears : B → Episode → Prop) (Performed DoubtsThought : Act → Prop)
    (performer : Act → B) (Realizes : Act → Episode → Prop)
    (made : DoubtIsPerformed Performed DoubtsThought)
    (realized : PerformedDoubtIsThought Performed DoubtsThought (OccursAt w) Realizes)
    (alignment : AgentOfEpisodeBearsIt
      (DoubtAgency Performed DoubtsThought performer (OccursAt w) Realizes) Bears)
    (presence : BearerExistsWhereEpisodeOccurs m OccursAt Bears)
    (classify : ExistingInActAt m InAct esse w) :
    ∃ a e, Performed a ∧ DoubtsThought a ∧ OccursAt w e ∧ Realizes a e ∧
      Bears (performer a) e ∧ m.ExistsAt w (performer a) ∧ HasEsseInRe InAct esse (performer a) := by
  obtain ⟨a, performed, doubts⟩ := made
  obtain ⟨e, here, realizes⟩ := realized a performed doubts
  have agency : DoubtAgency Performed DoubtsThought performer (OccursAt w) Realizes (performer a) e :=
    ⟨a, performed, doubts, here, realizes, rfl⟩
  exact ⟨a, e, performed, doubts, here, realizes, bearingHere m w OccursAt Bears _ (performer a) e
    here (alignment (performer a) e agency) (presence w (performer a) e) (classify (performer a))⟩

/-- Assembly of the population premise from the asserter's witness. -/
theorem populationFromAssertion {W B R Content Episode : Type} (m : Ontic W B) (w : W)
    (InAct : B → R → Prop) (esse : R) (OccursAt : W → Episode → Prop)
    (Bears : B → Episode → Prop) (Asserts : B → Content → Prop) (claim : Content)
    (Realizes : B → Content → Episode → Prop)
    (made : AssertionMade Asserts claim)
    (realized : AssertionRealized Asserts claim (OccursAt w) Realizes)
    (alignment : AgentOfEpisodeBearsIt (AssertionAgency Asserts claim (OccursAt w) Realizes) Bears)
    (presence : BearerExistsWhereEpisodeOccurs m OccursAt Bears)
    (classify : ExistingInActAt m InAct esse w) :
    InhabitedConcreteAt m (HasEsseInRe InAct esse) w := by
  obtain ⟨b, _, _, _, hExists, hConcrete⟩ :=
    assertionWitness m w InAct esse OccursAt Bears Asserts claim Realizes
      made realized alignment presence classify
  exact ⟨b, hConcrete, hExists⟩

/-- Assembly of the population premise from the doubter's witness. -/
theorem populationFromDoubt {W B R Act Episode : Type} (m : Ontic W B) (w : W)
    (InAct : B → R → Prop) (esse : R) (OccursAt : W → Episode → Prop)
    (Bears : B → Episode → Prop) (Performed DoubtsThought : Act → Prop)
    (performer : Act → B) (Realizes : Act → Episode → Prop)
    (made : DoubtIsPerformed Performed DoubtsThought)
    (realized : PerformedDoubtIsThought Performed DoubtsThought (OccursAt w) Realizes)
    (alignment : AgentOfEpisodeBearsIt
      (DoubtAgency Performed DoubtsThought performer (OccursAt w) Realizes) Bears)
    (presence : BearerExistsWhereEpisodeOccurs m OccursAt Bears)
    (classify : ExistingInActAt m InAct esse w) :
    InhabitedConcreteAt m (HasEsseInRe InAct esse) w := by
  obtain ⟨a, _, _, _, _, _, _, hExists, hConcrete⟩ :=
    doubtWitness m w InAct esse OccursAt Bears Performed DoubtsThought performer Realizes
      made realized alignment presence classify
  exact ⟨performer a, hConcrete, hExists⟩

/-- Where the occurrence predicates are distinct, calibration transports the
very same doubt realizer into the selected world's slice. -/
theorem calibrateDoubt {W Act Episode : Type} (w : W) (OccursAt : W → Episode → Prop)
    (Occurs : Episode → Prop) (Performed DoubtsThought : Act → Prop)
    (Realizes : Act → Episode → Prop)
    (realized : PerformedDoubtIsThought Performed DoubtsThought Occurs Realizes)
    (locate : OccurringThoughtOccursAt OccursAt Occurs w) :
    PerformedDoubtIsThought Performed DoubtsThought (OccursAt w) Realizes := by
  intro a hPerformed hDoubts
  obtain ⟨e, occurs, realizes⟩ := realized a hPerformed hDoubts
  exact ⟨e, locate e occurs, realizes⟩

/-- Contingency requires accessible absence of this very bearer. -/
theorem sameBearerContingency {W B : Type} (m : Ontic W B) (w : W) (b : B)
    (existsHere : m.ExistsAt w b)
    (absence : ∃ v, m.frame.access w v ∧ ¬ m.ExistsAt v b) :
    ContingentAt m w b :=
  ⟨existsHere, absence⟩


/-- Export the asserter as a member of the selected existence extension. -/
theorem existenceFromAssertion {W B Content Episode : Type} (m : Ontic W B) (w : W)
    (OccursAt : W → Episode → Prop) (Bears : B → Episode → Prop)
    (Asserts : B → Content → Prop) (claim : Content) (Realizes : B → Content → Episode → Prop)
    (made : AssertionMade Asserts claim)
    (realized : AssertionRealized Asserts claim (OccursAt w) Realizes)
    (alignment : AgentOfEpisodeBearsIt (AssertionAgency Asserts claim (OccursAt w) Realizes) Bears)
    (presence : BearerExistsWhereEpisodeOccurs m OccursAt Bears) :
    SomeExistent (m.ExistsAt w) := by
  obtain ⟨b, asserted⟩ := made
  obtain ⟨e, here, realizes⟩ := realized b asserted
  exact ⟨b, presence w b e here (alignment b e ⟨asserted, here, realizes⟩)⟩

/-- Export the assigned performer as a member of the selected existence extension. -/
theorem existenceFromDoubt {W B Act Episode : Type} (m : Ontic W B) (w : W)
    (OccursAt : W → Episode → Prop) (Bears : B → Episode → Prop)
    (Performed DoubtsThought : Act → Prop) (performer : Act → B) (Realizes : Act → Episode → Prop)
    (made : DoubtIsPerformed Performed DoubtsThought)
    (realized : PerformedDoubtIsThought Performed DoubtsThought (OccursAt w) Realizes)
    (alignment : AgentOfEpisodeBearsIt
      (DoubtAgency Performed DoubtsThought performer (OccursAt w) Realizes) Bears)
    (presence : BearerExistsWhereEpisodeOccurs m OccursAt Bears) :
    SomeExistent (m.ExistsAt w) := by
  obtain ⟨a, performed, doubts⟩ := made
  obtain ⟨e, here, realizes⟩ := realized a performed doubts
  exact ⟨performer a, presence w (performer a) e here
    (alignment (performer a) e ⟨a, performed, doubts, here, realizes, rfl⟩)⟩

open TruthCore.Logic.FirstPersonWitness.Control

/-- One performed doubt is realized here. Empty bearing makes alignment fail
even though the bearer-existence conditional holds. -/
theorem bearerlessControl :
    DoubtIsPerformed marked marked ∧
    PerformedDoubtIsThought marked marked (occursAt false false) realizes ∧
    BearerExistsWhereEpisodeOccurs (ontic true) (occursAt false) (bearing False) ∧
    ExistingInActAt (ontic true) (inAct True) () false ∧
    (∀ b e, ¬ bearing False b e) ∧
    ¬ AgentOfEpisodeBearsIt
      (DoubtAgency marked marked performer (occursAt false false) realizes) (bearing False) ∧
    ¬ InhabitedConcreteAt (ontic true) (HasEsseInRe (inAct True) ()) false := by
  exact ⟨⟨(), trivial, trivial⟩, fun _ _ _ => ⟨(), rfl, trivial⟩, fun _ _ _ _ h => h.elim,
    fun _ _ => trivial, fun _ _ h => h,
    fun align => align () () ⟨(), trivial, trivial, rfl, trivial, rfl⟩,
    fun ⟨_, _, absent⟩ => Bool.noConfusion absent⟩

/-- The same performer bears the local episode and exists here. With the
esse extension empty, the classification contract fails at the performer. -/
theorem nonconcretePerformerControl :
    DoubtIsPerformed marked marked ∧
    PerformedDoubtIsThought marked marked (occursAt false false) realizes ∧
    AgentOfEpisodeBearsIt
      (DoubtAgency marked marked performer (occursAt false false) realizes) (bearing True) ∧
    BearerExistsWhereEpisodeOccurs (ontic false) (occursAt false) (bearing True) ∧
    bearing True (performer ()) () ∧ (ontic false).ExistsAt false (performer ()) ∧
    ¬ ExistingInActAt (ontic false) (inAct False) () false ∧
    ¬ InhabitedConcreteAt (ontic false) (HasEsseInRe (inAct False) ()) false := by
  exact ⟨⟨(), trivial, trivial⟩, fun _ _ _ => ⟨(), rfl, trivial⟩, fun _ _ _ => trivial,
    fun _ _ _ here _ => here, trivial, rfl, fun classify => classify () rfl, fun ⟨_, h, _⟩ => h⟩

/-- The marked act has a realizer whose occurrence is confined to the other world,
where its assigned performer exists. The selected slice has no realizing occurrence.
Bearing and world-local existential import are both retained. -/
theorem elsewherePerformerControl :
    DoubtIsPerformed marked marked ∧
    PerformedDoubtIsThought marked marked (occursAt true true) realizes ∧
    AgentOfEpisodeBearsIt
      (DoubtAgency marked marked performer (occursAt true true) realizes) (bearing True) ∧
    BearerExistsWhereEpisodeOccurs (ontic true) (occursAt true) (bearing True) ∧
    ExistingInActAt (ontic true) (inAct True) () false ∧
    (ontic true).ExistsAt true (performer ()) ∧ ¬ (ontic true).ExistsAt false (performer ()) ∧
    ¬ PerformedDoubtIsThought marked marked (occursAt true false) realizes ∧
    ¬ InhabitedConcreteAt (ontic true) (HasEsseInRe (inAct True) ()) false := by
  exact ⟨⟨(), trivial, trivial⟩, fun _ _ _ => ⟨(), rfl, trivial⟩, fun _ _ _ => trivial,
    fun _ _ _ here _ => here, fun _ _ => trivial, rfl, fun h => Bool.noConfusion h,
    fun realized => let ⟨_, h, _⟩ := realized () trivial trivial; Bool.noConfusion h,
    fun ⟨_, _, absent⟩ => Bool.noConfusion absent⟩

/-- With the local occurrence and bearing kept fixed, the ontology can
omit local presence. This falsifies the existential-import bridge. -/
theorem presenceOmissionControl :
    DoubtIsPerformed marked marked ∧
    PerformedDoubtIsThought marked marked (occursAt false false) realizes ∧
    AgentOfEpisodeBearsIt
      (DoubtAgency marked marked performer (occursAt false false) realizes) (bearing True) ∧
    ExistingInActAt (ontic true) (inAct True) () false ∧
    ¬ BearerExistsWhereEpisodeOccurs (ontic true) (occursAt false) (bearing True) ∧
    ¬ InhabitedConcreteAt (ontic true) (HasEsseInRe (inAct True) ()) false := by
  exact ⟨⟨(), trivial, trivial⟩, fun _ _ _ => ⟨(), rfl, trivial⟩, fun _ _ _ => trivial,
    fun _ _ => trivial, fun presence => Bool.noConfusion (presence false () () rfl trivial),
    fun ⟨_, _, absent⟩ => Bool.noConfusion absent⟩

end TruthCore.Results.Logic.FirstPersonWitness
