import TruthCore.Results.Causality.IntentionalExemplarExtension.Solution
import TruthCore.Causality.SoleEsseGiver

/-! A local diagnostic for two subjects asking what accounts for their present
esse. Possible answers are descriptions for testing evidence, not worlds in
which the actual source changes its essence. -/
namespace ReflectiveGround

inductive Account
  | subsistent
  | primitivelyActual
  | fromFirst
  | fromSecond
  deriving DecidableEq

/-- Underivedness alone does not distinguish the identity explanation from
stopping at a primitive underived actuality. -/
def received : Account → Bool
  | .subsistent | .primitivelyActual => false
  | .fromFirst | .fromSecond => true

inductive Constitution
  | identity
  | primitive
  | participated
  deriving DecidableEq

/-- Positive insight into how the subject is constituted, if attained,
distinguishes the identity explanation without identifying a giver. -/
def constitution : Account → Constitution
  | .subsistent => .identity
  | .primitivelyActual => .primitive
  | .fromFirst | .fromSecond => .participated

/-- At one subject, evidence discriminates the actual account from every
other answer on the selected menu. This says nothing about cognitive uptake. -/
def DistinguishesAt {E : Type} (evidence : Account → E) (actual : Account) : Prop :=
  ∀ other, evidence other = evidence actual → other = actual

/-- Knowing only that this very subject exists leaves its account open.
Recognizing its constitution can settle the subsistent answer and still leave
the identity of the principal giver open in the participant. -/
theorem accessByConstitution :
    ¬ DistinguishesAt (fun _ => ()) .subsistent ∧
    ¬ DistinguishesAt (fun _ => ()) .fromFirst ∧
    ¬ DistinguishesAt received .subsistent ∧
    DistinguishesAt constitution .subsistent ∧
    ¬ DistinguishesAt constitution .fromFirst := by
  refine ⟨fun h => Account.noConfusion (h .fromFirst rfl),
    fun h => Account.noConfusion (h .subsistent rfl),
    fun h => Account.noConfusion (h .primitivelyActual rfl), ?_,
    fun h => Account.noConfusion (h .fromSecond rfl)⟩
  intro other h
  cases other <;> simp_all [constitution]

/-- A warranted identification of the selected principal (represented here
only by the exclusion it supplies) supplements recognition of receipt. -/
def secondSupplies : Account → Bool
  | .fromSecond => true
  | .subsistent | .primitivelyActual | .fromFirst => false

theorem recipientWithIdentification :
    DistinguishesAt (fun a => (constitution a, secondSupplies a)) .fromFirst := by
  intro other h
  cases other <;> simp_all [constitution, secondSupplies]

/-- Even a full correct answer about constitution and principal is consistent
with different explanatory assessments of the obtaining of this very bearer.
The pair keeps the *same* positive constitution, including essence/esse
identity in the source. Its second coordinate records whether the subject's
obtaining is taken to have a sufficient reason in that constitution. -/
theorem constitutionLeavesObtainingOpen (account : Account) :
    ¬ ∀ other : Account × Bool,
      other.1 = account → other = (account, true) := by
  intro h
  have wrong := congrArg Prod.snd (h (account, false) rfl)
  exact Bool.noConfusion wrong

/-- The objective exclusion available to a reasoning participant on the
existing single-principal account. Neither argument availability nor actual
uptake by the participant follows from this theorem. -/
theorem principalIdentified
    {B P R : Type} (f : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (Participated OwnBeing : B → Prop) (s x : B)
    (hSource : TruthCore.Causality.SoleEsseGiver.SoleEssentialGiver f Participated OwnBeing s)
    (actual : f.InAct x f.esse) (participant : Participated x) :
    f.CausesIn s x f.esse ∧
    ∀ t, t ≠ s → ¬ (t ≠ x ∧ f.InAct t f.esse ∧ OwnBeing t ∧ f.CausesIn t x f.esse) := by
  obtain ⟨hs, only⟩ := hSource.2 x actual participant
  refine ⟨hs.2.2.2, ?_⟩
  rintro t hne ⟨htx, ht, ho, hc⟩
  exact hne (only t htx ht ho hc)

/-- In the existing positive source interpretation the source grasps itself
in its own immediate form. The reflective recipient actually apprehends its
own object on the same apprehension relation. The richer account question
can already discriminate unequally on either of the tested evidence bases. -/
theorem selfApprehensionAndDifferentAccess :
    TruthCore.Results.Causality.IntentionalExemplarExtension.ImmanentSelfPresence.Control.positive ∧
    TruthCore.Causality.IntentionalExemplarExtension.Control.frame.CausesIn true false () ∧
    TruthCore.Results.Causality.IntentionalExemplarExtension.ImmanentSelfPresence.Control.allAct false () ∧
    TruthCore.Results.Causality.IntentionalExemplarExtension.ImmanentSelfPresence.Control.selfApp false false ∧
    (DistinguishesAt constitution .subsistent ∧ ¬ DistinguishesAt constitution .fromFirst) ∧
    (DistinguishesAt (fun a => (constitution a, secondSupplies a)) .fromFirst ∧
      ¬ DistinguishesAt (fun _ => ()) .subsistent) :=
  ⟨TruthCore.Results.Causality.IntentionalExemplarExtension.immanentSelfPresenceControls.2.2,
    ⟨rfl, rfl⟩, trivial, rfl, accessByConstitution.2.2.2,
    recipientWithIdentification, accessByConstitution.1⟩

end ReflectiveGround
