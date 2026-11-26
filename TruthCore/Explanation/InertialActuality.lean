module

public import TruthCore.Causality.Frame
public import TruthCore.Explanation.InducerFreePersistence
public import TruthCore.Explanation.LocationPersistence
public import TruthCore.Modal.ModalGrounding
public import TruthCore.Ontology.ExistenceInEssence

/-! Temporal actuality here is existential quantification over one history's
dates. No inference from dated presence to metaphysical esse is assumed. -/

@[expose] public section

namespace TruthCore.Explanation.InertialActuality

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)
open TruthCore.Modal.TemporalHistory
open TruthCore.Modal.ModalGrounding (EssentialTruth)
open TruthCore.Ontology.ExistenceInEssence (NatureEntailsExistence)
open TruthCore.Explanation.LocationPersistence (ReportedLocationContrast)

variable {W B R P : Type}

/-- Actuality within the represented temporal profile of a rigid bearer. -/
def TemporalActuality (h : History W B Int) (v : W) (x : B) : Prop :=
  ∃ t, h.IsAt v x t

abbrev noInducer : Bool → Bool → Int → Prop := fun _ _ _ => False

/-- Both world-indexed histories in one frame have the same no-loss
background and the same ever-present background bearer, indexed by true. -/
def LawLeavesActualityOpen : Prop :=
  (∃ F : CausalityFrame Bool Bool Int Unit,
    CessationNeedsInducer F.history noInducer ∧
    (∀ v, EverlastingAt F.history v true) ∧
    EverlastingAt F.history true false ∧
    TemporalActuality F.history true false ∧ ¬ TemporalActuality F.history false false) ∧
  ¬ (∀ F : CausalityFrame Bool Bool Int Unit,
    CessationNeedsInducer F.history noInducer →
    (∀ v, EverlastingAt F.history v true) → TemporalActuality F.history false false)

/-- The earlier-date reason for a successful temporal application of inertia
already has an actuality witness, independently of the later conclusion. -/
def InertialReasonRequiresActuality : Prop :=
  ∀ (W B R : Type) (F : CausalityFrame W B Int R) (D : W → B → Int → Prop)
    (v : W) (x : B) (s t : Int),
    CessationNeedsInducer F.history D →
    (originOrInertia F.history ⟨F.GivesAt⟩ D).Explains v (.inr s) x t →
    F.history.IsAt v x t ∧ (F.history.IsAt v x s ∧ TemporalActuality F.history v x)

/-- OPEN. The specified nature truth has existence-entailing content over
the frame's represented worlds. Its truth in a given world is a separate
input. The dictionary can instead contain merely existence-conditional truths. -/
def NatureSuppliesActuality (F : CausalityFrame W B Int R)
    (Essential : B → (W → Prop) → Prop) (φ : W → Prop) (x : B) : Prop :=
  NatureEntailsExistence F (fun bearer fact => EssentialTruth Essential bearer fact ∧ fact = φ) x

/-- Where the at-now coherence profile holds, a fact which entails ontic
existence selects a history with an actuality witness. -/
def NatureSelection (F : CausalityFrame W B Int R) (φ : W → Prop) (x : B) : Prop :=
  CoherentAtNow F.history → ∀ v, φ v → TemporalActuality F.history v x

/-- The law admits both everlasting g and omission of g. With the same
dictionary and selected fact across the pair, the added conditional nature
principle excludes the omission as a site of that fact. No such fact or
principle about an actual divine candidate is asserted. -/
def EverlastingParity : Prop :=
  ∃ F : CausalityFrame Bool Bool Int Unit,
    CessationNeedsInducer F.history noInducer ∧ CoherentAtNow F.history ∧
    (∀ v, EverlastingAt F.history v true) ∧
    EverlastingAt F.history true false ∧ ¬ TemporalActuality F.history false false ∧
    ∀ Essential φ, NatureSuppliesActuality F Essential φ false →
      (∀ v, φ v → v = true ∧ TemporalActuality F.history v false)

/-- The two histories have the same actually exercised x-only interval reason
for two supplied dates and agree on x at every date. They vary the actuality
of the distinct y. The exact x-only input (the law and the reason at 0,1)
therefore does not entail y's actuality. -/
def OtherBearerActualityOpen : Prop :=
  (∃ (F : CausalityFrame Bool Bool Int Unit) (x y : Bool),
    x ≠ y ∧ CessationNeedsInducer F.history noInducer ∧
    (∀ t, F.history.IsAt true x t ↔ F.history.IsAt false x t) ∧
    (∀ v, (originOrInertia F.history ⟨F.GivesAt⟩ noInducer).Explains v (.inr 0) x 1) ∧
    TemporalActuality F.history true y ∧ ¬ TemporalActuality F.history false y) ∧
  ¬ (∀ (F : CausalityFrame Bool Bool Int Unit) (x y : Bool) (v : Bool),
    x ≠ y →
    CessationNeedsInducer F.history noInducer →
    (originOrInertia F.history ⟨F.GivesAt⟩ noInducer).Explains v (.inr 0) x 1 →
    TemporalActuality F.history v y)

/-- A protector is present only in the protected history. The loss inducer
occurs against the receiver at 1 exactly where the protector is absent at 1.
The receiver is present at 0 in both and at 1 only in the protected history.
The law holds and no giver gives the receiver being at 1. -/
def ExternalProtectionCompatible : Prop :=
  ∃ (F : CausalityFrame Bool Bool Int Unit) (D : Bool → Bool → Int → Prop),
    CessationNeedsInducer F.history D ∧
    F.history.IsAt true true 1 ∧ ¬ F.history.IsAt false true 1 ∧
    (∀ v, D v false 1 ↔ ¬ F.history.IsAt v true 1) ∧
    (∀ u, ¬ D true false u) ∧
    (∀ v, F.history.IsAt v false 0) ∧
    F.history.IsAt true false 1 ∧ ¬ F.history.IsAt false false 1 ∧
    (∀ v g, ¬ F.GivesAt v g false 1) ∧
    (originOrInertia F.history ⟨F.GivesAt⟩ D).Explains true (.inr 0) false 1 ∧
    ¬ ExplanationNeedsGiver F.history ⟨F.GivesAt⟩ (originOrInertia F.history ⟨F.GivesAt⟩ D)
      falseReceived

/-- OPEN (state reading). For the designated substantial bearer, presence
at an adjacent date survives when the next date is inducer-free and there
is no current strict production. The frame alone imposes no such rule. -/
def ExistenceStateWithoutProduction (F : CausalityFrame W B Int R)
    (D : W → B → Int → Prop) (v : W) (x : B) : Prop :=
  ∀ s, F.history.IsAt v x s → ¬ D v x (s + 1) →
    (¬ ∃ g, F.GivesAt v g x (s + 1)) → F.history.IsAt v x (s + 1)

/-- OPEN (received-act reading). For the designated substantial bearer,
its esse is a received act in some principle. No temporal-presence or
strict-giving bridge is assumed. -/
def ReceivedAct (EsseReceivedIn : B → P → Prop) (x : B) : Prop :=
  ∃ r, EsseReceivedIn x r

/-- Reversible comparison window for applying the stationary location form.
Besides no inducer and no production at any date, the window independently
excludes a transition into presence. These controls do not follow from the
forward state premise. -/
def AnchoredExistenceWithoutProduction (F : CausalityFrame W B Int R)
    (D : W → B → Int → Prop) (v : W) (x : B) : Prop :=
  (∀ t, ¬ D v x t) → (∀ t g, ¬ F.GivesAt v g x t) →
  (∀ s, F.history.IsAt v x (s + 1) → F.history.IsAt v x s) →
  ∀ s, F.history.IsAt v x s → EverlastingAt F.history v x

/-- The worked location contrast still holds in a configuration with a
failing state premise, even where the no-onset and no-production controls
hold for the designated bearer. -/
def LocationDoesNotSupplyStateLaw : Prop :=
  ReportedLocationContrast ∧
  ∃ F : CausalityFrame Bool Bool Int Unit,
    (∀ t g, ¬ F.GivesAt false g false t) ∧
    (∀ s, F.history.IsAt false false (s + 1) → F.history.IsAt false false s) ∧
    ¬ ExistenceStateWithoutProduction F noInducer false false

/-- The state-transition and received-act theses can hold of the same bearer
in an interpretation with a populated profile and no strict giver. -/
def StateAndReceiptCompatible : Prop :=
  ∃ F : CausalityFrame Bool Bool Int Unit,
    EverlastingAt F.history true false ∧
    (∀ t g, ¬ F.GivesAt true g false t) ∧
    ExistenceStateWithoutProduction F noInducer true false ∧
    ReceivedAct falseReceived false

end TruthCore.Explanation.InertialActuality
