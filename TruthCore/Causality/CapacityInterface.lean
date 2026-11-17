module

public import TruthCore.Explanation.BorrowedExercise
public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Causality.Round2ExistenceAct

/-! Analyst capacity interface for #1659/#1652. Possession is primitive and
indexed by a situation, bearer and specified effect/respect. It contains no
activation, occurrence, sourcehood, existence or concreteness law. The adapters
below expose exactly which information is retained or forgotten. They do not
replace the existing consumers or establish applicability to real agents.
See docs/power-existence-scope-boundary.md, Indexed capacity adapter. -/

@[expose] public section

namespace TruthCore.Causality.CapacityInterface

open TruthCore.Causality.JointGroups
open TruthCore.Explanation

/-- A bearer possesses the capacity for the specified effect/respect in a
situation, including when it is not exercised. `possesses` is an interpreted
primitive, not a reduction of capacity to occurrence or successful activation. -/
structure Capacity (Situation Bearer Respect : Type) where
  possesses : Situation → Bearer → Respect → Prop

/-- Explicit correspondence of event scenarios to situations, and events to
bearers and specified effects/respects. No map is assumed injective or onto. -/
structure Indexing (Scenario Event Situation Bearer Respect : Type) where
  situation : Scenario → Situation
  bearer : Event → Bearer
  respect : Event → Respect

variable {S E W B R G : Type}

/-- Read the indexed possession predicate at the three selected indices. -/
def eventProfile (p : Capacity W B R) (i : Indexing S E W B R) : S → E → Prop :=
  fun s e => p.possesses (i.situation s) (i.bearer e) (i.respect e)

/-- Exact correspondence, at every scenario/event pair, not merely actual or
allowed pairs. Restrict the index domain explicitly for a weaker application. -/
def Corresponds (i : Indexing S E W B R) (cap : S → E → Prop)
    (p : Capacity W B R) : Prop :=
  ∀ s e, cap s e ↔ eventProfile p i s e

/-- Agreement on all indices identified by the maps. Collapsing scenarios as
well as events requires agreement; fixed-scenario agreement alone is weaker. -/
def FiberAgreement (i : Indexing S E W B R) (cap : S → E → Prop) : Prop :=
  ∀ s t e f, i.situation s = i.situation t → i.bearer e = i.bearer f →
    i.respect e = i.respect f → (cap s e ↔ cap t f)

/-- Existential image of an event profile. Outside the represented image it is
false by construction, not evidence of absence of a real capacity. It recovers
cap exactly only under FiberAgreement. -/
def descend (i : Indexing S E W B R) (cap : S → E → Prop) : Capacity W B R where
  possesses w b r := ∃ s e, i.situation s = w ∧ i.bearer e = b ∧
    i.respect e = r ∧ cap s e

/-- Fix a specified respect to obtain the actual W → B → Prop interface of
EveryExistentHasCausalPowerAt and PowerRequiresConcreteAt. No quantification
or existential aggregation over all respects is implicit. -/
def bearerProfile (p : Capacity W B R) (r : R) : W → B → Prop :=
  fun w b => p.possesses w b r

/-- Embed an existing thin bearer profile with one unspecified selected respect.
Unit adds no claim that several different powers agree. -/
def fromBearer (power : W → B → Prop) : Capacity W B Unit where
  possesses w b _ := power w b

/-- Use the actual bearers of an existing Exercise. Scenario/world and
respect/effect correspondence remain explicitly supplied. -/
def exerciseIndex (m : Exercise B E G S) (world : S → W) (respect : E → R) :
    Indexing S E W B R := ⟨world, m.bearer, respect⟩

/-- Lossless representation of an arbitrary event profile: retain the event
identity alongside its specified respect. This does not assert that event
identity is dispensable, nor that the capacity is shared by all such events. -/
def fromEvents (m : Exercise B E G S) (respect : E → R)
    (cap : S → E → Prop) : Capacity S B (R × E) where
  possesses s b re := m.bearer re.2 = b ∧ respect re.2 = re.1 ∧ cap s re.2

/-- The lossless adapter keeps scenarios unchanged and retains event identity. -/
def retainedIndex (m : Exercise B E G S) (respect : E → R) :
    Indexing S E S B (R × E) :=
  exerciseIndex m id (fun e => (respect e, e))

/-- Exact criterion for forgetting indices, with a canonical realization. -/
def Factorization : Prop :=
  ∀ (S E W B R : Type) (i : Indexing S E W B R) (cap : S → E → Prop),
    (FiberAgreement i cap ↔ ∃ p, Corresponds i cap p) ∧
    (FiberAgreement i cap → Corresponds i cap (descend i cap))

/-- Adapters preserve arbitrary event data losslessly and preserve the thin
bearer profile. Neither result asserts a common-bearer factorization. -/
def RoundTrips : Prop :=
  (∀ (B E G S R : Type) (m : Exercise B E G S) (respect : E → R)
      (cap : S → E → Prop),
    Corresponds (retainedIndex m respect) cap (fromEvents m respect cap)) ∧
  (∀ (W B : Type) (power : W → B → Prop),
    bearerProfile (fromBearer power) () = power)

/-- Exact event-profile correspondence preserves the actual BorrowedExercise
consumers, including the separate exercise-to-capacity premise. -/
def BorrowedTransport : Prop :=
  ∀ (B E G S W R : Type) (m : Exercise B E G S) (world : S → W)
      (respect : E → R) (cap : S → E → Prop) (p : Capacity W B R),
    Corresponds (exerciseIndex m world respect) cap p →
    (∀ e, BorrowedExercise.Borrowed m cap e ↔
      BorrowedExercise.Borrowed m (eventProfile p (exerciseIndex m world respect)) e) ∧
    (∀ e, BorrowedExercise.Retained m cap e ↔
      BorrowedExercise.Retained m (eventProfile p (exerciseIndex m world respect)) e) ∧
    (BorrowedExercise.PowerRequired m cap ↔
      BorrowedExercise.PowerRequired m (eventProfile p (exerciseIndex m world respect)))

/-- The unchanged root-route capacity premises consume precisely the recovered
thin profile. These are equivalences of formulas, not proofs of the premises. -/
def RootConsumerTransport : Prop :=
  ∀ (W B Episode : Type)
      (o : TruthCore.German.Kant.CosmologicalInference.Ontic W B)
      (a : TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect.OperationAttribution B Episode)
      (concrete : B → Prop) (power : W → B → Prop) (w : W),
    (Round2ExistenceAct.EveryExistentHasCausalPowerAt o
        (bearerProfile (fromBearer power) ()) w ↔
      Round2ExistenceAct.EveryExistentHasCausalPowerAt o power w) ∧
    (Round2ExistenceAct.IntellectualExerciserHasPowerAt a
        (bearerProfile (fromBearer power) ()) w ↔
      Round2ExistenceAct.IntellectualExerciserHasPowerAt a power w) ∧
    (CausalPowerConcreteness.PowerRequiresConcreteAt concrete
        (bearerProfile (fromBearer power) ()) w ↔
      CausalPowerConcreteness.PowerRequiresConcreteAt concrete power w)

/-- Two events identified in bearer AND respect can disagree in capacity. -/
def collapsedEvents : Indexing Unit Bool Unit Unit Unit :=
  ⟨id, fun _ => (), fun _ => ()⟩

def eventDisagreement : Unit → Bool → Prop := fun _ e => e = true

/-- Identifying two scenarios also loses information, even with one event. -/
def collapsedScenarios : Indexing Bool Unit Unit Unit Unit :=
  ⟨fun _ => (), id, id⟩

def scenarioDisagreement : Bool → Unit → Prop := fun s _ => s = true

/-- The same bearer can retain distinct powers when the respect remains. -/
def separatedRespects : Indexing Unit Bool Unit Unit Bool :=
  ⟨id, fun _ => (), id⟩

def respectCapacity : Capacity Unit Unit Bool := ⟨fun _ _ r => r = true⟩

/-- Finite index-loss controls, not counterexamples to metaphysical principles. -/
def IndexControls : Prop :=
  (¬ ∃ p, Corresponds collapsedEvents eventDisagreement p) ∧
  (¬ ∃ p, Corresponds collapsedScenarios scenarioDisagreement p) ∧
  Corresponds separatedRespects eventDisagreement respectCapacity

/-- Reuse the existing same-exercise capOccurs/capAll contrast and omission of
PowerRequired exactly. No new defeat or real-world interpretation is claimed. -/
def ExistingControls : Prop :=
  BorrowedExercise.InstrumentRegress ∧ BorrowedExercise.SecondaryRegress ∧ BorrowedExercise.PowerOmission

def Certificate : Prop :=
  Factorization ∧ RoundTrips ∧ BorrowedTransport ∧ RootConsumerTransport ∧
    IndexControls ∧ ExistingControls

end TruthCore.Causality.CapacityInterface
