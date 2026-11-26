module

public import TruthCore.Causality.DeiFiliusUnifiedRoute
public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit

/-! Root certificates from identity and finite ancestry on one actual esse relation. -/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived

open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Causality.FirstMoverNecessity (IdentityScopedEsseReception)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (ClosedActualEsseCollectionsRooted)
open TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit (EveryActualEsseBearerHasFiniteRootAudit)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

/-- Each actual bearer whose represented esse is its essence has no incoming
edge in the fixed actual esse-cause relation. -/
def ActualIdentityEsseHasNoSupplier {B P R : Type} (p : Profile B P R) : Prop :=
  ∀ x, p.InAct x p.esse → p.esseOf x = p.essenceOf x → ∀ c, ¬ ActualEsseCause p c x

/-- Actual identity bearers that reach the target by a finite path of actual
esse causes. An actual identity target belongs to its own set. -/
def actualIdentityAncestors {B P R : Type} (p : Profile B P R) (x : B) : Set B :=
  { r | p.InAct r p.esse ∧ p.esseOf r = p.essenceOf r ∧
    Relation.ReflTransGen (ActualEsseCause p) r x }

/-- Only the actual identity ancestors of each actual target must form a
finite set. The full actual roster and full ancestral cone may be infinite. -/
def ActualIdentityAncestorSetsFinite {B P R : Type} (p : Profile B P R) : Prop :=
  ∀ x, p.InAct x p.esse → (actualIdentityAncestors p x).Finite

/-- No actual identity bearer lies on a nonempty actual esse-cause loop.
The path may pass through bearers with distinct esse. -/
def ActualIdentityAncestryAcyclic {B P R : Type} (p : Profile B P R) : Prop :=
  ∀ r, p.InAct r p.esse → p.esseOf r = p.essenceOf r →
    ¬ Relation.TransGen (ActualEsseCause p) r r

/-- A distinct-esse recipient is directly supplied by an identity bearer
that is itself directly supplied by an underived identity bearer. The finite
and acyclic identity ancestry premises apply on this same profile. -/
def FiniteAcyclicIdentityAncestryAllowsSupply : Prop :=
  ∃ (p : Profile (Fin 3) Bool Unit) (root supplier recipient : Fin 3),
    p.esseOf root = p.essenceOf root ∧ (∀ c, ¬ ActualEsseCause p c root) ∧
    p.esseOf supplier = p.essenceOf supplier ∧ ActualEsseCause p root supplier ∧
    p.esseOf recipient ≠ p.essenceOf recipient ∧ ActualEsseCause p supplier recipient ∧
    ActualIdentityAncestorSetsFinite p ∧ ActualIdentityAncestryAcyclic p ∧
    EveryDistinctEsseHasEsseIsEssenceSource p ∧ EveryActualEsseBearerHasFiniteRootAudit p ∧
    ¬ ActualIdentityEsseHasNoSupplier p

/-- With two distinct actual bearers, finite identity ancestry can coexist
with incoming supply at the actual identity bearer. The distinct bearer has
internal receipt; the identity bearer has external supply without internal
receipt. The reception laws hold apart from the bridge that connects these
two kinds of dependence. -/
def ExternalSupplyWithoutIdentityReceipt : Prop :=
  ∃ (p : Profile Bool Bool Unit) (Received Potency : Bool → Bool → Prop),
    p.InAct true p.esse ∧ p.esseOf true = p.essenceOf true ∧
    ActualEsseCause p false true ∧ (∀ z, ¬ Received true z) ∧
    Received false false ∧ ActualEsseCause p true false ∧
    IdentityScopedEsseReception p.essenceOf p.esseOf Received ∧
    ReceiverInPotencyToReceivedEsseReading p.esseOf Received Potency ∧
    NothingInReceptivePotencyToItself Potency ∧
    EveryDistinctEsseHasEsseIsEssenceSource p ∧
    ¬ CausedEsseIsReceived p.CausesIn p.esse Received ∧
    ¬ ActualIdentityEsseHasNoSupplier p ∧
    ¬ ClosedActualEsseCollectionsRooted p ∧
    ¬ EveryActualEsseBearerHasFiniteRootAudit p

end TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
