module

public import TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
public import TruthCore.Results.Aquinas.DeEnte.FiniteEsseRootAudit.Solution

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.ReceivedOrUnderived

open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Causality.FirstMoverNecessity (IdentityScopedEsseReception)
open TruthCore.Latin.Aquinas.DeEnte
  (ActualEsseCause EveryDistinctEsseHasEsseIsEssenceSource ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (ClosedActualEsseCollectionsRooted sourceFreeFiniteCircle)
open TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit (EveryActualEsseBearerHasFiniteRootAudit)
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Results.Aquinas.DeEnte.FiniteEsseRootAudit (closedOfFiniteRootAudits)
open TruthCore.Results.Causality.SupplierAuditCertificates (positiveCertificate)

variable {B P R : Type}

/-- Causal origination would give internal reception. At identity, the
receiver would then stand in potency to the very same principle. -/
theorem identityEsseUnderivedOfReception (p : Profile B P R)
    (Received : B → P → Prop) (Potency : P → P → Prop)
    (caused : CausedEsseIsReceived p.CausesIn p.esse Received)
    (own : IdentityScopedEsseReception p.essenceOf p.esseOf Received)
    (receives : ReceiverInPotencyToReceivedEsseReading p.esseOf Received Potency)
    (irreflexive : NothingInReceptivePotencyToItself Potency) :
    ActualIdentityEsseHasNoSupplier p := by
  intro x _ identity c edge
  obtain ⟨z, receipt⟩ := caused c x edge.1 edge.2.2.2
  have self := receives x z receipt
  rw [own x z identity receipt, identity] at self
  exact irreflexive _ self

/-- Audit the identity bearer itself, or an actual identity ancestor and the
finite path named by the distinct-esse premise. -/
theorem auditsOfIdentityAncestry (p : Profile B P R)
    (underived : ActualIdentityEsseHasNoSupplier p)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (em : ExcludedMiddle) :
    EveryActualEsseBearerHasFiniteRootAudit p := by
  intro x actual
  rcases em (p.esseOf x = p.essenceOf x) with identity | distinct
  · exact ⟨x, actual, (positiveCertificate (ActualEsseCause p) x x).mp
      ⟨.refl, underived x actual identity⟩⟩
  · obtain ⟨r, actualRoot, identity, path⟩ := ancestry x ⟨actual, distinct⟩
    exact ⟨r, actualRoot, (positiveCertificate (ActualEsseCause p) r x).mp
      ⟨path.to_reflTransGen, underived r actualRoot identity⟩⟩

private def cycle : Profile Bool Bool Unit :=
  { sourceFreeFiniteCircle with esseOf := Bool.not }

private def received (x z : Bool) : Prop := x = false ∧ z = false
private def potency (z act : Bool) : Prop := z = false ∧ act = true

private theorem cycleEdge {c x : Bool} (different : c ≠ x) :
    ActualEsseCause cycle c x :=
  ⟨different, trivial, trivial, different⟩

/-- The distinct bearer receives internally and has the identity bearer as
an actual cause. It also supplies the identity bearer, whose esse is never
received internally. Every bearer therefore has an incoming supplier. -/
theorem externalSupplyWithoutIdentityReceipt : ExternalSupplyWithoutIdentityReceipt := by
  have incoming : ActualEsseCause cycle false true := cycleEdge Bool.false_ne_true
  have outgoing : ActualEsseCause cycle true false := cycleEdge Bool.false_ne_true.symm
  have noReceipt : ∀ z, ¬ received true z := fun _ receipt => Bool.false_ne_true.symm receipt.1
  have notClosed : ¬ ClosedActualEsseCollectionsRooted cycle := by
    intro closed
    apply closed (fun _ => True) ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ _ _ => trivial⟩
      (fun x _ root => root.2 (!x)
        (by cases x
            · exact ⟨trivial, trivial, outgoing⟩
            · exact ⟨trivial, trivial, incoming⟩))
      true trivial
  refine ⟨cycle, received, potency, trivial, rfl, incoming, noReceipt, ⟨rfl, rfl⟩, outgoing,
    ?_, ?_, ?_, ?_, ?_, ?_, notClosed, fun audits => notClosed (closedOfFiniteRootAudits cycle audits)⟩
  · exact fun _ _ _ receipt => receipt.2
  · intro x z receipt
    obtain ⟨rfl, rfl⟩ := receipt
    exact ⟨rfl, rfl⟩
  · intro z self
    exact Bool.false_ne_true (self.1.symm.trans self.2)
  · intro x distinct
    cases x
    · exact ⟨true, trivial, rfl, .single outgoing⟩
    · exact (distinct.2 rfl).elim
  · intro caused
    obtain ⟨z, receipt⟩ := caused false true incoming.1 incoming.2.2.2
    exact noReceipt z receipt
  · exact fun underived => underived true trivial rfl false incoming

end TruthCore.Results.Aquinas.DeEnte.ReceivedOrUnderived
