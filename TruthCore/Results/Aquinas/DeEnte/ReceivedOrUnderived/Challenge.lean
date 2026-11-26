import TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
import TruthCore.Results.Aquinas.DeEnte.FiniteEsseRootAudit.Solution

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

/-- Causal origination would give internal reception. At identity, the
receiver would then stand in potency to the very same principle. -/
theorem identityEsseUnderivedOfReception (p : Profile B P R)
    (Received : B → P → Prop) (Potency : P → P → Prop)
    (caused : CausedEsseIsReceived p.CausesIn p.esse Received)
    (own : IdentityScopedEsseReception p.essenceOf p.esseOf Received)
    (receives : ReceiverInPotencyToReceivedEsseReading p.esseOf Received Potency)
    (irreflexive : NothingInReceptivePotencyToItself Potency) :
    ActualIdentityEsseHasNoSupplier p := by
  sorry

/-- Audit the identity bearer itself, or an actual identity ancestor and the
finite path named by the distinct-esse premise. -/
theorem auditsOfIdentityAncestry (p : Profile B P R)
    (underived : ActualIdentityEsseHasNoSupplier p)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (em : ExcludedMiddle) :
    EveryActualEsseBearerHasFiniteRootAudit p := by
  sorry

/-- The distinct bearer receives internally and has the identity bearer as
an actual cause. It also supplies the identity bearer, whose esse is never
received internally. Every bearer therefore has an incoming supplier. -/
theorem externalSupplyWithoutIdentityReceipt : ExternalSupplyWithoutIdentityReceipt := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.ReceivedOrUnderived
