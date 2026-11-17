import TruthCore.Causality.SourceScopedAscent
import TruthCore.Results.Causality.MaximalFromEsseSource.Solution

namespace TruthCore.Results.Causality.SourceScopedAscent
open TruthCore.Causality.SourceScopedAscent
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Latin.Aquinas.DeEnte
  (CommonEsseIsEssenceSource ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Causality.EsseReception
  (EsseReceivedOnlyInOwnEssence NothingInReceptivePotencyToItself)
open TruthCore.Causality.ReceptionLimitation (ReceivedEsseIsLimited)
open TruthCore.Causality.Round2PerfectionPrimacy (LimitedEsseApproachesLess GreaterDegreeIsMore)
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception
  (EsseLimitedOnlyThroughReceptionReading)
open TruthCore.Causality.Q44SourceSupply (ActualEsseCauseComposes)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

theorem restrictAscent {B P R : Type} (p : Profile B P R)
    (MoreIn : R → B → B → Prop)
    (h : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse) :
    IdentityCauseAscent p MoreIn := by
  sorry

/-- Absolute nonlimitation is obtained through the explicit reception premises,
not through freedom from this one target's capacity. All comparisons are at esse. -/
theorem identityAscentFromReception {B P R D : Type} [Preorder D]
    (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (Received : B → P → Prop) (Potency : P → P → Prop)
    (Limited : B → Prop) (degree : B → D)
    (hOwn : EsseReceivedOnlyInOwnEssence p.essenceOf Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading p.esseOf Received Potency)
    (hNotSelf : NothingInReceptivePotencyToItself Potency)
    (hReceived : CausedEsseIsReceived p.CausesIn p.esse Received)
    (hLimited : ReceivedEsseIsLimited Limited Received)
    (hOnly : EsseLimitedOnlyThroughReceptionReading Limited Received)
    (hLess : LimitedEsseApproachesLess Limited degree)
    (hMore : GreaterDegreeIsMore (fun (_ : Unit) => MoreIn p.esse)
      (fun x (_ : Unit) => degree x)) :
    IdentityCauseAscent p MoreIn := by
  sorry

/-- Consume the weaker source-scoped input in the accepted same-witness route. -/
theorem maximalCausesFromIdentityAscent {B P R : Type} (p : Profile B P R)
    (MoreIn : R → B → B → Prop)
    (hSource : CommonEsseIsEssenceSource p)
    (hCompose : ActualEsseCauseComposes p)
    (hAscent : IdentityCauseAscent p MoreIn)
    (hEM : ExcludedMiddle) :
    MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse := by
  sorry

theorem crossReception : RelativeStepAudit := by
  sorry

end TruthCore.Results.Causality.SourceScopedAscent
