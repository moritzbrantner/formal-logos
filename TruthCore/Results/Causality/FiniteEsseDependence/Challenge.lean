import TruthCore.Causality.FiniteEsseDependence

namespace TruthCore.Results.Causality.FiniteEsseDependence

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Causality.FiniteEsseDependence
open TruthCore.Causality.FirstMoverNecessity (IdentityScopedEsseReception)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.PureActRoot (ActualRootHasEveryPureDetermination)
open TruthCore.Causality.TimeSymmetricGiving (ReceivedEsseHasCauseOfBeing)
open TruthCore.Causality.WholePowerPerfection (InfiniteHasEveryPurePerfection)
open TruthCore.Latin.Aquinas.DeEnte (ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseRequiresExternalCauseReading)

/-- Derive the existing tenseless coverage premise on all recipients, without
silently supplying actuality or asserting that the recipient principle is the giver. -/
theorem receivedEsseHasCause {B P R : Type}
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (Received : B → P → Prop) (Potency : P → P → Prop)
    (hActual : ReceiptImpliesActuality Received p.InAct p.esse)
    (hOwn : IdentityScopedEsseReception p.essenceOf p.esseOf Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading p.esseOf Received Potency)
    (hIrrefl : NothingInReceptivePotencyToItself Potency)
    (hCause : DistinctEsseRequiresExternalCauseReading p) :
    ReceivedEsseHasCauseOfBeing p.CausesIn p.esse Received := by
  sorry

/-- Keep the receiver and the cause in their respective types, and carry the
same distinct cause into the actual concrete grounding relation. -/
theorem limitedEsseHasGroundingGiver {W B P R : Type} (m : Profile W B) (w : W)
    (Limited : B → Prop) (Received : B → P → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hLimit : EsseLimitedOnlyThroughReceptionReading Limited Received)
    (hCause : ReceivedEsseHasCauseOfBeing CausesIn esse Received)
    (hGround : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    LimitedEsseHasGroundingGiverAt m w Limited CausesIn esse := by
  sorry

/-- Root perfection through finitude's standing need for a giver, without
requiring a root to exist or first stipulating that each root is its own esse. -/
theorem rootPerfectionFromFiniteDependence {W B R D : Type} (m : Profile W B) (w : W)
    (Limited Infinite : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hGiver : LimitedEsseHasGroundingGiverAt m w Limited CausesIn esse)
    (hInfinite : UnlimitedEsseIsInfiniteReading Limited Infinite)
    (hPerfection : InfiniteHasEveryPurePerfection Infinite Has Pure) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  sorry

end TruthCore.Results.Causality.FiniteEsseDependence
