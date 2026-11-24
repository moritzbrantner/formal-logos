module

public import TruthCore.Causality.FiniteEsseDependence

@[expose] public section

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
  intro x z hReceipt
  have hDistinct : p.esseOf x ≠ p.essenceOf x := by
    intro hIdentity
    have hRecipient : z = p.esseOf x := (hOwn x z hIdentity hReceipt).trans hIdentity.symm
    have hSelf := hPotency x z hReceipt
    rw [hRecipient] at hSelf
    exact hIrrefl _ hSelf
  obtain ⟨g, hNe, _, hg⟩ := hCause x ⟨hActual x z hReceipt, hDistinct⟩
  exact ⟨g, hNe, hg⟩

/-- Keep the receiver and the cause in their respective types, and carry the
same distinct cause into the actual concrete grounding relation. -/
theorem limitedEsseHasGroundingGiver {W B P R : Type} (m : Profile W B) (w : W)
    (Limited : B → Prop) (Received : B → P → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hLimit : EsseLimitedOnlyThroughReceptionReading Limited Received)
    (hCause : ReceivedEsseHasCauseOfBeing CausesIn esse Received)
    (hGround : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    LimitedEsseHasGroundingGiverAt m w Limited CausesIn esse := by
  intro x hx hLimited
  obtain ⟨z, hReceipt⟩ := hLimit x hLimited
  obtain ⟨g, hNe, hg⟩ := hCause x z hReceipt
  exact ⟨g, hNe, hg, hGround g x hNe hx hg⟩

/-- The supplied actual root itself has no formal limitation of esse. -/
theorem rootUnlimited {W B R : Type} (m : Profile W B) (w : W) (Limited : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hGiver : LimitedEsseHasGroundingGiverAt m w Limited CausesIn esse)
    {n : B} (hn : ActualRoot m w n) : ¬ Limited n := by
  intro hLimited
  obtain ⟨g, _, _, hg⟩ := hGiver n hn.1 hLimited
  exact hn.2 g hg

/-- Root perfection through finitude's standing need for a giver, without
requiring a root to exist or first stipulating that each root is its own esse. -/
theorem rootPerfectionFromFiniteDependence {W B R D : Type} (m : Profile W B) (w : W)
    (Limited Infinite : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hGiver : LimitedEsseHasGroundingGiverAt m w Limited CausesIn esse)
    (hInfinite : UnlimitedEsseIsInfiniteReading Limited Infinite)
    (hPerfection : InfiniteHasEveryPurePerfection Infinite Has Pure) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  intro n hn
  exact hPerfection n (hInfinite n (rootUnlimited m w Limited CausesIn esse hGiver hn))

end TruthCore.Results.Causality.FiniteEsseDependence
