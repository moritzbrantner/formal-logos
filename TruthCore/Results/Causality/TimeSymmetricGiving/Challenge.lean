import TruthCore.Causality.TimeSymmetricGiving

namespace TruthCore.Results.Causality.TimeSymmetricGiving

open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized)
open TruthCore.Modal.TemporalHistory (History)

/-- The momentary PSR and the productive bridge give weak concurrent
actualization `40a97664`. -/
theorem concurrentOfMomentaryPSR {W B T P R : Type} (h : History W B T)
    (G : BeingGiving W B T) (X : PresenceExplanation W B T R) (EsseReceivedIn : B → P → Prop)
    (hPSR : MomentaryPSR h X EsseReceivedIn)
    (hBridge : ExplanationNeedsGiver h G X EsseReceivedIn) :
    ConcurrentlyActualized h G EsseReceivedIn := by
  sorry

/-- Under the momentary PSR the productive bridge is weak concurrent
actualization. -/
theorem psrBridgeCarriesTheCrux : PSRBridgeCarriesTheCrux := by
  sorry

/-- Coverage, exercise and time symmetry give concurrent actualization for
homogeneous things: the cause of being gives at one moment of presence, and an
automorphism preserving the history carries that moment to any other. -/
theorem homogeneousConcurrentOfSymmetry {W B T P R : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (Facts : W → B → T → Prop) (CausesIn : B → B → R → Prop)
    (esse : R) (EsseReceivedIn : B → P → Prop)
    (hCover : ReceivedEsseHasCauseOfBeing CausesIn esse EsseReceivedIn)
    (hExercise : CausesOfBeingAreExercised h G CausesIn esse)
    (hSymmetry : GivingRespectsTimeSymmetry h G Facts) :
    ConcurrentlyActualizedIfHomogeneous h G Facts EsseReceivedIn := by
  sorry

/-- Strength order: weak concurrent actualization entails its restriction to
homogeneous things. -/
theorem homogeneousOfConcurrent {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (Facts : W → B → T → Prop) (EsseReceivedIn : B → P → Prop)
    (hCA : ConcurrentlyActualized h G EsseReceivedIn) :
    ConcurrentlyActualizedIfHomogeneous h G Facts EsseReceivedIn := by
  sorry

open TruthCore.Causality.TimeSymmetricGiving.Control
open TruthCore.Causality.SustainingCausation.Control (trueCausesFalse noCauses)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)

/-- Omission, rival-reading and nonvacuity controls (`Control.Certificate`). -/
theorem controls : TruthCore.Causality.TimeSymmetricGiving.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.TimeSymmetricGiving
