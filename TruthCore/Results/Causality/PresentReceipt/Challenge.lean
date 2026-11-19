import TruthCore.Causality.PresentReceipt

namespace TruthCore.Results.Causality.PresentReceipt

open TruthCore.Causality.PresentReceipt
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.SustainingDependence (ReceivedOnsetIsGiven)
open TruthCore.Modal.TemporalHistory (History BeginsAt)

/-- Present-tense reception and correlativity give weak concurrent
actualization `40a97664`: a received-esse thing present at `t` is receiving its
esse at `t`, and whatever is receiving at `t` is given being at `t`. -/
theorem concurrentOfPresentReceipt {W B T P : Type} (h : History W B T)
    (G : BeingGiving W B T) (R : Receipt W B T P) (EsseReceivedIn : B → P → Prop)
    (hPresent : ReceptionIsPresent h R EsseReceivedIn)
    (hCorrelative : ReceivingIsCorrelativeWithGiving G R) :
    ConcurrentlyActualized h G EsseReceivedIn := by
  sorry

/-- The onset reading and correlativity give received onset is given
`fa3e228b`. -/
theorem onsetOfOnsetReceipt {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (R : Receipt W B T P) (EsseReceivedIn : B → P → Prop)
    (hOnset : ReceptionAtOnset h R EsseReceivedIn)
    (hCorrelative : ReceivingIsCorrelativeWithGiving G R) :
    ReceivedOnsetIsGiven h G EsseReceivedIn := by
  sorry

/-- Strength order: the present-tense reading entails the onset reading. -/
theorem onsetOfPresentReceipt {W B T P : Type} [Preorder T] (h : History W B T)
    (R : Receipt W B T P) (EsseReceivedIn : B → P → Prop)
    (hPresent : ReceptionIsPresent h R EsseReceivedIn) :
    ReceptionAtOnset h R EsseReceivedIn := by
  sorry

/-- On the passion sense correlativity holds by definition and the
present-tense reading is weak concurrent actualization. -/
theorem passionReadingIsTheCrux : PassionReadingIsTheCrux := by
  sorry

/-- On the standing sense the present-tense reading holds by definition and
correlativity is weak concurrent actualization. -/
theorem standingReadingIsTheCrux : StandingReadingIsTheCrux := by
  sorry

/-- Some receipt interpretation satisfies the present-tense reading and
correlativity iff weak concurrent actualization holds: forward by
`concurrentOfPresentReceipt`, backward with the standing sense. -/
theorem someReceiptCarriesTheCrux : SomeReceiptCarriesTheCrux := by
  sorry

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control
open TruthCore.Causality.PresentReceipt.Control

/-- Omission, rival-reading, separation and nonvacuity controls
(`Control.Certificate`). -/
theorem controls : TruthCore.Causality.PresentReceipt.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.PresentReceipt
