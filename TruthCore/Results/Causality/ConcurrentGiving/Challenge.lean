import TruthCore.Causality.ConcurrentGiving
import TruthCore.Results.Causality.PresentReceipt.Solution
import TruthCore.Results.Causality.TimeSymmetricGiving.Solution

namespace TruthCore.Results.Causality.ConcurrentGiving

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FrameAdapters (giving)
open TruthCore.Causality.ConcurrentGiving
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized ConcurrentlyActualizedByAnother)
open TruthCore.Causality.RelationalReceipt
open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Causality.PresentReceipt

theorem distinctOfMomentaryExplanation {W B T R P X : Type}
    (F : CausalityFrame W B T R) (E : B → P → Prop) (expl : PresenceExplanation W B T X)
    (hPSR : MomentaryPSR F.history expl E)
    (hBridge : ExplanationNeedsGiver F.history (giving F) expl E)
    (hNoSelf : NoReceivedSelfGiving F E) :
    ConcurrentlyActualizedByAnother F.history (giving F) E := by
  sorry

theorem distinctOfOriginTerm {W B T R P : Type}
    (F : CausalityFrame W B T R) (E : B → P → Prop) (O : OriginRelation W B T)
    (hAccompanies : RelationAccompaniesEsse F.history O E)
    (hGives : TermGives (giving F) O)
    (hIrreflexive : Irreflexive O) :
    ConcurrentlyActualizedByAnother F.history (giving F) E := by
  sorry

theorem distinctOfPresentReceipt {W B T R P : Type}
    (F : CausalityFrame W B T R) (E : B → P → Prop) (receipt : Receipt W B T P)
    (hPresent : ReceptionIsPresent F.history receipt E)
    (hCorrelative : ReceivingIsCorrelativeWithGiving (giving F) receipt)
    (hNoSelf : NoReceivedSelfGiving F E) :
    ConcurrentlyActualizedByAnother F.history (giving F) E := by
  sorry

theorem jointInertia : Control.JointInertia := by
  sorry

theorem onsetOnlyPassion : Control.OnsetOnlyPassion := by
  sorry

end TruthCore.Results.Causality.ConcurrentGiving
