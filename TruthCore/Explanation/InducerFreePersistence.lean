module

public import TruthCore.Causality.EsseCausePriority
public import TruthCore.Causality.PresentReceipt
public import TruthCore.Causality.TimeSymmetricGiving

@[expose] public section

namespace TruthCore.Explanation.InducerFreePersistence

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Causality.PresentReceipt
open TruthCore.Causality.ConcurrentCessation.C3ActualWorld (originGiving sustainedGiving)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)
open TruthCore.Causality.EsseCausePriority.InertialNecessaryOrigin (history NecessaryOriginWithoutConservation)

/-- At the interval where the law is applied, an inducer of existential loss
must occur somewhere in (s,t]. No uniform cause or least loss time is needed. -/
def IntervalEquivalence : Prop :=
  ∀ (W B T : Type) [Preorder T] (h : History W B T) (D : W → B → T → Prop),
    CessationNeedsInducer h D ↔
      ∀ v x s t, s < t → h.IsAt v x s →
        (∀ u, s < u → u ≤ t → ¬ D v x u) → h.IsAt v x t

abbrev absentInducer : Bool → Bool → Nat → Prop := fun _ _ _ => False

/-- Hold the explanans dictionary fixed even on the sustained interpretation:
an origin or an inducer-free past suffices as an explanation token in both. -/
abbrev reasons := originOrInertia history originGiving absentInducer
abbrev receipt := standingReceipt history falseReceived

def MatchedAssignments : Prop :=
  NecessaryOriginWithoutConservation ∧
  CessationNeedsInducer history absentInducer ∧ MomentaryPSR history reasons falseReceived ∧
  reasons.Explains true (.inr 1) false 2 ∧ receipt.ReceivesAt true () false 2 ∧
  (¬ ∃ g, originGiving.GivesAt true g false 2) ∧ sustainedGiving.GivesAt true true false 2 ∧
  ¬ ExplanationNeedsGiver history originGiving reasons falseReceived ∧
  ¬ ReceivingIsCorrelativeWithGiving originGiving receipt ∧
  ExplanationNeedsGiver history sustainedGiving reasons falseReceived ∧
  ReceivingIsCorrelativeWithGiving sustainedGiving receipt

end TruthCore.Explanation.InducerFreePersistence
