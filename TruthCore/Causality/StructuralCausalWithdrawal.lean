module

public import TruthCore.Causality.StructuralCausalAdapters
public import TruthCore.Causality.FrameAdapters
public import TruthCore.Causality.TimeSymmetricGiving

/-! Interpret a matched SCM withdrawal on the same begun bearer in two histories.
The truth of every bridge to strict giving and temporal presence is supplied
by the application. See §13 of the sustaining-versus-inertia note. -/

@[expose] public section

namespace TruthCore.Causality.StructuralCausalModel.Withdrawal

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FrameAdapters (giving)
open TruthCore.Causality.InterventionTransitivity (Variable)
open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Explanation.MechanismInterventionParity (TwoState natural)
open TruthCore.Modal.TemporalHistory (BeginsAt)

abbrev baseline (m : Model Variable TwoState Bool) :=
  m.response ⟨true, true⟩ (Mechanism.setting natural)

abbrev removed (m : Model Variable TwoState Bool) :=
  m.response ⟨true, true⟩ (Mechanism.setting ⟨none, some false⟩)

/-- A directed comparison licensed by the supplied admissibility criterion.
Both histories use one frame, one bearer, one onset giver and one onset
moment. The earlier input is true in the two runs and both histories have
the same onset. The loss-inducer predicate is inherited from the cessation
law; its absence in each interval is supplied separately from either later
readout. The current-channel binding concerns the giver's exercise at
`later`, so it has no implication for the giver's own existence. -/
structure Calibration {W B T R : Type} [Preorder T] (F : CausalityFrame W B T R)
    (Allowed : W → W → Prop) (D : W → B → T → Prop)
    (m : Model Variable TwoState Bool) (before cut : W) (giver bearer : B)
    (earlier later : T) : Prop where
  admissible : Allowed before cut
  distinct : giver ≠ bearer
  ordered : earlier < later
  earlierBefore : baseline m .x = true ↔ BeginsAt F.history before bearer earlier
  earlierCut : removed m .x = true ↔ BeginsAt F.history cut bearer earlier
  originBefore : F.GivesAt before giver bearer earlier
  originCut : F.GivesAt cut giver bearer earlier
  noLossBefore : ∀ u, earlier < u → u ≤ later → ¬ D before bearer u
  noLossCut : ∀ u, earlier < u → u ≤ later → ¬ D cut bearer u
  channelBefore : baseline m .y = true ↔ F.GivesAt before giver bearer later
  channelCut : removed m .y = true ↔ F.GivesAt cut giver bearer later
  otherAbsent : ∀ other, other ≠ giver → ¬ F.GivesAt cut other bearer later
  readoutBefore : baseline m .z = true ↔ F.history.IsAt before bearer later
  readoutCut : removed m .z = true ↔ F.history.IsAt cut bearer later

/-- The background response yields a counterinstance to the productive bridge
if the chosen received bearer has a reason for its cut-history presence
there. The responsive loss violates the local instance of the cessation law
when the calibrated cut is inducer-free. Each implication is about its
own admissible pair; it does not assert either pair exists. -/
def CalibratedContrast : Prop :=
  ∀ (W B T R P Q : Type) [Preorder T] (F : CausalityFrame W B T R)
    (Allowed : W → W → Prop) (D : W → B → T → Prop)
    (X : PresenceExplanation W B T Q) (E : B → P → Prop)
    (before cut : W) (giver bearer : B) (earlier later : T),
    (Calibration F Allowed D Mechanism.background before cut giver bearer earlier later →
      ∀ principle reason, E bearer principle → X.Explains cut reason bearer later →
        F.history.IsAt cut bearer later ∧
        ¬ ExplanationNeedsGiver F.history (giving F) X E) ∧
    (Calibration F Allowed D Mechanism.responsive before cut giver bearer earlier later →
      ¬ F.history.IsAt cut bearer later ∧
      ¬ CessationNeedsInducer F.history D)

end TruthCore.Causality.StructuralCausalModel.Withdrawal
