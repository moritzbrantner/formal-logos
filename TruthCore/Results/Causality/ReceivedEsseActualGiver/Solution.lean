public import TruthCore.Causality.ReceivedEsseActualGiver
public import TruthCore.Results.Causality.FirstMoverNecessity.Solution

/-!
Explicit conditional bridges from received esse to an actual distinct source
of esse. The Challenge is frozen before Solution. These connections neither
establish R1 nor identify receiving, causing and grounding.
-/

@[expose] public section

namespace TruthCore.Results.Causality.ReceivedEsseActualGiver

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.ReceivedEsseActualGiver (ContingentHasActualEsseGiverAt)
open TruthCore.Causality.FirstMoverNecessity
  (ContingentReceivesEsse IdentityScopedEsseReception ContingentHasDistinctEsseCause esseProfile)
open TruthCore.Causality.TimeSymmetricGiving (ReceivedEsseHasCauseOfBeing)
open TruthCore.Causality.UnderivedNonComposite (UnitingCausesPresent)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseRequiresExternalCauseReading)

/-- R1 + the existing reception-to-CAUSE_2 coverage bridge + the explicit actual-cause presence interface. The same x and c are retained. -/
theorem actualGiverFromReceivedCause {W B T R P : Type}
    (F : CausalityFrame W B T R) (w : W) (Received : B → P → Prop)
    (hR1 : ContingentReceivesEsse F w Received)
    (hCoverage : ReceivedEsseHasCauseOfBeing F.CausesIn F.esse Received)
    (hPresence : UnitingCausesPresent F.history.ontic F.CausesIn F.esse w) :
    ContingentHasActualEsseGiverAt F w := by
  intro x hx
  obtain ⟨p, hp⟩ := hR1 x hx
  obtain ⟨c, hcNe, hcEsse⟩ := hCoverage x p hp
  exact ⟨c, hcNe, hPresence c x hx.1 hcNe hcEsse, hcEsse⟩

/-- A second route shares R1 and actual-cause presence, but uses R3, De ente, irreflexivity and the separately open q.3 a.4 causal reading instead of coverage. -/
theorem actualGiverFromReceptionAndQ3 {W B T R P : Type}
    (F : CausalityFrame W B T R) (w : W) (InAct : B → R → Prop)
    (essenceOf esseOf : B → P) (suffice : B → Prop)
    (Received : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (hR1 : ContingentReceivesEsse F w Received)
    (hR3 : IdentityScopedEsseReception essenceOf esseOf Received)
    (hDeEnte : TruthCore.Latin.Aquinas.DeEnte.ReceiverInPotencyToReceivedEsseReading
      esseOf Received ReceptivePotencyTo)
    (hIrrefl : TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself
      ReceptivePotencyTo)
    (hActual : ExistingInActAt F.history.ontic InAct F.esse w)
    (hQ3 : DistinctEsseRequiresExternalCauseReading
      (esseProfile F InAct essenceOf esseOf suffice))
    (hPresence : UnitingCausesPresent F.history.ontic F.CausesIn F.esse w) :
    ContingentHasActualEsseGiverAt F w := by
  have hDistinct :=
    TruthCore.Results.Causality.FirstMoverNecessity.contingentDistinctEsseFromReception
      F essenceOf esseOf Received ReceptivePotencyTo w hR1 hR3 hDeEnte hIrrefl
  have hCause :=
    TruthCore.Results.Causality.FirstMoverNecessity.contingentEsseCauseFromDistinctEsse
      F InAct essenceOf esseOf suffice w hDistinct hActual hQ3
  intro x hx
  obtain ⟨c, hcNe, hcEsse⟩ := hCause x hx
  exact ⟨c, hcNe, hPresence c x hx.1 hcNe hcEsse, hcEsse⟩

/-- B2 is a weakening of the selected-world actual-giver endpoint. The pre-existing First Way result retains its original first-mover witness. -/
theorem actualGiverImpliesB2 {W B T R : Type}
    (F : CausalityFrame W B T R) (w : W)
    (hGiver : ContingentHasActualEsseGiverAt F w) :
    ContingentHasDistinctEsseCause F w := by
  intro x hx
  obtain ⟨c, hcNe, _, hcEsse⟩ := hGiver x hx
  exact ⟨c, hcNe, hcEsse⟩

end TruthCore.Results.Causality.ReceivedEsseActualGiver
