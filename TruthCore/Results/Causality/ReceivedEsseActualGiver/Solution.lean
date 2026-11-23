module

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
  (ContingentReceivesEsse ContingentHasDistinctEsse ContingentHasDistinctEsseCause esseProfile)
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

/-- B6 + the q.3 a.4 cause reading yield a distinct CAUSE_2. The
separate cause-presence interface makes that same giver actual at w. Existing
#1877 R1/R3/De ente/irreflexivity support for B6 composes upstream. -/
theorem actualGiverFromDistinctEsseAndQ3 {W B T R P : Type}
    (F : CausalityFrame W B T R) (w : W) (InAct : B → R → Prop)
    (essenceOf esseOf : B → P) (suffice : B → Prop)
    (hDistinct : ContingentHasDistinctEsse F w essenceOf esseOf)
    (hActual : ExistingInActAt F.history.ontic InAct F.esse w)
    (hQ3 : DistinctEsseRequiresExternalCauseReading
      (esseProfile F InAct essenceOf esseOf suffice))
    (hPresence : UnitingCausesPresent F.history.ontic F.CausesIn F.esse w) :
    ContingentHasActualEsseGiverAt F w := by
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

/-- Finite nonvacuous separation: B2 supplies a distinct but nonexistent
tenseless CAUSE_2 of the mover `true`. That does not yield an actual distinct
giver, and the world-presence interface fails (that the other route premises
hold here is checked in `presenceControls`). No possibility or
substantive participation claim follows from this syntactic model. -/
theorem absentSourceSeparatesB2FromActualGiver :
    TruthCore.German.Kant.CosmologicalInference.ContingentAt
      TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceFrame.history.ontic
      true true ∧
    ContingentHasDistinctEsseCause
      TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceFrame true ∧
    ¬ ContingentHasActualEsseGiverAt
      TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceFrame true ∧
    ¬ UnitingCausesPresent
      TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceFrame.history.ontic
      TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceFrame.CausesIn
      TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceFrame.esse true := by
  dsimp only [ContingentHasDistinctEsseCause, ContingentHasActualEsseGiverAt,
    UnitingCausesPresent, TruthCore.German.Kant.CosmologicalInference.ContingentAt,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceFrame,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceExists,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceCauses,
    TruthCore.Causality.FirstMoverNecessity.Model.mk]
  have hx :
      ((true = true ∧ true = true) ∧
        ∃ v : Bool, True ∧ ¬ (v = true ∧ true = true)) :=
    ⟨⟨rfl, rfl⟩, ⟨false, ⟨trivial, by decide⟩⟩⟩
  refine ⟨hx, ?_, ?_, ?_⟩
  · intro x hcont
    have hxt : x = true := hcont.1.2
    subst x
    exact ⟨false, by decide, rfl, rfl, rfl⟩
  · intro h
    obtain ⟨c, hne, hAt, _⟩ := h true hx
    exact hne hAt.2
  · intro h
    have hFalse := h false true ⟨rfl, rfl⟩ (by decide) ⟨rfl, rfl, rfl⟩
    exact (by decide : ¬ (false = true)) hFalse.2

/-- Presence controls: strictness of the actual-giver endpoint over B2, and
omission witnesses for the world-presence interface in both routes, in the
same absent-source frame. -/
theorem presenceControls :
    TruthCore.Causality.ReceivedEsseActualGiver.Control.PresenceControls := by
  dsimp only [TruthCore.Causality.ReceivedEsseActualGiver.Control.PresenceControls,
    ContingentHasDistinctEsseCause, ContingentHasActualEsseGiverAt,
    UnitingCausesPresent, TruthCore.German.Kant.CosmologicalInference.ContingentAt,
    ContingentReceivesEsse, ReceivedEsseHasCauseOfBeing, ContingentHasDistinctEsse,
    ExistingInActAt, DistinctEsseRequiresExternalCauseReading, esseProfile,
    TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.DistinctEsseAt,
    TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.HasExternalEsseCause,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceFrame,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceExists,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.absentSourceCauses,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.receivedByMover,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.actAll,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.esseFalse,
    TruthCore.Causality.ReceivedEsseActualGiver.Control.essenceSelf,
    TruthCore.Causality.FirstMoverNecessity.Model.mk]
  have hx :
      ((true = true ∧ true = true) ∧
        ∃ v : Bool, True ∧ ¬ (v = true ∧ true = true)) :=
    ⟨⟨rfl, rfl⟩, ⟨false, ⟨trivial, by decide⟩⟩⟩
  refine ⟨hx, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => trivial, ?_⟩
  · -- B2: the absent `false` causes the contingent mover's esse.
    intro x hcont
    have hxt : x = true := hcont.1.2
    subst x
    exact ⟨false, by decide, rfl, rfl, rfl⟩
  · -- No actual giver: the only cause, `false`, exists at no world.
    intro h
    obtain ⟨c, hne, hAt, _⟩ := h true hx
    exact hne hAt.2
  · -- World presence fails for the edge from `false`.
    intro h
    have hFalse := h false true ⟨rfl, rfl⟩ (by decide) ⟨rfl, rfl, rfl⟩
    exact (by decide : ¬ (false = true)) hFalse.2
  · -- Route 1: R1.
    intro x hcont
    exact ⟨true, hcont.1.2⟩
  · -- Route 1: reception-to-CAUSE_2 coverage.
    intro x _ hx'
    subst hx'
    exact ⟨false, by decide, rfl, rfl, rfl⟩
  · -- Route 2: B6.
    intro x hcont
    have hxt : x = true := hcont.1.2
    subst x
    exact (by decide : (false : Bool) ≠ true)
  · -- Route 2: the q.3 a.4 reading.
    intro x hx'
    cases x with
    | false => exact absurd rfl hx'.2
    | true => exact ⟨false, by decide, trivial, rfl, rfl, rfl⟩

end TruthCore.Results.Causality.ReceivedEsseActualGiver
