module

public import TruthCore.Explanation.InertialActuality
public import TruthCore.Results.Explanation.InducerFreePersistence.Solution
public import TruthCore.Results.Explanation.LocationPersistence.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.InertialActuality

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)
open TruthCore.Explanation.InertialActuality
open TruthCore.Explanation.LocationPersistence (Sound Stationary)
open TruthCore.Modal.TemporalHistory
open TruthCore.Results.Explanation.InducerFreePersistence (intervalEquivalence)
open TruthCore.Results.Explanation.LocationPersistence (anchoredLocation samePresenceDifferentLocation)

private def frameFor (present : Bool → Bool → Int → Prop) :
    CausalityFrame Bool Bool Int Unit where
  history :=
    { ontic :=
        { frame := ⟨fun _ _ => True⟩
          ExistsAt := fun v x => present v x 0
          Causes := fun _ _ _ => False }
      IsAt := present
      now := 0 }
  GivesAt := fun _ _ _ _ => False
  CausesIn := fun _ _ _ => False
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := ()

-- true as a bearer is the common background. false is the candidate.
private def pairedFrame : CausalityFrame Bool Bool Int Unit :=
  frameFor (fun v x _ => x = true ∨ v = true)

private theorem pairedLaw : CessationNeedsInducer pairedFrame.history noInducer :=
  fun _ _ _ _ _ earlier absent => (absent earlier).elim

private theorem backgroundEverlasting (v : Bool) :
    EverlastingAt pairedFrame.history v true :=
  fun _ => Or.inl rfl

private theorem candidateEverlasting : EverlastingAt pairedFrame.history true false :=
  fun _ => Or.inr rfl

private theorem candidateOmitted : ¬ TemporalActuality pairedFrame.history false false := by
  rintro ⟨_, h⟩
  change false = true ∨ false = true at h
  simp at h

theorem lawLeavesActualityOpen : LawLeavesActualityOpen := by
  refine ⟨⟨pairedFrame, pairedLaw, backgroundEverlasting, candidateEverlasting,
    ⟨0, candidateEverlasting 0⟩, candidateOmitted⟩, ?_⟩
  intro entails
  exact candidateOmitted (entails pairedFrame pairedLaw backgroundEverlasting)

theorem inertialReasonRequiresActuality : InertialReasonRequiresActuality := by
  intro W B R F D v x s t law reason
  obtain ⟨before, earlier, clear⟩ := reason
  have later := (intervalEquivalence W B Int F.history D).mp law v x s t before earlier clear
  exact ⟨later, earlier, ⟨s, earlier⟩⟩

theorem natureSelection {W B R : Type} (F : CausalityFrame W B Int R)
    (Essential : B → (W → Prop) → Prop) (φ : W → Prop) (x : B)
    (nature : NatureSuppliesActuality F Essential φ x) : NatureSelection F φ x := by
  intro coherent v fact
  obtain ⟨_, ⟨_, rfl⟩, entails⟩ := nature
  exact ⟨F.history.now, (coherent v x).mp (entails v fact)⟩

theorem everlastingParity : EverlastingParity := by
  have coherent : CoherentAtNow pairedFrame.history := fun _ _ => Iff.rfl
  refine ⟨pairedFrame, pairedLaw, coherent, backgroundEverlasting, candidateEverlasting,
    candidateOmitted, ?_⟩
  intro Essential φ nature v fact
  have actual := natureSelection pairedFrame Essential φ false nature coherent v fact
  cases v with
  | false => exact (candidateOmitted actual).elim
  | true => exact ⟨rfl, actual⟩

theorem otherBearerActualityOpen : OtherBearerActualityOpen := by
  have reason (v : Bool) :
      (originOrInertia pairedFrame.history ⟨pairedFrame.GivesAt⟩ noInducer).Explains
        v (.inr 0) true 1 :=
    ⟨by decide, backgroundEverlasting v 0, fun _ _ _ hd => hd⟩
  refine ⟨⟨pairedFrame, true, false, by decide, pairedLaw,
    fun t => ⟨fun _ => backgroundEverlasting false t, fun _ => backgroundEverlasting true t⟩,
    reason, ⟨0, candidateEverlasting 0⟩, candidateOmitted⟩, ?_⟩
  intro entails
  exact candidateOmitted (entails pairedFrame true false false (by decide) pairedLaw (reason false))

private def protectionFrame : CausalityFrame Bool Bool Int Unit :=
  frameFor (fun v x t => if x then v = true else v = true ∨ t < 1)

private def lossWithoutProtector (v x : Bool) (t : Int) : Prop :=
  v = false ∧ x = false ∧ t = 1

private theorem protectionLaw : CessationNeedsInducer protectionFrame.history lossWithoutProtector := by
  intro v x s t before earlier absent
  cases v <;> cases x <;> simp [protectionFrame, frameFor] at earlier absent
  exact ⟨1, earlier, absent, rfl, rfl, rfl⟩

theorem externalProtectionCompatible : ExternalProtectionCompatible := by
  have clear (u : Int) : ¬ lossWithoutProtector true false u :=
    fun h => Bool.noConfusion h.1
  have present : protectionFrame.history.IsAt true false 1 := Or.inl rfl
  have absent : ¬ protectionFrame.history.IsAt false false 1 := by
    simp [protectionFrame, frameFor]
  have reason :
      (originOrInertia protectionFrame.history ⟨protectionFrame.GivesAt⟩
        lossWithoutProtector).Explains true (.inr 0) false 1 :=
    ⟨by decide, Or.inl rfl, fun u _ _ => clear u⟩
  refine ⟨protectionFrame, lossWithoutProtector, protectionLaw, rfl, by simp [protectionFrame, frameFor], ?_, clear,
    fun _ => Or.inr (by decide), present, absent, fun _ _ hg => hg, reason, ?_⟩
  · intro v
    cases v <;> simp [lossWithoutProtector, protectionFrame, frameFor]
  · intro bridge
    obtain ⟨_, hg⟩ := bridge true false 1 () (.inr 0) rfl present reason
    exact hg

theorem transferLocation {W B R : Type} (F : CausalityFrame W B Int R)
    (D : W → B → Int → Prop) (v : W) (x : B)
    (state : ExistenceStateWithoutProduction F D v x) :
    AnchoredExistenceWithoutProduction F D v x := by
  classical
  intro clear noGiving noOnset s earlier
  let trace (t : Int) : Option Unit := if F.history.IsAt v x t then some () else none
  have report (t : Int) : trace t = some () ↔ F.history.IsAt v x t := by
    by_cases ht : F.history.IsAt v x t <;> simp [trace, ht]
  have sound : Sound F.history v x trace := by
    intro t place atPlace
    cases place
    exact (report t).mp atPlace
  have stationary : Stationary trace := by
    intro t
    have step : F.history.IsAt v x (t + 1) ↔ F.history.IsAt v x t :=
      ⟨noOnset t, fun ht => state t ht (clear (t + 1)) (fun ⟨g, hg⟩ => noGiving (t + 1) g hg)⟩
    change trace (t + 1) = trace t
    simp [trace, step]
  intro t
  exact (anchoredLocation W B Unit F.history v x trace s () sound stationary
    ((report s).mpr earlier) t).2

theorem locationDoesNotSupplyStateLaw : LocationDoesNotSupplyStateLaw := by
  refine ⟨samePresenceDifferentLocation, protectionFrame, fun _ _ hg => hg, ?_, ?_⟩
  · intro s later
    change false = true ∨ s + 1 < 1 at later
    change false = true ∨ s < 1
    exact later.elim Or.inl (fun h => Or.inr (by omega))
  · intro state
    have after := state 0 (Or.inr (by decide)) (fun hg => hg) (fun ⟨_, hg⟩ => hg)
    change false = true ∨ (0 : Int) + 1 < 1 at after
    simp at after

theorem stateAndReceiptCompatible : StateAndReceiptCompatible := by
  refine ⟨pairedFrame, candidateEverlasting, fun _ _ hg => hg, ?_, ⟨(), rfl⟩⟩
  intro s _ _ _
  exact candidateEverlasting (s + 1)

end TruthCore.Results.Explanation.InertialActuality
