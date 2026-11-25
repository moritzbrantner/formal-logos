import TruthCore.Causality.EssentialPower
import TruthCore.Causality.Q44EssentialSource
import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource

namespace ConstrainedPopulation

open TruthCore.Causality (PowerTransmissionRule)
open TruthCore.Causality.Q44EssentialSource (ParticipatedHasEssentialSource)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (tailAtState)

/-- Two latch stops at positions −1 and +1. A sum linkage displaces each
spring from its neutral length by the signed sum of its two end settings. -/
def stop (setting : Bool) : Int := if setting then 1 else -1

def loaded (a b c : Bool) : Fin 3 → Bool
  | 0 => decide (stop a + stop b ≠ 0)
  | 1 => decide (stop b + stop c ≠ 0)
  | 2 => decide (stop c + stop a ≠ 0)

theorem oddLoad : ∀ a b c, (loaded a b c 0 ^^ loaded a b c 1 ^^ loaded a b c 2) = true := by
  decide

theorem someLoad : ∀ a b c, ∃ i, loaded a b c i = true := by decide

theorem anySoleLoad : ∀ i, ∃ a b c, ∀ j, loaded a b c j = true ↔ j = i := by decide

/-- Reverse only the last contact's preferred alignment. Now all can be relaxed. -/
theorem reversedContact : ∃ a b c : Bool,
    stop a + stop b = 0 ∧ stop b + stop c = 0 ∧ stop c - stop a = 0 := by decide

/-- Three upstream chains. A contact load specifies the state at the bottom of
its chain. This last biconditional is an additional constitutive hypothesis. -/
def assembled (intact active : Fin 3 → Nat → Prop) : Prop :=
  (∀ i, PowerTransmissionRule (fun y x : Nat => y = x + 1 ∧ intact i x) (active i)) ∧
  ∃ a b c, ∀ i, active i 0 ↔ loaded a b c i = true

theorem loadedChannel {intact active} (h : assembled intact active) :
    ∃ i, active i 0 ∧ ∀ n, intact i n ∧ active i (n + 1) := by
  obtain ⟨law, a, b, c, matching⟩ := h
  obtain ⟨i, load⟩ := someLoad a b c
  have start := (matching i).mpr load
  have step (n) (hn : active i n) : intact i n ∧ active i (n + 1) := by
    obtain ⟨_, ⟨rfl, hx⟩, ha⟩ := (law i n).mp hn
    exact ⟨hx, ha⟩
  have allActive (n) : active i n := by
    induction n with
    | zero => exact start
    | succ n ih => exact (step n ih).2
  exact ⟨i, start, fun n => step n (allActive n)⟩

/-- Existence of a joint assignment requires and suffices that one complete
chain have no break. The latch settings are free in this existence test. -/
theorem assemblyCriterion (intact : Fin 3 → Nat → Prop) :
    (∃ active, assembled intact active) ↔ ∃ i, ∀ n, intact i n := by
  constructor
  · rintro ⟨active, h⟩
    obtain ⟨i, _, supplied⟩ := loadedChannel h
    exact ⟨i, fun n => (supplied n).1⟩
  · rintro ⟨i, clear⟩
    obtain ⟨a, b, c, sole⟩ := anySoleLoad i
    refine ⟨fun j _ => j = i, ?_, a, b, c, fun j => (sole j).symm⟩
    intro j n
    constructor
    · rintro rfl
      exact ⟨n + 1, ⟨rfl, clear n⟩, rfl⟩
    · rintro ⟨_, _, hj⟩
      exact hj

/-- The selected chain can still have an actual distinct supplier at each
stage and fail the q44 target under the interpretation OwnBeing nowhere. -/
theorem rootlessChannel {intact active} (h : assembled intact active) :
    ∃ i, active i 0 ∧
      (∀ n, ActualEsseCause (tailAtState (active i)) (n + 1) n) ∧
      ¬ ParticipatedHasEssentialSource (tailAtState (active i)) (active i) (fun _ => False) := by
  obtain ⟨i, start, supplied⟩ := loadedChannel h
  have current (n) : active i n := by
    cases n with
    | zero => exact start
    | succ k => exact (supplied k).2
  refine ⟨i, start, fun n => ⟨Nat.succ_ne_self _, (supplied n).2, current n, rfl⟩, ?_⟩
  intro source
  obtain ⟨_, _, _, own, _⟩ := source 0 start
  exact own

end ConstrainedPopulation
