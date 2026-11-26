module

public import TruthCore.Explanation.InducerFreePersistence
public import TruthCore.Results.Causality.EsseCausePriority.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.InducerFreePersistence
open TruthCore.Explanation.InducerFreePersistence

theorem intervalEquivalence : IntervalEquivalence := by
  classical
  intro W B T _ h D
  constructor
  · intro law v x s t hst hs clear
    by_contra lost
    obtain ⟨u, hu, ut, hd⟩ := law v x s t hst hs lost
    exact clear u hu ut hd
  · intro persist v x s t hst hs lost
    by_contra hex
    exact lost (persist v x s t hst hs (fun u hu ut hd => hex ⟨u, hu, ut, hd⟩))

open TruthCore.Causality.EsseCausePriority.InertialNecessaryOrigin (history)
open TruthCore.Causality.ConcurrentCessation.C3ActualWorld (originGiving sustainedGiving)

theorem matchedAssignments : MatchedAssignments := by
  have later : reasons.Explains true (.inr 1) false 2 :=
    ⟨by decide, Or.inr ⟨rfl, rfl, by decide⟩, fun _ _ _ h => h⟩
  have received : receipt.ReceivesAt true () false 2 :=
    ⟨rfl, Or.inr ⟨rfl, rfl, by decide⟩⟩
  have stopped : ¬ ∃ g, originGiving.GivesAt true g false 2 := by
    rintro ⟨_, _, _, _, ht⟩
    contradiction
  have ongoing (v x : Bool) (t : Nat) (hx : x = false) (ht : history.IsAt v x t) :
      ∃ g, sustainedGiving.GivesAt v g x t := by
    rcases ht with hs | ⟨hv, _, hn⟩
    · simp_all
    · exact ⟨true, hv, rfl, hx, hn⟩
  refine ⟨TruthCore.Results.Causality.EsseCausePriority.InertialNecessaryOrigin.necessaryOriginWithoutConservation,
    ?_, ?_, later, received, stopped, ⟨rfl, rfl, rfl, by decide⟩, ?_, ?_, ?_, ?_⟩
  · intro v x s t hst hs lost
    apply False.elim (lost ?_)
    rcases hs with hc | ⟨hv, hx, hn⟩
    · exact Or.inl hc
    · exact Or.inr ⟨hv, hx, by omega⟩
  · intro v x t _ hx ht
    change x = false at hx
    rcases ht with hs | ⟨hv, _, hn⟩
    · simp_all
    · by_cases first : t = 1
      · exact ⟨.inl true, hv, rfl, hx, first⟩
      · exact ⟨.inr 1, by omega, Or.inr ⟨hv, hx, by decide⟩, fun _ _ _ h => h⟩
  · exact fun h => stopped (h true false 2 () (.inr 1) rfl received.2 later)
  · exact fun h => stopped (h true () false 2 received)
  · exact fun v x t _ _ hx ht _ => ongoing v x t hx ht
  · exact fun v _ x t hr => ongoing v x t hr.1 hr.2

end TruthCore.Results.Explanation.InducerFreePersistence
