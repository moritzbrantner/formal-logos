module

public import TruthCore.Explanation.InertialReceiverNature
public import TruthCore.Results.Explanation.InducerFreePersistence.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.InertialReceiverNature
open TruthCore.Explanation.InertialReceiverNature

theorem receiverNature : ReceiverNatureControl := by
  have sound (v : Bool) : originIfPresent v := by
    rintro (h | hv)
    · contradiction
    · exact ⟨hv, rfl, rfl, rfl⟩
  refine ⟨InducerFreePersistence.matchedAssignments, ⟨rfl, rfl⟩, sound, ?_⟩
  rintro ⟨φ, ⟨_, rfl⟩, entails⟩
  rcases entails false (sound false) with h | h <;> contradiction

end TruthCore.Results.Explanation.InertialReceiverNature
