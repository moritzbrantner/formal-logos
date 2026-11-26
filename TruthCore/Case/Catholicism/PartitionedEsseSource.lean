module

public import TruthCore.Case.Catholicism.GodIsOneFromEsse

/-! The existing two-domain partition supplies no common giver to all actual recipients. -/

@[expose] public section

namespace TruthCore.Case.Catholicism.PartitionedEsseSource

open TruthCore.Case.Catholicism.GodIsOneFromEsse
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem noCommonGiver : ¬ MaximeEnsCausesBeingOfAllReading
    (fun (_ : Bool × Bool) (_ : Bool) => True) sourceAbove domainGift true := by
  rintro ⟨⟨d, s⟩, _, gives⟩
  have other : (!d, false) ≠ (d, s) := by
    intro heq
    have : (!d) = d := congrArg Prod.fst heq
    cases d <;> contradiction
  have missed := gives (!d, false) other trivial
  obtain ⟨_, _, same⟩ := missed
  cases d <;> contradiction

end TruthCore.Case.Catholicism.PartitionedEsseSource
