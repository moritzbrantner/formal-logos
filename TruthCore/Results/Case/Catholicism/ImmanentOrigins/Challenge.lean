import TruthCore.Case.Catholicism.ImmanentOrigins

namespace TruthCore.Results.Case.Catholicism.ImmanentOrigins
open TruthCore.Case.Catholicism.ImmanentOrigins

theorem threeCandidates (d : Profile) (modes : TwoModes d) (personal : Subsistence d)
    (order : PersonalOrder d) (separate : Separation d) : AtLeast d := by
  sorry

theorem exhaustPersons (d : Profile) (lower : AtLeast d) (inventory : Inventory d) :
    Exactly d := by
  sorry

theorem restrictExact (d : Profile) (h : Exactly d) : AtLeast d := by
  sorry

theorem collapse : TokenCollapse := by
  sorry

set_option synthInstance.maxSize 4096
set_option maxRecDepth 4000

local macro "finite_check" : tactic =>
  `(tactic| (dsimp [single, coincident, complete, separateReceptions, iterated, fixture, TwoModes, Separation,
      PersonalOrder, Subsistence, Inventory, SourceUnderived, Classifies, UniqueUnderived,
      UniqueTerm, Underived, Receives, Realizer, Divine] <;> decide))

theorem controls : Controls := by
  sorry

end TruthCore.Results.Case.Catholicism.ImmanentOrigins
