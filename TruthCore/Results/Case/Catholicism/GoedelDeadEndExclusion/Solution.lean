module

public import TruthCore.Results.Isabelle.NotesOnGoedel.Inconsistency.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.GoedelDeadEndExclusion

open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1

/-- Register the existing frame consequence of the explicit Gödel premises. -/
theorem noDeadEndOfPositivity {World Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (ax2a : PositiveOrNegationPositiveExclusively P)
    (ax4 : PositiveClosedUnderNecessaryInclusion F ex P)
    (emptyExcluded : EmptyPropertyNotPositive P) :
    NoDeadEndWorld F := by
  exact TruthCore.Results.Isabelle.NotesOnGoedel.Inconsistency.noDeadEndWorld F ex P ax2a ax4 emptyExcluded

end TruthCore.Results.Case.Catholicism.GoedelDeadEndExclusion
