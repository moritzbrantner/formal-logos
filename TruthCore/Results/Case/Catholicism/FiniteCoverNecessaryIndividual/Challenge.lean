import TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCover.Proof

namespace TruthCore.Results.Case.Catholicism.FiniteCoverNecessaryIndividual

open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Logic (ExcludedMiddle)

universe u v

/-- Register the existing finite-omission and population-cover proof. -/
theorem necessaryIndividualOfFiniteCover {W : Type u} {I : Type v}
    (F : Frame W) (present : ExistsAt W I) (w : W)
    (em : ExcludedMiddle) (successor : AccessibleSuccessor F w)
    (amalgamation : AbsenceAmalgamation F present w)
    (cover : FinitePopulationCover F present w) (population : DeDicto F present w) :
    DeRe F present w := by
  sorry

end TruthCore.Results.Case.Catholicism.FiniteCoverNecessaryIndividual
