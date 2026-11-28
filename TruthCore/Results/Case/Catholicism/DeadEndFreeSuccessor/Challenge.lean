import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.FinitePopulationCover

namespace TruthCore.Results.Case.Catholicism.DeadEndFreeSuccessor

open TruthCore.Modal (Frame)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (AccessibleSuccessor)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (NoDeadEndWorld)
open TruthCore.Logic (ExcludedMiddle)

/-- In a frame with no dead ends, excluded middle gives a successor at the
selected world. The proof does not require self-access. -/
theorem successorWithoutDeadEnds {W : Type} (F : Frame W) (w : W)
    (noDeadEnd : NoDeadEndWorld F) (em : ExcludedMiddle) : AccessibleSuccessor F w := by
  sorry

end TruthCore.Results.Case.Catholicism.DeadEndFreeSuccessor
