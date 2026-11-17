import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.DirectorInheritance
import TruthCore.Case.Catholicism.StageOneQuintaVia
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Aquinas.SummaTheologiae.DirectorInheritance
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.DirectorInheritance
open TruthCore.Case.Catholicism (NaturalDirectionReducedToIntelligentImmobileDirector)

theorem weaken {Being Respect End : Type} (NaturalBody : Being → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (Directs : Being → Being → End → Prop)
    (hThrough : DirectionPassesToMoversOfDirectors MovesIn Directs) :
    SameEndMoverSelection NaturalBody MovesIn Directs := by
  sorry

theorem fromSelection {Being Respect End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop)
    (hOther : MovedByAnotherReading MovedIn MovesIn)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved)
    (hEM : ExcludedMiddle)
    (hSelect : SameEndMoverSelection NaturalBody MovesIn Directs)
    (hDesign : UnmovedDirectorKnowsAndUnderstands MovedIn HasCognition Intelligent Directs) :
    NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody HasCognition
      Intelligent Directs := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.DirectorInheritance
