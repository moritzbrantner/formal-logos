import TruthCore.Causality.ComparativePerfectionScale
import TruthCore.Causality.TermSenseForks3

namespace TruthCore.Results.Causality.ComparativePerfectionScale

open TruthCore.Causality.Round3FourthWay
open TruthCore.Causality.TermSenseForks
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem moreInBeingTracksDegreeOfExactCalibration {B R D : Type} [Preorder D]
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R) (value : B → D)
    (hCal : MoreInMatchesDegreeEverywhere MoreIn esse value)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn) :
    MoreInBeingTracksDegree InAct MoreIn esse value := by
  sorry

end TruthCore.Results.Causality.ComparativePerfectionScale
