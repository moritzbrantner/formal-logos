module

public import TruthCore.Causality.ComparativePerfectionScale
public import TruthCore.Causality.TermSenseForks3

@[expose] public section

namespace TruthCore.Results.Causality.ComparativePerfectionScale

open TruthCore.Causality.Round3FourthWay
open TruthCore.Causality.TermSenseForks
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem moreInBeingTracksDegreeOfExactCalibration {B R D : Type} [Preorder D]
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R) (value : B → D)
    (hCal : MoreInMatchesDegreeEverywhere MoreIn esse value)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn) :
    MoreInBeingTracksDegree InAct MoreIn esse value :=
  fun y m h => ⟨hHas esse y m h, (hCal y m).mp h⟩

end TruthCore.Results.Causality.ComparativePerfectionScale
