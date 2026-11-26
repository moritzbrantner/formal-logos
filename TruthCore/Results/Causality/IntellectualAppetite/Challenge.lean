import TruthCore.Causality.IntellectualAppetite

namespace TruthCore.Results.Causality.IntellectualAppetite

open TruthCore.Case.Catholicism (GodHasIntellect GodHasWill)
open TruthCore.Causality.IntellectualAppetite

theorem godHasWillFromAppraisedForm {B F : Type}
    {IsGod HasIntellect HasWill : B → Prop}
    {HasForm Appraises InclinedTo : B → F → Prop} {Intelligible : F → Prop}
    (hIntellect : GodHasIntellect IsGod HasIntellect)
    (hAppraisal : GodIntellectApprehendsGood IsGod HasIntellect HasForm Appraises Intelligible)
    (hInclination : AppraisedFormInclines IsGod HasForm Appraises InclinedTo Intelligible)
    (hRecognition : AppraisedInclinationIsWill IsGod Appraises InclinedTo Intelligible HasWill) :
    GodHasWill IsGod HasWill := by
  sorry

end TruthCore.Results.Causality.IntellectualAppetite
