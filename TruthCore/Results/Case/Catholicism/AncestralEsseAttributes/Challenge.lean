import TruthCore.Case.Catholicism.AncestralEsseAttributes

namespace TruthCore.Results.Case.Catholicism.AncestralEsseAttributes

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.AncestralEsseAttributes
open TruthCore.Case.Catholicism.AttributesFromEsse (PerfectInFrame)
open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause CommonEsseIsEssenceSource)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Logic (ExcludedMiddle)

/-- Each named maximum is the common source, by exclusion at the last edge. -/
theorem oneFromAncestry {B P R : Type} (p : Profile B P R)
    (IsGod : B → Prop) (MoreIn : R → B → B → Prop)
    (source : CommonEsseIsEssenceSource p)
    (maximal : GodIsMaximalInBeing IsGod p.InAct MoreIn p.esse)
    (exclude : MaximumHasNoDistinctEsseCause p.InAct MoreIn p.CausesIn p.esse)
    (em : ExcludedMiddle) : GodIsOne IsGod := by
  sorry

/-- From any actual respect at a recipient, repeat the preexistence law along
its esse-cause path to the same named maximum. -/
theorem perfectFromAncestry {W B T R P : Type} (F : GradesFrame W B T R)
    (IsGod : B → Prop) (essenceOf esseOf : B → P) (sufficient : B → Prop)
    (source : CommonEsseIsEssenceSource (profileOf F essenceOf esseOf sufficient))
    (maximal : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (exclude : MaximumHasNoDistinctEsseCause F.InAct F.MoreIn F.CausesIn F.esse)
    (em : ExcludedMiddle)
    (being : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (preexist : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse) :
    PerfectInFrame F IsGod := by
  sorry

open TruthCore.Case.Catholicism.AncestralEsseAttributes.Control
open TruthCore.Causality.Q44SourceSupply.Control (Being chainCause)
open TruthCore.Causality.Q44EssentialSource.Control.Three

/-- The populated finite chain satisfies the premises and conclusions of the two attribute conditionals and shows
that the same nonlogical inputs can hold with direct supreme goodness false. -/
theorem chainControl : ChainControl := by
  sorry

end TruthCore.Results.Case.Catholicism.AncestralEsseAttributes
