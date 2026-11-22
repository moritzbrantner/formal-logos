import TruthCore.Case.Catholicism.MaximumFirstByPriorCause
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Case.Catholicism.MaximumFirstByPriorCause
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.MaximumFirstByPriorCause
open TruthCore.Logic

/-- Whatever is maximal in being is the first being: if `y` is simply prior to
the maximum `m`, then `y` causes `m`'s being; a distinct such cause is excluded
by `MaximumHasNoDistinctEsseCause`, so `y = m` (case split by excluded middle). -/
theorem maximumInBeingIsFirstBeingOfPriorCause {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (PriorSimply : Being → Being → Prop)
    (hPrior : SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse)
    (hNoCause : MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn esse)
    (hEM : ExcludedMiddle) :
    MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
  sorry

/-- The three finite interpretations of `Controls`. -/
theorem controls : Controls := by
  sorry

end TruthCore.Results.Case.Catholicism.MaximumFirstByPriorCause
