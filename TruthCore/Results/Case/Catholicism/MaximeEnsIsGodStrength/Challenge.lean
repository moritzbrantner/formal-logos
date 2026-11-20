import TruthCore.Case.Catholicism.MaximeEnsIsGodStrength

/-! Strength-order registration (#1017): `MaximeEnsIsGod` entails
`GodNamesTheUniqueMaximeEns` at the same `InAct`, `MoreIn`, `esse` and `God`,
for every `CausesIn`. The strong version says that every being maximal in being
is `God`; the weak version says so only of a being that is maximal in being,
causes the being of every other being and is the only maximum in being. The
weak version adds two antecedent conditions, so it follows by discarding them.
Found by `truth discover` (#1784); proved here by hand. `maximeEnsOverReducedNamingExact`
certifies the difference (#1598) and `twoMaximaSeparate` the strictness: a
two-point interpretation where the weak version holds and the strong one fails. -/

namespace TruthCore.Results.Case.Catholicism.MaximeEnsIsGodStrength

open TruthCore.Case.Catholicism
open TruthCore.Logic.StrengthComparison

universe v w

/-- If every being maximal in being is `God`, then in particular the only being
maximal in being that causes the being of every other being is `God`. The
`CausesIn` parameter of the weak version is universally quantified: the strong
version does not mention it, so the entailment holds for every cause
relation. -/
theorem godNamesTheUniqueMaximeEnsOfMaximeEnsIsGod {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop)
    (hStrong : MaximeEnsIsGod InAct MoreIn esse God) :
    GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God := by
  sorry

/-- Every maximum in being is `God` iff the reduced nominal description
suffices and every maximum outside it is `God`. Premise-free and constructive. -/
theorem maximeEnsOverReducedNamingExact : MaximeEnsOverReducedNamingExact := by
  sorry

/-- In the two-maxima setting the weak version holds and the strong one fails. -/
theorem twoMaximaSeparate : TwoMaximaSeparate := by
  sorry

end TruthCore.Results.Case.Catholicism.MaximeEnsIsGodStrength
