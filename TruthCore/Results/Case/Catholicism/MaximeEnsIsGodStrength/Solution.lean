module

public import TruthCore.Case.Catholicism.StageOneQuartaVia

/-! Strength-order registration (#1017): `MaximeEnsIsGod` entails
`GodNamesTheUniqueMaximeEns` at the same `InAct`, `MoreIn`, `esse` and `God`,
for every `CausesIn`. The strong version says that every being maximal in being
is `God`; the weak version says so only of a being that is maximal in being,
causes the being of every other being and is the only maximum in being. The
weak version adds two antecedent conditions, so it follows by discarding them.
Found by `truth discover` (#1784); proved here by hand. Strictness (that the
weak version does not entail the strong one) is not checked here. -/

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.MaximeEnsIsGodStrength

open TruthCore.Case.Catholicism

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
    GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God :=
  fun m hMax _hCauses _hUnique => hStrong m hMax

end TruthCore.Results.Case.Catholicism.MaximeEnsIsGodStrength
