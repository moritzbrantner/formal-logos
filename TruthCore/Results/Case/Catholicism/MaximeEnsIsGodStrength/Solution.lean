module

public import TruthCore.Case.Catholicism.MaximeEnsIsGodStrength

/-! Strength-order registration (#1017): `MaximeEnsIsGod` entails
`GodNamesTheUniqueMaximeEns` at the same `InAct`, `MoreIn`, `esse` and `God`,
for every `CausesIn`. The strong version says that every being maximal in being
is `God`; the weak version says so only of a being that is maximal in being,
causes the being of every other being and is the only maximum in being. The
weak version adds two antecedent conditions, so it follows by discarding them.
Found by `truth discover` (#1784); proved here by hand. `maximeEnsOverReducedNamingExact`
certifies the difference (#1598) and `twoMaximaSeparate` the strictness: a
two-point interpretation where the weak version holds and the strong one fails. -/

@[expose] public section

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
    GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God :=
  fun m hMax _hCauses _hUnique => hStrong m hMax

/-- Every maximum in being is `God` iff the reduced nominal description
suffices and every maximum outside it is `God`. Premise-free and constructive. -/
theorem maximeEnsOverReducedNamingExact : MaximeEnsOverReducedNamingExact := by
  intro Being Respect InAct MoreIn CausesIn esse God
  constructor
  · intro hStrong
    exact ⟨godNamesTheUniqueMaximeEnsOfMaximeEnsIsGod InAct MoreIn CausesIn esse God hStrong,
      fun m hMax => Or.inr (hStrong m hMax)⟩
  · rintro ⟨hWeak, hDelta⟩ m hMax
    rcases hDelta m hMax with ⟨hCauses, hUnique⟩ | hGod
    · exact hWeak m hMax hCauses hUnique
    · exact hGod

/-- In the two-maxima setting the weak version holds and the strong one fails. -/
theorem twoMaximaSeparate : TwoMaximaSeparate := by
  refine ⟨trivial, ?_, ?_⟩
  · intro m _ _ hUnique
    have hOther := hUnique (!m) ⟨trivial, fun _ h => h⟩
    cases m <;> cases hOther
  · intro hStrong
    exact hStrong true ⟨trivial, fun _ h => h⟩

end TruthCore.Results.Case.Catholicism.MaximeEnsIsGodStrength
