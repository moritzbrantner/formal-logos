module

public import TruthCore.Case.Catholicism.StageOneQuartaVia
public import TruthCore.Logic.StrengthComparison

/-! Certified difference (#1598) and strictness control for the strength order
`MaximeEnsIsGod` ⇒ `GodNamesTheUniqueMaximeEns` (#1017), found by
`truth discover` (#1784). Both sides share `InAct`, `MoreIn`, `esse` and `God`;
the comparison adds the weak version's `CausesIn`, which the strong version does
not mention. The strong version adds exactly that the name applies also to every
maximum in being that does not meet the reduced description. No premise is
asserted here. -/

@[expose] public section

namespace TruthCore.Case.Catholicism

open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)
open TruthCore.Logic.StrengthComparison

universe v w

/-- Every maximum in being either meets the reduced nominal description (it
causes the being of every other being and is the only maximum in being) or is
`God`. Stated as a disjunction so that it needs no decidability; classically it
says that every maximum in being outside the reduced description is `God`. It
says nothing about maxima that meet the description. -/
def MaximeEnsOutsideReducedDescriptionIsGod {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn esse m →
    (CausesAllInGenus InAct CausesIn esse m ∧
      ∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m) ∨ God m

/-- `MaximeEnsIsGod` over `GodNamesTheUniqueMaximeEns`; difference: the clause
for maxima outside the reduced description. No background. -/
def maximeEnsOverReducedNaming {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop) : ComparisonSpec where
  stronger := MaximeEnsIsGod InAct MoreIn esse God
  weaker := GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God
  delta := MaximeEnsOutsideReducedDescriptionIsGod InAct MoreIn CausesIn esse God

/-- Exact factorization: every maximum in being is `God` iff the reduced
nominal description suffices and every maximum outside it is `God`, for every
interpretation of the shared vocabulary and every `CausesIn`. -/
def MaximeEnsOverReducedNamingExact : Prop :=
  ∀ {Being : Sort v} {Respect : Sort w} (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop),
    MaximeEnsIsGod InAct MoreIn esse God ↔
      GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God ∧
        MaximeEnsOutsideReducedDescriptionIsGod InAct MoreIn CausesIn esse God

/-- Separating setting: two beings, both in act as to being, nothing more a
being than anything, nothing causes anything, and nothing is `God`. Both beings
are maximal, so no maximum is unique. A formal interpretation only. -/
def twoMaximaSetting : ComparisonSpec :=
  maximeEnsOverReducedNaming (Being := Bool) (Respect := Unit)
    (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => False) () (fun _ => False)

/-- In the two-maxima setting the reduced nominal description holds vacuously
(no maximum is unique) and `MaximeEnsIsGod` fails (no maximum is `God`). -/
def TwoMaximaSeparate : Prop := Separation twoMaximaSetting

end TruthCore.Case.Catholicism
