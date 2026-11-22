module

public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Causality.ActPriorityThetaEight

/-!
GOD_4 cannot fail to be in being: a divine-attribute bridge found by the
target-free conjecture pilot of #1834 (candidate C10 in
`explorations/conjectures/actualization-grades-1834.toml`).

It composes two families that no registered argument joins at this point. The
*quarta via* side: whatever is GOD_4 is maximal in being
(`GodIsMaximalInBeing`, open) and whatever is maximal in being is the first
being (`MaximumInBeingIsFirstBeing`). The act/potency side: every first being
is simply incorruptible (`FirstBeingIsIncorruptibleSimply`, the open *Metaphysics*
Θ.8 analyst premise whose denial is a contingent first being). The two sides
meet only in the one simple-priority relation `PriorSimply` (PRIOR_1, tagged on
both declarations). The Θ.8 respect carrier and its `esse` are kept apart from
the *quarta via*'s `Respect` and `esse`: the conclusion uses the Θ.8 ones, and
no identification of the two respects of being is assumed.

`IncorruptibleSimply` is CORRUPTIBLE_INCORRUPTIBLE_1 (cannot fail to be in the
respect of being). It is not the *tertia via*'s necessary being
(`IsNecessary`, DEF-NECESSARY-BEING: x cannot not-be, it is not possible that x
is not): pilot control C11 certifies a model in which the three premises hold
and GOD_4 is incorruptible in this sense but not necessary in that one.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.GodIncorruptibility

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Causality.ActPriorityThetaEight

/-- Whatever is GOD_4 is simply incorruptible: it cannot fail to be in the
respect `esse` (CORRUPTIBLE_INCORRUPTIBLE_1). It says nothing about failing to
be in a place, quantity or quality, and nothing about the *tertia via*'s
temporal-modal necessity. -/
def GodIsIncorruptibleSimply {Being R : Type} (IsGod : Being → Prop)
    (CanFailToBe : Being → R → Prop) (esse : R) : Prop :=
  ∀ g, IsGod g → IncorruptibleSimply CanFailToBe esse g

namespace Control

/-- One being, GOD_4, maximal and first in being and unable to fail to be: the
three premises hold together with an instance of GOD_4 (nonvacuity), so the
result is not vacuous in the antecedent. -/
def Witness : Prop :=
  GodIsMaximalInBeing (Being := Unit) (Respect := Unit) (fun _ => True) (fun _ _ => True)
      (fun _ _ _ => False) () ∧
    MaximumInBeingIsFirstBeing (Being := Unit) (Respect := Unit) (fun _ _ => True)
      (fun _ _ _ => False) () (fun _ _ => True) ∧
    FirstBeingIsIncorruptibleSimply (B := Unit) (R := Unit) (fun _ _ => False) ()
      (fun _ _ => True) ∧
    ∃ g : Unit, (fun _ => True) g

/-- Omitting `GodIsMaximalInBeing`: over two beings, `true` is GOD_4 but nothing
is in act, so nothing is maximal; each being is simply prior to the other, so
nothing is first; and everything can fail to be. -/
def OmitGodMaximal : Prop :=
  MaximumInBeingIsFirstBeing (Being := Bool) (Respect := Unit) (fun _ _ => False)
      (fun _ _ _ => False) () (fun y x => y ≠ x) ∧
    FirstBeingIsIncorruptibleSimply (B := Bool) (R := Unit) (fun _ _ => True) ()
      (fun y x => y ≠ x) ∧
    ¬ GodIsIncorruptibleSimply (Being := Bool) (R := Unit) (fun g => g = true)
      (fun _ _ => True) ()

/-- Omitting `MaximumInBeingIsFirstBeing`: `true` is GOD_4 and maximal, but
`false` is simply prior to it, so it is not first; it can fail to be. -/
def OmitMaximumFirst : Prop :=
  GodIsMaximalInBeing (Being := Bool) (Respect := Unit) (fun g => g = true) (fun _ _ => True)
      (fun _ _ _ => False) () ∧
    FirstBeingIsIncorruptibleSimply (B := Bool) (R := Unit) (fun _ _ => True) ()
      (fun y x => y ≠ x) ∧
    ¬ GodIsIncorruptibleSimply (Being := Bool) (R := Unit) (fun g => g = true)
      (fun _ _ => True) ()

/-- Omitting `FirstBeingIsIncorruptibleSimply` (the contingent-first-being
rival): the only being is GOD_4, maximal and first in being, and can fail to
be. -/
def OmitFirstIncorruptible : Prop :=
  GodIsMaximalInBeing (Being := Unit) (Respect := Unit) (fun _ => True) (fun _ _ => True)
      (fun _ _ _ => False) () ∧
    MaximumInBeingIsFirstBeing (Being := Unit) (Respect := Unit) (fun _ _ => True)
      (fun _ _ _ => False) () (fun _ _ => True) ∧
    ¬ GodIsIncorruptibleSimply (Being := Unit) (R := Unit) (fun _ => True)
      (fun _ _ => True) ()

/-- The *tertia via* control (pilot C11): over one being that is GOD_4, the three
premises hold (with the values of `Witness`) and GOD_4 is simply incorruptible,
but it is possible that GOD_4 is not (`IsNecessary`, DEF-NECESSARY-BEING, fails:
the possibility predicate holds of every condition and the being is at no time).
So the bundle does not give the *tertia via*'s necessary being. -/
def NotTertiaViaNecessary : Prop :=
  GodIsMaximalInBeing (Being := Unit) (Respect := Unit) (fun _ => True) (fun _ _ => True)
      (fun _ _ _ => False) () ∧
    MaximumInBeingIsFirstBeing (Being := Unit) (Respect := Unit) (fun _ _ => True)
      (fun _ _ _ => False) () (fun _ _ => True) ∧
    FirstBeingIsIncorruptibleSimply (B := Unit) (R := Unit) (fun _ _ => False) ()
      (fun _ _ => True) ∧
    GodIsIncorruptibleSimply (Being := Unit) (R := Unit) (fun _ => True) (fun _ _ => False) () ∧
    ¬ ∀ g : Unit, (fun _ => True) g →
      IsNecessary (Time := Unit) (fun _ => True) (fun _ _ => False) g

/-- The five controls together. -/
def Certificate : Prop :=
  Witness ∧ OmitGodMaximal ∧ OmitMaximumFirst ∧ OmitFirstIncorruptible ∧ NotTertiaViaNecessary

end Control

end TruthCore.Case.Catholicism.GodIncorruptibility
