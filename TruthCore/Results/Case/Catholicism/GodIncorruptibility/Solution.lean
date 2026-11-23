module

public import TruthCore.Case.Catholicism.GodIncorruptibility

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.GodIncorruptibility
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Causality.ActPriorityThetaEight
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.GodIncorruptibility

/-- GOD_4 cannot fail to be in being (CORRUPTIBLE_INCORRUPTIBLE_1), from the
*quarta via* side (whatever is GOD_4 is maximal in being; whatever is maximal in
being is the first being) and the *Metaphysics* Θ.8 side (every first being is
simply incorruptible). The two sides share only `PriorSimply`; the Θ.8 respect
carrier `R` and its `esse'` are separate from the *quarta via*'s `Respect` and
`esse`. Found by the target-free conjecture pilot of #1834 (candidate C10). -/
theorem godIsIncorruptibleSimply {Being Respect R : Type}
    (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (PriorSimply : Being → Being → Prop)
    (CanFailToBe : Being → R → Prop) (esse' : R)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse' PriorSimply) :
    GodIsIncorruptibleSimply IsGod CanFailToBe esse' := by
  intro g hg
  exact hIncorruptible g (hFirstBeing g (hMaximal g hg))

/-- The controls of `Control.Certificate`: a nonvacuity witness, the three
omission models (each premise is needed) and the *tertia via* control. The
proof uses no axiom: every step is case analysis on `Bool`/`Unit`, `decide`
on concrete Booleans, or an explicit term. -/
theorem controls : TruthCore.Case.Catholicism.GodIncorruptibility.Control.Certificate := by
  -- no first being when each of two beings is simply prior to the other
  have noFirst : ∀ f : Bool, (∀ y : Bool, y ≠ f → y = f) → False := by
    intro f hf
    have h := hf (!f) (by cases f <;> decide)
    cases f
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  refine ⟨⟨?_, ?_, ?_, ⟨(), trivial⟩⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro _ _; exact ⟨trivial, fun _ h => h⟩
  · intro _ _ _ _; rfl
  · intro _ _ h; exact h
  · intro m hm; exact absurd hm.1 id
  · intro f hf _; exact noFirst f hf
  · intro h; exact h true rfl trivial
  · intro g hg; cases hg; exact ⟨trivial, fun _ h => h⟩
  · intro f hf _; exact noFirst f hf
  · intro h; exact h true rfl trivial
  · intro _ _; exact ⟨trivial, fun _ h => h⟩
  · intro _ _ _ _; rfl
  · intro h; exact h () trivial trivial
  · intro _ _; exact ⟨trivial, fun _ h => h⟩
  · intro _ _ _ _; rfl
  · intro _ _ h; exact h
  · intro _ _ h; exact h
  · intro h; exact h () trivial trivial

end TruthCore.Results.Case.Catholicism.GodIncorruptibility
