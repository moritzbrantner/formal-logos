module

public import TruthCore.Case.Catholicism.MaximumFirstByPriorCause
public import TruthCore.Logic.ExcludedMiddle

@[expose] public section

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
  intro m hMax y hy
  rcases hEM (y = m) with h | h
  · exact h
  · exact absurd (hPrior y m hy) (hNoCause m hMax y h)

/-- The three finite interpretations of `Controls`. -/
theorem controls : Controls := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ _ => True, fun _ x y => x = true ∧ y = false,
      fun c x _ => c = true ∧ x = false, fun y x => y = true ∧ x = false,
      ?_, ?_, ?_, ⟨rfl, rfl⟩, ?_⟩
    · intro y x hyx
      exact hyx
    · intro m hm c _ hcm
      exact hm.2 c hcm
    · exact ⟨True.intro, fun y hy => Bool.noConfusion hy.2⟩
    · intro m hm y hy
      exact (hm.2 y hy).elim
  · refine ⟨fun _ _ => True, fun _ _ _ => False,
      fun c x _ => c = true ∧ x = false, fun y x => y = true ∧ x = false,
      fun y x hyx => hyx, ?_⟩
    intro h
    exact Bool.noConfusion (h false ⟨True.intro, fun _ hn => hn⟩ true ⟨rfl, rfl⟩)
  · refine ⟨fun _ _ => True, fun _ _ _ => False, fun _ _ _ => False,
      fun y x => y = true ∧ x = false, fun _ _ _ _ hc => hc, ?_⟩
    intro h
    exact Bool.noConfusion (h false ⟨True.intro, fun _ hn => hn⟩ true ⟨rfl, rfl⟩)

end TruthCore.Results.Case.Catholicism.MaximumFirstByPriorCause
