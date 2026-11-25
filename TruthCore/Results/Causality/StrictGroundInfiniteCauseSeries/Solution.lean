module

public import TruthCore.Causality.StrictGroundInfiniteCauseSeries
public import TruthCore.Results.Causality.CausalMapsBatch1.Solution
public import TruthCore.Results.Causality.DependenceStrictGroundMap.Solution
public import TruthCore.Results.Causality.Round2PerfectionPrimacy.Solution
public import TruthCore.Results.Aquinas.SummaTheologiae.SecundaVia.Solution

@[expose] public section

namespace TruthCore.Results.Causality.StrictGroundInfiniteCauseSeries

open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.StrictGroundInfiniteCauseSeries
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Results.Modern.Fine.InfiniteDescent
open TruthCore.Results.Modern.Fine.PlgDerivedRules

/-- The consistent PLG successor series realizes the exact P2 consumer,
including its other premises, while the per se causes have no first member. -/
theorem strictGroundConsumerAllowsInfiniteCauses : ConsumerModel := by
  let D := fun x y : Nat => x < y
  let C := fun c x : Nat => c = x + 1
  let E := fun c x (_ : Unit) => C c x
  let P := fun c x : Nat => x < c
  obtain ⟨S, hCons, hStep, _⟩ := nonCircularityAllowsInfiniteDescent
  have hMap : DependenceMapsToStrictExistenceGround D id S := by
    intro x y hne hxy
    clear hne
    change x < y at hxy
    change StrictlyGrounds S y x
    induction y with
    | zero => exact False.elim (Nat.not_lt_zero _ hxy)
    | succ y ih =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hxy) with h | rfl
      · exact strictTrans (hStep y) (ih h)
      · exact hStep x
  have hP2 := DependenceStrictGroundMap.nonmutualDependenceFromStrictGround D id S hCons hMap
  have hDep : EffectDependsOnEfficientCause E D := by
    intro c x _ he
    exact (show c = x + 1 from he) ▸ Nat.lt_succ_self x
  have hNoSelf : NothingIsEfficientCauseOfItselfReading E :=
    fun x _ h => Nat.ne_of_lt (Nat.lt_succ_self x) h
  have hConsumer := Round2PerfectionPrimacy.efficientCauseNotDependent E D hDep hNoSelf hP2
  have hOrder : OrderOfEfficientCausesFoundReading E := ⟨1, 0, (), rfl⟩
  have hSuff : NonmutualDependenceSufficesForPriority P D := fun _ _ h _ => h
  have hPrior := CausalMapsBatch1.efficientCausePrior E P D hDep hConsumer hSuff
  have hIrrefl : NothingPriorToItselfReading P := Nat.lt_irrefl
  have hMiddle : SecondEfficientCausesCauseOnlyAsCausedReading E C := fun _ _ _ _ h _ => h
  have hNoFirst : ¬ ∃ f, IsFirstEfficientCause E f := fun ⟨f, _, h⟩ => h (f + 1) () rfl
  refine ⟨S, hCons, hMap, hP2, hDep, hNoSelf, hConsumer, hOrder, hPrior, hIrrefl,
    hMiddle, ?_, hNoFirst⟩
  intro hRegress
  exact Aquinas.SummaTheologiae.SecundaVia.secundaVia E P C hOrder hPrior hIrrefl
    hMiddle hRegress hNoFirst

end TruthCore.Results.Causality.StrictGroundInfiniteCauseSeries
