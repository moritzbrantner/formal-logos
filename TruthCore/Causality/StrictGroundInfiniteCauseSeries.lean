module

public import TruthCore.Causality.DependenceStrictGroundMap

@[expose] public section

namespace TruthCore.Causality.StrictGroundInfiniteCauseSeries

open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Modern.Fine.PureLogicOfGround

/-- One interpretation of the strict-ground map and its efficient-cause consumer
on the successor series. Every member is caused in its sole respect. -/
def ConsumerModel : Prop :=
  let D := fun x y : Nat => x < y
  let C := fun c x : Nat => c = x + 1
  let E := fun c x (_ : Unit) => C c x
  let P := fun c x : Nat => x < c
  ∃ S : Set (Sequent Nat),
    Consistent S ∧ DependenceMapsToStrictExistenceGround D id S ∧
    DistinctBeingsNotMutuallyDependent D ∧
    EffectDependsOnEfficientCause E D ∧ NothingIsEfficientCauseOfItselfReading E ∧
    EfficientCauseNotDependentOnEffect E D ∧
    OrderOfEfficientCausesFoundReading E ∧ EfficientCauseIsPriorToEffectReading E P ∧
    NothingPriorToItselfReading P ∧ SecondEfficientCausesCauseOnlyAsCausedReading E C ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading C ∧ ¬ ∃ f, IsFirstEfficientCause E f

end TruthCore.Causality.StrictGroundInfiniteCauseSeries
