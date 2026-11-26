module

public import TruthCore.Results.Alternatives.RespectSwitch.Solution
public import TruthCore.Results.Aquinas.SummaTheologiae.GoodnessFromDesirability.Solution
public import TruthCore.Results.Aristotle.Physics.Typed.NoMoverMovesItself.Solution
public import TruthCore.Results.Case.Catholicism.CauseOfBeingHasBeing.Solution
public import TruthCore.Results.Case.Catholicism.PossessionConsumerReductions.Solution
public import TruthCore.Results.Case.Catholicism.PreexistenceWithoutTransfer.Solution
public import TruthCore.Results.Causality.ActPriorityAtFirst.Solution
public import TruthCore.Results.Causality.ActPriorityThetaEight.Solution
public import TruthCore.Results.Causality.PrimaViaCertificates.Solution
public import TruthCore.Results.Causality.PriorityInBeing.Solution
public import TruthCore.Results.Causality.ReflexiveDependenceScope.Solution
public import TruthCore.Results.Causality.RootWiring.Solution
public import TruthCore.Results.Logic.AssertionRetorsion.Solution

/-! Finite omission controls selected by `truth countermodel` for the stage 1–2 sweep.
Each certificate gives the falsity of the omitted input, the truth of the
other displayed inputs, and the falsity of the encoded conclusion.
The models interpret only their theorem's formal vocabulary. -/

@[expose] public section

namespace TruthCore.Case.Catholicism.DiscoverySweepControls

/-! `TruthCore.Results.Causality.ReflexiveDependenceScope.priorityTransitiveFromDependence`, omitting `hReq`. -/
namespace ReflexiveDependenceScope.priorityTransitiveFromDependence.omit_hReq

abbrev B := Fin 2
abbrev PriorSimply : B → B → Prop := fun x0 x1 =>
  (x0 = 0 ∧ x1 = 1) ∨
  (x0 = 1 ∧ x1 = 0)
abbrev D : B → B → Prop := fun _ _ => False
theorem certificate :
    (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply D) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.PriorityRequiresNonmutualDependence PriorSimply D) ∧
    (TruthCore.Causality.ReflexiveDependenceScope.DependenceForBeingTransitive D) ∧
    ¬ (TruthCore.Alternatives.ActPotencyRegress.SimplePriorityTransitiveReading PriorSimply) := by
  delta
    TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority
    TruthCore.Causality.CausalMapsBatch1.PriorityRequiresNonmutualDependence
    TruthCore.Causality.ReflexiveDependenceScope.DependenceForBeingTransitive
    TruthCore.Alternatives.ActPotencyRegress.SimplePriorityTransitiveReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end ReflexiveDependenceScope.priorityTransitiveFromDependence.omit_hReq

/-! `TruthCore.Results.Causality.PrimaViaCertificates.reciprocityIncompatibleViaDependence`, omitting `hReq`. -/
namespace PrimaViaCertificates.reciprocityIncompatibleViaDependence.omit_hReq

abbrev Being := Fin 2
abbrev Respect := Fin 1
abbrev InAct : Being → Respect → Prop := fun _ _ => True
abbrev InPotency : Being → Respect → Prop := fun _ _ => True
abbrev MovesIn : Being → Being → Respect → Prop := fun x0 x1 x2 =>
  (x0 = 0 ∧ x1 = 1 ∧ x2 = 0) ∨
  (x0 = 1 ∧ x1 = 0 ∧ x2 = 0)
abbrev PriorSimply : Being → Being → Prop := fun x0 x1 =>
  (x0 = 0 ∧ x1 = 1) ∨
  (x0 = 1 ∧ x1 = 0)
abbrev DependsForBeing : Being → Being → Prop := fun _ _ => False
theorem certificate :
    (TruthCore.Alternatives.NightCosmogony.ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.PriorityRequiresNonmutualDependence PriorSimply DependsForBeing) ∧
    (TruthCore.Causality.PrimaViaCertificates.ReciprocalCrossRespectMoving InAct InPotency MovesIn) ∧
    ¬ (TruthCore.Logic.ConfigurationFalse) := by
  delta
    TruthCore.Alternatives.NightCosmogony.ActualMoverIsSimplyPriorReading
    TruthCore.Causality.CausalMapsBatch1.PriorityRequiresNonmutualDependence
    TruthCore.Causality.PrimaViaCertificates.ReciprocalCrossRespectMoving
    TruthCore.Logic.ConfigurationFalse
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end PrimaViaCertificates.reciprocityIncompatibleViaDependence.omit_hReq

/-! `TruthCore.Results.Causality.PriorityInBeing.priorityInBeingRequiresNonmutualDependence`, omitting `hAllows`. -/
namespace PriorityInBeing.priorityInBeingRequiresNonmutualDependence.omit_hAllows

abbrev B := Fin 2
abbrev DependsForBeing : B → B → Prop := fun _ _ => False
abbrev CanBeWithout : B → B → Prop := fun x0 x1 => (x0 = 1 ∧ x1 = 0)
theorem certificate :
    (TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout DependsForBeing CanBeWithout) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Logic.ExcludedMiddle) ∧
    ¬ (TruthCore.Causality.PriorityInBeing.PriorityInBeingRequiresNonmutualDependence CanBeWithout DependsForBeing) := by
  delta
    TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout
    TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout
    TruthCore.Logic.ExcludedMiddle
    TruthCore.Causality.PriorityInBeing.PriorityInBeingRequiresNonmutualDependence
    TruthCore.Causality.PriorityInBeing.PriorInBeing
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | decide | exact Classical.em

end PriorityInBeing.priorityInBeingRequiresNonmutualDependence.omit_hAllows

/-! `TruthCore.Results.Causality.PriorityInBeing.priorityInBeingRequiresNonmutualDependence`, omitting `hExcludes`. -/
namespace PriorityInBeing.priorityInBeingRequiresNonmutualDependence.omit_hExcludes

abbrev B := Fin 2
abbrev DependsForBeing : B → B → Prop := fun x0 x1 =>
  (x0 = 0 ∧ x1 = 1) ∨
  (x0 = 1 ∧ x1 = 0)
abbrev CanBeWithout : B → B → Prop := fun x0 x1 =>
  (x0 = 0 ∧ x1 = 0) ∨
  (x0 = 1 ∧ x1 = 0) ∨
  (x0 = 1 ∧ x1 = 1)
theorem certificate :
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Logic.ExcludedMiddle) ∧
    ¬ (TruthCore.Causality.PriorityInBeing.PriorityInBeingRequiresNonmutualDependence CanBeWithout DependsForBeing) := by
  delta
    TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout
    TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout
    TruthCore.Logic.ExcludedMiddle
    TruthCore.Causality.PriorityInBeing.PriorityInBeingRequiresNonmutualDependence
    TruthCore.Causality.PriorityInBeing.PriorInBeing
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | decide | exact Classical.em

end PriorityInBeing.priorityInBeingRequiresNonmutualDependence.omit_hExcludes

/-! `TruthCore.Results.Case.Catholicism.PreexistenceWithoutTransfer.distinctCauseGivesOfCauseGives`, omitting `h`. -/
namespace PreexistenceWithoutTransfer.distinctCauseGivesOfCauseGives.omit_h

abbrev B := Fin 2
abbrev R := Fin 1
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = 1 ∧ x1 = 0 ∧ x2 = 0)
abbrev InAct : B → R → Prop := fun _ _ => False
theorem certificate :
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) := by
  delta
    TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives
    TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives
  refine ⟨?_, ?_⟩ <;> decide

end PreexistenceWithoutTransfer.distinctCauseGivesOfCauseGives.omit_h

/-! `TruthCore.Results.Case.Catholicism.CauseOfBeingHasBeing.causeOfBeingGivesOfCauseGives`, omitting `h`. -/
namespace CauseOfBeingHasBeing.causeOfBeingGivesOfCauseGives.omit_h

abbrev B := Fin 1
abbrev R := Fin 1
abbrev esse : R := 0
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => True
theorem certificate :
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives CausesIn InAct esse) := by
  delta
    TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives
    TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives
  refine ⟨?_, ?_⟩ <;> decide

end CauseOfBeingHasBeing.causeOfBeingGivesOfCauseGives.omit_h

/-! `TruthCore.Results.Case.Catholicism.PossessionConsumerReductions.nothingMovesExceptInAct`, omitting `hCause`. -/
namespace PossessionConsumerReductions.nothingMovesExceptInAct.omit_hCause

abbrev B := Fin 2
abbrev R := Fin 1
abbrev MovesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = 0 ∧ x1 = 1 ∧ x2 = 0)
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev PartOf : B → B → Prop := fun _ _ => False
theorem certificate :
    (TruthCore.Logic.ExcludedMiddle) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart MovesIn PartOf) ∧
    (TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart PartOf InAct) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct) := by
  delta
    TruthCore.Logic.ExcludedMiddle
    TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo
    TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives
    TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart
    TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart
    TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | exact Classical.em

end PossessionConsumerReductions.nothingMovesExceptInAct.omit_hCause

/-! `TruthCore.Results.Causality.PrimaViaCertificates.causesInIncompatible`, omitting `hCauses`. -/
namespace PrimaViaCertificates.causesInIncompatible.omit_hCauses

abbrev Being := Fin 2
abbrev Respect := Fin 1
abbrev MovedIn : Being → Respect → Prop := fun x0 x1 => (x0 = 1 ∧ x1 = 0)
abbrev MovesIn : Being → Being → Respect → Prop := fun x0 x1 x2 => (x0 = 0 ∧ x1 = 1 ∧ x2 = 0)
abbrev CausesIn : Being → Being → Respect → Prop := fun _ _ _ => False
abbrev InAct : Being → Respect → Prop := fun x0 x1 => (x0 = 0 ∧ x1 = 0)
abbrev CanBe : Being → Respect → Prop := fun x0 x1 => (x0 = 1 ∧ x1 = 0)
theorem certificate :
    (TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading MovedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading MovedIn MovesIn InAct) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading MovedIn
  (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsHad CausesIn InAct) ∧
    ¬ (TruthCore.Logic.ConfigurationFalse) := by
  delta
    TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading
    TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading
    TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading
    TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency
    TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo
    TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsHad
    TruthCore.Logic.ConfigurationFalse
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end PrimaViaCertificates.causesInIncompatible.omit_hCauses

/-! `TruthCore.Results.Causality.ActPriorityAtFirst.firstBeingNoPotencyOfComposition`, omitting `hBridge`. -/
namespace ActPriorityAtFirst.firstBeingNoPotencyOfComposition.omit_hBridge

abbrev B := Fin 2
abbrev R := Fin 1
abbrev esse : R := 0
abbrev InAct : B → R → Prop := fun _ _ => True
abbrev InPotency : B → R → Prop := fun x0 x1 => (x0 = 1 ∧ x1 = 0)
abbrev PriorSimply : B → B → Prop := fun _ _ => False
abbrev Composite : B → Prop := fun x0 => (x0 = 1)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = 0 ∧ x1 = 1 ∧ x2 = 0)
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => False
theorem certificate :
    (TruthCore.Causality.ActPriorityAtFirst.FirstBeingIsInSomeAct InAct PriorSimply) ∧
    (TruthCore.Causality.ActPriorityAtFirst.ActAndPotencyMakeComposite InAct InPotency Composite) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply) := by
  delta
    TruthCore.Causality.ActPriorityAtFirst.FirstBeingIsInSomeAct
    TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing
    TruthCore.Causality.ActPriorityAtFirst.ActAndPotencyMakeComposite
    TruthCore.Latin.Aquinas.SummaTheologiae.CompositeHasAUnitingCauseReading
    TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
    TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading
    TruthCore.Latin.Aquinas.SummaTheologiae.FirstBeingIsInNoWayInPotencyReading
    TruthCore.Latin.Aquinas.SummaTheologiae.PureAct
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end ActPriorityAtFirst.firstBeingNoPotencyOfComposition.omit_hBridge

/-! `TruthCore.Results.Causality.ActPriorityThetaEight.weakOfThetaEight`, omitting `hBridge`. -/
namespace ActPriorityThetaEight.weakOfThetaEight.omit_hBridge

abbrev B := Fin 2
abbrev R := Fin 1
abbrev esse : R := 0
abbrev InAct : B → R → Prop := fun _ _ => True
abbrev InPotency : B → R → Prop := fun x0 x1 => (x0 = 1 ∧ x1 = 0)
abbrev CanFailToBe : B → R → Prop := fun _ _ => False
abbrev PriorSimply : B → B → Prop := fun _ _ => False
abbrev Composite : B → Prop := fun x0 => (x0 = 1)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = 0 ∧ x1 = 1 ∧ x2 = 0)
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => False
theorem certificate :
    (TruthCore.Causality.ActPriorityThetaEight.FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply) ∧
    (TruthCore.Latin.Aquinas.InMetaphysicam.IncorruptibleIsInActReading InAct CanFailToBe esse) ∧
    (TruthCore.Causality.ActPriorityThetaEight.ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) ∧
    ¬ (TruthCore.Causality.ActPriorityAtFirst.FirstBeingActPriority InAct InPotency PriorSimply) := by
  delta
    TruthCore.Causality.ActPriorityThetaEight.FirstBeingIsIncorruptibleSimply
    TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing
    TruthCore.Latin.Aquinas.InMetaphysicam.IncorruptibleSimply
    TruthCore.Latin.Aquinas.InMetaphysicam.IncorruptibleIsInActReading
    TruthCore.Causality.ActPriorityThetaEight.ActInBeingAndPotencyMakeComposite
    TruthCore.Latin.Aquinas.SummaTheologiae.CompositeHasAUnitingCauseReading
    TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
    TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading
    TruthCore.Causality.ActPriorityAtFirst.FirstBeingActPriority
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end ActPriorityThetaEight.weakOfThetaEight.omit_hBridge

/-! `TruthCore.Results.Case.Catholicism.PossessionConsumerReductions.nothingMovesExceptInAct`, omitting `hWhole`. -/
namespace PossessionConsumerReductions.nothingMovesExceptInAct.omit_hWhole

abbrev B := Fin 2
abbrev R := Fin 1
abbrev MovesIn : B → B → R → Prop := fun x0 x1 x2 =>
  (x0 = 0 ∧ x1 = 1 ∧ x2 = 0) ∨
  (x0 = 1 ∧ x1 = 1 ∧ x2 = 0)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 =>
  (x0 = 0 ∧ x1 = 1 ∧ x2 = 0) ∨
  (x0 = 1 ∧ x1 = 1 ∧ x2 = 0)
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = 0 ∧ x1 = 0)
abbrev PartOf : B → B → Prop := fun x0 x1 => (x0 = 0 ∧ x1 = 1)
theorem certificate :
    (TruthCore.Logic.ExcludedMiddle) ∧
    (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart MovesIn PartOf) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart PartOf InAct) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct) := by
  delta
    TruthCore.Logic.ExcludedMiddle
    TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo
    TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives
    TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart
    TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart
    TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | exact Classical.em

end PossessionConsumerReductions.nothingMovesExceptInAct.omit_hWhole

/-! `TruthCore.Results.Alternatives.RespectSwitch.consecutiveRespects`, omitting `hInMoved`. -/
namespace RespectSwitch.consecutiveRespects.omit_hInMoved

abbrev Being := Fin 1
abbrev Respect := Fin 1
abbrev MovedIn : Being → Respect → Prop := fun _ _ => False
abbrev InAct : Being → Respect → Prop := fun _ _ => True
abbrev InPotency : Being → Respect → Prop := fun _ _ => False
abbrev MovesIn : Being → Being → Respect → Prop := fun _ _ _ => True
theorem certificate :
    ¬ (TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading MovesIn MovedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading MovedIn InPotency) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading InAct InPotency) ∧
    ¬ (TruthCore.Alternatives.RespectSwitch.ConsecutiveMoversHaveDistinctRespects MovesIn) := by
  delta
    TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading
    TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading
    TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
    TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading
    TruthCore.Alternatives.RespectSwitch.ConsecutiveMoversHaveDistinctRespects
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end RespectSwitch.consecutiveRespects.omit_hInMoved

/-! `TruthCore.Results.Aristotle.Physics.Typed.NoMoverMovesItself.noMoverMovesItself`, omitting `hInMoved`. -/
namespace NoMoverMovesItself.noMoverMovesItself.omit_hInMoved

abbrev Being := Fin 1
abbrev Respect := Fin 1
abbrev MovedIn : Being → Respect → Prop := fun _ _ => False
abbrev InPotency : Being → Respect → Prop := fun _ _ => False
abbrev ActualizedQuaPotential : Being → Respect → Prop := fun _ _ => False
abbrev InAct : Being → Respect → Prop := fun _ _ => True
abbrev MovesIn : Being → Being → Respect → Prop := fun _ _ _ => True
theorem certificate :
    (TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential) ∧
    ¬ (TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading MovesIn MovedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading InAct InPotency) ∧
    ¬ (TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading MovesIn) := by
  delta
    TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading
    TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading
    TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
    TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading
    TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end NoMoverMovesItself.noMoverMovesItself.omit_hInMoved

/-! `TruthCore.Results.Logic.AssertionRetorsion.thoughtFromAssertion`, omitting `hMade`. -/
namespace AssertionRetorsion.thoughtFromAssertion.omit_hMade

abbrev Agent := Fin 1
abbrev Content := Fin 1
abbrev Episode := Fin 1
abbrev claim : Content := 0
abbrev Asserts : Agent → Content → Prop := fun _ _ => False
abbrev Occurs : Episode → Prop := fun _ => False
abbrev Realizes : Agent → Content → Episode → Prop := fun _ _ _ => False
theorem certificate :
    ¬ (TruthCore.Logic.AssertionRetorsion.AssertionMade Asserts claim) ∧
    (TruthCore.Logic.AssertionRetorsion.AssertionRealized Asserts claim Occurs Realizes) ∧
    ¬ (TruthCore.Logic.CogitoSubject.ThoughtOccurs Occurs) := by
  delta
    TruthCore.Logic.AssertionRetorsion.AssertionMade
    TruthCore.Logic.AssertionRetorsion.AssertionRealized
    TruthCore.Logic.CogitoSubject.ThoughtOccurs
  refine ⟨?_, ?_, ?_⟩ <;> decide

end AssertionRetorsion.thoughtFromAssertion.omit_hMade

/-! `TruthCore.Results.Logic.AssertionRetorsion.meaningFromAssertion`, omitting `hMade`. -/
namespace AssertionRetorsion.meaningFromAssertion.omit_hMade

abbrev Agent := Fin 1
abbrev Content := Fin 1
abbrev claim : Content := 0
abbrev Asserts : Agent → Content → Prop := fun _ _ => False
abbrev Meaningful : Content → Prop := fun _ => False
theorem certificate :
    ¬ (TruthCore.Logic.AssertionRetorsion.AssertionMade Asserts claim) ∧
    (TruthCore.Logic.AssertionRetorsion.AssertedContentIsMeaningful Asserts claim Meaningful) ∧
    ¬ (TruthCore.Logic.AssertionRetorsion.SomeMeaningfulContent Meaningful) := by
  delta
    TruthCore.Logic.AssertionRetorsion.AssertionMade
    TruthCore.Logic.AssertionRetorsion.AssertedContentIsMeaningful
    TruthCore.Logic.AssertionRetorsion.SomeMeaningfulContent
  refine ⟨?_, ?_, ?_⟩ <;> decide

end AssertionRetorsion.meaningFromAssertion.omit_hMade

/-! `TruthCore.Results.Logic.AssertionRetorsion.experienceFromAssertion`, omitting `hMade`. -/
namespace AssertionRetorsion.experienceFromAssertion.omit_hMade

abbrev Agent := Fin 1
abbrev Content := Fin 1
abbrev Episode := Fin 1
abbrev claim : Content := 0
abbrev Asserts : Agent → Content → Prop := fun _ _ => False
abbrev Occurs : Episode → Prop := fun _ => False
abbrev Experienced : Episode → Prop := fun _ => False
abbrev Realizes : Agent → Content → Episode → Prop := fun _ _ _ => False
theorem certificate :
    ¬ (TruthCore.Logic.AssertionRetorsion.AssertionMade Asserts claim) ∧
    (TruthCore.Logic.AssertionRetorsion.AssertionRealized Asserts claim Occurs Realizes) ∧
    (TruthCore.Logic.AssertionRetorsion.AssertionRealizationsExperienced Asserts claim Occurs Experienced Realizes) ∧
    ¬ (TruthCore.Logic.AssertionRetorsion.ExperienceOccurs Occurs Experienced) := by
  delta
    TruthCore.Logic.AssertionRetorsion.AssertionMade
    TruthCore.Logic.AssertionRetorsion.AssertionRealized
    TruthCore.Logic.AssertionRetorsion.AssertionRealizationsExperienced
    TruthCore.Logic.AssertionRetorsion.ExperienceOccurs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end AssertionRetorsion.experienceFromAssertion.omit_hMade

/-! `TruthCore.Results.Aquinas.SummaTheologiae.GoodnessFromDesirability.goodnessIsActualityFromDesirability`, omitting `hPerfect`. -/
namespace GoodnessFromDesirability.goodnessIsActualityFromDesirability.omit_hPerfect

abbrev Being := Fin 1
abbrev Perfection := Fin 1
abbrev GoodIn : Being → Perfection → Prop := fun _ _ => False
abbrev DesirableIn : Being → Perfection → Prop := fun _ _ => False
abbrev PerfectIn : Being → Perfection → Prop := fun _ _ => False
abbrev Has : Being → Perfection → Prop := fun _ _ => True
theorem certificate :
    (TruthCore.Latin.Aquinas.SummaTheologiae.GoodIsDesirableReading GoodIn DesirableIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.DesirableInsofarAsPerfectReading DesirableIn PerfectIn) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.PerfectInsofarAsInActReading PerfectIn Has) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading GoodIn Has) := by
  delta
    TruthCore.Latin.Aquinas.SummaTheologiae.GoodIsDesirableReading
    TruthCore.Latin.Aquinas.SummaTheologiae.DesirableInsofarAsPerfectReading
    TruthCore.Latin.Aquinas.SummaTheologiae.PerfectInsofarAsInActReading
    TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end GoodnessFromDesirability.goodnessIsActualityFromDesirability.omit_hPerfect

/-! `TruthCore.Results.Logic.AssertionRetorsion.experienceFromAssertion`, omitting `hRealizes`. -/
namespace AssertionRetorsion.experienceFromAssertion.omit_hRealizes

abbrev Agent := Fin 1
abbrev Content := Fin 1
abbrev Episode := Fin 1
abbrev claim : Content := 0
abbrev Asserts : Agent → Content → Prop := fun _ _ => True
abbrev Occurs : Episode → Prop := fun _ => False
abbrev Experienced : Episode → Prop := fun _ => False
abbrev Realizes : Agent → Content → Episode → Prop := fun _ _ _ => False
theorem certificate :
    (TruthCore.Logic.AssertionRetorsion.AssertionMade Asserts claim) ∧
    ¬ (TruthCore.Logic.AssertionRetorsion.AssertionRealized Asserts claim Occurs Realizes) ∧
    (TruthCore.Logic.AssertionRetorsion.AssertionRealizationsExperienced Asserts claim Occurs Experienced Realizes) ∧
    ¬ (TruthCore.Logic.AssertionRetorsion.ExperienceOccurs Occurs Experienced) := by
  delta
    TruthCore.Logic.AssertionRetorsion.AssertionMade
    TruthCore.Logic.AssertionRetorsion.AssertionRealized
    TruthCore.Logic.AssertionRetorsion.AssertionRealizationsExperienced
    TruthCore.Logic.AssertionRetorsion.ExperienceOccurs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end AssertionRetorsion.experienceFromAssertion.omit_hRealizes

/-! `TruthCore.Results.Causality.RootWiring.thoughtOccursFromRetorsion`, omitting `hDoubt`. -/
namespace RootWiring.thoughtOccursFromRetorsion.omit_hDoubt

abbrev Act := Fin 1
abbrev Episode := Fin 1
abbrev Performed : Act → Prop := fun _ => False
abbrev DoubtsThought : Act → Prop := fun _ => False
abbrev Occurs : Episode → Prop := fun _ => False
theorem certificate :
    (TruthCore.Logic.ExcludedMiddle) ∧
    ¬ (TruthCore.Causality.Round3CogitoBase.DoubtIsPerformed Performed DoubtsThought) ∧
    (TruthCore.Causality.Round3CogitoBase.PerformedDoubtOfThoughtSelfRefuting Performed DoubtsThought Occurs) ∧
    ¬ (TruthCore.Logic.CogitoSubject.ThoughtOccurs Occurs) := by
  delta
    TruthCore.Logic.ExcludedMiddle
    TruthCore.Causality.Round3CogitoBase.DoubtIsPerformed
    TruthCore.Causality.Round3CogitoBase.PerformedDoubtOfThoughtSelfRefuting
    TruthCore.Logic.PerformedDenial.NoEpisodeOccurs
    TruthCore.Logic.CogitoSubject.ThoughtOccurs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | decide | exact Classical.em

end RootWiring.thoughtOccursFromRetorsion.omit_hDoubt

end TruthCore.Case.Catholicism.DiscoverySweepControls
