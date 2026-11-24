import TruthCore.Causality.DependenceOrderSenses
import TruthCore.Results.Causality.OneDependenceOrder.Solution

/-!
# Sense splits for the one dependence order (#1926 phase 3, continued)

(i) SERIES_OF_CAUSES_4, the existential per se efficient-cause link:

* `perSeEsseSeriesOfPerSeEsseRegress`: the PER_SE_5 regress (ea251340) and the
  restated bridge (every existential per se link is a PER_SE_5 actual cause of
  being) give the existential no-regress premise.
* `perSeEsseLinksOfPresentEsseCause`: no self-causation (8b2561cd) and the
  cross-vocabulary bridge (a here-and-now efficient cause of another's being is an
  actual cause of its being) give the restated bridge.
* `perSeEsseSeriesOfPerSeEfficientSeries`: 97f5850f (SERIES_OF_CAUSES_3) and the
  inclusion of SERIES_OF_CAUSES_4 into SERIES_OF_CAUSES_3 give the existential
  no-regress premise.
* `perSeEsseLinksOfPerSeEfficientLinks`: e8664ab8 and the inclusion give the
  restated bridge.

(ii) PRIOR_4:

* `priorityInBeingWFOfActualGroundingWF`: actual grounding well-founded and the
  PRIOR_4 bridge among actual concreta give PRIOR_4 well-founded among actual
  concreta.

Controls: omissions and nonvacuity for each result, `secundaSplitLimit` and
`priorityConsumerLimit`.
-/

namespace TruthCore.Results.Causality.DependenceOrderSenses

open TruthCore.Causality.DependenceOrderSenses
open TruthCore.Causality.DependenceOrderSenses.Control
open TruthCore.Causality.OneDependenceOrder
  (PerSeEfficientCausesArePerSeEsseCauses ActualEsseCauseIsActualGround
   wellFounded_of_predecessorInclusion not_wellFounded_of_twoCycle not_wellFounded_of_loop
   wellFounded_of_singleEdge not_wellFounded_succ actualGroundingWF_of_wellFounded)
open TruthCore.Causality.OneDependenceOrder.Control
open TruthCore.Results.Causality.OneDependenceOrder
  (true_ne_false' cyc_not_wf noRel_wf edgeTF_wf edge10_wf pNone_regress pEdge_regress)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.PriorityInBeing (PriorInBeing)
open TruthCore.Latin.Aquinas.DeEnte
  (ActualEsseCause PerSeActualEsseCause NoInfiniteActualEsseCauseRegress
   NoInfinitePerSeActualEsseCauseRegress)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (NoInfinitePerSeEfficientCauseSeriesReading NothingIsEfficientCauseOfItselfReading)

/-! ## (i) The existential per se series -/

/-- Existential per se links into PER_SE_5 actual causes of being: every
existential link is a PER_SE_5 link (restated bridge), so accessibility along
PER_SE_5 links gives accessibility along existential links. -/
theorem perSeEsseSeriesOfPerSeEsseRegress {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (AsCaused : B → B → Prop)
    (hRegress : NoInfinitePerSeActualEsseCauseRegress p AsCaused)
    (hBridge : PerSeEsseLinksArePerSeEsseCauses p EfficientlyCausesIn AsCaused) :
    NoInfinitePerSeEsseEfficientCauseSeries EfficientlyCausesIn p.esse AsCaused := by
  sorry

/-- The restated bridge from its parts: an existential link's cause is other than
its effect (no efficient self-causation), so the cross-vocabulary bridge makes it
an actual cause of being; the per se link carries over unchanged. -/
theorem perSeEsseLinksOfPresentEsseCause {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (AsCaused : B → B → Prop)
    (hSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn)
    (hPresent : PresentEfficientEsseCauseIsActualEsseCause p EfficientlyCausesIn) :
    PerSeEsseLinksArePerSeEsseCauses p EfficientlyCausesIn AsCaused := by
  sorry

/-- SERIES_OF_CAUSES_4 into SERIES_OF_CAUSES_3: accessibility along
`CausesAsCaused` gives accessibility along existential links included in it. -/
theorem perSeEsseSeriesOfPerSeEfficientSeries {B R : Type}
    (EfficientlyCausesIn : B → B → R → Prop) (esse : R) (AsCaused CausesAsCaused : B → B → Prop)
    (hSeries : NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused)
    (hIncl : PerSeEsseLinkIsPerSeCauseLink EfficientlyCausesIn esse AsCaused CausesAsCaused) :
    NoInfinitePerSeEsseEfficientCauseSeries EfficientlyCausesIn esse AsCaused := by
  sorry

/-- The restated bridge from e8664ab8 and the inclusion: an existential link is a
`CausesAsCaused` link, which e8664ab8 makes a PER_SE_5 link. -/
theorem perSeEsseLinksOfPerSeEfficientLinks {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (AsCaused CausesAsCaused : B → B → Prop)
    (hOld : PerSeEfficientCausesArePerSeEsseCauses p AsCaused CausesAsCaused)
    (hIncl : PerSeEsseLinkIsPerSeCauseLink EfficientlyCausesIn p.esse AsCaused CausesAsCaused) :
    PerSeEsseLinksArePerSeEsseCauses p EfficientlyCausesIn AsCaused := by
  sorry

/-! ## (ii) Priority in being -/

/-- PRIOR_4 among actual concreta into grounding: each PRIOR_4 step between
actual concreta is a grounding step (bridge), so well-foundedness of grounding
among actual concreta transfers. -/
theorem priorityInBeingWFOfActualGroundingWF {W B : Type} (m : GProfile W B) (w : W)
    (CanBeWithout : B → B → Prop)
    (hWF : ActualGroundingWF m w)
    (hBridge : PriorInBeingAmongActualConcretaIsGround m w CanBeWithout) :
    PriorityInBeingWFAmongActualConcreta m w CanBeWithout := by
  sorry

/-! ## Controls -/

theorem perSeEsseSeriesControls : PerSeEsseSeriesControls := by
  sorry

theorem presentCauseControls : PresentCauseControls := by
  sorry

theorem senseInclusionControls : SenseInclusionControls := by
  sorry

theorem oldBridgeControls : OldBridgeControls := by
  sorry

theorem secundaSplitLimit : SecundaSplitLimit := by
  sorry

theorem priorityInBeingControls : PriorityInBeingControls := by
  sorry

theorem priorityConsumerLimit : PriorityConsumerLimit := by
  sorry

end TruthCore.Results.Causality.DependenceOrderSenses
