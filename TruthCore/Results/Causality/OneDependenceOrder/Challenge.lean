import TruthCore.Causality.OneDependenceOrder

/-!
# One dependence order (#1926 phase 3)

* `esseRegressOfActualGroundingWF`: actual grounding well-founded, an actual
  concretum's distinct esse cause is its actual concrete ground (cb1cdea9),
  what is in act of esse exists at `w` (546975ef) and is concrete (2d9807a5)
  give no infinite regress of actual causes of being (fd12ad3d).
* `actualGroundingWFOfEsseRegress`: the converse inclusion. The esse regress,
  an actual concrete ground of an actual concretum is a distinct cause of its
  esse (98efaa9e) and what exists at `w` is in act of esse (0436de86) give
  well-founded actual grounding.
* `simplePriorityWFOfActualGroundingWF`: actual grounding well-founded, what is
  simply prior to something other than itself is its actual concrete ground
  (86efed1a) and nothing is prior to itself (32d77f18) give well-founded simple
  priority (d85de8e1), for the frame's `F.PriorSimply`.
* `perSeEfficientSeriesOfPerSeEsseRegress`: the per se esse regress
  (ea251340) and the new bridge that per se efficient-cause links are per se
  actual causes of being give no infinite per se series of efficient causes
  (97f5850f).

Each step transfers well-foundedness along an explicit inclusion; nothing
identifies the relations. The controls show each input is needed under the
encoded predicates, that actual grounding is not recovered from what it implies
without the converse bridge, and (`ascentLimit`) that no recorded inclusion
gives the quarta via's no-infinite-ascent premise from actual grounding.
-/

namespace TruthCore.Results.Causality.OneDependenceOrder

open TruthCore.Causality.OneDependenceOrder
open TruthCore.Causality.OneDependenceOrder.Control
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Latin.Aquinas.DeEnte
  (ActualEsseCause NoInfiniteActualEsseCauseRegress NoInfinitePerSeActualEsseCauseRegress)
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.GradedSupportFoundation
  (ActualGroundIsDistinctEsseCause NoInfiniteAscentAmongActualConcreta)
open TruthCore.Causality.Round5Worklist (SimplePriorityWellFounded)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (NothingPriorToItselfReading NoInfinitePerSeEfficientCauseSeriesReading)

/-! ## The derivations -/

/-- Esse causing into actual grounding: every actual cause of being `c` of `x`
is, by the two actuality calibrations, a cause of the esse of an actual
concretum, hence (bridge) an actual concrete ground of it. Well-foundedness of
grounding among actual concreta transfers to actual causes of being. -/
theorem esseRegressOfActualGroundingWF {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hWF : ActualGroundingWF m w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExists : ActOfEsseSufficesForExistenceAt m.ontic p.InAct p.esse w)
    (hConcrete : EsseInReIsConcrete m p.InAct p.esse) :
    NoInfiniteActualEsseCauseRegress p := by
  sorry

/-- Actual grounding into esse causing: a ground between actual concreta is a
distinct cause of the grounded thing's esse (bridge), and both are in act of
esse because they exist at `w`. Well-foundedness of actual causes of being
transfers to grounding among actual concreta. -/
theorem actualGroundingWFOfEsseRegress {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hRegress : NoInfiniteActualEsseCauseRegress p)
    (hGround : ActualGroundIsDistinctEsseCause m w p.CausesIn p.esse)
    (hInAct : ExistingInActAt m.ontic p.InAct p.esse w) :
    ActualGroundingWF m w := by
  sorry

/-- Simple priority into actual grounding: what is simply prior to x is other
than x (irreflexivity) and hence (bridge) an actual concrete ground of x.
Well-foundedness of grounding among actual concreta transfers to simple
priority on the whole carrier. -/
theorem simplePriorityWFOfActualGroundingWF {W B T R : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w)
    (hPrior : SimplyPriorIsActualConcreteGround m w F.PriorSimply)
    (hIrrefl : NothingPriorToItselfReading F.PriorSimply) :
    SimplePriorityWellFounded F.PriorSimply := by
  sorry

/-- Per se efficient causing into per se esse causing: every per se link is a
per se actual cause of being (bridge), so accessibility along per se actual
causes of being gives accessibility along per se efficient-cause links. -/
theorem perSeEfficientSeriesOfPerSeEsseRegress {B P R : Type}
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (AsCaused CausesAsCaused : B → B → Prop)
    (hRegress : NoInfinitePerSeActualEsseCauseRegress p AsCaused)
    (hBridge : PerSeEfficientCausesArePerSeEsseCauses p AsCaused CausesAsCaused) :
    NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused := by
  sorry

/-! ## Controls -/

theorem esseRegressControls : EsseRegressControls := by
  sorry

theorem converseControls : ConverseControls := by
  sorry

theorem priorityControls : PriorityControls := by
  sorry

theorem secundaControls : SecundaControls := by
  sorry

theorem ascentLimit : AscentLimit := by
  sorry

end TruthCore.Results.Causality.OneDependenceOrder
