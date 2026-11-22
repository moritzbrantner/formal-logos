import TruthCore.Causality.MetricBeginningArrival
import TruthCore.Results.Causality.MetricGrimReaper.Solution
import TruthCore.Results.Causality.ActualEuclidean.Solution

namespace TruthCore.Results.Causality.MetricBeginningArrival
open TruthCore.Causality.MetricBeginningArrival
open TruthCore.Causality.MetricGrimReaper
open TruthCore.Causality.GrimReaperPatchwork (PopulatedAt)
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)
open TruthCore.Modal.TemporalHistory (History)

/-- B1 in sense BEGINS_2 from metrically finite populated pasts: a possibly
populated history is accessible, and every populated moment of every accessible
history has a past of finite duration, so that history began a finite time
ago. -/
theorem possiblyBeginsFiniteDurationOfMetricallyFinite {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hFinite : PopulatedPastsMetricallyFinite h Concrete k w)
    (hPopulated : PossiblyPopulated h Concrete w) :
    PossiblyBeginsFiniteDuration h Concrete k w := by
  sorry

/-- Strength order (linear time, any real clock): a possible BEGINS_1 beginning
is a possible BEGINS_2 beginning, since a past with a first moment has finite
duration. -/
theorem possiblyFiniteDurationOfFirstMoment {W B T : Type} [LinearOrder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hFirst : PossiblyBeginsFirstMoment h Concrete w) :
    PossiblyBeginsFiniteDuration h Concrete k w := by
  sorry

/-- Arrival B in sense BEGINS_2, with Euclidean access at the selected world
only. Reuses `ActualEuclidean.externalNecessaryConcrete` on the metric
Scenario; the grounding field of the conclusion's profile is an arbitrary
parameter. -/
theorem necessaryConcreteOfFiniteDurationBeginning {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (G : W → B → B → Prop) (w : W)
    (hEuclidean : EuclideanAt h.ontic.frame w)
    (hReflexive : ActualReflexive h.ontic w)
    (hBegins : PossiblyBeginsFiniteDuration h Concrete k w)
    (hOpportunity : FiniteDurationCausalOpportunity h Concrete k causes w) :
    TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt
      ⟨h.ontic, Concrete, G⟩ w := by
  sorry

/-- B1 and B2 in sense BEGINS_2 already give the possibility of a necessary
concrete individual, with no frame condition: the external cause in the
accessible history is necessary there. -/
theorem possiblyNecessaryOfFiniteDurationOpportunity {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (G : W → B → B → Prop) (w : W)
    (hBegins : PossiblyBeginsFiniteDuration h Concrete k w)
    (hOpportunity : FiniteDurationCausalOpportunity h Concrete k causes w) :
    TruthCore.Causality.ComingToBeHorns.PossiblyNecessaryConcrete h Concrete G w := by
  sorry

open TruthCore.Causality.MetricBeginningArrival.Control
open TruthCore.Causality.MetricGrimReaper.Control (PosReal posClock intClock openBelow)
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot)
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Results.Causality.MetricGrimReaper (posFinite posNotBegun openBelowContingent
  unboundedOfSpaced)
open TruthCore.Results.Causality.GrimReaperPatchwork (pivotOne pivotPopulated)

/-- Independence, nonvacuity and sense controls. -/
theorem controls : Certificate := by
  sorry

theorem necessaryActualWithPossibleConcurrentGiving {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hEuclidean : EuclideanAt f.history.ontic.frame w)
    (hReflexive : ActualReflexive f.history.ontic w)
    (hBegins : PossiblyBeginsFiniteDuration f.history Concrete k w)
    (hOpportunity : ConcurrentFiniteDurationCausalOpportunity f Concrete k w) :
    NecessaryConcreteWithPossibleConcurrentGivingAt f Concrete w := by
  sorry

theorem necessaryConcreteOfPossibleConcurrentGiver {W B T S : Type}
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hGiver : NecessaryConcreteWithPossibleConcurrentGivingAt f Concrete w) :
    TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt
      ⟨f.history.ontic, Concrete, G⟩ w := by
  sorry

theorem possiblyNecessaryConcurrentGiver {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hBegins : PossiblyBeginsFiniteDuration f.history Concrete k w)
    (hOpportunity : ConcurrentFiniteDurationCausalOpportunity f Concrete k w) :
    ∃ v c, f.history.ontic.frame.access w v ∧ Concrete c ∧
      f.history.ontic.ExistsAt v c ∧ NecessaryAt f.history.ontic v c ∧
      ConcurrentTotalityGivingAt f Concrete v c := by
  sorry


theorem inertGivingSeparatesOpportunity :
    FiniteDurationCausalOpportunity openBelowSource all posClock
      (fun v c => v = true ∧ c = none) true ∧
    ¬ ConcurrentFiniteDurationCausalOpportunity inertGivingFrame all posClock true := by
  sorry


theorem functioningConcurrentOpportunity :
    ConcurrentFiniteDurationCausalOpportunity functioningGivingFrame all posClock true := by
  sorry


theorem mixedPossibleGivingWithoutActualGiving :
    PossiblyBeginsFiniteDuration mixedTemporal all posClock true ∧
    ConcurrentFiniteDurationCausalOpportunity mixedGivingFrame all posClock true ∧
    EuclideanAt mixedTemporal.ontic.frame true ∧
    ActualReflexive mixedTemporal.ontic true ∧
    PopulatedAt mixedTemporal all true (⟨1, one_pos⟩ : PosReal) ∧
    (∀ c t, ¬ mixedGivingFrame.GivesAt true c (some true) t) := by
  sorry


theorem necessaryOfUniversalMemberwiseGiving {W B T S : Type}
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (w v : W) (c : B)
    (hwv : f.history.ontic.frame.access w v)
    (hc : Concrete c) (he : f.history.ontic.ExistsAt v c)
    (hGiving : ConcurrentTotalityGivingAt f Concrete v c)
    (hNoSelf : NoSelfGivingOnAccessible f w)
    (hTemporal : ContingentConcretaTemporallyPresent f Concrete w) :
    NecessaryAt f.history.ontic v c := by
  sorry


theorem externalOpportunityOfMemberwiseGiving {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hOpportunity : NonexternalConcurrentGivingOpportunity f Concrete k w)
    (hNoSelf : NoSelfGivingOnAccessible f w)
    (hTemporal : ContingentConcretaTemporallyPresent f Concrete w) :
    ConcurrentFiniteDurationCausalOpportunity f Concrete k w := by
  sorry


end TruthCore.Results.Causality.MetricBeginningArrival
