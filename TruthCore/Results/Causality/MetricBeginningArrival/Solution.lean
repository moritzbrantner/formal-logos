module

public import TruthCore.Causality.MetricBeginningArrival
public import TruthCore.Results.Causality.MetricGrimReaper.Solution
public import TruthCore.Results.Causality.ActualEuclidean.Solution

@[expose] public section

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
  obtain ⟨v, hwv, t, hPop⟩ := hPopulated
  refine ⟨v, hwv, ⟨t, hPop⟩, ?_⟩
  rintro s ⟨x, hx, hCont, hxs⟩
  exact hFinite v hwv x s hx hCont hxs

/-- Strength order (linear time, any real clock): a possible BEGINS_1 beginning
is a possible BEGINS_2 beginning, since a past with a first moment has finite
duration. -/
theorem possiblyFiniteDurationOfFirstMoment {W B T : Type} [LinearOrder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hFirst : PossiblyBeginsFirstMoment h Concrete w) :
    PossiblyBeginsFiniteDuration h Concrete k w := by
  obtain ⟨v, hwv, hSome, hAll⟩ := hFirst
  exact ⟨v, hwv, hSome, fun t hPop =>
    TruthCore.Results.Causality.MetricGrimReaper.metricallyFiniteOfBegun k t (hAll t hPop)⟩

/-- A BEGINS_2 beginning of a history is a beginning of its metric Scenario. -/
theorem possiblyBeginsAtOfFiniteDuration {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (w : W)
    (hBegins : PossiblyBeginsFiniteDuration h Concrete k w) :
    PossiblyBeginsAt (finiteDurationScenario h Concrete k causes) w := by
  obtain ⟨v, hwv, hB⟩ := hBegins
  obtain ⟨⟨_, x, hx, hCont, _⟩, _⟩ := id hB
  exact ⟨v, hwv, hB, x, hx, hCont⟩

/-- The totality-cause relation does no logical work: causal opportunity for
any relation gives it for the relation that always holds. -/
theorem trivialCauseOpportunity {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (w : W)
    (hOpportunity : FiniteDurationCausalOpportunity h Concrete k causes w) :
    FiniteDurationCausalOpportunity h Concrete k (fun _ _ => True) w := by
  intro hBegins
  obtain ⟨v, hwv, hB, c, hc, he, _, hOutside⟩ := hOpportunity hBegins
  exact ⟨v, hwv, hB, c, hc, he, trivial, hOutside⟩

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
      ⟨h.ontic, Concrete, G⟩ w :=
  TruthCore.Results.Causality.ActualEuclidean.externalNecessaryConcrete
    (finiteDurationScenario h Concrete k causes) w hEuclidean hReflexive
    (possiblyBeginsAtOfFiniteDuration h Concrete k causes w hBegins) hOpportunity

/-- B1 and B2 in sense BEGINS_2 already give the possibility of a necessary
concrete individual, with no frame condition: the external cause in the
accessible history is necessary there. -/
theorem possiblyNecessaryOfFiniteDurationOpportunity {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (G : W → B → B → Prop) (w : W)
    (hBegins : PossiblyBeginsFiniteDuration h Concrete k w)
    (hOpportunity : FiniteDurationCausalOpportunity h Concrete k causes w) :
    TruthCore.Causality.ComingToBeHorns.PossiblyNecessaryConcrete h Concrete G w := by
  obtain ⟨v, hwv, _, c, hc, he, _, hOutside⟩ :=
    hOpportunity (possiblyBeginsAtOfFiniteDuration h Concrete k causes w hBegins)
  exact ⟨v, hwv, c, hc, he,
    TruthCore.Causality.LocalFramePossibleExternalCause.necessaryOfExternalCandidate
      (finiteDurationScenario h Concrete k causes) v c hc he hOutside⟩

open TruthCore.Causality.MetricBeginningArrival.Control
open TruthCore.Causality.MetricGrimReaper.Control (PosReal posClock intClock openBelow)
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot)
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Results.Causality.MetricGrimReaper (posFinite posNotBegun openBelowContingent
  unboundedOfSpaced)
open TruthCore.Results.Causality.GrimReaperPatchwork (pivotOne pivotPopulated)

/-- No integer moment has a past of finite duration on the identity clock. -/
theorem intNotFinite (t : Int) : ¬ MetricallyFinitePast intClock t := by
  intro hFin
  have hDesc : TruthCore.Causality.GrimReaperPatchwork.Descent
      (fun n : Nat => t - (n : Int)) := by
    intro n; push_cast; omega
  have hSlots : SlotsAtLeast intClock (fun n : Nat => t - (n : Int)) := by
    refine ⟨1, one_pos, fun n => ?_⟩
    show (1 : ℝ) ≤ ((t - (n : Int) : Int) : ℝ) - ((t - ((n + 1 : Nat) : Int) : Int) : ℝ)
    push_cast; linarith
  exact unboundedOfSpaced intClock _ hDesc hSlots (by simpa using hFin)

theorem openBelowSourceContingent (n : Int) :
    ContingentAt openBelowSource.ontic true (some n) :=
  ⟨rfl, false, trivial, Bool.false_ne_true⟩

/-- Independence, nonvacuity and sense controls. -/
theorem controls : Certificate := by
  refine ⟨⟨⟨1, trivial, 0, pivotPopulated⟩, ?_⟩,
    ⟨fun _ _ _ _ => trivial, trivial, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro ⟨v, _, ⟨t, hPop⟩, hAll⟩
    exact intNotFinite t (hAll t hPop)
  · exact ⟨true, trivial, ⟨⟨1, one_pos⟩, 0, trivial, openBelowContingent 0, rfl⟩,
      fun t _ => posFinite t⟩
  · rintro ⟨v, _, ⟨t, hPop⟩, hAll⟩
    exact posNotBegun t (hAll t hPop)
  · intro hOpp
    have hB : PossiblyBeginsFiniteDuration openBelow all posClock true :=
      ⟨true, trivial, ⟨⟨1, one_pos⟩, 0, trivial, openBelowContingent 0, rfl⟩,
        fun t _ => posFinite t⟩
    obtain ⟨_, _, _, _, _, _, hc, _⟩ :=
      hOpp (possiblyBeginsAtOfFiniteDuration _ _ _ _ _ hB)
    exact hc
  · rintro G v ⟨c, _, _, hn⟩
    have hFalse : openBelow.ontic.ExistsAt false c := hn false trivial
    exact Bool.false_ne_true hFalse
  · exact ⟨true, trivial, ⟨⟨1, one_pos⟩, some 0, trivial, openBelowSourceContingent 0, rfl⟩,
      fun t _ => posFinite t⟩
  · intro _
    have hPop : PopulatedAt openBelowSource all true (⟨1, one_pos⟩ : PosReal) :=
      ⟨some 0, trivial, openBelowSourceContingent 0, rfl⟩
    have hBegins : FiniteDurationBeginningAt openBelowSource all posClock true :=
      ⟨⟨_, hPop⟩, fun t _ => posFinite t⟩
    refine ⟨true, trivial, ⟨hBegins, some 0, trivial, openBelowSourceContingent 0⟩,
      none, trivial, trivial, ⟨rfl, rfl⟩, ?_⟩
    intro x _ hCont hEq
    subst hEq
    obtain ⟨_, _, _, hAbsent⟩ := hCont
    exact hAbsent trivial
  · intro _ _ _ _
    trivial
  · trivial
  · intro G
    exact ⟨none, trivial, trivial, fun _ _ => trivial⟩


/-- The stronger causal B2 really can yield a necessary concrete being that
ACTUALLY gives being to all contingent concreta in its accessible history.
The causal conjunct contributes to this stronger conclusion, while the
necessity of the bearer still follows from externality and modal semantics. -/
theorem possiblyNecessaryConcurrentGiver {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hBegins : PossiblyBeginsFiniteDuration f.history Concrete k w)
    (hOpportunity : ConcurrentFiniteDurationCausalOpportunity f Concrete k w) :
    ∃ v c, f.history.ontic.frame.access w v ∧ Concrete c ∧
      f.history.ontic.ExistsAt v c ∧ NecessaryAt f.history.ontic v c ∧
      ConcurrentTotalityGivingAt f Concrete v c := by
  obtain ⟨v, hv, _, c, hc, he, hGiving, hOutside⟩ :=
    hOpportunity
      (possiblyBeginsAtOfFiniteDuration f.history Concrete k
        (ConcurrentTotalityGivingAt f Concrete) w hBegins)
  have hNec : NecessaryAt f.history.ontic v c :=
    TruthCore.Causality.LocalFramePossibleExternalCause.necessaryOfExternalCandidate
      (finiteDurationScenario f.history Concrete k
        (ConcurrentTotalityGivingAt f Concrete)) v c hc he hOutside
  exact ⟨v, c, hv, hc, he, hNec, hGiving⟩

/-- With Euclidean accessibility and actual reflexivity, the SAME rigid source
is necessary at w and actually exercises its being-giving causal power in
a world possible from w. No giving of being at w is inferred. -/
theorem necessaryActualWithPossibleConcurrentGiving {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hEuclidean : EuclideanAt f.history.ontic.frame w)
    (hReflexive : ActualReflexive f.history.ontic w)
    (hBegins : PossiblyBeginsFiniteDuration f.history Concrete k w)
    (hOpportunity : ConcurrentFiniteDurationCausalOpportunity f Concrete k w) :
    ∃ c, Concrete c ∧ f.history.ontic.ExistsAt w c ∧
      NecessaryAt f.history.ontic w c ∧
      ∃ v, f.history.ontic.frame.access w v ∧
        ConcurrentTotalityGivingAt f Concrete v c := by
  obtain ⟨v, c, hv, hc, _, hNec, hGiving⟩ :=
    possiblyNecessaryConcurrentGiver f Concrete k w hBegins hOpportunity
  obtain ⟨heW, hNecW⟩ :=
    TruthCore.Causality.ActualEuclidean.necessaryAtOrigin
      f.history.ontic w v c hEuclidean hReflexive hv hNec
  exact ⟨c, hc, heW, hNecW, v, hv, hGiving⟩

/-- The existing metric Arrival B endpoint remains valid with the genuinely
causal B2, for any separate grounding relation G. This is a corollary of
the stronger conclusion, not a new proof from the empty totality label. -/
theorem necessaryConcreteOfConcurrentGiving {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T)
    (G : W → B → B → Prop) (w : W)
    (hEuclidean : EuclideanAt f.history.ontic.frame w)
    (hReflexive : ActualReflexive f.history.ontic w)
    (hBegins : PossiblyBeginsFiniteDuration f.history Concrete k w)
    (hOpportunity : ConcurrentFiniteDurationCausalOpportunity f Concrete k w) :
    TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt
      ⟨f.history.ontic, Concrete, G⟩ w := by
  obtain ⟨c, hc, he, hn, _, _, _⟩ :=
    necessaryActualWithPossibleConcurrentGiving
      f Concrete k w hEuclidean hReflexive hBegins hOpportunity
  exact ⟨c, hc, he, hn⟩

/-- Existing externally labelled B2 can hold although the shared actual
being-giving relation is everywhere empty. The old source example has no
causation of being, even though its schematic cause predicate names none. -/
theorem inertGivingSeparatesOpportunity :
    FiniteDurationCausalOpportunity openBelowSource all posClock
      (fun v c => v = true ∧ c = none) true ∧
    ¬ ConcurrentFiniteDurationCausalOpportunity inertGivingFrame all posClock true := by
  constructor
  · exact controls.2.2.2.1
  · intro hStrong
    have hBegins : PossiblyBeginsFiniteDuration openBelowSource all posClock true :=
      controls.2.2.1
    obtain ⟨v, _, _, c, _, _, hGiving, _⟩ :=
      hStrong (possiblyBeginsAtOfFiniteDuration openBelowSource all posClock
        (ConcurrentTotalityGivingAt inertGivingFrame all) true hBegins)
    obtain ⟨x, t, _, _, _, hg⟩ := hGiving.1
    exact hg

/-- The original positive openBelowSource history can also support the
stronger concurrent reading when its causal field is genuinely populated. -/
theorem functioningGivingAtTrue :
    ConcurrentTotalityGivingAt functioningGivingFrame all true none := by
  constructor
  · exact ⟨some 0, (⟨1, one_pos⟩ : PosReal), trivial,
      openBelowSourceContingent 0, rfl, ⟨rfl, rfl, 0, rfl⟩⟩
  · intro x _ _ hCont _
    cases x with
    | none =>
      obtain ⟨_, v, _, hAbsent⟩ := hCont
      exact (hAbsent trivial).elim
    | some n =>
      exact ⟨rfl, rfl, n, rfl⟩

theorem functioningConcurrentOpportunity :
    ConcurrentFiniteDurationCausalOpportunity functioningGivingFrame all posClock true := by
  intro _
  have hPop : PopulatedAt openBelowSource all true (⟨1, one_pos⟩ : PosReal) :=
    ⟨some 0, trivial, openBelowSourceContingent 0, rfl⟩
  have hBegin : FiniteDurationBeginningAt openBelowSource all posClock true :=
    ⟨⟨_, hPop⟩, fun t _ => posFinite t⟩
  refine ⟨true, trivial,
    ⟨hBegin, some 0, trivial, openBelowSourceContingent 0⟩,
    none, trivial, trivial, functioningGivingAtTrue, ?_⟩
  intro x _ hCont hEq
  subst x
  obtain ⟨_, _, _, hAbsent⟩ := hCont
  exact hAbsent trivial

/-- A model with actual contingent population at true and complete concurrent
being-giving at the alternative world false. The strong B2 is satisfied at
true, but no being-giving at all is exercised at true. This is a semantic
countermodel to transferring possible causal efficacy to actual causal
efficacy, not a metaphysical counterexample to the B2 principle itself. -/
theorem mixedGivingAtFalse :
    ConcurrentTotalityGivingAt mixedGivingFrame all false none := by
  constructor
  · exact ⟨some false, (⟨1, one_pos⟩ : PosReal), trivial,
      TruthCore.Causality.PossibleCauseOfContingency.mixedContingentAtFalse,
      rfl, ⟨rfl, rfl, rfl⟩⟩
  · intro x _ _ _ hAt
    cases x with
    | none =>
      exact hAt.elim
    | some b =>
      cases b with
      | false => exact ⟨rfl, rfl, rfl⟩
      | true => exact (Bool.false_ne_true hAt).elim

theorem mixedConcurrentOpportunity :
    ConcurrentFiniteDurationCausalOpportunity mixedGivingFrame all posClock true := by
  intro _
  have hPop : PopulatedAt mixedTemporal all false (⟨1, one_pos⟩ : PosReal) :=
    ⟨some false, trivial,
      TruthCore.Causality.PossibleCauseOfContingency.mixedContingentAtFalse, rfl⟩
  have hBegin : FiniteDurationBeginningAt mixedTemporal all posClock false :=
    ⟨⟨_, hPop⟩, fun t _ => posFinite t⟩
  refine ⟨false, trivial,
    ⟨hBegin, some false, trivial,
      TruthCore.Causality.PossibleCauseOfContingency.mixedContingentAtFalse⟩,
    none, trivial, trivial, mixedGivingAtFalse, ?_⟩
  intro x _ hCont hEq
  subst x
  obtain ⟨_, _, _, hAbsent⟩ := hCont
  exact hAbsent trivial

theorem mixedPossibleGivingWithoutActualGiving :
    PossiblyBeginsFiniteDuration mixedTemporal all posClock true ∧
    ConcurrentFiniteDurationCausalOpportunity mixedGivingFrame all posClock true ∧
    EuclideanAt mixedTemporal.ontic.frame true ∧
    ActualReflexive mixedTemporal.ontic true ∧
    PopulatedAt mixedTemporal all true (⟨1, one_pos⟩ : PosReal) ∧
    (∀ c t, ¬ mixedGivingFrame.GivesAt true c (some true) t) := by
  have hPop : PopulatedAt mixedTemporal all true (⟨1, one_pos⟩ : PosReal) :=
    ⟨some true, trivial,
      TruthCore.Causality.PossibleCauseOfContingency.mixedContingentAtTrue, rfl⟩
  refine ⟨?_, mixedConcurrentOpportunity, ?_, ?_, hPop, ?_⟩
  · exact ⟨true, trivial, ⟨⟨_, hPop⟩, fun t _ => posFinite t⟩⟩
  · intro v z _ _
    trivial
  · trivial
  · intro c t hg
    exact (by decide : (true : Bool) ≠ false) hg.1

end TruthCore.Results.Causality.MetricBeginningArrival
