module

public import TruthCore.Causality.MetricBeginningArrival
public import TruthCore.Results.Causality.MetricGrimReaper.Solution
public import TruthCore.Results.Causality.ActualEuclidean.Solution
public import TruthCore.Causality.FrameAdapters

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
    NecessaryConcreteWithPossibleConcurrentGivingAt f Concrete w := by
  obtain ⟨v, c, hv, hc, _, hNec, hGiving⟩ :=
    possiblyNecessaryConcurrentGiver f Concrete k w hBegins hOpportunity
  obtain ⟨heW, hNecW⟩ :=
    TruthCore.Causality.ActualEuclidean.necessaryAtOrigin
      f.history.ontic w v c hEuclidean hReflexive hv hNec
  exact ⟨c, hc, heW, hNecW, v, hv, hGiving⟩


/-- Project the SAME necessarily existing concrete causal candidate to the
original stage-one necessary-concrete node. This intentionally forgets the
possible-world causal exercise but not the witness's rigid identity; it is a
weaker logical conclusion, not a new independent reason for the premise. -/
theorem necessaryConcreteOfPossibleConcurrentGiver {W B T S : Type}
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hGiver : NecessaryConcreteWithPossibleConcurrentGivingAt f Concrete w) :
    TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt
      ⟨f.history.ontic, Concrete, G⟩ w := by
  obtain ⟨c, hc, he, hNecessary, _⟩ := hGiver
  exact ⟨c, hc, he, hNecessary⟩

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


/-- A source that actually gives being to EVERY contingent concrete member of
an accessible history cannot itself be contingent, if contingent concreta
occur at some time and strict giving-of-being is irreflexive. No exteriority
or necessary-existence condition is assumed of c in this theorem. -/
theorem necessaryOfUniversalMemberwiseGiving {W B T S : Type}
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (w v : W) (c : B)
    (hwv : f.history.ontic.frame.access w v)
    (hc : Concrete c) (he : f.history.ontic.ExistsAt v c)
    (hGiving : ConcurrentTotalityGivingAt f Concrete v c)
    (hNoSelf : NoSelfGivingOnAccessible f w)
    (hTemporal : ContingentConcretaTemporallyPresent f Concrete w) :
    NecessaryAt f.history.ontic v c := by
  classical
  intro u hvu
  by_contra hAbsent
  have hCont : ContingentAt f.history.ontic v c :=
    ⟨he, ⟨u, hvu, hAbsent⟩⟩
  obtain ⟨t, hct⟩ := hTemporal v hwv c hc hCont
  have hSelf : f.GivesAt v c c t := hGiving.2 c t hc hCont hct
  exact hNoSelf v hwv c t hSelf

/-- A non-externality-stipulating causal opportunity, no-self-giving, and
temporal presence of contingent concreta yield the registered B2 that
explicitly demands an external source. Exteriority is derived from the
universal scope of the giving clause over a possibly contingent source, plus
no-self-giving and temporal presence; it is not stated in the antecedent. The
commitment to a possibly necessary concretum is not thereby removed: it sits in
that universal clause, and under the two principles the antecedent and the
conclusion are equivalent (`nonexternalIffExternalOpportunity` below). The
bridge is conditional on memberwise concurrent esse-giving, not a holistic or
merely temporally prior notion of causation. -/
theorem externalOpportunityOfMemberwiseGiving {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hOpportunity : NonexternalConcurrentGivingOpportunity f Concrete k w)
    (hNoSelf : NoSelfGivingOnAccessible f w)
    (hTemporal : ContingentConcretaTemporallyPresent f Concrete w) :
    ConcurrentFiniteDurationCausalOpportunity f Concrete k w := by
  intro hBegins
  obtain ⟨v, hv, hB, c, hc, he, hGiving⟩ := hOpportunity hBegins
  have hn : NecessaryAt f.history.ontic v c :=
    necessaryOfUniversalMemberwiseGiving
      f Concrete w v c hv hc he hGiving hNoSelf hTemporal
  refine ⟨v, hv, hB, c, hc, he, hGiving, ?_⟩
  intro x _ hCont hEq
  subst x
  obtain ⟨_, u, hu, hAbsent⟩ := hCont
  exact hAbsent (hn u hu)

/-- Converse, with no further premise: the external B2 gives the nonexternal
one by forgetting the exteriority conjunct of the same witness. -/
theorem nonexternalOpportunityOfExternal {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hOpportunity : ConcurrentFiniteDurationCausalOpportunity f Concrete k w) :
    NonexternalConcurrentGivingOpportunity f Concrete k w := by
  intro hBegins
  obtain ⟨v, hv, hB, c, hc, he, hGiving, _⟩ := hOpportunity hBegins
  exact ⟨v, hv, hB, c, hc, he, hGiving⟩

/-- Under no-self-giving and temporal presence of contingent concreta, the
nonexternal and the external causal opportunity premises are equivalent. So a
rival who denies that a necessary concretum is possible, while keeping both
principles, rejects the nonexternal premise exactly as the external one: the
derivation relocates the modal commitment into the universal giving clause, it
does not remove it. -/
theorem nonexternalIffExternalOpportunity {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hNoSelf : NoSelfGivingOnAccessible f w)
    (hTemporal : ContingentConcretaTemporallyPresent f Concrete w) :
    NonexternalConcurrentGivingOpportunity f Concrete k w ↔
      ConcurrentFiniteDurationCausalOpportunity f Concrete k w :=
  ⟨fun h => externalOpportunityOfMemberwiseGiving f Concrete k w h hNoSelf hTemporal,
    nonexternalOpportunityOfExternal f Concrete k w⟩

/-- The universal clause of memberwise giving is CAUSE_OF_BEING_2
(`SustainsBeing`, disambiguation 88a8fba7) over the frame's being-giving,
restricted to the contingent concrete individuals present at some moment. -/
theorem concurrentTotalityGiving_iff_sustains {W B T S : Type}
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (v : W) (c : B) :
    ConcurrentTotalityGivingAt f Concrete v c ↔
      (∃ x t, Concrete x ∧ ContingentAt f.history.ontic v x ∧
        f.history.IsAt v x t ∧ f.GivesAt v c x t) ∧
      ∀ x, Concrete x → ContingentAt f.history.ontic v x →
        (∃ t, f.history.IsAt v x t) →
          TruthCore.Causality.SustainingCausation.SustainsBeing f.history
            (TruthCore.Causality.FrameAdapters.giving f) v c x := by
  constructor
  · rintro ⟨hSome, hAll⟩
    exact ⟨hSome, fun x hc hx hPresent =>
      ⟨hPresent, fun t ht => hAll x t hc hx ht⟩⟩
  · rintro ⟨hSome, hAll⟩
    exact ⟨hSome, fun x t hc hx ht => (hAll x hc hx ⟨t, ht⟩).2 t ht⟩

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


/-- On the same open-below finite-duration populated history, every candidate
is concrete, contingent and temporally present. A self-giving universal source
satisfies non-external causal opportunity, but the strong external opportunity
fails because there is no necessary candidate. This omits no-self-giving while
retaining the new temporal-presence bridge. Pure structural model. -/
theorem selfGivingSeparatesNoSelf :
    NonexternalConcurrentGivingOpportunity selfGivingFrame all posClock true ∧
    ContingentConcretaTemporallyPresent selfGivingFrame all true ∧
    ¬ NoSelfGivingOnAccessible selfGivingFrame true ∧
    ¬ ConcurrentFiniteDurationCausalOpportunity selfGivingFrame all posClock true := by
  have hPop : PopulatedAt openBelow all true (⟨1, one_pos⟩ : PosReal) :=
    ⟨0, trivial, openBelowContingent 0, rfl⟩
  have hBegin : FiniteDurationBeginningAt openBelow all posClock true :=
    ⟨⟨_, hPop⟩, fun t _ => posFinite t⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _
    refine ⟨true, trivial, ⟨hBegin, 0, trivial, openBelowContingent 0⟩,
      0, trivial, rfl, ?_⟩
    constructor
    · exact ⟨0, (⟨1, one_pos⟩ : PosReal), trivial,
        openBelowContingent 0, rfl, rfl⟩
    · intro _ _ _ _ _
      rfl
  · intro v _ x _ hCont
    exact ⟨(⟨1, one_pos⟩ : PosReal), hCont.1⟩
  · intro hNoSelf
    exact hNoSelf true trivial 0 (⟨1, one_pos⟩ : PosReal) rfl
  · intro hStrong
    have hB : PossiblyBeginsFiniteDuration openBelow all posClock true :=
      ⟨true, trivial, hBegin⟩
    obtain ⟨v, _, _, c, _, he, _, hOutside⟩ :=
      hStrong (possiblyBeginsAtOfFiniteDuration openBelow all posClock
        (ConcurrentTotalityGivingAt selfGivingFrame all) true hB)
    have hv : v = true := he
    subst v
    exact hOutside c trivial (openBelowContingent c) rfl

theorem unmanifestSourceContingent (x : Bool) :
    ContingentAt unmanifestSourceHistory.ontic true x :=
  ⟨rfl, false, trivial, Bool.false_ne_true⟩

/-- In a Boolean-roster model, strict no-self-giving can hold and an
unmanifested contingent source can give being to every actually present
contingent effect. Without the temporal-presence condition, the stronger
external-source B2 fails. This is a structural reading separation, not evidence
that contingent timeless concreta are metaphysically available. -/
theorem unmanifestSourceSeparatesTemporal :
    NonexternalConcurrentGivingOpportunity unmanifestSourceFrame all posClock true ∧
    NoSelfGivingOnAccessible unmanifestSourceFrame true ∧
    ¬ ContingentConcretaTemporallyPresent unmanifestSourceFrame all true ∧
    ¬ ConcurrentFiniteDurationCausalOpportunity
      unmanifestSourceFrame all posClock true := by
  have hPop : PopulatedAt unmanifestSourceHistory all true
      (⟨1, one_pos⟩ : PosReal) :=
    ⟨true, trivial, unmanifestSourceContingent true, ⟨rfl, rfl⟩⟩
  have hBegin : FiniteDurationBeginningAt unmanifestSourceHistory all posClock true :=
    ⟨⟨_, hPop⟩, fun t _ => posFinite t⟩
  have hGiving : ConcurrentTotalityGivingAt unmanifestSourceFrame all true false := by
    constructor
    · exact ⟨true, (⟨1, one_pos⟩ : PosReal), trivial,
        unmanifestSourceContingent true, ⟨rfl, rfl⟩,
        ⟨rfl, rfl, rfl⟩⟩
    · intro x _ _ _ hAt
      exact ⟨hAt.1, rfl, hAt.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _
    exact ⟨true, trivial, ⟨hBegin, true, trivial, unmanifestSourceContingent true⟩,
      false, trivial, rfl, hGiving⟩
  · intro v _ c t hSelf
    have h : v = true ∧ c = false ∧ c = true := hSelf
    exact Bool.false_ne_true (h.2.1.symm.trans h.2.2)
  · intro hTemporal
    obtain ⟨t, hAt⟩ :=
      hTemporal true trivial false trivial (unmanifestSourceContingent false)
    exact Bool.false_ne_true hAt.2
  · intro hStrong
    have hB : PossiblyBeginsFiniteDuration unmanifestSourceHistory all posClock true :=
      ⟨true, trivial, hBegin⟩
    obtain ⟨v, _, _, c, _, he, _, hOutside⟩ :=
      hStrong (possiblyBeginsAtOfFiniteDuration unmanifestSourceHistory all posClock
        (ConcurrentTotalityGivingAt unmanifestSourceFrame all) true hB)
    have hv : v = true := he
    subst v
    exact hOutside c trivial (unmanifestSourceContingent c) rfl


end TruthCore.Results.Causality.MetricBeginningArrival
