module

public import TruthCore.Causality.MetricGrimReaper
public import TruthCore.Causality.PossibleCauseOfContingency
public import TruthCore.Causality.ActualEuclidean
public import TruthCore.Causality.ComingToBeHorns
public import TruthCore.Causality.Frame

/-!
# Two senses of "contingent concrete reality begins", and Arrival B in the metric one

Analyst formulation for the modal spine to "God exists"
(`docs/notes/modal-spine.md`, Arrival B, premise B1). Attribution deferred.

**What B1 says now.** The existing premise B1
(`PossibleCauseOfContingency.PossiblyBeginsAt`) is stated for a `Scenario`
whose field `beginsContingency : World → Prop` is an *uninterpreted parameter*:
the Scenario has no times, and "begins" is whatever predicate is supplied.
`LocalFramePossibleExternalCause.necessaryConcrete` and
`ActualEuclidean.externalNecessaryConcrete` hold for every such predicate,
including the constant `True` (the existing controls use it). So B1 as typed
fixes no sense of beginning, and the arrival's validity does not depend on one;
the content of B1 and of the causal-opportunity premise B2 depends on the
predicate supplied.

**Two typed senses (disambiguation BEGINS).** Both constrain the *time* before
the populated moments of a history, not contingent reality itself. History `v`
has a populated moment (some contingent concrete individual present) and

* BEGINS_1 (`FirstMomentBeginningAt`): the time before every populated moment
  of `v` has a first moment (`BegunComingToBe.BegunAt`); or
* BEGINS_2 (`FiniteDurationBeginningAt`): the time before every populated
  moment of `v` is of finite duration on the supplied clock
  (`MetricGrimReaper.MetricallyFinitePast`); the intended clock is CLOCK_1.
  With a bounded clock every past is finite and BEGINS_2 reduces to population.

Examples. Discrete or continuous time with a first moment satisfies both. A
populated history whose time is open below and of finite duration (the order
and metric shape of standard FLRW cosmic time: the initial singularity is not a
moment) satisfies BEGINS_2 and not BEGINS_1 (`Control.Certificate` 2). An
endless succession of populated days satisfies neither (`Control.Certificate`
1). Non-examples showing that these are senses about time, not about the
beginning of contingent reality: integer time, empty before `0` and populated
from `0` on, satisfies neither, although contingent reality began a finite time
ago; non-negative real time, empty at `0` and populated after it, satisfies
BEGINS_1 although there is no first populated moment. A third sense, a first
populated moment after emptiness (related to premise A3 of Arrival A), is not
formalized here. In linear time BEGINS_1 gives BEGINS_2
(`possiblyFiniteDurationOfFirstMoment`). Neither is the individual coming-to-be
of `TemporalHistory.BeginsAt`, nor an empty first state.

**The metric Scenario.** `finiteDurationScenario` instantiates the Scenario's
beginning predicate with BEGINS_2 and leaves its totality-cause relation a
parameter. B1 in sense BEGINS_2 (`PossiblyBeginsFiniteDuration`) and B2 in
sense BEGINS_2 (`FiniteDurationCausalOpportunity`) are separate statements from
the parameter-sense B1 and B2, so the senses cannot be exchanged silently.
Because the cause relation is unconstrained, B2 for any relation gives B2 for
the relation that always holds (`trivialCauseOpportunity` in the results),
and the arrival needs only the latter: the content B2 contributes is that,
given B1, possibly a BEGINS_2 history contains an existing concrete individual
outside the contingent totality. The cause conjunct does no logical work.

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.MetricBeginningArrival

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.BegunComingToBe (BegunAt)
open TruthCore.Causality.GrimReaperPatchwork (PopulatedAt)
open TruthCore.Causality.MetricGrimReaper
open TruthCore.Causality.PossibleCauseOfContingency

/-- BEGINS_1: in history `v` some contingent concrete individual is present at
some moment, and the time before every moment at which one is present has a
first moment. A constraint on time, not on when contingent reality began. -/
def FirstMomentBeginningAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W) : Prop :=
  (∃ t, PopulatedAt h Concrete v t) ∧ ∀ t, PopulatedAt h Concrete v t → BegunAt t

/-- BEGINS_2: in history `v` some contingent concrete individual is present at
some moment, and the time before every moment at which one is present is of
finite duration on the clock `k`. A constraint on time, not on when contingent
reality began. -/
def FiniteDurationBeginningAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (v : W) : Prop :=
  (∃ t, PopulatedAt h Concrete v t) ∧
    ∀ t, PopulatedAt h Concrete v t → MetricallyFinitePast k t

/-- B1 in sense BEGINS_1: possibly, a populated history in which the time
before every populated moment has a first moment. -/
def PossiblyBeginsFirstMoment {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ FirstMomentBeginningAt h Concrete v

/-- B1 in sense BEGINS_2: possibly, a populated history in which the time
before every populated moment is of finite duration on the clock `k`. -/
def PossiblyBeginsFiniteDuration {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ FiniteDurationBeginningAt h Concrete k v

/-- Possibly, some contingent concrete individual is present at some moment:
some history accessible from `w` is populated. No beginning, duration or
cause is mentioned. -/
def PossiblyPopulated {W B T : Type} (h : History W B T) (Concrete : B → Prop)
    (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ ∃ t, PopulatedAt h Concrete v t

/-- The Scenario of `PossibleCauseOfContingency` over a history, with the
beginning predicate instantiated by BEGINS_2 and a supplied totality-cause
relation. Ontic, concreteness and the cause relation are those supplied. -/
def finiteDurationScenario {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (causes : W → B → Prop) : Scenario W B where
  ontic := h.ontic
  concrete := Concrete
  beginsContingency := FiniteDurationBeginningAt h Concrete k
  causesContingencyTotality := causes

/-- B2 in sense BEGINS_2: if some accessible history is a BEGINS_2 history with
a contingent concrete individual, then some accessible history is one in which,
moreover, some existing concrete individual, distinct from every contingent
concrete individual there, stands in the supplied totality-cause relation. The
relation is an unconstrained parameter: nothing makes it causal. -/
def FiniteDurationCausalOpportunity {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (causes : W → B → Prop) (w : W) : Prop :=
  CausalOpportunityAt (finiteDurationScenario h Concrete k causes) w


/-- An explicitly causal, strong reading of "a source of the totality":
the same concrete candidate actually exercises the shared CausalityFrame.GivesAt
relation for the being of every contingent concrete individual at every moment
of its presence in v. At least one exercise on a populated effect is required,
so the relation cannot be vacuous. GivesAt is the existing primitive of
concurrent being-giving, not a synonym for logical implication, temporally
prior efficient causation, Ontic.Causes, or a bare totality label.

This reading is sufficient for treating the source as an actual provider of
the contingent members' being. It is STRONGER than causation of the contingent
whole taken collectively: a cause of a totality need not directly cause every
member. Source existence and externality are separate conditions imposed by
the causal opportunity premise below; this definition does not prove them. -/
def ConcurrentTotalityGivingAt {W B T S : Type}
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (v : W) (c : B) : Prop :=
  (∃ x t, Concrete x ∧ ContingentAt f.history.ontic v x ∧
    f.history.IsAt v x t ∧ f.GivesAt v c x t) ∧
  (∀ x t, Concrete x → ContingentAt f.history.ontic v x →
    f.history.IsAt v x t → f.GivesAt v c x t)

/-- B2 in BEGINS_2 under the strong concurrent-being-giving interpretation:
if a finite-duration populated history is possible, then there is an accessible
finite-duration populated history with an EXISTING concrete source outside all
contingent concrete individuals that actually gives being to all its
contingent concrete members whenever they are present.

This B2 is still an OPEN substantive modal causal-availability premise. It
contains the possibility of a necessary external bearer via externality;
the causal content is additional rather than a proof of that availability. -/
def ConcurrentFiniteDurationCausalOpportunity {W B T S : Type} [Preorder T]
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (k : TimeClock T) (w : W) : Prop :=
  FiniteDurationCausalOpportunity f.history Concrete k
    (ConcurrentTotalityGivingAt f Concrete) w



/-- At the selected world, the SAME rigid concrete individual exists necessarily
and is the actual concurrent giver of all contingent beings in SOME accessible
history. It does NOT assert giving of being in the selected actual history.
This is strictly richer semantic content than the stage-one necessary-concrete
conclusion; an ordinary necessary bearer may have no giving relation anywhere. -/
def NecessaryConcreteWithPossibleConcurrentGivingAt {W B T S : Type}
    (f : TruthCore.Causality.Frame.CausalityFrame W B T S)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∃ c, Concrete c ∧ f.history.ontic.ExistsAt w c ∧
    NecessaryAt f.history.ontic w c ∧
    ∃ v, f.history.ontic.frame.access w v ∧
      ConcurrentTotalityGivingAt f Concrete v c

namespace Control

open TruthCore.Causality.MetricGrimReaper.Control (PosReal posClock intClock openBelow)
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot)
open TruthCore.Causality.InertEmptiness.Control (all)

/-- `openBelow` with one more individual, `none`, existing at both worlds and
present at no moment; individual `some n` exists and is present at every
moment exactly at world `true`. Times are the positive reals. -/
def openBelowSource : History Bool (Option Int) PosReal where
  ontic := { frame := TruthCore.Causality.InertEmptiness.Control.universal,
             ExistsAt := fun w x => match x with
               | none => True
               | some _ => w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w x _ => match x with
    | none => False
    | some _ => w = true
  now := ⟨1, one_pos⟩


/-- A source outside the contingent inventory can exist without exercising
any causal giving-of-being relation. This extends the already verified
openBelowSource model with the family's shared causal primitives. -/
def inertGivingFrame :
    TruthCore.Causality.Frame.CausalityFrame Bool (Option Int) PosReal Unit where
  history := openBelowSource
  GivesAt := fun _ _ _ _ => False
  CausesIn := fun _ _ _ => False
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := ()

/-- The same ontic/temporal history with actual concurrent being-giving at the
populated world. Source none exists necessarily but need not occupy a moment;
every contingent some n is temporally present and receives its being from it.
This is a STRUCTURAL satisfaction test, not a metaphysical existence witness. -/
def functioningGivingFrame :
    TruthCore.Causality.Frame.CausalityFrame Bool (Option Int) PosReal Unit :=
  { inertGivingFrame with
    GivesAt := fun v c x _ => v = true ∧ c = none ∧ ∃ n : Int, x = some n }

/-- Both worlds have contingent concrete individuals, but the same rigid none
candidate gives being only in world false. A real possibility of totality
giving at false does not make it exercised at the designated world true. -/
def mixedTemporal : History Bool (Option Bool) PosReal where
  ontic := TruthCore.Causality.PossibleCauseOfContingency.mixed.ontic
  IsAt := fun v x _ => match x with
    | none => False
    | some b => v = b
  now := ⟨1, one_pos⟩

def mixedGivingFrame :
    TruthCore.Causality.Frame.CausalityFrame Bool (Option Bool) PosReal Unit where
  history := mixedTemporal
  GivesAt := fun v c x _ => v = false ∧ c = none ∧ x = some false
  CausesIn := fun _ _ _ => False
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := ()

/-- Every individual counts as concrete:
(1) in the beginningless integer history `pivot` (identity clock) contingent
concrete things are possibly present, and no accessible history begins in
sense BEGINS_2;
(2) in `openBelow` (positive real times, identity clock): Euclidean access and
reflexivity at `true` hold, B1 holds in sense BEGINS_2 and fails in sense
BEGINS_1, the causal opportunity premise in sense BEGINS_2 fails for the empty
totality-cause relation, and for every grounding relation no concrete
individual is necessary at either world;
(3) in `openBelowSource`, with `none` the totality cause at world `true`, B1
and B2 in sense BEGINS_2, Euclidean access and reflexivity at `true` all hold,
together with a necessary concrete individual at `true`. -/
def Certificate : Prop :=
  (PossiblyPopulated pivot all 1 ∧ ¬ PossiblyBeginsFiniteDuration pivot all intClock 1) ∧
  (ActualEuclidean.EuclideanAt openBelow.ontic.frame true ∧
    NecessarilyUnderived.ActualReflexive openBelow.ontic true ∧
    PossiblyBeginsFiniteDuration openBelow all posClock true ∧
    ¬ PossiblyBeginsFirstMoment openBelow all true ∧
    ¬ FiniteDurationCausalOpportunity openBelow all posClock (fun _ _ => False) true ∧
    (∀ G v, ¬ BruteFoundationBoundary.NecessaryConcreteAt ⟨openBelow.ontic, all, G⟩ v)) ∧
  (PossiblyBeginsFiniteDuration openBelowSource all posClock true ∧
    FiniteDurationCausalOpportunity openBelowSource all posClock
      (fun w c => w = true ∧ c = none) true ∧
    ActualEuclidean.EuclideanAt openBelowSource.ontic.frame true ∧
    NecessarilyUnderived.ActualReflexive openBelowSource.ontic true ∧
    ∀ G, BruteFoundationBoundary.NecessaryConcreteAt ⟨openBelowSource.ontic, all, G⟩ true)

end Control

end TruthCore.Causality.MetricBeginningArrival
