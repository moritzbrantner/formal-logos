module

public import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
public import TruthCore.Causality.TermSenseForks2

/-!
# The totality of received actual being and its cause (#1724, C1)

Analyst formulation, attribution deferred. This module asks whether the
closed-collection foundation premise `ClosedActualEsseCollectionsRooted`
(CCR, statement 20babef7) follows from commitments about the cause of a
*totality* of received being, instead of being taken as a bare primitive.

All relations stay on one fixed q.3 a.4 profile `p` and its existing
`ActualEsseCause` (distinct, both actual as to esse, `CausesIn … esse`,
tenseless and mode-unspecified). Nothing here is efficient, presently
sustaining, world-indexed or modal.

`TotalityCause` is an explicit PRIMITIVE predicate parameter: `TotalityCause e`
reads, in its intended collective sense (TOTALITY_CAUSE_1), "e is a cause of
the esse of the totality of received actual bearers, taken together". It is
constrained only by the two premises below. Its meaning and examples are in the
linked definition and in `docs/notes/unique-feedback-explanation-311.md`
(C1 section). The distributive sense (TOTALITY_CAUSE_2,
`DistributiveTotalityCause`: e causes some received member) is a different
predicate; under it premise A is classically trivial and premise B is the whole claim
(control 2).

Because the parameter is constrained only by A and B, some predicate satisfies
both exactly when, if anything is received, one actual bearer is a cause of
every received bearer's esse (`jointIffCommonCause` in the Solution). The
substantive content therefore lies in A and B jointly, whichever premise a
reading of `TotalityCause` makes carry it. With no self-causation of esse this
yields a single uncaused cause of every received bearer, which is strictly
stronger than CCR (controls 6 and 7).

A plural non-circularity principle restricted to *closed* collections ("no
nonempty closed collection with no uncaused member jointly causes its own
esse", with "jointly causes" read distributively) says that no such collection
is nonempty, which is CCR itself; it is a re-presentation and adds no
independent evidence. This is recorded in the note, not formalized here.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.AggregateEsseCause

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing)

variable {B P R : Type}

/-- x is in act as to esse and is not uncaused in the fixed actual esse-cause
relation: it is not the case that no actual bearer is a distinct cause of its
esse. Under excluded middle this is "x has an actual distinct cause of its
esse" (received esse); the double-negative form keeps every derivation below
free of classical axioms. -/
def ReceivedActual (p : Profile B P R) (x : B) : Prop :=
  p.InAct x p.esse ∧ ¬ ∀ c, ¬ ActualEsseCause p c x

/-- OPEN analyst premise A (collective reception of the totality), attribution
deferred: if some actual bearer has received esse, then some actual bearer is a
cause of the esse of the totality of received actual bearers taken together
(`TotalityCause`, an explicit primitive). The totality is the collection of ALL
received actual bearers, not only a closed one, and it may be infinite. No
claim is made that the cause is outside the totality: that follows only with
premise B and no self-causation. Principal rival: the Hume–Edwards view that a
totality whose every member has a cause needs no cause of its own. -/
def ReceivedTotalityHasAggregateCause (p : Profile B P R)
    (TotalityCause : B → Prop) : Prop :=
  (∃ x, ReceivedActual p x) → ∃ e, p.InAct e p.esse ∧ TotalityCause e

/-- OPEN analyst premise B (whole to members), attribution deferred: whatever
causes the esse of the received totality is a cause, in the same esse respect,
of the esse of each received actual bearer (`CausesIn`, mode unspecified, so
not necessarily immediate or efficient). The analogue for the spacetime whole is
`NaturalismConsequences.CausingWholeCausesParts` (#1109) in a different
vocabulary; no identification of the two is made. Principal rival: a causal
loop or holistic whole whose cause of the totality is one of its own members
and does not cause itself. -/
def TotalityCauseCausesEachReceived (p : Profile B P R)
    (TotalityCause : B → Prop) : Prop :=
  ∀ e, TotalityCause e → ∀ m, ReceivedActual p m → p.CausesIn e m p.esse

/-- If any actual bearer has received esse, one actual bearer with no actual
cause of its esse is a distinct actual cause of the esse of every received
actual bearer. Not asserted: that it is the only uncaused bearer, that its esse
is its essence, that its causing is immediate, efficient or present, or that it
is necessary. Strictly stronger than CCR (controls 6 and 7). It neither
implies nor is implied by the finite-path common source
`CommonEsseIsEssenceSource`: it is vacuous when nothing is received and says
nothing of esse-essence identity, and control 6 satisfies that source without
it on the given edges. -/
def CommonUncausedCauseOfReceived (p : Profile B P R) : Prop :=
  (∃ x, ReceivedActual p x) →
    ∃ e, p.InAct e p.esse ∧ (∀ c, ¬ ActualEsseCause p c e) ∧
      ∀ m, ReceivedActual p m → ActualEsseCause p e m

/-- TOTALITY_CAUSE_2, the distributive sense: e is a distinct actual cause of
the esse of some received actual bearer. Every member-cause of a totality is a
cause of it in this sense. It is a defined predicate, not the primitive
collective `TotalityCause` of premise A. -/
def DistributiveTotalityCause (p : Profile B P R) (e : B) : Prop :=
  ∃ m, ReceivedActual p m ∧ ActualEsseCause p e m

/-! ## Exact interpretations (controls), not metaphysical models -/

/-- Hume–Edwards regress: every natural number is an actual bearer whose esse
is caused by its successor; no bearer has esse equal to essence. -/
def regressProfile : Profile Nat Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => c = x + 1
  essenceOf := fun _ => false
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- Every bearer causes every bearer's esse, itself included. -/
def selfCauserProfile : Profile Bool Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun _ _ _ => True
  essenceOf := fun _ => false
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- `none` directly causes every `some n`, and `some (n+1)` causes `some n`:
a root-backed infinite descending chain. -/
def commonRootEdge (c x : Option Nat) : Prop :=
  (c = none ∧ x ≠ none) ∨ ∃ n, c = some (n + 1) ∧ x = some n

/-- An idle actual `none` beside the rootless chain `some (n+1) → some n`. -/
def idleRootEdge (c x : Option Nat) : Prop :=
  ∃ n, c = some (n + 1) ∧ x = some n

/-- An ascending chain from a root: `none → some 0` and `some n → some (n+1)`.
Every bearer has finite root access; no single bearer causes all received ones. -/
def ascendingEdge (c x : Option Nat) : Prop :=
  (c = none ∧ x = some 0) ∨ ∃ n, c = some n ∧ x = some (n + 1)

/-- Two independent roots `(false, i)`, each the only cause of its own
dependent `(true, i)`. Every root has esse equal to essence; each dependent
has distinct esse. The relation is already transitively closed, so the failure
of a common cause below does not depend on reading `CausesIn` as immediate. -/
def pluralRootsProfile : Profile (Bool × Bool) Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => c.1 = false ∧ x.1 = true ∧ c.2 = x.2
  essenceOf := fun x => !x.1
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- Seven exact interpretations. (1) A positive joint model: A, B, no
self-causation, distinct-esse coverage, identity uniqueness and a received
bearer hold together with the common uncaused cause, CCR and an infinite
descending chain (no well-foundedness). (2) Hume–Edwards regress: no
predicate whatever satisfies both A and B; the distributive reading
(TOTALITY_CAUSE_2) satisfies A and fails B; no self-causation, coverage,
uniqueness, every bearer received and loop freedom hold; CCR fails. The
relation is a bare successor relation: no per se, present or power typing.
(3) A two-bearer loop with internal totality causes: B fails; A, no
self-causation and all bearers received hold; CCR fails. (4) An actual
uncaused totality cause that supplies no member: B fails; CCR fails. (5) A
self-causing totality cause: no self-causation fails; A and B hold; CCR fails.
(6) An ascending rooted chain: CCR and the finite-path common source hold while
the common uncaused cause fails; here the failure uses the given edges as the
whole `CausesIn` relation, so a reading that also counted mediate causes would
make the root common. (7) Two independent roots: CCR, coverage and no
self-causation hold, identity uniqueness and the common uncaused cause fail,
with a transitively closed relation; so, by `commonOfAggregate`, no predicate
satisfies both A and B there. Plural foundations keep CCR and reject the joint
claim of A and B. Logical controls only. -/
def AggregateEsseCauseControls : Prop :=
  (∃ (p : Profile (Option Nat) Bool Unit) (T : Option Nat → Prop),
    ReceivedTotalityHasAggregateCause p T ∧ TotalityCauseCausesEachReceived p T ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧ DistinctEsseHasOtherActualCause p ∧
    AtMostOneEsseIsEssence p ∧ (∃ x, ReceivedActual p x) ∧
    CommonUncausedCauseOfReceived p ∧ ClosedActualEsseCollectionsRooted p ∧
    ¬ NoInfiniteActualEsseCauseRegress p) ∧
  (∃ p : Profile Nat Bool Unit,
    (∀ T : Nat → Prop,
      ¬ (ReceivedTotalityHasAggregateCause p T ∧ TotalityCauseCausesEachReceived p T)) ∧
    ReceivedTotalityHasAggregateCause p (DistributiveTotalityCause p) ∧
    ¬ TotalityCauseCausesEachReceived p (DistributiveTotalityCause p) ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧ DistinctEsseHasOtherActualCause p ∧
    AtMostOneEsseIsEssence p ∧ (∀ x, ReceivedActual p x) ∧
    (∀ x, ¬ Relation.TransGen (ActualEsseCause p) x x) ∧
    ¬ ClosedActualEsseCollectionsRooted p) ∧
  (∃ (p : Profile Bool Bool Unit) (T : Bool → Prop),
    ReceivedTotalityHasAggregateCause p T ∧ ¬ TotalityCauseCausesEachReceived p T ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧ (∀ x, ReceivedActual p x) ∧
    ¬ ClosedActualEsseCollectionsRooted p) ∧
  (∃ (p : Profile (Option Nat) Bool Unit) (T : Option Nat → Prop),
    ReceivedTotalityHasAggregateCause p T ∧ ¬ TotalityCauseCausesEachReceived p T ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    (∃ e, T e ∧ p.InAct e p.esse ∧ ∀ c, ¬ ActualEsseCause p c e) ∧
    ¬ ClosedActualEsseCollectionsRooted p) ∧
  (∃ (p : Profile Bool Bool Unit) (T : Bool → Prop),
    ReceivedTotalityHasAggregateCause p T ∧ TotalityCauseCausesEachReceived p T ∧
    ¬ NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    ¬ ClosedActualEsseCollectionsRooted p) ∧
  (∃ p : Profile (Option Nat) Bool Unit,
    ClosedActualEsseCollectionsRooted p ∧ DistinctEsseHasOtherActualCause p ∧
    AtMostOneEsseIsEssence p ∧ CommonEsseIsEssenceSource p ∧
    (∃ x, ReceivedActual p x) ∧ ¬ CommonUncausedCauseOfReceived p) ∧
  (∃ p : Profile (Bool × Bool) Bool Unit,
    ClosedActualEsseCollectionsRooted p ∧ DistinctEsseHasOtherActualCause p ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    ¬ AtMostOneEsseIsEssence p ∧ (∃ x, ReceivedActual p x) ∧
    (∀ a b c, p.CausesIn a b p.esse → p.CausesIn b c p.esse → p.CausesIn a c p.esse) ∧
    ¬ CommonUncausedCauseOfReceived p)

end TruthCore.Latin.Aquinas.DeEnte.AggregateEsseCause
