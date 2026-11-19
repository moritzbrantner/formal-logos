module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Group.Int
public import TruthCore.Causality.SustainingDependence

/-!
# Horizontal tests of concurrent actualization: momentary PSR and time symmetry

Analyst formulations, attribution deferred. Note:
`docs/notes/ca-horizontal-support.md`. Target: weak concurrent actualization
`40a97664` (`ConcurrentActualization.ConcurrentlyActualized`), the crux between
sustaining causation of being and existential inertia
(`docs/notes/sustaining-vs-existential-inertia.md`). Every earlier test came
from the Thomist esse/act-potency family and restated the crux. This module
tests two premises from other families, over the same history frame
(`TemporalHistory.History`, `SustainingCausation.BeingGiving`, STRICT
esse-giving reading of `GivesAt`, definition `158301bc`).

**Part I: the momentary principle of sufficient reason.** Schmid 2021 (read;
passage `SCHMID-INERTIA-REPLY-3-ARTICLE`, paragraph beginning "And this
discovery especially helps") accepts Feser's auxiliary thesis that something
must explain the fact that an object continues to exist, a "PSR or PSR-like
explanatory principle", and rejects the second auxiliary thesis, that without a
sustaining cause there is no extrinsic explanation. His explanation of S's
existence at m (paragraphs beginning "For S to fail" and "Here, we seem to
have") cites (i) S's existence before m, (ii) that nothing induced S's
cessation, and (iii) the law that a change occurs only if some factor induces
it. `MomentaryPSR` types the first thesis over a primitive explanation relation;
`ExplanationNeedsGiver` types the second, contraposed and at the matching type
(every explanation of a received-esse thing's presence at `t` comes with
something giving it being at `t`). `originOrInertia` is Schmid's explanation as
a defined sense of the primitive. The momentary PSR is shared: both sides accept
it, and Schmid's explanation satisfies it with no giver after onset.

**Part II: time symmetry (the Leibnizian contrastive principle) for things
without a beginning.** Onset `fa3e228b` is silent on things with no first
moment of presence, and parity `5b24ef26` reaches them only by being the crux
restated. Part II asks what other families say about a received-esse thing
whose moments of presence cannot be told apart: a beginningless, unchanging
thing in a stationary history, the case Aquinas grants is not shown impossible
(an eternal created world, ST I q.46 a.2, not re-read here, a lead with no
weight). Three premises:

* *Coverage* (`ReceivedEsseHasCauseOfBeing`): whatever has received esse has
  its being caused by another (tenseless `CausesIn c x esse`, `c ≠ x`). The
  converse direction of the reception bridge `da72ae93`; the tenseless De ente
  c.4 reading (whatever has esse not from its essence has it from another),
  in the vocabulary of `EsseReceivedIn` rather than the world-indexed
  `DistinctEsseAt` of `457698e4` (no bridge between them is built here).
* *Exercise* (`CausesOfBeingAreExercised`): a cause of another's being gives
  it being at some moment at which it is present. The time index of `GivesAt`
  is the effect side, so this says the cause's activity bears on the effect at
  some moment of its presence. For a begun thing the onset moment satisfies it,
  as an inertialist who grants onset `fa3e228b` accepts.
* *Time symmetry* (`GivingRespectsTimeSymmetry`): if an order automorphism of
  time preserves, in a history, every being's presence and every supplied
  non-giving time-indexed fact (`Facts`), then giving at a moment and giving at
  its image go together. This is the contrastive principle of sufficient reason
  applied to moments, in the shape of Leibniz's argument that uniform absolute
  space leaves no reason for one arrangement over another (statement
  `7dd2af35`; its application to moments is the analyst's); Clarke's reply that a will
  may choose without an external difference (`81ec01fe`) is its recorded rival.
  `Facts` must not encode giving or causing being; with an incomplete `Facts`
  the premise is stronger than the contrastive principle, since a map that
  preserves the supplied facts may move unsupplied ones.

They give concurrent actualization for *homogeneous* things
(`ConcurrentlyActualizedIfHomogeneous`: any two moments of the thing's presence
are related by such an automorphism), with one cause of being giving at every
moment. On integer time an automorphism preserving a begun thing's presence
fixes its first moment, so a begun thing present at more than one moment is not
homogeneous and the premises are silent on it: Part II is not parity restated.

*Structural properties.* `OrderIso` is Mathlib's order automorphism; on
integers these are the shifts. `HomogeneousIn` is relative to the supplied
`Facts`. No premise relates `CausesIn` to `GivesAt` beyond exercise, which
asks for one moment only.

Applicability of every premise to reality remains OPEN. A countermodel in
`Control` shows a premise is needed in that interpretation, not that it is
false.
-/

@[expose] public section

namespace TruthCore.Causality.TimeSymmetricGiving

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized)

/-! ## Part I: the momentary principle of sufficient reason -/

/-- Explicitly identified PRIMITIVE relation (Encode first).

* `Explains v r x t`: in history `v`, the reason `r` explains `x`'s being
  present at moment `t`. A reason is any explanans token, causal or not: a
  giver, an earlier state with a law, a necessity. Not giving, not causing,
  not grounding.

No axiom constrains it. -/
structure PresenceExplanation (W B T R : Type) where
  Explains : W → R → B → T → Prop

/-- Momentary PSR: in every history, whatever has received esse has, at every
moment at which it is present, some explanation of its being present then. -/
def MomentaryPSR {W B T P R : Type} (h : History W B T) (X : PresenceExplanation W B T R)
    (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x t z, EsseReceivedIn x z → h.IsAt v x t → ∃ r, X.Explains v r x t

/-- Productive bridge: in every history, whenever a received-esse thing's
presence at a moment is explained at all, something gives it being at that
moment. -/
def ExplanationNeedsGiver {W B T P R : Type} (h : History W B T) (G : BeingGiving W B T)
    (X : PresenceExplanation W B T R) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x t z r, EsseReceivedIn x z → h.IsAt v x t → X.Explains v r x t →
    ∃ g, G.GivesAt v g x t

/-- Schmid's causal law on cessation, item (iii): a thing present at `s` and
absent at a later `t` has some inducer of its cessation (`D v x u`, a primitive
parameter) at a moment in `(s, t]`. -/
def CessationNeedsInducer {W B T : Type} [Preorder T] (h : History W B T)
    (D : W → B → T → Prop) : Prop :=
  ∀ v x s t, s < t → h.IsAt v x s → ¬ h.IsAt v x t → ∃ u, s < u ∧ u ≤ t ∧ D v x u

/-- Schmid's explanation as a defined sense of the primitive: a reason is
either a giver at `t` (`inl g`: `g` gives `x` being at `t`) or an earlier
moment (`inr s`: `s < t`, `x` was present at `s`, and nothing induced its
cessation in `(s, t]`). -/
def originOrInertia {W B T : Type} [Preorder T] (h : History W B T) (G : BeingGiving W B T)
    (D : W → B → T → Prop) : PresenceExplanation W B T (B ⊕ T) :=
  ⟨fun v r x t => Sum.elim (fun g => G.GivesAt v g x t)
    (fun s => s < t ∧ h.IsAt v x s ∧ ∀ u, s < u → u ≤ t → ¬ D v x u) r⟩

/-- Under the shared momentary PSR the productive bridge is weak concurrent
actualization: for every history, giving relation, explanation relation and
reception predicate, if the momentary PSR holds then the bridge holds iff
`40a97664` does. -/
def PSRBridgeCarriesTheCrux : Prop :=
  ∀ (W B T P R : Type) (h : History W B T) (G : BeingGiving W B T)
    (X : PresenceExplanation W B T R) (E : B → P → Prop),
    MomentaryPSR h X E → (ExplanationNeedsGiver h G X E ↔ ConcurrentlyActualized h G E)

/-! ## Part II: time symmetry for things without a beginning -/

/-- The order automorphism `σ` of time preserves history `v`: every being is
present at `t` iff at `σ t`, and every supplied fact holds at `t` iff at
`σ t`. -/
def PreservesHistory {W B T : Type} [Preorder T] (h : History W B T)
    (Facts : W → B → T → Prop) (v : W) (σ : T ≃o T) : Prop :=
  ∀ y t, (h.IsAt v y t ↔ h.IsAt v y (σ t)) ∧ (Facts v y t ↔ Facts v y (σ t))

/-- Time symmetry of giving: in every history, an order automorphism of time
preserving presence and the supplied non-giving facts preserves giving. -/
def GivingRespectsTimeSymmetry {W B T : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (Facts : W → B → T → Prop) : Prop :=
  ∀ v (σ : T ≃o T), PreservesHistory h Facts v σ →
    ∀ g x t, (G.GivesAt v g x t ↔ G.GivesAt v g x (σ t))

/-- `x` is homogeneous in history `v`: any two moments of its presence are
related by an order automorphism of time preserving the history. -/
def HomogeneousIn {W B T : Type} [Preorder T] (h : History W B T)
    (Facts : W → B → T → Prop) (v : W) (x : B) : Prop :=
  ∀ s t, h.IsAt v x s → h.IsAt v x t → ∃ σ : T ≃o T, PreservesHistory h Facts v σ ∧ σ s = t

/-- Coverage: whatever has received esse has its being caused by another. -/
def ReceivedEsseHasCauseOfBeing {B R P : Type} (CausesIn : B → B → R → Prop) (esse : R)
    (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ x z, EsseReceivedIn x z → ∃ c, c ≠ x ∧ CausesIn c x esse

/-- Exercise: in every history, a cause of another's being, if the effect is
present at some moment, gives it being at some moment at which it is
present. -/
def CausesOfBeingAreExercised {W B T R : Type} (h : History W B T) (G : BeingGiving W B T)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ v c x, c ≠ x → CausesIn c x esse → (∃ t, h.IsAt v x t) →
    ∃ t, h.IsAt v x t ∧ G.GivesAt v c x t

/-- Concurrent actualization for homogeneous things: in every history,
whatever has received esse and is homogeneous there is given being by
something at every moment at which it is present. -/
def ConcurrentlyActualizedIfHomogeneous {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (Facts : W → B → T → Prop) (EsseReceivedIn : B → P → Prop) :
    Prop :=
  ∀ v x t z, EsseReceivedIn x z → HomogeneousIn h Facts v x → h.IsAt v x t →
    ∃ g, G.GivesAt v g x t

namespace Control

open TruthCore.Causality.SustainingCausation.Control (unitFrame trueCausesFalse noCauses)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)
open TruthCore.Causality.SustainingDependence (ReceivedOnsetIsGiven)

/-- A beginningless stationary history: both individuals present at every
integer moment. -/
def eternal : History Unit Bool Int where
  ontic := { frame := unitFrame, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  IsAt := fun _ _ _ => True
  now := 0

/-- A begun history: `true` present at every moment, `false` from moment `0`
on. -/
def begun : History Unit Bool Int where
  ontic := { frame := unitFrame, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  IsAt := fun _ b t => b = true ∨ 0 ≤ t
  now := 0

/-- No giving. -/
def noGivingZ : BeingGiving Unit Bool Int := ⟨fun _ _ _ _ => False⟩

/-- `true` gives `false` being at moment `0` only. -/
def givesAtZero : BeingGiving Unit Bool Int := ⟨fun _ c x t => c = true ∧ x = false ∧ t = 0⟩

/-- `true` gives `false` being at every moment. -/
def givesAlways : BeingGiving Unit Bool Int := ⟨fun _ c x _ => c = true ∧ x = false⟩

/-- No further time-indexed facts. -/
def noFacts : Unit → Bool → Int → Prop := fun _ _ _ => False

/-- No inducer of cessation. -/
def noInducer : Unit → Bool → Int → Prop := fun _ _ _ => False

/-- No explanations. -/
def noExplanation : PresenceExplanation Unit Bool Int Unit := ⟨fun _ _ _ _ => False⟩

/-- Controls, one world, integer times, `false` alone with received esse,
`esse := ()`.
(1) Eternal inertia (`eternal`, no giving, no cause of being): Schmid's
explanation satisfies the momentary PSR and the cessation law; the productive
bridge and `40a97664` fail; `false` is homogeneous; coverage fails while
exercise and time symmetry hold; the homogeneous conclusion fails.
(2) Eternal, `true` causes `false`'s being and gives at moment `0` only:
coverage and exercise hold; time symmetry and the conclusion fail.
(3) Eternal, `true` causes `false`'s being and never gives: coverage and time
symmetry hold; exercise and the conclusion fail.
(4) Begun inertia (`begun`, giving at moment `0` only): coverage, exercise,
time symmetry, the momentary PSR on Schmid's explanation, the cessation law and
received onset is given all hold; `40a97664` fails while concurrent
actualization for homogeneous things holds, since `false` is not homogeneous.
(5) Eternal sustaining (`givesAlways`): every premise of both parts and
`40a97664` hold.
(6) No explanations: the productive bridge holds vacuously; the momentary PSR
and `40a97664` fail. -/
def Certificate : Prop :=
  (MomentaryPSR eternal (originOrInertia eternal noGivingZ noInducer) falseReceived ∧
    CessationNeedsInducer eternal noInducer ∧
    ¬ ExplanationNeedsGiver eternal noGivingZ (originOrInertia eternal noGivingZ noInducer)
      falseReceived ∧
    ¬ ConcurrentlyActualized eternal noGivingZ falseReceived ∧
    HomogeneousIn eternal noFacts () false ∧
    ¬ ReceivedEsseHasCauseOfBeing noCauses () falseReceived ∧
    CausesOfBeingAreExercised eternal noGivingZ noCauses () ∧
    GivingRespectsTimeSymmetry eternal noGivingZ noFacts ∧
    ¬ ConcurrentlyActualizedIfHomogeneous eternal noGivingZ noFacts falseReceived) ∧
  (ReceivedEsseHasCauseOfBeing trueCausesFalse () falseReceived ∧
    CausesOfBeingAreExercised eternal givesAtZero trueCausesFalse () ∧
    ¬ GivingRespectsTimeSymmetry eternal givesAtZero noFacts ∧
    ¬ ConcurrentlyActualizedIfHomogeneous eternal givesAtZero noFacts falseReceived) ∧
  (ReceivedEsseHasCauseOfBeing trueCausesFalse () falseReceived ∧
    GivingRespectsTimeSymmetry eternal noGivingZ noFacts ∧
    ¬ CausesOfBeingAreExercised eternal noGivingZ trueCausesFalse () ∧
    ¬ ConcurrentlyActualizedIfHomogeneous eternal noGivingZ noFacts falseReceived) ∧
  (ReceivedEsseHasCauseOfBeing trueCausesFalse () falseReceived ∧
    CausesOfBeingAreExercised begun givesAtZero trueCausesFalse () ∧
    GivingRespectsTimeSymmetry begun givesAtZero noFacts ∧
    MomentaryPSR begun (originOrInertia begun givesAtZero noInducer) falseReceived ∧
    CessationNeedsInducer begun noInducer ∧
    ReceivedOnsetIsGiven begun givesAtZero falseReceived ∧
    ¬ ConcurrentlyActualized begun givesAtZero falseReceived ∧
    ConcurrentlyActualizedIfHomogeneous begun givesAtZero noFacts falseReceived ∧
    ¬ HomogeneousIn begun noFacts () false) ∧
  (ReceivedEsseHasCauseOfBeing trueCausesFalse () falseReceived ∧
    CausesOfBeingAreExercised eternal givesAlways trueCausesFalse () ∧
    GivingRespectsTimeSymmetry eternal givesAlways noFacts ∧
    MomentaryPSR eternal (originOrInertia eternal givesAlways noInducer) falseReceived ∧
    ExplanationNeedsGiver eternal givesAlways (originOrInertia eternal givesAlways noInducer)
      falseReceived ∧
    ConcurrentlyActualized eternal givesAlways falseReceived ∧
    ConcurrentlyActualizedIfHomogeneous eternal givesAlways noFacts falseReceived) ∧
  (ExplanationNeedsGiver eternal noGivingZ noExplanation falseReceived ∧
    ¬ MomentaryPSR eternal noExplanation falseReceived ∧
    ¬ ConcurrentlyActualized eternal noGivingZ falseReceived)

end Control

end TruthCore.Causality.TimeSymmetricGiving
