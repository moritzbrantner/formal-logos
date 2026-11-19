module

public import TruthCore.Causality.ConcurrentActualization
public import TruthCore.Causality.Round2Grounding

/-!
# Sustaining causes of esse and dependence for being; onset and parity

Analyst formulations, attribution deferred. Research note:
`docs/notes/sustaining-vs-existential-inertia.md`.

## 1. The sustaining sibling of the esse-dependence premise

`2068f91c` (`Round2Grounding.EsseEffectDependsOnItsCause`) says: if `c`,
distinct from `x`, causes `x`'s esse (`CausesIn c x esse`, tenseless,
mode-unspecified), then `x` depends for its being on `c` (`DependsForBeing x c`,
DEF-DEPENDS-FOR-BEING: `x` would not be if `c` were not, the q.44 a.1 ad 2
counterfactual; a primitive parameter, not time-indexed). The esse-root routes
consume it at (maximum, root). Its open difficulty is the mode of `CausesIn`:
with an originating cause, a parent and a child, the child can be while the
parent is not.

**Sustaining sibling** (`SustainingEsseCauseIsDependedOn`, open). The same
premise restricted to causes of esse that sustain their effect in every history
in which the effect is present (CAUSE_OF_BEING_2, `SustainsBeing`). Entailed by
`2068f91c` (the added antecedent is unused).

**Co-presence bridge** (`CoPresentEsseCauseIsDependedOn`, open). If `c`,
distinct from `x`, causes `x`'s esse and, in every history of the model, `c` is
present at every moment at which `x` is, then `x` depends for its being on `c`.
*Meaning:* a strict conditional over the model's histories ("no history has `x`
at a moment without `c` then") yields the counterfactual of DEF-DEPENDS-FOR-BEING.
*Warrant:* in the standard counterfactual logics (Lewis, Stalnaker) a strict
conditional entails the corresponding counterfactual, vacuously so when the
antecedent is impossible, which matches DEF-DEPENDS-FOR-BEING's explicit
inclusion of impossible antecedents. The application needs the model's histories
to represent the alternatives relevant to the counterfactual (history
coverage); on a one-history model the bridge would be a much stronger
co-presence-plus-causation principle. The `CausesIn` antecedent blocks the
modal account's familiar overgeneration (everything "depending" on whatever is
present at every moment of every history, such as a necessary co-existent with
no causal role). The antecedent is pointwise and over all histories, so it
suffices for both readings of "would not be": would never have been, and would
not be at that moment.

Composed with the contact principle `c4661518` the bridge gives the sibling,
and the sibling with the weak sustaining reading `ce55210c` gives `2068f91c`.
So on this route `2068f91c` costs exactly `ce55210c` plus contact plus the
co-presence bridge, and the parent-child interpretation (`Control` part 1)
satisfies every input except `ce55210c`.

## 2. Onset and parity

**Received onset is given** (`ReceivedOnsetIsGiven`, open). In every history,
whatever has received esse is given being by something at a first moment of its
presence (`BeginsAt`). The existential-inertia rival accepts it: Schmid's causal
requirement on change covers coming to be, and in `Control` part 5 the inertial
history satisfies it.

**Parity of persistence with onset** (`PersistenceParity`, open). In every
history, if a received-esse thing is given being at a first moment of its
presence, it is given being at every moment at which it is present: its being
at a later moment is the same kind of fact as its being at its first moment.

Together they give concurrent actualization for things with a first moment of
presence (`ConcurrentlyActualizedOnceBegun`), which the weak concurrent
actualization `40a97664` entails. Parity is not independent of that crux: given
onset, it is concurrent actualization for begun things restated, and the
inertialist rejects it on the ground already recorded against `40a97664`
(onset is a change, persistence is not). The result shows where the parity
objection's force lies; it adds no item to the rival's price.

Applicability of every premise below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.SustainingDependence

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization

/-- Sustaining sibling of `2068f91c`: in the given model, if `c`, distinct from
`x`, causes `x`'s esse and sustains `x` (CAUSE_OF_BEING_2) in every history in
which `x` is present, then `x` depends for its being on `c`. -/
def SustainingEsseCauseIsDependedOn {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (DependsForBeing : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → CausesIn c x esse →
    (∀ v, (∃ t, h.IsAt v x t) → SustainsBeing h G v c x) → DependsForBeing x c

/-- Co-presence bridge: in the given model, if `c`, distinct from `x`, causes
`x`'s esse and is present at every moment at which `x` is, in every history,
then `x` depends for its being on `c`. -/
def CoPresentEsseCauseIsDependedOn {W B T Respect : Type} (h : History W B T)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (DependsForBeing : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → CausesIn c x esse →
    (∀ v t, h.IsAt v x t → h.IsAt v c t) → DependsForBeing x c

/-- Received onset is given: in every history, whatever has received esse is
given being by something at a first moment of its presence. -/
def ReceivedOnsetIsGiven {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x z b, EsseReceivedIn x z → BeginsAt h v x b → ∃ g, G.GivesAt v g x b

/-- Parity of persistence with onset: in every history, a received-esse thing
given being at a first moment of its presence is given being at every moment at
which it is present. -/
def PersistenceParity {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x z b, EsseReceivedIn x z → BeginsAt h v x b → (∃ g, G.GivesAt v g x b) →
    ∀ t, h.IsAt v x t → ∃ g, G.GivesAt v g x t

/-- Concurrent actualization for begun things: in every history, a
received-esse thing with a first moment of presence is given being by something
at every moment at which it is present. -/
def ConcurrentlyActualizedOnceBegun {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x z b, EsseReceivedIn x z → BeginsAt h v x b →
    ∀ t, h.IsAt v x t → ∃ g, G.GivesAt v g x t

namespace Control

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control
open TruthCore.Causality.Round2Grounding (EsseEffectDependsOnItsCause)

/-- Dependence read as co-presence in every history of `h`: `x` is never
present at a moment without `c`. -/
def coPresent {W B T : Type} (h : History W B T) : B → B → Prop :=
  fun x c => ∀ v t, h.IsAt v x t → h.IsAt v c t

/-- No dependence. -/
def noDependence : Bool → Bool → Prop := fun _ _ => False

/-- Omission, rival-reading, strictness and nonvacuity controls, one world and
natural-number times, reusing the histories of `SustainingCausation.Control`.
(1) Parent and child (`inertia`, dependence as co-presence): `true` gives `false`
being at time `1` only and is absent after time `1`; `false` persists. Contact,
the co-presence bridge and the sustaining sibling hold; the weak sustaining
reading `ce55210c` and `2068f91c` fail.
(2) `sustained` with no dependence: the weak sustaining reading and contact
hold; the co-presence bridge, the sibling and `2068f91c` fail.
(3) `absentGiver`, giving at every time, dependence as co-presence: the weak
sustaining reading and the bridge hold; contact, the sibling and `2068f91c` fail.
(4) `sustained`, dependence as co-presence: every premise, the sibling and
`2068f91c` hold, and `false` depends on `true`.
(5) Inertia (`inertia`, `false` alone received): received onset is given;
parity and concurrent actualization for begun things fail.
(6) Inertia with no giving: parity holds; received onset and concurrent
actualization for begun things fail.
(7) `sustained`: received onset, parity and concurrent actualization for begun
things hold. -/
def Certificate : Prop :=
  (GiverPresentWhenGiving inertia inertiaGiving ∧
    CoPresentEsseCauseIsDependedOn inertia trueCausesFalse () (coPresent inertia) ∧
    SustainingEsseCauseIsDependedOn inertia inertiaGiving trueCausesFalse () (coPresent inertia) ∧
    ¬ CausingAnothersBeingIsSustaining inertia inertiaGiving trueCausesFalse () ∧
    ¬ EsseEffectDependsOnItsCause trueCausesFalse () (coPresent inertia)) ∧
  (CausingAnothersBeingIsSustaining sustained sustainedGiving trueCausesFalse () ∧
    GiverPresentWhenGiving sustained sustainedGiving ∧
    ¬ CoPresentEsseCauseIsDependedOn sustained trueCausesFalse () noDependence ∧
    ¬ SustainingEsseCauseIsDependedOn sustained sustainedGiving trueCausesFalse () noDependence ∧
    ¬ EsseEffectDependsOnItsCause trueCausesFalse () noDependence) ∧
  (CausingAnothersBeingIsSustaining absentGiver alwaysGiving trueCausesFalse () ∧
    CoPresentEsseCauseIsDependedOn absentGiver trueCausesFalse () (coPresent absentGiver) ∧
    ¬ GiverPresentWhenGiving absentGiver alwaysGiving ∧
    ¬ SustainingEsseCauseIsDependedOn absentGiver alwaysGiving trueCausesFalse ()
      (coPresent absentGiver) ∧
    ¬ EsseEffectDependsOnItsCause trueCausesFalse () (coPresent absentGiver)) ∧
  (CausingAnothersBeingIsSustaining sustained sustainedGiving trueCausesFalse () ∧
    GiverPresentWhenGiving sustained sustainedGiving ∧
    CoPresentEsseCauseIsDependedOn sustained trueCausesFalse () (coPresent sustained) ∧
    SustainingEsseCauseIsDependedOn sustained sustainedGiving trueCausesFalse ()
      (coPresent sustained) ∧
    EsseEffectDependsOnItsCause trueCausesFalse () (coPresent sustained) ∧
    coPresent sustained false true) ∧
  (ReceivedOnsetIsGiven inertia inertiaGiving falseReceived ∧
    ¬ PersistenceParity inertia inertiaGiving falseReceived ∧
    ¬ ConcurrentlyActualizedOnceBegun inertia inertiaGiving falseReceived) ∧
  (PersistenceParity inertia noGiving falseReceived ∧
    ¬ ReceivedOnsetIsGiven inertia noGiving falseReceived ∧
    ¬ ConcurrentlyActualizedOnceBegun inertia noGiving falseReceived) ∧
  (ReceivedOnsetIsGiven sustained sustainedGiving falseReceived ∧
    PersistenceParity sustained sustainedGiving falseReceived ∧
    ConcurrentlyActualizedOnceBegun sustained sustainedGiving falseReceived)

end Control

end TruthCore.Causality.SustainingDependence
