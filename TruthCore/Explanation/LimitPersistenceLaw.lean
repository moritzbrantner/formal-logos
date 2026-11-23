module

public import Mathlib.Order.WithBot
public import TruthCore.Causality.TimeSymmetricGiving

/-!
# Limit-inclusive existential persistence under ¬C3

An isolated unregistered control for the existential-inertia comparison in
issue #1801. It does not modify frozen Challenge imports or the registered
LawActuality / NoFoundationLawChaos results.
-/

@[expose] public section

namespace TruthCore.Explanation.LimitPersistenceLaw
open TruthCore.Modal.TemporalHistory

/-! ## An existential-inertia law across a limit time (¬C3 / #1801)

The previous finite-record law test concerns state values, not existence. This
separate scoped control uses one rigid bearer, a source, and the *existing*
History, BeingGiving, CessationNeedsInducer and ConcurrentlyActualized
vocabularies. Time is Mathlib's ω+1, `WithTop Nat`. Finite-stage survival
and survival at the separate limit are different propositions.

A Schmid-style interval-wide no-positive-destruction rule ranges over the
limit too; it is deliberately stronger than stepwise survival. It can hold of
a received-esse bearer while strictly concurrent `GivesAt` fails. A
destructive occurrence at the limit restores that same rule for the
limit-disappearance configuration, but its *physical/ontological reality*
is not assumed. The controls distinguish mathematical adequacy from the
metaphysical scope of a persistence law and do not say the real world has a
supertask or that absence automatically counts as positive destruction.
-/

open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.TimeSymmetricGiving (CessationNeedsInducer)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)

-- The two histories have the same bearers and agree on *all* finite moments.
-- `true` is the source, present throughout; `false` is the target.
/-- At every finite stage the target exists; at the limit it does not. -/
def disappearsAtLimit : History Unit Bool (WithTop Nat) where
  ontic :=
    { frame := ⟨fun _ _ => True⟩
      ExistsAt := fun _ _ => True
      Causes := fun _ _ _ => False }
  IsAt := fun _ x t => x = true ∨ t ≠ ⊤
  now := 0

/-- The target exists through the limit, with exactly the same finite past. -/
def existsAtLimit : History Unit Bool (WithTop Nat) where
  ontic := disappearsAtLimit.ontic
  IsAt := fun _ _ _ => True
  now := 0

/-- The originating exercise at stage zero only, shared by both histories.
No later or limit-time being-giving is postulated. -/
def givingAtOrigin : BeingGiving Unit Bool (WithTop Nat) :=
  ⟨fun _ c x t => c = true ∧ x = false ∧ t = 0⟩

/-- A stepwise constraint on existence, not a complete history-selection law.
At finite stages `n`, presence entails presence at stage `n+1`. -/
def FiniteStepPersistence (h : History Unit Bool (WithTop Nat)) : Prop :=
  ∀ x (n : Nat), h.IsAt () x (n : WithTop Nat) →
    h.IsAt () x ((n+1 : Nat) : WithTop Nat)

/-- No positive destructive process is represented. -/
def noInducer : Unit → Bool → WithTop Nat → Prop := fun _ _ _ => False

/-- Alternative disputed interpretation: a genuine destructive event occurs
exactly at the limit, affecting the same receiver. This is not a definition
identifying *absence* or giver-withdrawal with efficient destruction. -/
def atLimitInducer : Unit → Bool → WithTop Nat → Prop :=
  fun _ x t => x = false ∧ t = ⊤

/-- Joint structural discriminator. Its positive branch is a law-governed
existential-inertia history with an actual bearer and strictly no concurrent
giver at the limit. The negative branch shows that finite-step preservation
does not imply survival at a limit. Neither branch supplies warrant for the
law's physical/metaphysical applicability or for ultimate source selection. -/
def LimitCertificate : Prop :=
  CoherentAtNow disappearsAtLimit ∧
  CoherentAtNow existsAtLimit ∧
  (∀ x (n : Nat), disappearsAtLimit.IsAt () x (n : WithTop Nat) ↔
    existsAtLimit.IsAt () x (n : WithTop Nat)) ∧
  FiniteStepPersistence disappearsAtLimit ∧
  FiniteStepPersistence existsAtLimit ∧
  disappearsAtLimit.IsAt () false (0 : WithTop Nat) ∧
  ¬ disappearsAtLimit.IsAt () false ⊤ ∧
  existsAtLimit.IsAt () false ⊤ ∧
  givingAtOrigin.GivesAt () true false (0 : WithTop Nat) ∧
  (¬ ∃ g, givingAtOrigin.GivesAt () g false ⊤) ∧
  ¬ CessationNeedsInducer disappearsAtLimit noInducer ∧
  CessationNeedsInducer existsAtLimit noInducer ∧
  CessationNeedsInducer disappearsAtLimit atLimitInducer ∧
  ¬ ConcurrentlyActualized existsAtLimit givingAtOrigin falseReceived

end TruthCore.Explanation.LimitPersistenceLaw
