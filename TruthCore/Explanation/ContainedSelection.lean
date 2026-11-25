module

public import TruthCore.Explanation.ExplanatorySymmetry
public import TruthCore.Explanation.BruteContingencyParity

/-!
# Restrictions, actual exercise and existential scope

Analyst continuation of #1910, with the existing #742 `acting` arena held fixed.
The experiment removes only reasons for its distinct act fact `member 0`.
No new causal, intentional or adequacy relation is introduced. In particular,
admitting a source-to-act reason is not a proof of its explanatory adequacy.
-/

@[expose] public section

namespace TruthCore.Explanation.ContainedSelection

open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.HistorySelection
open TruthCore.Explanation.BruteContingencyParity

variable {W B F : Type}

/-- An actually obtaining condition that entails this fact throughout the
selected accessible scope. This is a determination test, not explanation. -/
def DeterminesFact (A : Arena W B F) (a : W) (p : W → Prop) (f : F) : Prop :=
  p a ∧ ∀ v, Access A a v → p v → A.holds v f

/-- All accessible valuations agree with actuality on every represented fact.
Calling these *complete metaphysical possibilities* requires an exhaustive fact
representation and justified accessibility, neither supplied here. -/
def CompleteTruthFixed (A : Arena W B F) (a : W) : Prop :=
  ∀ v, Access A a v → ∀ f, A.holds v f ↔ A.holds a f

/-- Necessary constraints, including arbitrary whole-vector functions of them,
cannot determine an actually contingent fact. If all represented truths are
fixed, no represented truth is contingent. This strengthens no account of
explanation into a necessitating account: its test is explicitly informational. -/
def RestrictionBoundary : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (base : F → Prop) (a : W),
    NecessaryBase A base a → ∀ p f, EvidenceOnly A.holds base p →
      DeterminesFact A a p f → ¬ Contingent A a f) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W),
    CompleteTruthFixed A a → ∀ f, ¬ Contingent A a f)

/-- Exactly the #742 ontology, world-relative truth and existence-fact map.
The act-to-target and direct source-to-target explanations remain. Only the
source-to-act edge for `member 0` is removed; other target facts are unchanged.
This is a controlled interpretation, not a possible deity or physical source. -/
def unexplainedAct : Arena Nat (Option Bool) Fact :=
  { acting.arena with
    explains := fun w r f => ActingReason w r f ∧ f ≠ .member 0 }

/-- A narrow adapter to #312's existence-fact/token vocabulary. A token about
a bearer is admitted exactly when that bearer's existence fact is a reason for
the target's existence fact. It deliberately omits non-existential fact reasons;
no general completeness or adequate-reason-to-token bridge is asserted. -/
def existenceView (A : Arena W B F) : TruthCore.Explanation.ExistencePSR.Model W B where
  ontic := A.ontic
  explains := fun w r f => match f with
    | .fact x => A.explains w (A.exist (source r)) (A.exist x)

/-- The exact matched test requested in #1910. Original and cut arenas retain
the same necessary sources, contingent act and outcome, and local explanations
of the target. Both satisfy the exact contingent-existence token PSR through
the narrow adapter. Only the original covers every contingent fact at world 0;
the cut leaves the act brute at that fact-level scope. Neither reason relation
is necessitating. No causal Supply, agency, divine identity, philosophical
adequacy or metaphysical admissibility is inferred from these assignments. -/
def ExerciseComparison : Prop :=
  unexplainedAct.ontic = acting.arena.ontic ∧
  (∀ w f, unexplainedAct.holds w f ↔ acting.arena.holds w f) ∧
  (∀ w x, unexplainedAct.exist x = acting.arena.exist x ∧
    unexplainedAct.ontic.ExistsAt w x = acting.arena.ontic.ExistsAt w x) ∧
  Contingent acting.arena 0 (.member 0) ∧
  Contingent acting.arena 0 .target ∧
  acting.arena.explains 0 (.member 0) .target ∧
  unexplainedAct.explains 0 (.member 0) .target ∧
  unexplainedAct.explains 0 (.source true) .target ∧
  Explained acting.arena 0 (.member 0) ∧
  ¬ Explained unexplainedAct 0 (.member 0) ∧
  ContingentPSR acting.arena 0 ∧
  ¬ ContingentPSR unexplainedAct 0 ∧
  NoBruteContingentExistenceAt (existenceView acting.arena) 0 ∧
  NoBruteContingentExistenceAt (existenceView unexplainedAct) 0 ∧
  ¬ Necessitating acting.arena ∧
  ¬ Necessitating unexplainedAct

end TruthCore.Explanation.ContainedSelection
