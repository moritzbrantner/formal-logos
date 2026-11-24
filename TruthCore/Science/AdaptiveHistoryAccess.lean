module

public import TruthCore.Logic.CorrectionCriterion

/-! Analyst formulation continuing #1904 and #1913. A deterministic experiment
has a current state, a readout and an action-indexed transition. A policy chooses
its next action from its complete transcript. The relation used below is an
explicit output-preserving transition matching, not metaphysical identity or a
claim that equal present readings determine future responses.

The two-bit historical controls are structural surrogates. Their first bit is
a stipulated truth marker for a past event, not a construction of an admissible
fabricated history. The blind experiment cannot couple to that bit by definition;
the audit experiment can. Neither experiment is asserted to describe reality.
No causal, epistemic-warrant or probability relation is introduced. -/

@[expose] public section

namespace TruthCore.Science.AdaptiveHistoryAccess

/-- Total deterministic readout and transition functions for the specified
action repertoire. Completeness of the repertoire and of the relevant state
is an application obligation, not a theorem about real experiments. -/
structure Experiment (State Action Observation : Type) where
  readout : State → Observation
  transition : State → Action → State

/-- Related states have equal current readouts and remain related after every
same action. It permits different state representations. It does not follow
from current readout equality, and it need not hold for an enlarged repertoire. -/
def StableMatching {S T A O : Type} (e : Experiment S A O)
    (f : Experiment T A O) (r : S → T → Prop) : Prop :=
  ∀ s t, r s t → e.readout s = f.readout t ∧
    ∀ a, r (e.transition s a) (f.transition t a)

/-- A policy may depend on every previous observation, including transcript
length. Each step performs the selected action and appends its new readout. -/
def run {S A O : Type} (e : Experiment S A O) (policy : List O → A) :
    Nat → S → List O → List O
  | 0, _, record => record
  | n + 1, s, record =>
      let next := e.transition s (policy record)
      run e policy n next (record ++ [e.readout next])

/-- The initial readout followed by the readouts of n adaptively chosen actions.
This is a finite experiment; quantification over n asserts no completed infinity. -/
def transcript {S A O : Type} (e : Experiment S A O)
    (policy : List O → A) (n : Nat) (s : S) : List O :=
  run e policy n s [e.readout s]

/-- Every finite adaptive policy has equal transcripts on related states,
provided the relation preserves readouts and every permitted transition. -/
def AdaptiveAgreement : Prop :=
  ∀ (S T A O : Type) (e : Experiment S A O) (f : Experiment T A O)
    (r : S → T → Prop), StableMatching e f r →
    ∀ policy n s t, r s t →
      transcript e policy n s = transcript f policy n t

/-- First coordinate: stipulated past-event truth marker. Second coordinate:
mutable present readout. These are mathematical states, not possible worlds. -/
abbrev HistoryState := Bool × Bool

def PastOccurred (s : HistoryState) : Prop := s.1 = true

def SameVisible (s t : HistoryState) : Prop := s.2 = t.2

/-- Both actions can be used repeatedly: true toggles the readout; false leaves
it unchanged. The past marker is unchanged and never consulted. -/
def blind : Experiment HistoryState Bool Bool where
  readout := Prod.snd
  transition s a := (s.1, if a then !s.2 else s.2)

/-- A distinct experimental interface: true copies the past marker to the
readout; false toggles the readout. Its history-sensitive action is a supplied
discriminator, not a guarantee that such an action is physically available. -/
def audit : Experiment HistoryState Bool Bool where
  readout := Prod.snd
  transition s a := (s.1, if a then s.1 else !s.2)

def probe (_ : List Bool) : Bool := true

/-- Nonvacuous controls. The blind experiment admits arbitrary finite adaptive
testing and nonconstant readings while opposite historical markers remain
indistinguishable; the existing exact-criterion meaning therefore excludes an
exact classifier from any one such transcript. Initial readings also agree in
the audit experiment, but one action distinguishes the markers and supplies an
exact classifier for this toy model. Exact classification is not warranted
belief, and no fallible epistemic norm is asserted by this certificate. -/
def HistoryControls : Prop :=
  StableMatching blind blind SameVisible ∧
  (∀ policy n s t, SameVisible s t →
    transcript blind policy n s = transcript blind policy n t) ∧
  (∀ policy n, ¬ TruthCore.Logic.CorrectionCriterion.AdmitsCriterion
    (transcript blind policy n) PastOccurred) ∧
  transcript blind probe 2 (false, false) = [false, true, false] ∧
  audit.readout (false, false) = audit.readout (true, false) ∧
  transcript audit probe 1 (false, false) ≠
    transcript audit probe 1 (true, false) ∧
  TruthCore.Logic.CorrectionCriterion.AdmitsCriterion
    (transcript audit probe 1) PastOccurred

end TruthCore.Science.AdaptiveHistoryAccess
