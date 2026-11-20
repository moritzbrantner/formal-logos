module

public import TruthCore.Epistemology.NoFoundationPractice
public import TruthCore.Results.Epistemology.UltimateExplanation.Solution

@[expose] public section

namespace TruthCore.Results.Epistemology.NoFoundationPractice

open TruthCore.Epistemology.NoFoundationPractice
open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Modern.Hume.Induction
open TruthCore.Logic.SelfApplication

/-- Reuse the actual populated open-future cells certified in #737. The
mathematical traces agree through n but have opposite results at n+1. -/
private theorem pairedCells (n : Nat) :
    Cell (openFuture n) on n on ∧
    Cell (openFuture n) on n (delayedFailure (n+1)) := by
  rcases TruthCore.Results.Epistemology.UltimateExplanation.certificate with
    ⟨_, _, _, _, _, _, hOpen, _, _, _⟩
  exact ⟨(hOpen n).1, (hOpen n).2.1⟩

/-- Every total deterministic method has one actual (mathematically admitted)
countercontinuation; every policy on the fixed three-action menu fails the
strong payoff-two promise on one such continuation. Neither proof assumes a
probability distribution or quantifies over unrelated real tasks. -/
theorem uniformBarrier : UniformBarrier := by
  intro s hBoth
  constructor
  · intro method n
    cases h : method on n with
    | false =>
      refine ⟨on, (hBoth n).1, ?_⟩
      simp [h, on]
    | true =>
      refine ⟨delayedFailure (n+1), (hBoth n).2, ?_⟩
      simp [h, delayedFailure]
  · intro policy n
    cases h : policy on n with
    | safe =>
      refine ⟨on, (hBoth n).1, ?_⟩
      simp [h, payoff]
    | betTrue =>
      refine ⟨delayedFailure (n+1), (hBoth n).2, ?_⟩
      simp [h, payoff, delayedFailure]
    | betFalse =>
      refine ⟨on, (hBoth n).1, ?_⟩
      simp [h, payoff, on]

/-- The two admitted next outcomes make every particular strict claim fail
its advertised standard. Applying the existing `Norm.selfApplication` theorem
is valid because both claim constructors are explicitly in this norm's scope.
This says nothing about a position that does NOT endorse that strong norm. -/
theorem internalDiscipline : InternalDiscipline := by
  intro s hBoth
  have hFails (c : Claim) : ¬ (strictNorm s).standard c := by
    cases c with
    | scientific method n =>
      intro hGuarantee
      obtain ⟨f, hf, hWrong⟩ := (uniformBarrier s hBoth).1 method n
      exact hWrong (hGuarantee f hf)
    | practical policy n =>
      intro hGuarantee
      obtain ⟨f, hf, hLow⟩ := (uniformBarrier s hBoth).2 policy n
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLow (hGuarantee f hf))
  constructor
  · intro hOwnNorm c
    exact (Norm.selfApplication
      (N := strictNorm s) (Acceptable := s.entitled) (self := c)
      trivial (hFails c)).1 hOwnNorm
  · rintro ⟨c, hEndorsed⟩ hOwnNorm
    exact (hFails c) (hOwnNorm c trivial hEndorsed)

/-- The strict norm admits an open-world abstainer; the same populated cell
also admits a positive safe action under an explicitly WEAKER practice norm.
The latter fails strict cross-future optimal payoff, as the rival should admit.
No entitlement predicate is identified with objective justification. -/
theorem openControls : OpenControls := by
  have hPrudent : BothSuccessors prudentOpen := by
    intro n
    exact pairedCells n
  have hAbstaining : BothSuccessors abstainingOpen := by
    intro n
    exact pairedCells n
  refine ⟨hPrudent, hAbstaining, ?_, ?_, ?_, ?_, ?_⟩
  · intro c _ hEndorsed
    exact False.elim hEndorsed
  · intro c hScope hEndorsed
    cases c with
    | scientific method n =>
      exact False.elim hScope
    | practical policy n =>
      intro f hf
      change policy on n = Action.safe at hEndorsed
      rw [hEndorsed]
      cases f (n+1) <;> decide
  · rfl
  · intro hStrong
    obtain ⟨f, hf, hLow⟩ := (uniformBarrier prudentOpen hPrudent).2 safePolicy 0
    have hHigh : 2 ≤ payoff (safePolicy on 0) (f (0+1)) :=
      hStrong (.practical safePolicy 0) trivial rfl f hf
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLow hHigh)
  · intro n f _
    change 1 ≤ payoff Action.safe (f (n+1))
    cases f (n+1) <;> decide

/-- The restricted stable law is strong enough to propagate the known initial
true state through every time. This is a *conditional* consequence of the
supplied profile, not a demonstration that actual nature must keep its laws. -/
private theorem stableTrue (n : Nat) (f : Trace) (hf : Cell stable on n f)
    (t : Nat) : f t = true := by
  induction t with
  | zero => exact hf.1.1
  | succ t ih =>
    exact (hf.1.2 t).trans ih

/-- The identical strict norm is satisfied with genuine positive entitlements
in a populated stable cell; its opposite-next trace fails stable lawhood. -/
theorem stableControl : StableControl := by
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · intro c _ hEndorsed
    cases c with
    | scientific method n =>
      intro f hf
      change method on n = true at hEndorsed
      exact hEndorsed.trans (stableTrue n f hf (n+1)).symm
    | practical policy n =>
      intro f hf
      change policy on n = Action.betTrue at hEndorsed
      rw [hEndorsed, stableTrue n f hf (n+1)]
      decide
  · exact ⟨⟨rfl, fun _ => rfl⟩, fun _ _ => rfl⟩
  · intro hBoth
    have hBad : Cell stable on 0 (delayedFailure 1) := (hBoth 0).2
    have hTrue := stableTrue 0 (delayedFailure 1) hBad 1
    have hFalse : delayedFailure 1 1 = false := by
      simp [delayedFailure]
    exact Bool.noConfusion (hTrue.symm.trans hFalse)

end TruthCore.Results.Epistemology.NoFoundationPractice
