module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Finite.Basic
public import TruthCore.Causality.ConvergentSchedule

/-!
# Zeno's motion arguments: analytic controls (issue #338)

These are **modern analyst reconstructions**, not additional propositions
attributed to Aristotle or changes to the frozen VI.9 Challenges. The sourced
propositional readings remain in `BookVI.Chapter9`.

An instant has a definite position because a trajectory is a function. That
does not assert a zero derivative. Rest at a single instant does not imply
global stationarity. Rest at *every* real instant does imply stationarity for
a differentiable trajectory, by Mathlib's mean-value theorem.

The existing `ConvergentZenoSchedule` is reused as a clock. Its countably
many mathematical checkpoints are not identified with separately performed
physical operations. No causal or metaphysical predicate is inferred here.
-/

@[expose] public section

namespace TruthCore.Greek.Aristotle.Physics.Typed.Zeno

open Filter Topology
open TruthCore.Causality

/-- A real-valued position over real time. A total trajectory assigns a
position at each instant; it says nothing about velocity. -/
abbrev Trajectory := ℝ → ℝ

/-- Velocity zero at one specified instant, in Mathlib's derivative sense. -/
def InstantaneousRest (x : Trajectory) (t : ℝ) : Prop :=
  HasDerivAt x 0 t

/-- Global rest: one position for all real times (not merely one instant). -/
def Stationary (x : Trajectory) : Prop :=
  ∃ p : ℝ, ∀ t : ℝ, x t = p

/-- Every-instant zero velocity is equivalent to global rest *in this real,
everywhere-differentiable model*. The forward direction is the mean-value
theorem, not an inference from occupying a position at each instant. -/
theorem everyInstantRest_iff_stationary (x : Trajectory) :
    (∀ t, InstantaneousRest x t) ↔ Stationary x := by
  constructor
  · intro h
    have hd : Differentiable ℝ x := fun t => (h t).differentiableAt
    have hv : ∀ t, deriv x t = 0 := fun t => (h t).deriv
    exact ⟨x 0, fun t => is_const_of_deriv_eq_zero hd hv t 0⟩
  · rintro ⟨p, hp⟩ t
    have hx : x = fun _ : ℝ => p := by
      funext s
      exact hp s
    rw [hx]
    exact hasDerivAt_const t p

/-- Discriminating countermodel to "at a definite place at each instant,
therefore stationary": x(t) = t is continuous, has a definite position at
every instant and velocity 1 everywhere, but is not stationary. -/
theorem positionAtEveryInstant_not_rest :
    ∃ x : Trajectory, Continuous x ∧
      (∀ t, ∃ p, x t = p) ∧
      (∀ t, HasDerivAt x 1 t) ∧ ¬ Stationary x := by
  refine ⟨id, continuous_id, ?_, ?_, ?_⟩
  · intro t
    exact ⟨t, rfl⟩
  · intro t
    exact hasDerivAt_id t
  · rintro ⟨p, hp⟩
    have h0 : (0 : ℝ) = p := hp 0
    have h1 : (1 : ℝ) = p := hp 1
    linarith

/-- A second countermodel to "velocity zero now, therefore stationary":
x(t) = t² has zero velocity at t=0 yet moves between 0 and 1. -/
theorem zeroVelocityAtOneInstant_not_stationary :
    ∃ x : Trajectory, InstantaneousRest x 0 ∧ ¬ Stationary x := by
  refine ⟨(fun t : ℝ => t ^ 2), ?_, ?_⟩
  · unfold InstantaneousRest
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  · rintro ⟨p, hp⟩
    have h0 := hp 0
    have h1 := hp 1
    norm_num at h0 h1
    linarith

/-- The n-th interior cut of repeated bisection of the interval [0,1]:
1/2, 3/4, 7/8, ... . These are *mathematical* positions, not acts. Reuse
the previously verified `zenoStageTime`, skipping its initial point 0. -/
noncomputable def bisectionCut (n : ℕ) : ℝ :=
  zenoStageTime (n + 1)

/-- Strict monotonicity from the existing convergent-schedule proposition
gives an injection of cut indices into real positions. -/
theorem bisectionCut_injective (schedule : ConvergentZenoSchedule) :
    Function.Injective bisectionCut := by
  intro m n heq
  exact Nat.add_right_cancel (schedule.1.injective heq)

/-- The first n possible cut positions form a *finite* set. -/
noncomputable def firstBisectionCuts (n : ℕ) : Finset ℝ := by
  classical
  exact (Finset.range n).image bisectionCut

/-- At every finite depth there are precisely n distinct cut positions.
No total physical operation count is part of this assertion. -/
theorem firstBisectionCuts_card (schedule : ConvergentZenoSchedule) (n : ℕ) :
    (firstBisectionCuts n).card = n := by
  classical
  unfold firstBisectionCuts
  rw [Finset.card_image_of_injective (Finset.range n) (bisectionCut_injective schedule)]
  simp

/-- The very same model also has an infinite set of all mathematical cuts.
Therefore arbitrary finite divisibility and an actually infinite *set* are
compatible in classical real analysis. Aristotle's denied physical/separable
actuality is not the `Set.Infinite` predicate. -/
theorem mathematicalBisectionCuts_infinite (schedule : ConvergentZenoSchedule) :
    (Set.range bisectionCut).Infinite :=
  Set.infinite_range_of_injective (bisectionCut_injective schedule)

/-- No *finite* roster of performed operation times covers every cut.
Finiteness is an explicit added condition, not a consequence of physics. -/
theorem finiteOperationRoster_missesCut (schedule : ConvergentZenoSchedule)
    (performed : Finset ℝ) :
    ∃ n, bisectionCut n ∉ performed := by
  rcases (mathematicalBisectionCuts_infinite schedule).exists_notMem_finset performed with
    ⟨_, ⟨n, rfl⟩, hn⟩
  exact ⟨n, hn⟩

/-- A countermodel to the unsupported identification of mathematical cuts
with performed physical operations: the entire infinite cut set exists, while
the independently interpreted operation-event set is empty. This does not
say that *all* physically possible event sets are finite or empty. -/
theorem infiniteCuts_withoutPerformedOperations (schedule : ConvergentZenoSchedule) :
    ∃ performed : Set ℝ,
      (Set.range bisectionCut).Infinite ∧
      ¬ (∀ n, bisectionCut n ∈ performed) := by
  refine ⟨∅, mathematicalBisectionCuts_infinite schedule, ?_⟩
  intro h
  have h0 : bisectionCut 0 ∈ (∅ : Set ℝ) := h 0
  simpa using h0

/-- Dichotomy: a continuous position x(t)=t encounters every checkpoint
strictly before the endpoint and still reaches position 1 at time 1.
This defeats the bare inference from unboundedly many intermediate
mathematical positions to nonarrival. -/
theorem dichotomy_reachesEndpoint (schedule : ConvergentZenoSchedule) :
    ∃ x : Trajectory, Continuous x ∧
      (∀ n, x (zenoStageTime n) < x 1) ∧
      Tendsto (fun n => x (zenoStageTime n)) atTop (𝓝 (x 1)) ∧
      x 1 = 1 := by
  refine ⟨id, continuous_id, ?_, ?_, rfl⟩
  · intro n
    exact schedule.2.1 n
  · simpa only [id, zenoMomentTime] using schedule.2.2.1

/-- Achilles: two continuous linear trajectories, with the slower runner
initially one position ahead. At every listed pre-catch checkpoint the slower
runner remains ahead, yet the faster catches it at t=1. The sequence of
comparisons is not an exhaustive quantification over all real times. -/
theorem achilles_catchesAtLimit (schedule : ConvergentZenoSchedule) :
    ∃ fast slow : Trajectory,
      Continuous fast ∧ Continuous slow ∧
      (∀ n, fast (zenoStageTime n) < slow (zenoStageTime n)) ∧
      fast 1 = slow 1 := by
  refine ⟨(fun t : ℝ => 2 * t), (fun t : ℝ => 1 + t), ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul continuous_id
  · exact continuous_const.add continuous_id
  · intro n
    change (2 : ℝ) * zenoStageTime n < 1 + zenoStageTime n
    linarith [schedule.2.1 n]
  · norm_num

end TruthCore.Greek.Aristotle.Physics.Typed.Zeno
