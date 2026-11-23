module

public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Tactic.Linarith
public import TruthCore.Causality.FiniteBranching
public import TruthCore.Greek.Aristotle.Physics.Typed.Zeno

/-!
# Indexed operations, compact time, and local finiteness (#1859)

This is an **analyst model** of operation occurrences, not a definition of
physical causation. A time assignment may have multiple operation indices at
one timestamp. Mathlib's `LocallyFinite` counts *indices*, unlike a condition
on the range of timestamps.

The compact-time theorem is conditional: whether real physical operations
satisfy the indexed local-finiteness premise is open. The existing real Zeno
clock supplies an explicit failure at its endpoint; a strictly decreasing
negative-integer clock supplies a locally finite *infinite* causal ancestry.
Neither time precedence nor a mathematical checkpoint is an essentially
ordered efficient cause merely by its name.
-/

@[expose] public section

namespace TruthCore.Causality.OperationLocalFiniteness

open Set Filter Topology
open TruthCore.Causality
open TruthCore.Greek.Aristotle.Physics.Typed.Zeno

/-- Each distinct operation is indexed by its identity, even when two
operations have the same real-valued timestamp. This is precisely Mathlib's
`LocallyFinite` applied to the indexed singleton family, not an alternative
topological definition and not an empirical premise about physical events. -/
def LocallyFiniteOperationTimes {Operation : Type} (time : Operation → ℝ) : Prop :=
  LocallyFinite (fun op : Operation => ({time op} : Set ℝ))

/-- Only finitely many *operation indices*, not merely distinct time values,
can occur in any closed bounded clock interval if the entire indexed
singleton family is locally finite in the ambient real clock. The
topological premise applies at boundary instants, including the endpoint. -/
theorem finite_operations_in_compact_interval {Operation : Type}
    (time : Operation → ℝ) (hlocal : LocallyFiniteOperationTimes time)
    (a b : ℝ) :
    {op : Operation | time op ∈ Set.Icc a b}.Finite := by
  have hfinite :
      {op : Operation | (({time op} : Set ℝ) ∩ Set.Icc a b).Nonempty}.Finite :=
    LocallyFinite.finite_nonempty_inter_compact hlocal isCompact_Icc
  apply hfinite.subset
  intro op ht
  exact ⟨time op, ⟨rfl, ht⟩⟩

/-- A bounded locally finite *whole operation roster* is finite, without
requiring injective timestamps or a positive minimum per-operation duration. -/
theorem finite_operations_of_bounded {Operation : Type} (time : Operation → ℝ)
    (hlocal : LocallyFiniteOperationTimes time) (a b : ℝ)
    (hbounded : ∀ op, time op ∈ Set.Icc a b) :
    (Set.univ : Set Operation).Finite :=
  (finite_operations_in_compact_interval time hlocal a b).subset
    (fun op _ => hbounded op)

/-- Separate the general conditional theorem from a stipulation about
whether any concrete history satisfies its local-finiteness antecedent. -/
def CompactOperationCountCertificate : Prop :=
  ∀ (Operation : Type) (time : Operation → ℝ) (a b : ℝ),
    LocallyFiniteOperationTimes time →
      {op : Operation | time op ∈ Set.Icc a b}.Finite

/-- The original Zeno stage times tend to 1; thus *every* neighborhood of 1
meets infinitely many distinct stage indices. Failure is at the endpoint, not
a failure of mathematical convergence. -/
theorem zeno_not_locallyFinite_at_endpoint (schedule : ConvergentZenoSchedule) :
    ¬ ∃ U : Set ℝ, U ∈ 𝓝 (1 : ℝ) ∧
      {n : ℕ | (({zenoStageTime n} : Set ℝ) ∩ U).Nonempty}.Finite := by
  rintro ⟨U, hU, hfinite⟩
  have htend : Tendsto zenoStageTime atTop (𝓝 (1 : ℝ)) := by
    simpa only [zenoMomentTime] using schedule.2.2.1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually hU)
  have htail : (Set.Ici N : Set ℕ).Finite := by
    apply hfinite.subset
    intro n hn
    exact ⟨zenoStageTime n, ⟨rfl, hN n hn⟩⟩
  have hcompl : ((Set.Ici N : Set ℕ)ᶜ).Finite := by
    simpa only [Set.compl_Ici] using (Set.finite_Iio N)
  exact (Set.infinite_of_finite_compl hcompl) htail

/-- At each time strictly before the endpoint there is a neighborhood
meeting only finitely many Zeno stage indices. Thus the same schedule
satisfies local finiteness away from 1 but fails it at 1. -/
theorem zeno_locallyFinite_below_endpoint (schedule : ConvergentZenoSchedule)
    (x : ℝ) (hx : x < 1) :
    ∃ U : Set ℝ, U ∈ 𝓝 x ∧
      {n : ℕ | (({zenoStageTime n} : Set ℝ) ∩ U).Nonempty}.Finite := by
  have htend : Tendsto zenoStageTime atTop (𝓝 (1 : ℝ)) := by
    simpa only [zenoMomentTime] using schedule.2.2.1
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (htend.eventually (Ioi_mem_nhds hx))
  have hnx : x < zenoStageTime N := hN N le_rfl
  refine ⟨Set.Iio (zenoStageTime N), Iio_mem_nhds hnx, ?_⟩
  apply (Set.finite_Iio N).subset
  intro n hn
  obtain ⟨t, hsingle, hlt⟩ := hn
  have heq : t = zenoStageTime n := by simpa using hsingle
  have hstrict : zenoStageTime n < zenoStageTime N := by
    simpa only [Set.mem_Iio, heq] using hlt
  by_contra hnot
  have hge : N ≤ n := Nat.le_of_not_lt hnot
  exact (not_lt_of_ge (schedule.1.monotone hge)) hstrict

/-- Although all natural-number-indexed operations have the *same*
timestamp, their set of timestamps is finite while the indexed family is
not locally finite. Set-range cardinality forgets occurrence identity. -/
theorem finite_timestamps_infinite_operation_multiplicity :
    (Set.range (fun _ : ℕ => (0 : ℝ))).Finite ∧
    ¬ LocallyFiniteOperationTimes (fun _ : ℕ => (0 : ℝ)) := by
  constructor
  · apply (Set.finite_singleton (0 : ℝ)).subset
    rintro t ⟨n, rfl⟩
    exact Set.mem_singleton_iff.mpr rfl
  · intro hlocal
    have hfinite : (Set.univ : Set ℕ).Finite :=
      finite_operations_of_bounded (fun _ : ℕ => (0 : ℝ)) hlocal 0 1
        (by intro n; norm_num)
    exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) hfinite

/-- All the bisecting checkpoints are crossed by one continuously moving,
unit-velocity trajectory. Treating every selected crossing as an *additional
operation* yields a non-locally-finite indexed family. This does not assign
distinct constitutive physical acts to the crossings. -/
theorem smooth_motion_with_nonlocal_checkpoint_indices (schedule : ConvergentZenoSchedule) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => s) 1 t) ∧
    (∀ n : ℕ, (fun s : ℝ => s) (bisectionCut n) = bisectionCut n) ∧
    ¬ LocallyFiniteOperationTimes bisectionCut := by
  refine ⟨fun t => hasDerivAt_id t, fun n => rfl, ?_⟩
  intro hlocal
  have hbounded : ∀ n, bisectionCut n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    constructor
    · have hmono : zenoStageTime 0 ≤ zenoStageTime (n + 1) :=
        schedule.1.monotone (Nat.zero_le (n + 1))
      simpa only [bisectionCut, zenoStageTime, pow_zero, sub_self] using hmono
    · exact (schedule.2.1 (n + 1)).le
  have hfinite := finite_operations_of_bounded bisectionCut hlocal 0 1 hbounded
  exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) hfinite

/-- A beginningless, discrete clock with unbounded negative times. -/
def backwardClock (n : ℕ) : ℝ := -(n : ℝ)

/-- Unlike the convergent Zeno clock, an infinite backward clock with times
0, -1, -2, ... is locally finite in the full real topology. -/
theorem backwardClock_locallyFinite :
    LocallyFiniteOperationTimes backwardClock := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (1 - x)
  refine ⟨Set.Ioo (x - 1) (x + 1),
    Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (Set.finite_Iio N).subset
  intro n hn
  obtain ⟨t, hsingle, hinterval⟩ := hn
  have heq : t = backwardClock n := by simpa using hsingle
  have hreal : (n : ℝ) < (N : ℝ) := by
    have hleft : x - 1 < t := hinterval.1
    rw [heq] at hleft
    dsimp [backwardClock] at hleft
    linarith
  exact_mod_cast hreal

/-- SAME causal relation as `FiniteBranching.successorPredecessor`:
the next natural index is a direct upstream cause of the current one. Each
upstream cause is strictly earlier in the backward clock, the occurrence
times are locally finite, yet the causal predecessor relation is not
well-founded. Boundedness of elapsed duration is not assumed. -/
theorem locallyFiniteTimes_with_infiniteCausalAncestry :
    LocallyFiniteOperationTimes backwardClock ∧
    (∀ n, backwardClock (n + 1) < backwardClock n ∧
      FiniteBranching.successorPredecessor (n + 1) n) ∧
    ¬ WellFounded FiniteBranching.successorPredecessor := by
  refine ⟨backwardClock_locallyFinite, ?_, FiniteBranching.successorPredecessorNotWellFounded⟩
  intro n
  constructor
  · dsimp [backwardClock]
    push_cast
    linarith
  · rfl

end TruthCore.Causality.OperationLocalFiniteness
