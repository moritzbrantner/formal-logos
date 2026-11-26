module
public import TruthCore.Causality.ProductiveStore

/-! Energy accounting for one store starting at the cut, with boundary input
split into a named candidate feed and the aggregate of all other feeds. -/
@[expose] public section
namespace TruthCore.Causality.PostCutStore

open scoped BigOperators

def prefixSum (flow : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, flow t

/-- The audits constrain stocks through N and flows strictly before N.
The upper stock bound applies at time zero. Output is total work
and heat in one common energy unit, as in `ProductiveStore`. -/
def ObservationLedger (N : ℕ) (cap : ℝ)
    (lower upper stock output other candidate : ℕ → ℝ) : Prop :=
  stock 0 ≤ cap ∧
  (∀ t ≤ N, 0 ≤ stock t) ∧
  ∀ t < N, 0 ≤ output t ∧ 0 ≤ other t ∧ 0 ≤ candidate t ∧
    lower t ≤ output t ∧ other t ≤ upper t ∧
    stock (t + 1) + output t = stock t + (other t + candidate t)

/-- Characterizes finite observations permitting zero named replenishment. -/
def ZeroCandidateCriterion : Prop :=
  ∀ (N : ℕ) (cap : ℝ) (lower upper : ℕ → ℝ),
    0 ≤ cap → (∀ t < N, 0 ≤ lower t) → (∀ t < N, 0 ≤ upper t) →
    ((∃ stock output other : ℕ → ℝ,
         ObservationLedger N cap lower upper stock output other (fun _ => 0)) ↔
      ∀ n ≤ N, prefixSum lower n ≤ cap + prefixSum upper n)

/-- Every compatible ledger owes at least the prefix deficit to the named
feed, and a strictly positive deficit forces a positive interval of that feed. -/
def CandidateReplenishmentBound : Prop :=
  ∀ (N : ℕ) (cap : ℝ) (lower upper stock output other candidate : ℕ → ℝ),
    ObservationLedger N cap lower upper stock output other candidate →
    ∀ n ≤ N,
      prefixSum lower n - (cap + prefixSum upper n) ≤ prefixSum candidate n ∧
      (cap + prefixSum upper n < prefixSum lower n → ∃ t < n, 0 < candidate t)

end TruthCore.Causality.PostCutStore
