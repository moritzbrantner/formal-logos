module

public import TruthCore.Causality.AttenuationFit
public import TruthCore.Results.Causality.ConcreteRootAccess.Solution

/-! Fitting the quantitative reception witnesses to finite root access in the
same profile and world. Analyst construction, attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Causality.AttenuationFit

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.ClosedGroundingRoots
open TruthCore.Causality.ConcreteRootAccess (RootAccess)
open scoped BigOperators

variable {W B : Type}

/-- Retain an exact edge count in the existing finite root-access construction. -/
private inductive RootPathLength (m : Profile W B) (w : W) : ℕ → B → Prop
  | root {x} : ActualRoot m w x → RootPathLength m w 0 x
  | step {n y x} : RootPathLength m w n y → ActualConcrete m w x →
      ActualConcreteGround m w y x → RootPathLength m w (n + 1) x

private theorem rootPathHasLength {m : Profile W B} {w : W} {x : B}
    (h : RootAccess m w x) : ∃ n, RootPathLength m w n x := by
  induction h with
  | root hroot => exact ⟨0, .root hroot⟩
  | step _ hActual hGround ih =>
    obtain ⟨n, hPath⟩ := ih
    exact ⟨n + 1, .step hPath hActual hGround⟩

private theorem rootPathPredecessor {m : Profile W B} {w : W} {n : ℕ} {x : B}
    (h : RootPathLength m w n x) (hNonroot : ¬ ActualRoot m w x) :
    ∃ k y, n = k + 1 ∧ RootPathLength m w k y ∧ ActualConcreteGround m w y x := by
  cases h with
  | root hroot => exact (hNonroot hroot).elim
  | step hPath _ hGround => exact ⟨_, _, rfl, hPath, hGround⟩

/-- On countable actual concreta, closed-collection rootedness admits a fitted
attenuation profile. The amount is `(1/2)^d` at shortest root-path length `d`.
Each nonroot receives weight `1/2` from one predecessor on a shortest path,
and each root has own input one. Both common amount bound and row bound are
fixed independently of how large any individual path length can be. -/
theorem attenuationOfClosedRooted (m : Profile W B) (w : W)
    (hCount : Countable {x // ActualConcrete m w x})
    (hClosed : ClosedGroundingCollectionsRooted m w) : AttenuatedEsseReception m w := by
  classical
  let V := {x // ActualConcrete m w x}
  have reaches (v : V) : ∃ n, RootPathLength m w n v.val :=
    rootPathHasLength (ConcreteRootAccess.accessOfClosed m w hClosed Classical.em v.val v.property)
  let depth (v : V) : ℕ := Nat.find (reaches v)
  have rootDepth (v : V) (hRoot : ActualRoot m w v.val) : depth v = 0 :=
    Nat.eq_zero_of_le_zero (Nat.find_min' (reaches v) (.root hRoot))
  have hasPredecessor (v : V) (hNonroot : ¬ ActualRoot m w v.val) :
      ∃ u : V, m.grounds w u.val v.val ∧ depth v = depth u + 1 := by
    obtain ⟨n, y, hDepth, hPath, hGround⟩ :=
      rootPathPredecessor (Nat.find_spec (reaches v)) hNonroot
    let u : V := ⟨y, hGround.1, hGround.2.1⟩
    have shortened : depth u ≤ n := Nat.find_min' (reaches u) hPath
    have extended : depth v ≤ depth u + 1 :=
      Nat.find_min' (reaches v) (.step (Nat.find_spec (reaches u)) v.property hGround)
    exact ⟨u, hGround.2.2, by change depth v = n + 1 at hDepth; omega⟩
  let predecessor (v : V) (h : ¬ ActualRoot m w v.val) : V :=
    (hasPredecessor v h).choose
  let P (v : V) : ℝ := (1 / 2 : ℝ) ^ depth v
  let s (v : V) : ℝ := if ActualRoot m w v.val then 1 else 0
  let wt (v u : V) : ℝ :=
    if h : ¬ ActualRoot m w v.val then
      if u = predecessor v h then 1 / 2 else 0
    else 0
  have sumRow (a : V → ℝ) (v : V) :
      HasSum (fun u => wt v u * a u)
        (if h : ¬ ActualRoot m w v.val then (1 / 2 : ℝ) * a (predecessor v h) else 0) := by
    by_cases h : ¬ ActualRoot m w v.val
    · rw [dite_eq_left h]
      convert hasSum_ite_eq (predecessor v h) ((1 / 2 : ℝ) * a (predecessor v h)) using 1
      funext u
      by_cases hu : u = predecessor v h
      · subst u
        simp [wt, h]
      · simp [wt, h, hu]
    · have hRoot : ActualRoot m w v.val := not_not.mp h
      simp [wt, hRoot]
  have sumWeights (v : V) : HasSum (wt v)
      (if ¬ ActualRoot m w v.val then (1 / 2 : ℝ) else 0) := by
    simpa only [mul_one, dite_eq_ite] using sumRow (fun _ => 1) v
  refine ⟨hCount, wt, s, P, 1 / 2, 1, by norm_num, by norm_num, by norm_num,
    ?_, ?_, ?_, fun v => (sumWeights v).summable, ?_, fun v => (sumRow P v).summable,
    ?_, ?_, ?_, ?_⟩
  · intro v u
    dsimp [wt]
    split
    · split <;> norm_num
    · norm_num
  · intro v
    dsimp [s]
    split <;> norm_num
  · intro v
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · intro v
    rw [(sumWeights v).tsum_eq]
    split <;> norm_num
  · intro v
    rw [(sumRow P v).tsum_eq]
    by_cases h : ActualRoot m w v.val
    · simp [s, P, h, rootDepth v h]
    · have hDepth := (hasPredecessor v h).choose_spec.2
      simp only [s, ite_eq_right h, zero_add, dite_eq_left h]
      change (1 / 2 : ℝ) ^ depth v ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ depth (predecessor v h)
      change depth v = depth (predecessor v h) + 1 at hDepth
      rw [hDepth, pow_succ, mul_comm]
  · intro v u hPositive
    by_cases h : ¬ ActualRoot m w v.val
    · by_cases hu : u = predecessor v h
      · subst u
        exact (hasPredecessor v h).choose_spec.1
      · simp [wt, h, hu] at hPositive
    · have hRoot : ActualRoot m w v.val := not_not.mp h
      simp [wt, hRoot] at hPositive
  · intro v hPositive
    by_cases h : ActualRoot m w v.val
    · exact h.2
    · simp [s, h] at hPositive
  · intro v
    exact pow_pos (by norm_num) _

/-- When the quantitative witnesses are existentially chosen, attenuation has
exactly the content of countability and closed-collection rootedness. -/
theorem attenuationIffCountableAndClosedRooted (m : Profile W B) (w : W) :
    AttenuationFitCriterion m w :=
  ⟨fun h => ⟨h.1, ClosedGroundingRoots.closedRootedOfAttenuation m w h⟩,
    fun h => attenuationOfClosedRooted m w h.1 h.2⟩

open TruthCore.Causality.ClosedGroundingRoots.FixedAmounts

/-- A recipient with just one supplier must have less of the specified amount. -/
theorem amount_lt_sole_supplier {W B : Type} {m : Profile W B} {w : W}
    {wt s P q M} (laws : AttenuationLaws m w wt s P q M)
    (source recipient : {x // ActualConcrete m w x})
    (supplies : m.grounds w source.1 recipient.1)
    (sole : ∀ u : {x // ActualConcrete m w x}, m.grounds w u.1 recipient.1 → u = source) :
    P recipient < P source := by
  obtain ⟨_, hq, _, hw, hs, _, _, hr, _, hb, edge, own, positive⟩ := laws
  have noWeight (u) (hne : u ≠ source) : wt recipient u = 0 := by
    exact le_antisymm (le_of_not_gt fun h => hne (sole u (edge recipient u h))) (hw _ _)
  have hsup : ActualConcreteGround m w source.1 recipient.1 :=
    ⟨source.2.1, source.2.2, supplies⟩
  have noOwn : s recipient = 0 := le_antisymm
    (le_of_not_gt fun h => own recipient h source.1 hsup) (hs _)
  have weightBound := hr recipient
  rw [tsum_eq_single source noWeight] at weightBound
  have balance := hb recipient
  rw [noOwn, zero_add, tsum_eq_single source (fun u h => by rw [noWeight u h, zero_mul])] at balance
  exact balance.trans_lt (by simpa using mul_lt_mul_of_pos_right (weightBound.trans_lt hq) (positive source))

/-- With positive amounts fixed first, the full reception constraints on this graph
admit a choice of weights, inputs and bounds exactly when the recipient has less. -/
theorem fixedAmountCriterion : FixedAmounts.FixedAmountCriterion := by
  intro P pos
  constructor
  · rintro ⟨wt, s, q, M, h⟩
    exact amount_lt_sole_supplier h giver recipient ⟨rfl, rfl⟩
      (fun _ hu => Subtype.ext hu.1)
  · intro strict
    classical
    let q := P recipient / P giver
    have nonneg : 0 ≤ q := (div_pos (pos _) (pos _)).le
    have loss : q < 1 := (div_lt_one (pos giver)).2 strict
    have transfer : q * P giver = P recipient := div_mul_cancel₀ _ (pos giver).ne'
    let wt := fun (v u : Bearer) => if v = recipient ∧ u = giver then q else 0
    let s := fun v : Bearer => if v = giver then P giver else 0
    have exhaust (v : Bearer) : v = giver ∨ v = recipient := by
      rcases v with ⟨_ | _, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    have distinct : giver ≠ recipient := by decide
    have single (v u : Bearer) (h : u ≠ giver) : wt v u = 0 := by simp [wt, h]
    refine ⟨wt, s, q, P giver, nonneg, loss, (pos _).le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, pos⟩
    · intro v u
      simp only [wt]
      split <;> simp [nonneg]
    · intro v
      simp only [s]
      split <;> simp [(pos giver).le]
    · intro v
      rcases exhaust v with rfl | rfl
      · exact le_rfl
      · exact strict.le
    · intro v
      exact Summable.of_finite
    · intro v
      rw [tsum_eq_single giver (single v)]
      simp only [wt]
      split <;> simp [nonneg]
    · intro v
      exact Summable.of_finite
    · intro v
      rw [tsum_eq_single giver (fun u h => by rw [single v u h, zero_mul])]
      rcases exhaust v with rfl | rfl
      · simp [s, wt, distinct]
      · simp [s, wt, distinct.symm, transfer]
    · intro v u h
      by_cases hEdge : v = recipient ∧ u = giver
      · rcases hEdge with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      · simp [wt, hEdge] at h
    · intro v h y hy
      by_cases hv : v = giver
      · subst v
        exact Bool.noConfusion hy.2.2.2
      · simp [s, hv] at h

end TruthCore.Results.Causality.AttenuationFit
