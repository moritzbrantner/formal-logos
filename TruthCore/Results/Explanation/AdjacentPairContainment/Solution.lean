module

public import TruthCore.Explanation.AdjacentPairContainment
public import TruthCore.Results.Explanation.NoFoundationLawChaos.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.AdjacentPairContainment

open TruthCore.Explanation.AdjacentPairContainment
open TruthCore.Explanation.NoFoundationLawChaos
open TruthCore.Explanation.LawActuality (UsesRecord)
open TruthCore.Epistemology.UltimateExplanation (Profile Follows)
open TruthCore.Modern.Hume.Induction (Trace)

private theorem pair_profile (allowed : Trace → Prop) (n : Nat) :
    AdjacentPairRich allowed n ↔ ProfileObstruction allowed n := by
  classical
  constructor
  · intro h q hq t a b ht
    obtain ⟨f, hf, ha, hb⟩ := h t a b ht
    simpa only [ha, hb] using (hq f hf).2 t
  · intro h t a b ht
    by_contra missing
    -- This is an extensional exclusion, not a new governing-law claim.
    let q : Profile := ⟨true, fun s x y => s = t → x = a → y ≠ b⟩
    have hq : ∀ f, Admitted allowed n f → Follows q f := by
      intro f hf
      refine ⟨hf.1.1.1, ?_⟩
      intro s hs ha hb
      subst s
      exact missing ⟨f, hf, ha, hb⟩
    exact (h q hq t a b ht) rfl rfl rfl

private theorem bit_forecast (allowed : Trace → Prop) (n k : Nat) :
    BitRich allowed n k ↔ ForecastObstruction allowed n k := by
  classical
  constructor
  · intro rich predict record uniform
    obtain ⟨f, hf, hfalse⟩ := rich false
    obtain ⟨g, hg, htrue⟩ := rich true
    have same : predict f = predict g := record f g (fun i hi =>
      (hf.1.2 i hi).trans (hg.1.2 i hi).symm)
    have impossible : f k = g k :=
      (uniform f hf).symm.trans (same.trans (uniform g hg))
    rw [hfalse, htrue] at impossible
    exact Bool.noConfusion impossible
  · intro obstruction b
    by_contra missing
    apply obstruction (fun _ => !b) (fun _ _ _ => rfl)
    intro f hf
    have different : f k ≠ b := fun h => missing ⟨f, hf, h⟩
    cases b <;> cases value : f k <;> simp_all

private theorem finite_pair (allowed : Trace → Prop) (n : Nat)
    (rich : FiniteRich allowed n) : AdjacentPairRich allowed n := by
  intro t a b ht
  let tail : Trace := fun i => if i = t then a else b
  obtain ⟨f, hf, agrees⟩ := rich tail (t+1)
  refine ⟨f, hf, ?_, ?_⟩
  · calc
      f t = splice n tail t := agrees t (by omega)
      _ = a := by simp [splice, tail, show ¬ t < n+1 by omega]
  · calc
      f (t+1) = splice n tail (t+1) := agrees (t+1) (Nat.le_refl _)
      _ = b := by simp [splice, tail, show ¬ t+1 < n+1 by omega]

private theorem pair_bit (allowed : Trace → Prop) (n : Nat)
    (rich : AdjacentPairRich allowed n) (k : Nat) (hk : n+1 ≤ k) :
    BitRich allowed n k := by
  intro b
  obtain ⟨f, hf, hb, _⟩ := rich k b false hk
  exact ⟨f, hf, hb⟩

theorem exposureCertificate : ExposureCertificate := by
  refine ⟨pair_profile, bit_forecast, finite_pair, pair_bit, ?_⟩
  intro allowed n populated step
  exact finite_pair allowed n
    (TruthCore.Results.Explanation.NoFoundationLawChaos.recombinationFork.1
      allowed n populated step)

private theorem constant_admitted (n : Nat) (b : Bool) :
    Admitted (constantClass n) n (splice n (fun _ => b)) :=
  ⟨TruthCore.Results.Explanation.NoFoundationLawChaos.certificate.2.1 n _,
    ⟨b, rfl⟩⟩

private theorem constant_bit (n k : Nat) (hk : n+1 ≤ k) :
    BitRich (constantClass n) n k := by
  intro b
  exact ⟨splice n (fun _ => b), constant_admitted n b,
    by simp [splice, show ¬ k < n+1 by omega]⟩

private theorem constant_not_pair (n : Nat) :
    ¬ AdjacentPairRich (constantClass n) n := by
  intro rich
  obtain ⟨f, hf, hfalse, htrue⟩ := rich (n+1) false true (Nat.le_refl _)
  obtain ⟨b, rfl⟩ := hf.2
  have same : splice n (fun _ => b) (n+1) =
      splice n (fun _ => b) (n+1+1) := by
    simp [splice, show ¬ n+1+1 < n+1 by omega]
  rw [hfalse, htrue] at same
  exact Bool.noConfusion same

private theorem cycle_pair (k : Nat) (x y : Bool) :
    ∃ a b, parityCycle a b k = x ∧ parityCycle a b (k+1) = y := by
  have cases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases cases with h | h | h
  · have next : (k+1) % 3 = 1 := by omega
    exact ⟨x, y, by simp [parityCycle, h], by simp [parityCycle, next]⟩
  · have next : (k+1) % 3 = 2 := by omega
    have cancel : (x.xor y).xor x = y := by cases x <;> cases y <;> rfl
    exact ⟨x.xor y, x, by simp [parityCycle, h],
      by simpa [parityCycle, next] using cancel⟩
  · have next : (k+1) % 3 = 0 := by omega
    have cancel : y.xor (x.xor y) = x := by cases x <;> cases y <;> rfl
    exact ⟨y, x.xor y, by simpa [parityCycle, h] using cancel,
      by simp [parityCycle, next]⟩

private theorem cycle_rule (a b : Bool) (k : Nat) :
    parityCycle a b (k+2) =
      (parityCycle a b k).xor (parityCycle a b (k+1)) := by
  have cases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases cases with h | h | h
  · have h1 : (k+1) % 3 = 1 := by omega
    have h2 : (k+2) % 3 = 2 := by omega
    simp [parityCycle, h, h1, h2]
  · have h1 : (k+1) % 3 = 2 := by omega
    have h2 : (k+2) % 3 = 0 := by omega
    have cancel : a = b.xor (a.xor b) := by cases a <;> cases b <;> rfl
    simpa [parityCycle, h, h1, h2] using cancel
  · have h1 : (k+1) % 3 = 0 := by omega
    have h2 : (k+2) % 3 = 1 := by omega
    have cancel : b = (a.xor b).xor a := by cases a <;> cases b <;> rfl
    simpa [parityCycle, h, h1, h2] using cancel

private theorem parity_admitted (n : Nat) (a b : Bool) :
    Admitted (parityClass n) n (parityTrace n a b) :=
  ⟨TruthCore.Results.Explanation.NoFoundationLawChaos.certificate.2.1 n _,
    ⟨a, b, rfl⟩⟩

private theorem parity_after (n : Nat) (a b : Bool) (t : Nat)
    (ht : n+1 ≤ t) :
    parityTrace n a b t = parityCycle a b (t-(n+1)) := by
  simp [parityTrace, splice, show ¬ t < n+1 by omega]

private theorem parity_pair (n : Nat) : AdjacentPairRich (parityClass n) n := by
  intro t x y ht
  obtain ⟨a, b, ha, hb⟩ := cycle_pair (t-(n+1)) x y
  refine ⟨parityTrace n a b, parity_admitted n a b, ?_, ?_⟩
  · rw [parity_after n a b t ht]
    exact ha
  · rw [parity_after n a b (t+1) (by omega),
      show t+1-(n+1) = t-(n+1)+1 by omega]
    exact hb

private theorem parity_rule (n : Nat) (f : Trace)
    (hf : Admitted (parityClass n) n f) : TwoStepRule n f := by
  obtain ⟨a, b, rfl⟩ := hf.2
  intro t ht
  rw [parity_after n a b (t+2) (by omega), parity_after n a b t ht,
    parity_after n a b (t+1) (by omega),
    show t+2-(n+1) = t-(n+1)+2 by omega,
    show t+1-(n+1) = t-(n+1)+1 by omega]
  exact cycle_rule a b (t-(n+1))

private theorem parity_seeds (n : Nat) (a b : Bool) :
    parityTrace n a b (n+1) = a ∧ parityTrace n a b (n+2) = b := by
  constructor
  · rw [parity_after n a b (n+1) (Nat.le_refl _)]
    simp [parityCycle]
  · rw [parity_after n a b (n+2) (by omega),
      show n+2-(n+1) = 1 by omega]
    simp [parityCycle]

private theorem parity_unique (n : Nat) (f g : Trace)
    (hf : Admitted (parityClass n) n f) (hg : Admitted (parityClass n) n g)
    (first : f (n+1) = g (n+1)) (second : f (n+2) = g (n+2)) : f = g := by
  obtain ⟨a, b, rfl⟩ := hf.2
  obtain ⟨c, d, rfl⟩ := hg.2
  rw [(parity_seeds n a b).1, (parity_seeds n c d).1] at first
  rw [(parity_seeds n a b).2, (parity_seeds n c d).2] at second
  subst c
  subst d
  rfl

private theorem parity_not_finite (n : Nat) : ¬ FiniteRich (parityClass n) n := by
  intro rich
  obtain ⟨f, hf, agrees⟩ := rich (fun _ => true) (n+3)
  have value : ∀ t, t ≤ n+3 → f t = true := by
    intro t ht
    have h := agrees t ht
    simpa [splice] using h
  have recurrence : f (n+3) = (f (n+1)).xor (f (n+2)) := by
    simpa [Nat.add_assoc] using parity_rule n f hf (n+1) (Nat.le_refl _)
  rw [value (n+3) (Nat.le_refl _), value (n+1) (by omega),
    value (n+2) (by omega)] at recurrence
  exact Bool.noConfusion recurrence

theorem memoryControls : MemoryControls := by
  refine ⟨constant_bit, constant_not_pair, parity_pair, parity_rule,
    parity_unique, ?_⟩
  intro n
  refine ⟨parity_not_finite n, ?_⟩
  intro whole
  exact parity_not_finite n
    (fun tail _ => ⟨splice n tail, whole tail, fun _ _ => rfl⟩)

end TruthCore.Results.Explanation.AdjacentPairContainment
