module
public import Mathlib.Data.Set.Finite.Lattice

public import TruthCore.Logic.RegressHeadcount
public import TruthCore.Results.Causality.WorldSourceRegress.Solution

@[expose] public section

namespace TruthCore.Results.Logic.RegressHeadcount

open TruthCore.Logic.RegressHeadcount

theorem finiteAdditionCriterion (A B : Type) :
    SurvivesEveryFiniteAddition A B ↔ Finite A ∧ Infinite B := by
  constructor
  · intro h
    have smaller : ENat.card A < ENat.card B := by simpa using h 0
    refine ⟨ENat.card_lt_top.mp (smaller.trans_le le_top), ENat.card_eq_top.mp ?_⟩
    by_contra finiteCount
    have impossible := h (ENat.card B).toNat
    rw [ENat.natCast_toNat finiteCount] at impossible
    exact (not_lt_of_ge (le_add_self : ENat.card B ≤ ENat.card A + ENat.card B)) impossible
  · rintro ⟨hA, hB⟩ extra
    let := Fintype.ofFinite A
    simp [ENat.card_eq_coe_fintype_card]

/-- The cardinal reading applies to bearer headcount, or to distinct
independent posits when their assignment is injective along this regress. -/
theorem headcountCriterion : RegressHeadcountCriterion := by
  refine ⟨finiteAdditionCriterion, ?_, (finiteAdditionCriterion Unit ℕ).2 ⟨inferInstance, inferInstance⟩, ?_⟩
  · intro Node Posit Alternative G noCycles chain step charge distinct finiteAlternative
    have noRepeats := TruthCore.Results.Causality.WorldSourceRegress.chain_injective G noCycles chain step
    have injects : Function.Injective (charge ∘ chain) := by
      intro i j equalCharge
      exact noRepeats (distinct ⟨i, rfl⟩ ⟨j, rfl⟩ equalCharge)
    exact (finiteAdditionCriterion Alternative Posit).2
      ⟨finiteAlternative, Infinite.of_injective _ injects⟩
  · rw [Cardinal.mk_eq_aleph0, Cardinal.mk_eq_aleph0]

/-- Billing each pair together still incurs infinitely many distinct charges. -/
theorem pairedCharges :
    ¬ Function.Injective (fun n : ℕ => n / 2) ∧
      SurvivesEveryFiniteAddition Unit (Set.range (fun n : ℕ => n / 2)) := by
  constructor
  · intro injects
    have equal : (0 : ℕ) = 1 := injects (show 0 / 2 = 1 / 2 by decide)
    omega
  · let onePerPair (n : ℕ) : Set.range (fun k : ℕ => k / 2) :=
      ⟨n, 2 * n, by change 2 * n / 2 = n; omega⟩
    have injects : Function.Injective onePerPair := fun _ _ h => congrArg Subtype.val h
    exact (finiteAdditionCriterion _ _).2 ⟨inferInstance, Infinite.of_injective _ injects⟩

/-- An infinite bill with finitely many positions per visited charge requires
infinitely many distinct charges, regardless of how large the finite groups are. -/
theorem finiteFibersChargeInfinitely {Position Posit Alternative : Type} [Infinite Position]
    (billing : Position → Posit)
    (finitePerCharge : ∀ posit ∈ Set.range billing, (billing ⁻¹' {posit}).Finite)
    (finiteAlternative : Finite Alternative) :
    SurvivesEveryFiniteAddition Alternative (Set.range billing) := by
  refine (finiteAdditionCriterion _ _).2 ⟨finiteAlternative, not_finite_iff_infinite.mp ?_⟩
  intro finiteCharges
  have finiteImage : (billing '' Set.univ).Finite := by
    rw [Set.image_univ]
    exact finiteCharges
  have finitePositions := Set.Finite.of_finite_fibers billing (s := Set.univ) finiteImage (by
    intro posit visited
    simpa only [Set.univ_inter] using finitePerCharge posit (by simpa using visited))
  exact Set.infinite_univ finitePositions

/-- An infinite group can coexist with infinitely many distinct visited charges. -/
theorem mixedChargeFibers :
    let billing := fun n : ℕ => if n % 2 = 0 then 0 else n
    (billing ⁻¹' {0}).Infinite ∧
      SurvivesEveryFiniteAddition Unit (Set.range billing) := by
  dsimp only
  constructor
  · let evenPositions (n : ℕ) : {m : ℕ | (if m % 2 = 0 then 0 else m) = 0} :=
      ⟨2 * n, by simp⟩
    have distinct : Function.Injective evenPositions := by
      intro i j samePosition
      have equal : 2 * i = 2 * j := congrArg Subtype.val samePosition
      omega
    exact Set.infinite_coe_iff.mp (Infinite.of_injective _ distinct)
  · let oddCharges (n : ℕ) : Set.range (fun m : ℕ => if m % 2 = 0 then 0 else m) :=
      ⟨2 * n + 1, 2 * n + 1, by simp⟩
    have distinct : Function.Injective oddCharges := by
      intro i j sameCharge
      have equal : 2 * i + 1 = 2 * j + 1 := congrArg Subtype.val sameCharge
      omega
    exact (finiteAdditionCriterion _ _).2 ⟨inferInstance, Infinite.of_injective _ distinct⟩

end TruthCore.Results.Logic.RegressHeadcount
