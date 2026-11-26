module

public import TruthCore.Causality.SupplierAuditLikelihood
public import TruthCore.Results.Causality.PerSeRegressCardinality.Solution

@[expose] public section
namespace TruthCore.Results.Causality.SupplierAuditLikelihood

open TruthCore.Causality.FiniteReserveOdds
open TruthCore.Causality.PerSeRegressCardinality (asCaused)
open TruthCore.Causality.SupplierAudit
open TruthCore.Causality.SupplierAuditLikelihood
open TruthCore.Latin.Aquinas.SummaTheologiae
  (IsFirstEfficientCause NoInfinitePerSeEfficientCauseSeriesReading)
open TruthCore.Results.Causality.PerSeRegressCardinality (successorOrientationAndFiniteCycle)

private theorem prefixMatchesSourced (length depth : ℕ) :
    PrefixMatches length (sourced depth) ↔ length ≤ depth := by
  constructor
  · intro agrees
    by_contra notLe
    have audited : depth ∈ Set.Iio length := Nat.lt_of_not_le notLe
    obtain ⟨supplier, edge⟩ := endlessBorrower depth
    exact (oneRoot depth depth).mpr rfl supplier ((agrees depth audited supplier).mp edge)
  · intro le recipient audited supplier
    exact (sameLists depth recipient supplier (Nat.lt_of_lt_of_le audited le)).symm

private theorem likelihoodEqualsReserve (fits : ∀ depth length, UnitTraceFits depth length ↔
    length ≤ depth) (prior : ℕ → ℝ) (length : ℕ) :
    depthLikelihood prior length = reserveLikelihood prior length := by
  classical
  simp only [depthLikelihood, reserveLikelihood, prefixMatchesSourced, fits]

theorem prefixComparison (reserve : FiniteReserveComparison) : PrefixComparison := by
  have sameLikelihood := likelihoodEqualsReserve reserve.1
  refine ⟨prefixMatchesSourced, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro length
    exact ⟨fun _ _ _ => Iff.rfl, (prefixMatchesSourced length length).mpr le_rfl,
      sourcedReaches length 0, (oneRoot length length).mpr rfl⟩
  · intro observed depth
    constructor
    · exact fun agrees => ((oneRoot depth observed).mp agrees.2).symm
    · intro equal
      subst depth
      exact ⟨(prefixMatchesSourced observed observed).mpr le_rfl, (oneRoot observed observed).mpr rfl⟩
  · intro observed agrees
    obtain ⟨supplier, edge⟩ := endlessBorrower observed
    exact agrees.2 supplier edge
  · intro length
    let concentrated (depth : ℕ) : ℝ := if depth = length then 1 else 0
    have proper : HasSum concentrated 1 := hasSum_ite_eq length 1
    refine ⟨concentrated, fun depth => by unfold concentrated; split_ifs <;> norm_num,
      proper, ?_⟩
    classical
    unfold depthLikelihood
    refine (tsum_congr fun depth => ?_).trans proper.tsum_eq
    rw [prefixMatchesSourced]
    by_cases equal : depth = length
    · simp [equal]
    · simp [concentrated, equal]
  · intro prior nonnegative proper
    obtain ⟨mass, dominance⟩ := reserve.2.1 prior nonnegative proper
    refine ⟨fun length => (sameLikelihood prior length).trans (mass length), ?_⟩
    intro finiteWeight endlessWeight factor finitePos endlessPos factorPos
    have likelihoodBounds length :
        0 ≤ depthLikelihood prior length ∧
          depthLikelihood prior length ≤ reserveLikelihood prior length := by
      classical
      refine ⟨tsum_nonneg fun depth => ?_, (sameLikelihood prior length).le⟩
      split_ifs
      · exact nonnegative depth
      · exact le_rfl
    simpa only [mul_one] using dominance finiteWeight endlessWeight 1
      (depthLikelihood prior) (fun _ => 1) finitePos endlessPos zero_lt_one
      likelihoodBounds (fun _ => ⟨le_rfl, le_rfl⟩) factor factorPos
  · obtain ⟨proper, positive, control⟩ := reserve.2.2
    refine ⟨proper, positive, fun length => ?_⟩
    simpa only [sameLikelihood] using control length

/-- Interpret the audited supplies as efficient edges in one respect. The
as-caused relation filters those edges by whether the supplier is itself caused. -/
theorem selectedRegressControl :
    (∀ depth, NoInfinitePerSeEfficientCauseSeriesReading (asCaused (sourced depth)) ∧
      IsFirstEfficientCause (fun supplier recipient (_ : Unit) =>
        sourced depth supplier recipient) depth) ∧
    (¬ NoInfinitePerSeEfficientCauseSeriesReading (asCaused endless)) ∧
    ∀ d, (∀ y, ¬ asCaused (sourced (d + 1)) y d) ∧ sourced (d + 1) (d + 1) d := by
  refine ⟨?_, successorOrientationAndFiniteCycle.2.1.2.2.2.1, ?_⟩
  · intro depth
    let distance (x : ℕ) := if depth < x then 1 else depth - x
    have decrease {y x} (edge : sourced depth y x) : distance y < distance x := by
      rcases edge with ⟨below, rfl⟩ | ⟨above, rfl⟩ <;> simp only [distance] <;> split_ifs <;> omega
    refine ⟨(Subrelation.wf (fun h => decrease h.1) (measure distance).wf).apply, ?_⟩
    exact ⟨⟨depth + 1, (), Or.inr ⟨Nat.lt_succ_self depth, rfl⟩⟩,
      fun supplier _ => (oneRoot depth depth).mpr rfl supplier⟩
  · intro d
    constructor
    · intro y ⟨edge, z, supply⟩
      rcases edge with ⟨_, rfl⟩ | ⟨bad, _⟩
      · exact (oneRoot _ _).mpr rfl z supply
      · omega
    · exact Or.inl ⟨Nat.lt_succ_self _, rfl⟩

private theorem conditionalRatio (prior : ℕ → ℝ) (new observed : ℕ) :
    conditionalDepthLikelihood prior new observed =
      depthLikelihood prior (max new observed) / depthLikelihood prior observed := by
  classical
  unfold conditionalDepthLikelihood depthLikelihood
  congr 1
  apply tsum_congr
  intro depth
  simp only [prefixMatchesSourced, max_le_iff]

theorem prefixConditioning : PrefixConditioning := by
  have extension (prior : ℕ → ℝ) (new observed : ℕ) (ordered : observed ≤ new) :
      conditionalDepthLikelihood prior new observed =
        depthLikelihood prior new / depthLikelihood prior observed := by
    rw [conditionalRatio, max_eq_left ordered]
  refine ⟨?_, fun prior new observed ordered _ => extension prior new observed ordered, ?_⟩
  · intro prior new observed ordered positive
    rw [conditionalRatio, max_eq_right ordered, div_self positive.ne']
  · intro prior new observed finiteWeight endlessWeight ordered observedPos newPos finitePos
    rw [extension prior new observed ordered]
    field_simp [observedPos.ne', newPos.ne', finitePos.ne']

end TruthCore.Results.Causality.SupplierAuditLikelihood
