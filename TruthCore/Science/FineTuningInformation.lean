module

public import Mathlib.Probability.Distributions.Bernoulli
public import TruthCore.Logic.EpistemicAccuracy.BayesianRefinement
public import TruthCore.Logic.FiniteInformation
public import TruthCore.Science.FineTuningEvidence

/-! A binary report drawn from the existing observer-conditioned sampling pair.
The model labels index rows of a channel. The prior is for this comparison
after conditioning on observerhood, and is supplied independently of the rows. -/

@[expose] public section

namespace TruthCore.Science.FineTuningInformation

open MeasureTheory ProbabilityTheory
open FineTuningSelection FineTuningEvidence
open Logic.FiniteInformation
open Logic.EpistemicAccuracy.Refinement Logic.EpistemicAccuracy.BayesianRefinement

/-- Observer-conditioned rational likelihood, transported to Mathlib's unit interval. -/
def reportRate (s : Sampling) : unitInterval := ⟨(likelihood s : ℝ), by
  constructor
  · exact_mod_cast div_nonneg (le_of_lt s.evidence_pos) (le_of_lt s.observers_pos)
  · exact_mod_cast (div_le_one s.observers_pos).mpr
      (le_add_of_nonneg_right (s.nonnegative 1))⟩

/-- Two normalized binary report laws indexed by the comparison model. -/
noncomputable def binaryKernel (d n : unitInterval) : Kernel Bool Bool :=
  Kernel.ofFunOfCountable fun m => bernoulliMeasure true false (if m then d else n)

instance binaryKernel_isMarkov (d n : unitInterval) : IsMarkovKernel (binaryKernel d n) :=
  ⟨fun m => by
    change IsProbabilityMeasure (bernoulliMeasure true false (if m then d else n))
    infer_instance⟩

/-- Model label true indexes design; false indexes the natural rival.
Report true denotes the fine-evidence cell among observer worlds. -/
noncomputable def reportKernel (d n : Sampling) : Kernel Bool Bool :=
  binaryKernel (reportRate d) (reportRate n)

instance reportKernel_isMarkov (d n : Sampling) : IsMarkovKernel (reportKernel d n) :=
  inferInstanceAs (IsMarkovKernel (binaryKernel (reportRate d) (reportRate n)))

/-- Probability of sampling an observer before conditioning on observerhood. -/
def observerRate (s : Sampling) : unitInterval := ⟨((s.weight 0 + s.weight 1 : ℚ) : ℝ), by
  constructor
  · exact_mod_cast le_of_lt s.observers_pos
  · exact_mod_cast (calc
      s.weight 0 + s.weight 1 ≤ s.weight 0 + s.weight 1 + s.weight 2 :=
        le_add_of_nonneg_right (s.nonnegative 2)
      _ = 1 := by simpa [Fin.sum_univ_three, add_assoc] using s.normalized)⟩

/-- The supplied comparison prior gives design mass p and the natural rival mass 1-p. -/
noncomputable def modelPrior (p : unitInterval) : Measure Bool :=
  bernoulliMeasure true false p

instance modelPrior_isProbability (p : unitInterval) : IsProbabilityMeasure (modelPrior p) :=
  inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure true false p))

/-- Information about the model label carried by the report after observer selection. -/
noncomputable def reportInformation (p : unitInterval) (d n : Sampling) :=
  mutualInformation ((modelPrior p) ⊗ₘ reportKernel d n)

/-- The report screens off the distinction between the models precisely when
their observer-conditioned fine-report probabilities coincide. -/
def ObserverInformationCriterion : Prop :=
  ∀ (p : unitInterval) (d n : Sampling), 0 < (p : ℝ) → (p : ℝ) < 1 →
    (reportInformation p d n = 0 ↔ likelihood d = likelihood n)

/-- Unequal model weights coexist with screened reports; the calibrated
sampling pair supplies a separating report at the same prior. -/
def ScreeningControls : Prop :=
  let p : unitInterval := ⟨1/3, by norm_num, by norm_num⟩
  (modelPrior p).real {true} = 1/3 ∧ (modelPrior p).real {false} = 2/3 ∧
  reportKernel screenedDesign screenedNatural true = Measure.dirac true ∧
  reportKernel screenedDesign screenedNatural false = Measure.dirac true ∧
  reportInformation p screenedDesign screenedNatural = 0 ∧
  0 < reportInformation p design natural

/-- Under the existing coherent update equations and an interior predictive
probability, the binary Brier gain and Shannon information vanish together. -/
def AccuracyAgreement : Prop :=
  ∀ (p : unitInterval) (d n : Sampling) (w u v : ℝ),
    0 < (p : ℝ) → (p : ℝ) < 1 → 0 < w → w < 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
    w = p * (reportRate d : ℝ) + (1-p) * (reportRate n : ℝ) →
    w*u = p * (reportRate d : ℝ) →
    (1-w)*v = p * (1-(reportRate d : ℝ)) →
    (accuracyGain w u v = 0 ↔ reportInformation p d n = 0)

end TruthCore.Science.FineTuningInformation
