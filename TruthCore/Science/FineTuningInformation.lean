module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.MeasureTheory.Measure.Prod
public import TruthCore.Logic.EpistemicAccuracy.BayesianRefinement
public import TruthCore.Logic.FiniteInformation
public import TruthCore.Science.FineTuningEvidence
public import TruthCore.Science.Identifiability

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

/-! Observational identification under plenitude. The roster below is a
stipulated toy population, with one eligible observation center per instance.
A Boolean type denotes a residual report among observers, not observerhood.
Metaphysical and physical possibility are supplied sets, not definitions of
instantiation or probability. No cosmological application is assumed. -/
namespace Plenitude

open Set

abbrev Universe := Bool × ℕ

/-- The realized population includes every pair; the first coordinate records
the universe type. Neither coordinate is a first-person probability. -/
def roster : Set Universe := Set.univ

def realizedTypes : Set Bool := Prod.fst '' roster

/-- Use a fixed, full-support geometric law for the instance index, varying
only the Bernoulli law for the report. Both laws are normalized Mathlib
measures. No uniform measure over the infinite roster is presumed. -/
def half : unitInterval := ⟨1/2, by norm_num, by norm_num⟩

noncomputable def observationLaw (p : unitInterval) : Measure Universe :=
  (modelPrior p).prod (geometricMeasure half)

def fineEvent : Set Universe := ({true} : Set Bool) ×ˢ (Set.univ : Set ℕ)

abbrev InteriorRate := {p : unitInterval // 0 < (p : ℝ) ∧ (p : ℝ) < 1}

/-- The entire roster, type assignment and both possibility profiles are
unchanged across the compared observational models. A caller may stipulate
both profiles are univ; this is not a modal-realizability theorem. -/
def scopeData (possible reachable : Set Bool) (_ : InteriorRate) :
    Set Bool × Set Bool × Set Universe × (Universe → Bool) :=
  (possible, reachable, roster, Prod.fst)

/-- Finite exhaustion by two disjoint type slices. Different positive
rates enumerate the same entire roster. There is no claim that these are
physical cosmological time cutoffs. -/
def slice (a b n : ℕ) (tag : Bool) : Finset ℕ :=
  Finset.range ((if tag then a else b) * (n + 1))

def cutoffLikelihood (a b n : ℕ) : ℚ :=
  (↑(slice a b n true).card : ℚ) /
    (↑(slice a b n true).card + ↑(slice a b n false).card)

/-- Reweight the two observer cells of the existing Sampling model. Common
normalization cancels on conditioning on observerhood. Weights can model
record yield or a first-person sampling rule; they are not thereby calibrated
counts or physical probabilities. The results require positive weights and
positive masses for both cells. -/
def weightedLikelihood (s : Sampling) (r t : ℚ) : ℚ :=
  s.weight 0 * r / (s.weight 0 * r + s.weight 1 * t)

/-- All realized types have infinitely many distinct instances. This statement
also exhibits countable repetition explicitly, via an injection from Nat. -/
def RepeatedTypes : Prop :=
  realizedTypes = Set.univ ∧
  ∀ b : Bool, ∃ f : ℕ → Universe, Function.Injective f ∧
    ∀ n, f n ∈ roster ∧ (f n).1 = b

/-- Proper countably additive measures with positive singleton mass and any
interior report probability, on exactly the same population and type map.
Even the complete supplied ontology profile does not identify the likelihood. -/
def ObservationalUnderdetermination : Prop :=
  RepeatedTypes ∧
  (∀ p : InteriorRate, IsProbabilityMeasure (observationLaw p.val) ∧
    (∀ u : Universe, 0 < (observationLaw p.val).real {u}) ∧
    (observationLaw p.val).real fineEvent = (p.val : ℝ)) ∧
  (∀ possible reachable : Set Bool,
    ¬ Identifiability.Identifies (scopeData possible reachable)
      (fun p : InteriorRate => (observationLaw p.val).real fineEvent))

/-- Both finite slices are nested and exhaustive, but their uniform relative
type count has an arbitrary positive rational rate a/(a+b), already at every
stage. Exact constancy is stronger here than convergence of the ratios. -/
def CutoffUnderdetermination : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b →
    (∀ n m : ℕ, n ≤ m → ∀ tag, slice a b n tag ⊆ slice a b m tag) ∧
    (∀ tag k, k ∈ slice a b k tag) ∧
    (∀ n, cutoffLikelihood a b n = (a : ℚ) / ((a : ℚ) + b))

/-- With both observer cells nonempty in mass, merely varying the positive
relative sampling weights realizes every interior rational conditional
likelihood. Unit weights recover the existing unweighted likelihood. -/
def ObserverWeightUnderdetermination : Prop :=
  (∀ s : Sampling, weightedLikelihood s 1 1 = likelihood s) ∧
  (∀ s : Sampling, 0 < s.weight 1 → ∀ p : ℚ, 0 < p → p < 1 →
    ∃ r t : ℚ, 0 < r ∧ 0 < t ∧ weightedLikelihood s r t = p)

end Plenitude

end TruthCore.Science.FineTuningInformation
