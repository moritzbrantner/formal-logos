module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.MeasureTheory.Measure.Prod
public import TruthCore.Logic.EpistemicAccuracy.BayesianRefinement
public import TruthCore.Logic.FiniteInformation
public import TruthCore.Logic.CarrierProbability
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
open TruthCore.Logic.CarrierProbability

abbrev Universe := Bool × ℕ

/-- The realized population includes every pair; the first coordinate records
the universe type. Neither coordinate is a first-person probability. -/
def roster : Set Universe := Set.univ

def realizedTypes : Set Bool := Prod.fst '' roster

/-- Use a fixed, full-support geometric law for the instance index, varying
only the Bernoulli law for the report. Both laws are normalized Mathlib
measures. No uniform measure over the infinite roster is presumed. -/
noncomputable def half : unitInterval := ⟨1/2, by norm_num, by norm_num⟩

/-- The report coordinate uses Mathlib's Bernoulli law directly as a sampling
law over residual reports. It is not the design/natural comparison prior
`modelPrior`, although both are built from the same Mathlib constructor. -/
noncomputable def observationLaw (p : unitInterval) : Measure Universe :=
  (bernoulliMeasure true false p).prod (geometricMeasure half)

def fineEvent : Set Universe := ({true} : Set Bool) ×ˢ (Set.univ : Set ℕ)

/-- The entire roster, type assignment and both possibility profiles are
unchanged across the compared observational models. A caller may stipulate
both profiles are univ; this is not a modal-realizability theorem. The value
ignores the rate, so these data are constant across the compared models. The
order of the instance index (used by `geometricMeasure`) is not part of these
data. -/
def scopeData (possible reachable : Set Bool) (_ : InteriorRate) :
    Set Bool × Set Bool × Set Universe × (Universe → Bool) :=
  (possible, reachable, roster, Prod.fst)

/-- Stage n of the rate-(a, b) cutoff: the first a(n+1) instances of the
true type and the first b(n+1) instances of the false type. Different positive
rates enumerate the same entire roster. There is no claim that these are
physical cosmological time cutoffs. -/
def cutoffStage (a b n : ℕ) : Finset Universe :=
  ({true} ×ˢ Finset.range (a * (n + 1))) ∪ ({false} ×ˢ Finset.range (b * (n + 1)))

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
The third conjunct holds because `scopeData` is constant in the rate while the
report probability is not: a constant function does not determine a
nonconstant one. It records that the supplied scope data (possibility
profiles, roster and type map) carry no information about the rate. Those data
omit the order of the instance index. A rival that also reads that order, for
example natural density along the interleaved enumeration of Bool × ℕ, returns
1/2; `CutoffUnderdetermination` shows that other exhaustive orders return other
values. -/
def ObservationalUnderdetermination : Prop :=
  RepeatedTypes ∧
  (∀ p : InteriorRate, IsProbabilityMeasure (observationLaw p.val) ∧
    (∀ u : Universe, 0 < (observationLaw p.val).real {u}) ∧
    (observationLaw p.val).real fineEvent = (p.val : ℝ)) ∧
  (∀ possible reachable : Set Bool,
    ¬ Identifiability.Identifies (scopeData possible reachable)
      (fun p : InteriorRate => (observationLaw p.val).real fineEvent))

/-- For positive a and b the rate-(a, b) stages exhaust the roster, and the
relative frequency of the true type is a/(a+b) at every stage, hence also in
the limit. As a and b range over positive naturals, a/(a+b) ranges over
exactly the rationals strictly between zero and one. -/
def CutoffUnderdetermination : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b →
    Exhaustion (cutoffStage a b) ∧
    (∀ n, frequency fineEvent (cutoffStage a b n) = (a : ℝ) / ((a : ℝ) + b)) ∧
    HasDensity fineEvent (cutoffStage a b) ((a : ℝ) / ((a : ℝ) + b))

/-- With both observer cells nonempty in mass, merely varying the positive
relative sampling weights realizes every interior rational conditional
likelihood. Unit weights recover the existing unweighted likelihood. -/
def ObserverWeightUnderdetermination : Prop :=
  (∀ s : Sampling, weightedLikelihood s 1 1 = likelihood s) ∧
  (∀ s : Sampling, 0 < s.weight 1 → ∀ p : ℚ, 0 < p → p < 1 →
    ∃ r t : ℚ, 0 < r ∧ 0 < t ∧ weightedLikelihood s r t = p)

universe u

/-- The shared interior-mass statement. On every countable carrier with
measurable singletons, an event that is nonempty and has a nonempty
complement receives every strictly interior probability from some normalized
measure with positive mass at every point. Finite and infinite carriers are
both covered; infinity is not needed for this non-identification. It matters
only for the separate absence of a uniform default (on a finite carrier the
normalized counting measure is available). This does not say that no
probability on the carrier is warranted. -/
def ArbitraryInteriorMass : Prop :=
  ∀ (W : Type u) [Countable W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (s : Set W) [Nonempty s] [Nonempty (sᶜ : Set W)] (p : InteriorRate),
    ∃ μ : Measure W, IsProbabilityMeasure μ ∧ PointFullSupport μ ∧
      μ.real s = (p.val : ℝ)

end Plenitude

end TruthCore.Science.FineTuningInformation
