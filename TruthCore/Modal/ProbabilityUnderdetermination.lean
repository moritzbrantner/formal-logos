module

public import TruthCore.Modal.Kripke
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.Finset.Card

/-! Analyst mathematics, attribution deferred. World populations, valuations,
accessibility, measures and enumeration orders are different inputs. None of
these constructions asserts that the mathematical carrier exhausts metaphysical
possibility. Point support is used only on countable discrete spaces. -/

@[expose] public section

namespace TruthCore.Modal.ProbabilityUnderdetermination
open Set MeasureTheory
open scoped ENNReal Cardinal
universe u v

/-- Positive mass at every point, not the topological notion of support. -/
def PointFullSupport {W : Type u} [MeasurableSpace W] (μ : Measure W) : Prop :=
  ∀ x, 0 < μ {x}

/-- The uniform-point-mass demand on a countably infinite carrier. -/
def EqualPointMass {W : Type u} [MeasurableSpace W] (μ : Measure W) : Prop :=
  ∃ c : ℝ≥0∞, ∀ x, μ {x} = c

/-- A normalized finitely additive real set function on the entire power set.
Nonnegativity is not needed for the impossibility result. -/
def NormalizedAdditive {W : Type u} (m : Set W → ℝ) : Prop :=
  m univ = 1 ∧ ∀ s t : Set W, Disjoint s t → m (s ∪ t) = m s + m t

/-- Invariance under every bijection of the carrier, not merely under a
specified group of measurable or geometric symmetries. -/
def PermutationInvariant {W : Type u} {A : Type v} (m : Set W → A) : Prop :=
  ∀ (e : Equiv.Perm W) (s : Set W), m (e ⁻¹' s) = m s

/-- Relative frequency on a finite sample of distinct points. -/
noncomputable def frequency {W : Type u} (s : Set W) (t : Finset W) : ℝ := by
  classical
  exact ((t.filter (· ∈ s)).card : ℝ) / t.card

/-- Finite sets exhaust the whole carrier, with no multiplicities. -/
def Exhaustion {W : Type u} (E : ℕ → Finset W) : Prop :=
  Monotone E ∧ ∀ x, ∃ n, x ∈ E n

/-- The ordinary epsilon definition of the limiting frequency along E. -/
def HasDensity {W : Type u} (s : Set W) (E : ℕ → Finset W) (r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |frequency s (E n) - r| < ε

/-- Initial finite set of a bijective enumeration. -/
def prefix {W : Type u} (e : ℕ ≃ W) (n : ℕ) : Finset W :=
  (Finset.range n).map e.toEmbedding

/-- Truth event on the existing Kripke successor subtype. -/
def accessibleEvent {W : Type u} {Atom : Type v} (F : Frame W)
    (V : Valuation W Atom) (w : W) (φ : Formula Atom) :
    Set {v // F.access w v} :=
  {v | Holds F V v.val φ}

/-- Lebesgue measure restricted to the unit interval, as a probability on ℝ. -/
noncomputable def unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

def NoUniform : Prop :=
  ∀ (W : Type u) [Countable W] [Infinite W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (μ : Measure W) [IsProbabilityMeasure μ],
    ¬ EqualPointMass μ

def ArbitraryProbability : Prop :=
  ∀ (W : Type u) [Countable W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (s : Set W) [Infinite s] [Infinite (sᶜ : Set W)] (p : ℝ≥0∞),
    0 < p → p < 1 →
    ∃ μ : Measure W, IsProbabilityMeasure μ ∧ PointFullSupport μ ∧ μ s = p

def EqualCardinalityDifferent : Prop :=
  ∀ (W : Type u) [Countable W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (s : Set W) [Infinite s] [Infinite (sᶜ : Set W)],
    Cardinal.mk s = Cardinal.mk (sᶜ : Set W) ∧
    ∃ μ : Measure W, IsProbabilityMeasure μ ∧ PointFullSupport μ ∧ μ s ≠ μ sᶜ

def NoPermutationProbability : Prop :=
  ∀ (W : Type u) [Infinite W] (m : Set W → ℝ),
    NormalizedAdditive m → ¬ PermutationInvariant m

def NoAllSubsetsPermutationMeasure : Prop :=
  ∀ (W : Type u) [Infinite W] [MeasurableSpace W] (μ : Measure W)
    [IsProbabilityMeasure μ], (∀ s : Set W, MeasurableSet s) →
      ¬ PermutationInvariant (fun s => μ s)

def EnumerationDependence : Prop :=
  ∃ (s : Set ℕ) (e f : ℕ ≃ ℕ),
    Exhaustion (prefix e) ∧ Exhaustion (prefix f) ∧
    HasDensity s (prefix e) (1/2) ∧ HasDensity s (prefix f) (1/3)

def ContinuousControl : Prop :=
  IsProbabilityMeasure unitMeasure ∧ (∀ x : ℝ, unitMeasure {x} = 0) ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → unitMeasure (Icc 0 t) = ENNReal.ofReal t

/-- The frame, valuation, origin and formula are fixed before the probability
is chosen. The carrier of the probability is precisely the accessible worlds. -/
def ModalProbabilityFreedom : Prop :=
  ∀ (W : Type u) (Atom : Type v) (F : Frame W) (V : Valuation W Atom)
    (w : W) (φ : Formula Atom)
    [Countable {v // F.access w v}]
    [MeasurableSpace {v // F.access w v}]
    [MeasurableSingletonClass {v // F.access w v}]
    [Infinite (accessibleEvent F V w φ)]
    [Infinite ((accessibleEvent F V w φ)ᶜ : Set {v // F.access w v})]
    (p : ℝ≥0∞), 0 < p → p < 1 →
    ∃ μ : Measure {v // F.access w v},
      IsProbabilityMeasure μ ∧ PointFullSupport μ ∧ μ (accessibleEvent F V w φ) = p

end TruthCore.Modal.ProbabilityUnderdetermination
