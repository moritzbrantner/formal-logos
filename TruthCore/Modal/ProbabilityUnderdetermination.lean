module

public import TruthCore.Modal.Kripke
public import TruthCore.Logic.CarrierProbability
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.Finset.Card

/-! Analyst mathematics, attribution deferred. World populations, valuations,
accessibility, measures and enumeration orders are different inputs. None of
these constructions asserts that the mathematical carrier exhausts metaphysical
possibility. Point support is used only on countable discrete spaces. The
generic carrier-probability vocabulary (pointwise positive measures, interior
rates, finitely additive set functions, frequencies, exhaustions and Mathlib
`Tendsto` densities) is shared from `Logic.CarrierProbability`. -/

@[expose] public section

namespace TruthCore.Modal.ProbabilityUnderdetermination
open Set MeasureTheory
open TruthCore.Logic.CarrierProbability
open scoped ENNReal Cardinal
universe u v

/-- The uniform-point-mass demand on a countably infinite carrier. -/
def EqualPointMass {W : Type u} [MeasurableSpace W] (μ : Measure W) : Prop :=
  ∃ c : ℝ≥0∞, ∀ x, μ {x} = c

/-- Invariance under every bijection of the carrier, not merely under a
specified group of measurable or geometric symmetries. -/
def PermutationInvariant {W : Type u} {A : Type v} (m : Set W → A) : Prop :=
  ∀ (e : Equiv.Perm W) (s : Set W), m (e ⁻¹' s) = m s

/-- Initial finite set of a bijective enumeration. (`prefix` is a Lean
keyword, so the declaration is named `enumPrefix`.) -/
def enumPrefix {W : Type u} (e : ℕ ≃ W) (n : ℕ) : Finset W :=
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
    Exhaustion (enumPrefix e) ∧ Exhaustion (enumPrefix f) ∧
    HasDensity s (enumPrefix e) (1/2) ∧ HasDensity s (enumPrefix f) (1/3)

def ContinuousControl : Prop :=
  IsProbabilityMeasure unitMeasure ∧ (∀ x : ℝ, unitMeasure {x} = 0) ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → unitMeasure (Icc 0 t) = ENNReal.ofReal t

/-- The frame, valuation, origin and formula are fixed before the probability
is chosen. The carrier of the probability is precisely the accessible worlds.
Both truth classes need only be nonempty; the draft's infinite classes are a
special case. This is the shared interior-mass statement at the accessible-world
subtype. -/
def ModalProbabilityFreedom : Prop :=
  ∀ (W : Type u) (Atom : Type v) (F : Frame W) (V : Valuation W Atom)
    (w : W) (φ : Formula Atom)
    [Countable {v // F.access w v}]
    [MeasurableSpace {v // F.access w v}]
    [MeasurableSingletonClass {v // F.access w v}]
    [Nonempty (accessibleEvent F V w φ)]
    [Nonempty ((accessibleEvent F V w φ)ᶜ : Set {v // F.access w v})]
    (p : InteriorRate),
    ∃ μ : Measure {v // F.access w v},
      IsProbabilityMeasure μ ∧ PointFullSupport μ ∧
        μ.real (accessibleEvent F V w φ) = (p.val : ℝ)

end TruthCore.Modal.ProbabilityUnderdetermination
