module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.UnitInterval
public import Mathlib.Data.Finset.Card

/-! Shared vocabulary for probability on a fixed carrier: pointwise positive
measures, strictly interior probability values, finitely additive set
functions, and relative frequencies along finite exhaustions. Analyst
mathematics, attribution deferred. The plenitude controls
(`Science.FineTuningInformation.Plenitude`) and the modal-carrier controls
(`Modal.ProbabilityUnderdetermination`) both reuse these declarations, so
neither imports the other's vocabulary.

Four different things are called "probability" here and are kept apart
(see the probability-assignment disambiguation): a normalized countably
additive measure (`MeasureTheory.IsProbabilityMeasure`), a normalized finitely
additive real set function (`NormalizedAdditive`), a limiting relative
frequency along an exhaustion (`HasDensity`), and an observer-conditioned
likelihood (`Science.FineTuningInformation.Plenitude.weightedLikelihood`). No
declaration below passes between them. -/

@[expose] public section

namespace TruthCore.Logic.CarrierProbability

open MeasureTheory Set Filter Topology

/-- Positive mass at every point of a measurable space. This is pointwise
positivity of a measure, not the topological support of an atomless measure.
It is used only on countable carriers with measurable singletons. -/
def PointFullSupport {W : Type*} [MeasurableSpace W] (μ : Measure W) : Prop :=
  ∀ x, 0 < μ {x}

/-- A probability value strictly between zero and one, as a member of
Mathlib's unit interval. -/
abbrev InteriorRate := {p : unitInterval // 0 < (p : ℝ) ∧ (p : ℝ) < 1}

/-- A normalized finitely additive real set function on the entire power set.
Nonnegativity and countable additivity are deliberately not required. -/
def NormalizedAdditive {W : Type*} (m : Set W → ℝ) : Prop :=
  m univ = 1 ∧ ∀ s t : Set W, Disjoint s t → m (s ∪ t) = m s + m t

/-- Relative frequency of an event in a finite sample of distinct points. The
empty-sample value is Lean's total division and plays no role in limits. -/
noncomputable def frequency {W : Type*} (s : Set W) (t : Finset W) : ℝ := by
  classical
  exact ((t.filter (· ∈ s)).card : ℝ) / t.card

/-- A monotone sequence of finite sets containing every carrier member at
some stage. No sampling law or geometric order is assumed. -/
def Exhaustion {W : Type*} (E : ℕ → Finset W) : Prop :=
  Monotone E ∧ ∀ x, ∃ n, x ∈ E n

/-- The relative frequency of `s` along `E` converges to `r`, using Mathlib's
`Filter.Tendsto` at `atTop` into the neighbourhood filter of `r`. -/
def HasDensity {W : Type*} (s : Set W) (E : ℕ → Finset W) (r : ℝ) : Prop :=
  Tendsto (fun n => frequency s (E n)) atTop (𝓝 r)

end TruthCore.Logic.CarrierProbability
