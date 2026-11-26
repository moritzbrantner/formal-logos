module

public import TruthCore.Causality.RayObservation
public import TruthCore.Logic.PrefaceConnectivity

@[expose] public section

namespace TruthCore.Causality.SupplierPanelLikelihood

open MeasureTheory Set TruthCore.Causality.RayObservation TruthCore.Logic.PrefaceConnectivity
open scoped ENNReal

variable {K O Γ Λ : Type} {intact : K → Nat → Prop} {position : O → K × Nat} {n : ℕ}

/-- The sampled bit for a live ray is read at all its live positions. A position
with an upstream cut is off regardless of the sample. The numbering ranges
over exactly the ray identities observed on intact tails. -/
def positiveAt (index : ObservedRays intact position ≃ Fin n)
    (G : Set Γ) (C : Set Λ) (i : O) : Set (Γ × (Fin n → Λ)) :=
  {x | ∃ live : Live intact position i,
    x ∈ assertion G C (index (observedRay i live))}

/-- Joint observation that every requested position is on. -/
def allPositive (index : ObservedRays intact position ≃ Fin n)
    (G : Set Γ) (C : Set Λ) : Set (Γ × (Fin n → Λ)) :=
  ⋂ i, positiveAt index G C i

/-- Every draw specifies a realizable report. An all-positive panel with a
cut has zero probability, an empty all-live panel has probability one, and
a nonempty all-live panel samples the local condition once per distinct ray. -/
def PanelProbabilities : Prop :=
  ∀ (K O Γ Λ : Type) [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [Fintype Λ] [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ]
    (κ : Measure Γ) [IsProbabilityMeasure κ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (intact : K → Nat → Prop) (position : O → K × Nat) (n : ℕ)
    (index : ObservedRays intact position ≃ Fin n) (G : Set Γ) (C : Set Λ),
    (∀ x, ∃ report : O → Bool, Feasible intact position report ∧
      ∀ i, report i = true ↔ x ∈ positiveAt index G C i) ∧
    ((∃ i, ¬ Live intact position i) → profile κ ν n (allPositive index G C) = 0) ∧
    ((∀ i, Live intact position i) → profile κ ν n (allPositive index G C) =
      if n = 0 then 1 else κ G * ν C ^ n)

end TruthCore.Causality.SupplierPanelLikelihood
