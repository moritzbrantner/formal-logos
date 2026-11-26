module

public import TruthCore.Logic.Doxastic
public import TruthCore.Results.Logic.ThresholdBelief.Solution

/-! Finite probability-to-belief representation at a selected context.
The profile away from that context is a separate choice. -/

@[expose] public section
namespace TruthCore.Logic.DoxasticThreshold

open TruthCore.Modal MeasureTheory Set
open ThresholdBelief

variable {W : Type} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]

/-- Representation only requires a match at the selected agent and world.
The core is inhabited under the same guards. -/
theorem atWorld (μ : Measure W) [IsProbabilityMeasure μ] (t : ℝ)
    (positive : 0 < t) (atMostOne : t ≤ 1) (closed : ConjunctionClosed μ t) :
    (HeavyCore μ t).Nonempty ∧
      ∀ {Agent : Type} (c : Doxastic.Context Agent W) (a : Agent) (w : W)
        (_successors : ∀ v, (c.belief a).access w v ↔ v ∈ HeavyCore μ t) (A : Set W),
        Accepted μ t A ↔ Doxastic.Believes c a (· ∈ A) w := by
  obtain ⟨membership, closure, _, emptyRejected⟩ :=
    TruthCore.Results.Logic.ThresholdBelief.core W μ t positive atMostOne
  have coreAccepted := closure.mp closed
  refine ⟨?_, ?_⟩
  · by_contra empty
    exact emptyRejected (Set.not_nonempty_iff_eq_empty.mp empty ▸ coreAccepted)
  · intro Agent c a w successors A
    constructor
    · exact fun accepted v hv => (membership v).mp ((successors v).mp hv) A accepted
    · exact fun believed => coreAccepted.trans
        (measureReal_mono (μ := μ) fun v hv => believed v ((successors v).mpr hv))

/-- Choosing the same nonempty core at every world gives the KD45 laws.
Only the chosen probability policy is represented here. -/
theorem fixedCore (μ : Measure W) [IsProbabilityMeasure μ] (t : ℝ)
    (positive : 0 < t) (atMostOne : t ≤ 1) (closed : ConjunctionClosed μ t)
    (actual : W) :
    let c : Doxastic.Context Unit W := ⟨fun _ => Doxastic.fixed (· ∈ HeavyCore μ t), actual⟩
    FrameSatisfies .KD45 (c.belief ()) ∧
      ∀ A : Set W, Accepted μ t A ↔ Doxastic.Believes c () (· ∈ A) actual := by
  have h := atWorld μ t positive atMostOne closed
  exact ⟨Doxastic.fixedKD45 _ h.1, fun A => h.2 _ () actual (fun _ => Iff.rfl) A⟩

/-- Even a single row of a relation would give conjunction closure.
The existing uniform lottery refutes that representation below certainty. -/
theorem lotteryOmission (t : ℝ) (positive : 0 < t) (belowOne : t < 1) :
    ∃ N : ℕ, 2 ≤ N ∧ (∀ i : Fin N, Accepted (uniform N) t {i}ᶜ) ∧
      ¬ ∃ (F : Frame (Fin N)) (w : Fin N),
        ∀ A : Set (Fin N), Accepted (uniform N) t A ↔ ∀ v, F.access w v → v ∈ A := by
  obtain ⟨N, size, fails, tickets, _⟩ :=
    TruthCore.Results.Logic.ThresholdBelief.uniformBoundary.2 t positive belowOne
  refine ⟨N, size, tickets, ?_⟩
  rintro ⟨F, w, represents⟩
  apply fails
  intro A B hA hB
  exact (represents (A ∩ B)).mpr fun v hv =>
    ⟨(represents A).mp hA v hv, (represents B).mp hB v hv⟩

/-- The existing skew measure yields a coherent policy and a KD45 profile
for the same event. The false actual point still has positive probability. -/
theorem skewFixedControl :
    let c : Doxastic.Context Unit Bool :=
      ⟨fun _ => Doxastic.fixed (· ∈ HeavyCore skew (9/10)), false⟩
    FrameSatisfies .KD45 (c.belief ()) ∧
      Doxastic.Believes c () (· = true) false ∧ ¬ (false = true) ∧
      0 < skew.real {false} := by
  obtain ⟨probability, _, _, closed, accepted, _, mass, _⟩ :=
    TruthCore.Results.Logic.ThresholdBelief.skewSurvivor
  let := probability
  have h := fixedCore skew (9/10) (by norm_num) (by norm_num) closed false
  exact ⟨h.1, (h.2 {true}).mp accepted, Bool.noConfusion, mass⟩

end TruthCore.Logic.DoxasticThreshold
