module

public import TruthCore.Causality.Frame
public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Modal.CounterfactualSelection

/-!
The shared efficient-causal dependence primitive remains in the causal frame.
The intervention test is world-local. The route to real impossibility has its
own bridge premises, including coverage of accessible absence worlds.
-/

@[expose] public section

namespace TruthCore.Causality.CounterfactualDependence

open TruthCore.Causality.Frame
open TruthCore.Modal.CounterfactualSelection

variable {W B T R : Type}

/-- Ontic nonexistence, using the shared modal ontology. -/
def absent (f : CausalityFrame W B T R) (x : B) : Set W :=
  fun v => ¬ f.history.ontic.ExistsAt v x

/-- An externally supplied intervention outcome is selected only if it
realizes the antecedent. The intervention supplies the candidate world. -/
def interventionSelection (outcome : W → W) : Selector W :=
  fun w A v => v = outcome w ∧ v ∈ A

theorem intervention_success (outcome : W → W) : Success (interventionSelection outcome) :=
  fun _ _ _ hv => hv.2

theorem intervention_hasSelection_iff (outcome : W → W) (w : W) (A : Set W) :
    HasSelection (interventionSelection outcome) w A ↔ outcome w ∈ A :=
  ⟨fun ⟨_, he, hv⟩ => he ▸ hv, fun hA => ⟨outcome w, rfl, hA⟩⟩

theorem intervention_would_iff (outcome : W → W) (w : W) (A Q : Set W)
    (hA : outcome w ∈ A) : Would (interventionSelection outcome) w A Q ↔ outcome w ∈ Q :=
  ⟨fun h => h ⟨rfl, hA⟩, fun h _ ⟨he, _⟩ => he.symm ▸ h⟩

/-- The effect and agent exist at the origin,
and the agent gives being to the effect there at the designated instant. In the supplied agent-removal
outcome neither exists. Admissibility as a surgery holding the appropriate
background fixed is a separate interpretation of `remove`. -/
def SustainingRemovalTest (f : CausalityFrame W B T R) (remove : B → W → W)
    (w : W) (effect agent : B) : Prop :=
  f.history.ontic.ExistsAt w effect ∧ f.history.ontic.ExistsAt w agent ∧
    f.GivesAt w agent effect f.history.now ∧
    remove agent w ∈ absent f agent ∧ remove agent w ∈ absent f effect

theorem sustaining_removal_iff (f : CausalityFrame W B T R) (remove : B → W → W)
    (w : W) (effect agent : B) :
    SustainingRemovalTest f remove w effect agent ↔
      (f.history.ontic.ExistsAt w effect ∧ f.history.ontic.ExistsAt w agent ∧
        f.GivesAt w agent effect f.history.now ∧
        HasSelection (interventionSelection (remove agent)) w (absent f agent) ∧
        Would (interventionSelection (remove agent)) w (absent f agent) (absent f effect)) := by
  constructor
  · rintro ⟨he, ha, hg, hRemoval, hResponse⟩
    exact ⟨he, ha, hg, (intervention_hasSelection_iff _ _ _).mpr hRemoval,
      (intervention_would_iff _ _ _ _ hRemoval).mpr hResponse⟩
  · rintro ⟨he, ha, hg, hSelected, hWould⟩
    have hRemoval := (intervention_hasSelection_iff _ _ _).mp hSelected
    exact ⟨he, ha, hg, hRemoval, (intervention_would_iff _ _ _ _ hRemoval).mp hWould⟩

/-- Soundness required of a proposed reading of the shared primitive at the
given standpoint and selector. This does not interpret the converse. -/
def DependenceTracksSelectedAbsence (f : CausalityFrame W B T R)
    (select : Selector W) (w : W) : Prop :=
  ∀ x y, f.DependsForBeing x y → Would select w (absent f y) (absent f x)

/-- An antecedent-only coverage policy. Every accessible world where the
putative source is absent is selected. A single closest world or operation
need not cover even two accessible absence worlds. -/
def CoversAccessibleAbsence (f : CausalityFrame W B T R)
    (select : Selector W) (w : W) : Prop :=
  ∀ y v, f.history.ontic.frame.access w v → v ∈ absent f y → v ∈ select w (absent f y)

/-- The needed direction of interpretation of real possibility. If x can be
without y, some accessible world in this ontology realizes that contrast. -/
def BeingWithoutHasAccessibleWitness (f : CausalityFrame W B T R)
    (w : W) (CanBeWithout : B → B → Prop) : Prop :=
  ∀ x y, CanBeWithout x y → ∃ v, f.history.ontic.frame.access w v ∧
    f.history.ontic.ExistsAt v x ∧ v ∈ absent f y

/-- For each effect and putative source, preserve at least one accessible
contrast with the effect still present whenever such a contrast exists. -/
def PreservesAccessibleAbsenceWitnesses (f : CausalityFrame W B T R)
    (select : Selector W) (w : W) : Prop :=
  ∀ x y,
    (∃ v, f.history.ontic.frame.access w v ∧
      f.history.ontic.ExistsAt v x ∧ v ∈ absent f y) →
    ∃ v, f.history.ontic.frame.access w v ∧ f.history.ontic.ExistsAt v x ∧
      v ∈ absent f y ∧ v ∈ select w (absent f y)

end TruthCore.Causality.CounterfactualDependence
