module

public import TruthCore.Science.Identifiability
public import TruthCore.Results.Science.PolynomialInduction.Solution
public import TruthCore.Results.Science.MeasurementCalibration.Solution
public import TruthCore.Results.Explanation.MechanismInterventionParity.Solution
public import TruthCore.Causality.StructuralCausalIdentification
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-! Reuse controls for exact, statistical and intervention observations.
Their scope is the supplied mathematical models. -/

@[expose] public section

namespace TruthCore.Science.IdentifiabilityExamples

open TruthCore.Science.Identifiability

namespace Polynomial

open _root_.Polynomial

/-- Restricting the model class by degree changes the exact boundary for
recovery from distinct input/output samples. -/
theorem sample_threshold {K : Type*} [CommRing K] [IsDomain K] (s : Finset K) (d : Nat) :
    Identifies (fun p : {p : K[X] // p.natDegree ≤ d} => fun x : (s : Set K) => p.val.eval x.val)
      Subtype.val ↔ d < s.card := by
  rw [← TruthCore.Results.Science.PolynomialInduction.threshold]
  exact ⟨fun h p q hp hq same => h ⟨p, hp⟩ ⟨q, hq⟩ (funext fun x => same x x.property),
    fun h p q same => h p.val q.val p.property q.property
      (fun x hx => congrFun same ⟨x, hx⟩)⟩

end Polynomial

namespace Calibration

open TruthCore.Results.Science.MeasurementCalibration (certificate)

def readings (m : (Bool → Int) × Int) : Bool → Int :=
  fun x => m.1 x + m.2

def contrast (m : (Bool → Int) × Int) : Int := m.1 true - m.1 false

/-- Complete readings recover the within-signal contrast even when the
unknown constant instrument offset varies. -/
theorem identifies_contrast : Identifies readings contrast := by
  intro m n same
  obtain ⟨d, _, hs⟩ := (certificate.1 Bool Int m.1 n.1 m.2 n.2).mp (congrFun same)
  simp only [contrast, hs, add_sub_add_right_eq_sub]

theorem different_bias_same_contrast :
    ∃ m n, readings m = readings n ∧ m.2 ≠ n.2 ∧ contrast m = contrast n := by
  let m : (Bool → Int) × Int := (fun b => if b then 2 else 0, 1)
  let n : (Bool → Int) × Int := (fun b => if b then 3 else 1, 0)
  have same : readings m = readings n := by
    funext b
    cases b <;> decide
  exact ⟨m, n, same, by decide, identifies_contrast m n same⟩

end Calibration

namespace Surgery

open TruthCore.Explanation.MechanismInterventionParity
open TruthCore.Results.Explanation.MechanismInterventionParity (natural_agreement surgery_exposes_idle)

def run (m : TwoState × Bool) : Setting → Observation :=
  if m.2 then pluralRun m.1 else idleRun m.1

/-- A public surgery separates two mechanisms at the same background where
their natural reports agree. This control asserts one fiber split. -/
theorem one_fiber_split :
    ∃ m n : TwoState × Bool, run m natural = run n natural ∧ m.2 ≠ n.2 ∧
      augment (fun m => run m natural) Set.univ run m ≠
        augment (fun m => run m natural) Set.univ run n := by
  obtain ⟨s, i, hi⟩ := surgery_exposes_idle
  refine ⟨(s, true), (s, false), (natural_agreement s).2.1, Bool.noConfusion, ?_⟩
  intro same
  exact hi (congrFun (congrArg Prod.snd same) ⟨i, Set.mem_univ i⟩)

end Surgery

namespace Statistical

open MeasureTheory
open TruthCore.Causality.StructuralCausalModel
open TruthCore.Causality.StructuralCausalModel.Identification

noncomputable def experiment : Experiment (Model Bool Context Bool) Context (Bool × Bool) where
  sampleLaw := fun _ => contextLaw.toMeasure
  probability := fun _ => inferInstance
  readout := fun m u => observe (m.response u (fun _ => none))
  measurable_readout := fun _ => Measurable.of_discrete

theorem experiment_law (m : Model Bool Context Bool) :
    experiment.law m = (observational m).toMeasure :=
  PMF.toMeasure_map _ contextLaw (experiment.measurable_readout m)

/-- The earlier no-decoder result transfers to laws on the discrete measurable
observation space. The target is the probability of Y under surgical set-X. -/
theorem observational_does_not_identify :
    ¬ Identifies experiment.law (fun m => outcomeUnderSetX m true) := by
  intro h
  apply no_observational_identification
  apply (total_factor_iff _ _).mpr
  refine ⟨fun m n same => h m n ?_, Or.inl ⟨0⟩⟩
  rw [experiment_law, experiment_law, same]

theorem observational_fiber_has_two_targets :
    ∃ a b, a ∈ identifiedSet experiment.law (fun m => outcomeUnderSetX m true)
        (experiment.law forward) ∧
      b ∈ identifiedSet experiment.law (fun m => outcomeUnderSetX m true)
        (experiment.law forward) ∧ a ≠ b := by
  refine ⟨_, _, ⟨forward, rfl, rfl⟩, ⟨reverse, ?_, rfl⟩, ?_⟩
  · change experiment.law reverse = experiment.law forward
    rw [experiment_law, experiment_law, same_observational.1]
  · intro eq
    change outcomeUnderSetX forward true = outcomeUnderSetX reverse true at eq
    rw [intervention_masses.1, intervention_masses.2.1] at eq
    simp only [fraction, Nat.cast_ofNat, Nat.cast_one, ENNReal.coe_inj] at eq
    norm_num at eq

end Statistical

end TruthCore.Science.IdentifiabilityExamples
