module

public import TruthCore.Results.Modal.SelectedEffectBridge.Solution
public import Mathlib.Order.Bounds.Basic

/-! Stipulative optimization constraints, not a sourced theory of perfect agency.
Candidate options need not exist at the world where a choice is made. Fixed
feasibility and quality are backgrounds, not consequences of necessary agency. -/

@[expose] public section

namespace TruthCore.Modal.OptimalCreationChoice
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.German.Kant.CosmologicalInference

/-- An admissible candidate achieves a greatest quality in the fixed image.
Distinct candidates can have the same quality; `IsGreatest` concerns values. -/
def Optimal {B V : Type} [PartialOrder V] (feasible : Set B) (quality : B → V)
    (x : B) : Prop := x ∈ feasible ∧ IsGreatest (quality '' feasible) (quality x)

/-- Every accessible performance has an output, and all its outputs are optimal.
This combines totality and optimality without asserting local functionality. -/
def OptimalOutputs {W B A V : Type} [PartialOrder V]
    (p : OutputProfile W B A) (w : W) (a : A)
    (feasible : Set B) (quality : B → V) : Prop :=
  ∀ v, (v = w ∨ p.ontic.frame.access w v) →
    (p.performs v a → ∃ x, p.output v a x) ∧ ∀ x, p.output v a x → Optimal feasible quality x

/-- All admissible candidates admit a strictly better admissible candidate. -/
def StrictlyImprovable {B V : Type} [PartialOrder V]
    (feasible : Set B) (quality : B → V) : Prop :=
  ∀ x ∈ feasible, ∃ y ∈ feasible, quality x < quality y

/-- Both alternating effect candidates are feasible, including the one absent
at the selected world. The source is not a creation candidate. -/
def tiedCandidates : Set EffectBeing := {x | ∃ b, x = some b}
def tiedQuality (_ : EffectBeing) : Nat := 0

/-- One general stability constraint, its causal consequence, the no-best
obstruction, and a tied-optimum control on the existing varying ontology. -/
def OptimalChoiceCertificate : Prop :=
  (∀ (W B A V : Type) [PartialOrder V] (p : OutputProfile W B A)
    (w : W) (a : A) (feasible : Set B) (quality : B → V),
    OptimalOutputs p w a feasible quality →
    (∀ x y, Optimal feasible quality x → Optimal feasible quality y → x = y) →
    StableActOutput p w a) ∧
  (∀ (W B A V : Type) [PartialOrder V] (p : OutputProfile W B A)
    (w : W) (a : A) (x : B) (feasible : Set B) (quality : B → V),
    OptimalOutputs p w a feasible quality →
    (∀ x y, Optimal feasible quality x → Optimal feasible quality y → x = y) →
    SoundDistinctCauses p.ontic → RealizedOutputs p →
    SameActEverywhere p w a → p.output w a x →
    NecessaryAt p.ontic w x) ∧
  (∀ (B V : Type) [PartialOrder V] (feasible : Set B) (quality : B → V),
    StrictlyImprovable feasible quality → ¬ ∃ x, Optimal feasible quality x) ∧
  (∀ (B V : Type) [PartialOrder V] (feasible : Set B) (quality : B → V) (x y : B),
    Optimal feasible quality x → Optimal feasible quality y → quality x = quality y) ∧
  StrictlyImprovable (Set.univ : Set Nat) id ∧
  (OptimalOutputs varying false () tiedCandidates tiedQuality ∧
    Optimal tiedCandidates tiedQuality firstEffect ∧
    Optimal tiedCandidates tiedQuality secondEffect ∧ firstEffect ≠ secondEffect ∧
    LocallyDeterministic varying ∧ ¬ StableActOutput varying false () ∧
    ContingentAt varying.ontic false firstEffect)

/-! ## Issue #1737: omission, tied choice and contingent creation

These are finite structural interpretations of the existing world-indexed
\`OutputProfile\`, not a derivation of divine intellect, divine freedom,
simplicity or explanatory adequacy. An \`Option Bool\` world of \`none\`
means *no creature created*; an \`EffectBeing\` of \`none\` denotes the
same rigid necessary source at every world. They are different roles.
A world label is not an intrinsic selector or an explanation. -/

/-- An output's correspondence to an independently supplied selection table
at *all* worlds. Even full correspondence is only an extensional control,
not proof that selection intentionally causes the output. -/
def TracksSelectedCreation {W : Type}
    (p : OutputProfile W EffectBeing Unit) (selects : W → Bool → Prop) : Prop :=
  ∀ v b, p.output v () (some b) ↔ selects v b

/-- The same source exists at three mutually accessible worlds. \`none\` is
omission; \`some false\` and \`some true\` are two distinct created effects.
The source still exists, with no outgoing edge, at the omission world. -/
def threeWorldCreation : OutputProfile (Option Bool) EffectBeing Unit where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => x = source ∨ (w ≠ none ∧ x = w)
    Causes := fun w x y => x = source ∧ w ≠ none ∧ y = w
  }
  source := source
  performs := fun w _ => w ≠ none
  output := fun w _ x => w ≠ none ∧ x = w

/-- These only model source-borne *capacities*, not exercised intellect/will. -/
def hasIntellectualCapacity (_ : Option Bool) (x : EffectBeing) : Prop := x = source
def hasVolitionalCapacity (_ : Option Bool) (x : EffectBeing) : Prop := x = source

/-- Recognition of each possible candidate. Not omniscience, actual knowledge
of a contingent truth, intentional reference or a metaphysical possibility proof. -/
def recognizesOption (_ : Option Bool) (_ : Bool) : Prop := True

/-- Candidate selected as a table input; the world label supplies this datum
rather than explaining why the source makes that selection. -/
def selectedCandidate (w : Option Bool) (b : Bool) : Prop := w = some b

/-- An actual-world matching tag that fails to follow the second outcome. -/
def coincidentalTag (_ : Option Bool) (b : Bool) : Prop := b = false

/-- A single rigid source with stable powers, recognized admissible candidates,
causally sound and locally deterministic outputs, two contingent creations
and a genuine omission world. Full selection/output correlation can hold
while source necessity does not entail necessary performance or a fixed effect.
A matching tag at the first world fails cross-world selection/output fidelity. -/
def ThreeWorldCreationControl : Prop :=
  (∀ u v, threeWorldCreation.ontic.frame.access u v) ∧
  SoundDistinctCauses threeWorldCreation.ontic ∧
  NecessaryAt threeWorldCreation.ontic (some false) source ∧
  (∀ v, hasIntellectualCapacity v source ∧ hasVolitionalCapacity v source ∧
    ∀ b, recognizesOption v b) ∧
  RealizedOutputs threeWorldCreation ∧
  LocallyDeterministic threeWorldCreation ∧
  TracksSelectedCreation threeWorldCreation selectedCandidate ∧
  threeWorldCreation.output (some false) () firstEffect ∧
  threeWorldCreation.output (some true) () secondEffect ∧
  ContingentAt threeWorldCreation.ontic (some false) firstEffect ∧
  ContingentAt threeWorldCreation.ontic (some true) secondEffect ∧
  ¬ ExercisesCausation threeWorldCreation.ontic none source ∧
  ¬ SameActEverywhere threeWorldCreation (some false) () ∧
  ¬ StableActOutput threeWorldCreation (some false) () ∧
  (threeWorldCreation.output (some false) () firstEffect ∧
    coincidentalTag (some false) false) ∧
  ¬ TracksSelectedCreation threeWorldCreation coincidentalTag

/-- Two-world fixed-effect contrast: \`true\` produces the sole created
candidate, \`false\` produces nothing. Both worlds have the same source,
and the *same rigid act token is performed at both worlds*. This does not
define the intrinsic metaphysical identity of divine willing. -/
def alwaysPerformedOmission : OutputProfile Bool EffectBeing Unit where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => x = source ∨ (w = true ∧ x = firstEffect)
    Causes := fun w x y => x = source ∧ w = true ∧ y = firstEffect
  }
  source := source
  performs := fun _ _ => True
  output := fun w _ x => w = true ∧ x = firstEffect

/-- Identical ontic facts and outputs, but the productive act is not performed
at the no-creation world. This model changes only performance. -/
def optionallyPerformedOmission : OutputProfile Bool EffectBeing Unit :=
  { alwaysPerformedOmission with performs := fun w _ => w = true }

/-- Only the one created candidate is feasible; refraining is not a being or
another member of the created-effect candidate set. -/
def soleCreatedCandidate : Set EffectBeing := {firstEffect}

/-- The same effect's actual contingent existence is compatible with either
optional performance or universal act performance with an absent output.
The former retains selected-effect stability; the latter lacks it. -/
def OmissionStructureControl : Prop :=
  SoundDistinctCauses alwaysPerformedOmission.ontic ∧
  NecessaryAt alwaysPerformedOmission.ontic true source ∧
  RealizedOutputs alwaysPerformedOmission ∧
  RealizedOutputs optionallyPerformedOmission ∧
  LocallyDeterministic alwaysPerformedOmission ∧
  SameActEverywhere alwaysPerformedOmission true () ∧
  ¬ SameActEverywhere optionallyPerformedOmission true () ∧
  StableActOutput optionallyPerformedOmission true () ∧
  ¬ StableActOutput alwaysPerformedOmission true () ∧
  ContingentAt alwaysPerformedOmission.ontic true firstEffect ∧
  ¬ ExercisesCausation alwaysPerformedOmission.ontic false source

end TruthCore.Modal.OptimalCreationChoice
