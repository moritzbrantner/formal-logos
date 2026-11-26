module

public import TruthCore.Modal.CounterfactualSelectionControls

@[expose] public section

namespace TruthCore.Modal.WitnessPreservationIndividuation

open TruthCore.Causality.Frame
open TruthCore.Causality.CounterfactualDependence
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Modal.CounterfactualSelection
open TruthCore.Modal.CounterfactualSelectionControls
open World

/-- Provenance of the unique candidate for the tracked role at a standpoint.
A producer tag records history and by itself implies no current existence. -/
inductive Producer | source | backup
  deriving DecidableEq

/-- One role output at actual and far, with distinct provenance. Near has no output. -/
def replacementOutput : World → Option Producer
  | actual => some .source
  | near => none
  | far => some .backup

/-- EFFECT_INDIVIDUATION_1. Compare the unique candidate for the fixed role
with the actual output's producer tag. This is an exact-origin criterion for
this role and reference output. -/
def OriginIndividuation (output : World → Option Producer) (present : World → Prop) : Prop :=
  ∀ v, present v ↔ output v = some .source

/-- EFFECT_INDIVIDUATION_2. Track occupancy of the fixed role across worlds.
Either producer can supply an output that counts for that role. -/
def RoleIndividuation (output : World → Option Producer) (present : World → Prop) : Prop :=
  ∀ v, present v ↔ ∃ producer, output v = some producer

/-- Replace only the tracked effect's existence and presence interpretation.
The cause/dependence assignments, single moment, source and accessibility
are inherited from the replacement control. -/
def interpretedFrame (present : World → Prop) : CausalityFrame World Bool Unit Unit :=
  let base := Replacement.causalFrame
  let existsAt := fun v x => if x then v = actual else present v
  { base with
    history := { base.history with
      ontic := { base.history.ontic with ExistsAt := existsAt }
      IsAt := fun v x _ => existsAt v x } }

def caseCanBeWithout (present : World → Prop) (x y : Bool) : Prop :=
  ∃ v, (interpretedFrame present).history.ontic.ExistsAt v x ∧
    v ∈ absent (interpretedFrame present) y

def ReplacementPreservation (present : World → Prop) : Prop :=
  PreservesAccessibleAbsenceWitnesses (interpretedFrame present) (leastSelection rank) actual

def ReplacementExclusion (present : World → Prop) : Prop :=
  DependenceExcludesBeingWithout (interpretedFrame present).DependsForBeing
    (caseCanBeWithout present)

theorem case_realization (present : World → Prop) :
    BeingWithoutHasAccessibleWitness (interpretedFrame present) actual
      (caseCanBeWithout present) :=
  fun _ _ ⟨v, hx, hy⟩ => ⟨v, trivial, hx, hy⟩

theorem case_selected_loss (present : World → Prop) (loss : ¬ present near) :
    DependenceTracksSelectedAbsence (interpretedFrame present) (leastSelection rank) actual := by
  rintro _ _ ⟨rfl, rfl⟩ v hv
  have hNear := (least_away v).mp hv
  subst v
  exact loss

/-- If the far output counts and the near world has no such output, the
same least-absence selector omits the witness and still passes selected loss. -/
theorem omitted_far_witness (present : World → Prop)
    (survives : present far) (loss : ¬ present near) :
    ¬ PreservesAccessibleAbsenceWitnesses (interpretedFrame present) (leastSelection rank) actual := by
  intro preserve
  obtain ⟨v, _, hv, _, hSelected⟩ := preserve false true
    ⟨far, trivial, survives, fun h => World.noConfusion h⟩
  have hNear := (least_away v).mp hSelected
  subst v
  exact loss hv

theorem role_omits_witness (present : World → Prop)
    (individuate : RoleIndividuation replacementOutput present) :
    DependenceTracksSelectedAbsence (interpretedFrame present) (leastSelection rank) actual ∧
    ¬ PreservesAccessibleAbsenceWitnesses (interpretedFrame present) (leastSelection rank) actual ∧
    ¬ ReplacementExclusion present := by
  have nearLoss : ¬ present near := by
    intro h
    obtain ⟨_, hProducer⟩ := (individuate near).mp h
    cases hProducer
  have farPresent := (individuate far).mpr ⟨.backup, rfl⟩
  refine ⟨case_selected_loss present nearLoss, omitted_far_witness present farPresent nearLoss, ?_⟩
  intro excludes
  exact excludes false true ⟨rfl, rfl⟩ ⟨far, farPresent, fun h => World.noConfusion h⟩

/-- Change only the provenance of the far output. This is a historical-origin
assignment, with no commitment to an independently supported complete history. -/
def retainedOriginOutput : World → Option Producer :=
  fun v => if v = far then some .source else replacementOutput v

theorem retained_origin_omits_witness (present : World → Prop)
    (individuate : OriginIndividuation retainedOriginOutput present) :
    ¬ PreservesAccessibleAbsenceWitnesses (interpretedFrame present) (leastSelection rank) actual :=
  omitted_far_witness present ((individuate far).mpr rfl)
    (by
      intro h
      have hProducer := (individuate near).mp h
      cases hProducer)

end TruthCore.Modal.WitnessPreservationIndividuation
