module

public import TruthCore.Causality.ComposerTemporalDefinitionFork
public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Causality.PartMediatedSelfMotion
public import TruthCore.Causality.TermSenseForks

/-! Analyst restrictions on existing relations and frames. The origin bridge
is an explicit hypothesis. The test frames set each primitive independently. -/

@[expose] public section

namespace TruthCore.Case.Catholicism.NoSelfCauseScope

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.ComposerTemporalDefinitionFork

/-- Every effect has a distinct incoming efficient edge. -/
def EffectsHaveDistinctCauses {B R : Type}
    (EfficientlyCausesIn : B → B → R → Prop) : Prop :=
  ∀ x, (∃ c r, EfficientlyCausesIn c x r) →
    ∃ c r, c ≠ x ∧ EfficientlyCausesIn c x r

/-- A diagonal efficient edge has a distinct incoming efficient alternative
(possibly in a different respect), or the bearer is its own CAUSE_4 origin. -/
def SelfEfficientHasAlternativeOrOrigin {B R : Type} (f : CauseFrame B R) : Prop :=
  ∀ x r, f.EfficientlyCausesIn x x r →
    (∃ c s, c ≠ x ∧ f.EfficientlyCausesIn c x s) ∨ f.CausesOrigin x x

/-- No temporal efficient diagonal on an actual self-uniting tuple. -/
def NoTemporalSelfUniter (f : Frame) : Prop :=
  ∀ x a b, f.Unites x a b x → ∀ r, ¬ Temporal f x x r

namespace Control

open TruthCore.Causality.PartMediatedSelfMotion
open TruthCore.Alternatives.ActPotencyRegress (MovedNotYetInActReading)

/-- Retain both the component-patient lift and the whole-level attribution. -/
def MixedMotion (a b : Carrier) (r : Respect) : Prop :=
  PatientLift a b r ∨ AggregateLift a b r

/-- The distinct edge is assigned to origination. The diagonal is assigned to
a perfection at a different respect. The efficient relation is stipulated to
include both entries as a test of that coarse interpretation. -/
def accident : CauseFrame Bool Bool where
  MovedIn := fun _ _ => False
  MovesIn := fun _ _ _ => False
  EfficientlyCausesIn := fun c x r =>
    (c = false ∧ x = true ∧ r = false) ∨ (c = true ∧ x = true ∧ r = true)
  CausesIn := fun c x r => c = true ∧ x = true ∧ r = true
  CausesOrigin := fun c x => c = false ∧ x = true

/-- A past distinct uniter and a past diagonal outside its tuple. -/
def pastEdges : Frame where
  Being := Bool
  Respect := Bool
  Time := Bool
  now := true
  EfficientAt := fun t c x r => t = false ∧ accident.EfficientlyCausesIn c x r
  Attributed := accident.EfficientlyCausesIn
  Unites := fun c _ _ x => c = false ∧ x = true

/-- Populated structural comparisons of same-respect motion, restricted
origin and the temporal uniter. -/
def Boundaries : Prop :=
  (InternalMotion .whole .displacement ∧
    ReducedOnlyByABeingInActReading WholeMoved MixedMotion
      (fun a r => a = .motor ∧ r = .displacement) ∧
    MovedNotYetInActReading WholeMoved (fun a r => a = .motor ∧ r = .displacement) ∧
    (¬ NothingMovesItselfInSameRespectReading WholeMoved MixedMotion)) ∧
  (SomeSubjectCausesItsOwnPerfection accident ∧ accident.CausesOrigin false true ∧
    NothingOriginatesItself accident ∧
    SelfEfficientHasAlternativeOrOrigin accident ∧
    EffectsHaveDistinctCauses accident.EfficientlyCausesIn ∧
    (¬ SelfEfficientCausationIsSelfOrigination accident) ∧
    (¬ SelfEfficientCausationIsSelfMoving accident) ∧
    (¬ NothingCausesItselfInRouteSense accident.CausesIn) ∧
    (¬ NothingIsEfficientCauseOfItselfReading accident.EfficientlyCausesIn) ∧
    OrderOfEfficientCausesFoundReading accident.EfficientlyCausesIn ∧
    SecondEfficientCausesCauseOnlyAsCausedReading accident.EfficientlyCausesIn (fun _ _ => False) ∧
    NoInfinitePerSeEfficientCauseSeriesReading (fun (_ _ : Bool) => False) ∧
    IsFirstEfficientCause accident.EfficientlyCausesIn false) ∧
  (TemporalComposer pastEdges ∧ pastEdges.Unites false false true true ∧
    CurrentNoSelf pastEdges ∧ NoTemporalSelfUniter pastEdges ∧
    ¬ AllTimeNoSelf pastEdges)

end Control
end TruthCore.Case.Catholicism.NoSelfCauseScope
