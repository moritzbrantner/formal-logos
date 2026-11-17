module
public import TruthCore.Causality.JointGroups

/-! Atemporal analyst component for preservation research. Reuses the existing
contributor/enabler records. Their productive interpretation is an OPEN
primitive application burden, not inferred from admission, occurrence or a
withdrawal counterfactual.
The new content is an all-alternative source cut and its input-availability consequence.
Neither original PRESERVATION sense is bound to this component. -/
@[expose] public section
namespace TruthCore.Causality.PreservationMeaning
open JointGroups

/-- An admitted nonempty record for this exact effect token whose
contributors AND enablers occur in the selected scenario. No conclusion about
occurrence of the effect follows without a sufficiency premise. -/
def AvailableRecord {B E G S : Type} (m : Exercise B E G S) (s : S) (e : E) : Prop :=
  ∃ g, m.groups.admitted g ∧ m.groups.effect g = e ∧
    (∃ a, a ∈ m.groups.contributors g) ∧
    ∀ a, a ∈ m.groups.members g → m.occurs s a

/-- Every admitted record alternative for the SAME effect contains a
contributor borne by c. Enablers alone do not qualify. This is a structural
sufficient condition, not a necessary characterization of causal dependence:
inadmissible or unrealizable alternatives must not be silently discarded. -/
def SourceCut {B E G S : Type} (m : Exercise B E G S) (e : E) (c : B) : Prop :=
  ∀ g, m.groups.admitted g → m.groups.effect g = e →
    ∃ a, a ∈ m.groups.contributors g ∧ m.bearer a = c

/-- Nonvacuous route-relative source requirement: an available input record exists, and
all admitted routes have the source cut. No temporal sequence is imposed. -/
def PopulatedCut {B E G S : Type} (m : Exercise B E G S)
    (s : S) (e : E) (c : B) : Prop := AvailableRecord m s e ∧ SourceCut m e c

/-- No contributor event borne by c occurs. Other sources and enablers can
remain active; this is not nonexistence of c or an intervention law. -/
def SourceInactive {B E G S : Type} (m : Exercise B E G S) (s : S) (c : B) : Prop :=
  ∀ g a, m.groups.admitted g → a ∈ m.groups.contributors g →
    m.bearer a = c → ¬ m.occurs s a

/-- An adequacy premise for a chosen effect token, not a whole root conclusion:
its occurrence is covered by a nonempty admitted record with occurring inputs. This can
fail (e.g. a persistence interpretation) and is not supplied by Groups. -/
def RecordCovered {B E G S : Type} (m : Exercise B E G S) (e : E) : Prop :=
  ∀ s, m.allowed s → m.occurs s e → AvailableRecord m s e

/-- Conditional cut consequences, keeping effect occurrence and completeness
separate. No source distinctness, esse interpretation, or CausesIn is inferred. -/
def CutConsequences : Prop := ∀ (B E G S : Type) (m : Exercise B E G S)
    (e : E) (c : B), SourceCut m e c →
    (∀ s, AvailableRecord m s e → ∃ a, m.bearer a = c ∧ m.occurs s a) ∧
    (∀ s, SourceInactive m s c → ¬ AvailableRecord m s e) ∧
    (RecordCovered m e → ∀ s, m.allowed s → SourceInactive m s c → ¬ m.occurs s e)

namespace Control
/-- Two alternative episodes, the same source, one receptive enabler and the
same effect. This is a stipulated dependency circuit, not an esse example. -/
inductive Event | left | right | receptive | effect deriving DecidableEq
open Event
abbrev Scenario := Bool × Bool × Bool

def groups : Groups Event Bool where
  contributors := fun g => {a | if g then a = right else a = left}
  enablers := fun _ => {a | a = receptive}
  effect := fun _ => effect
  admitted := fun _ => True

/-- Direct recursor form keeps this truth table axiom-free; no executable
physical simulator is claimed. -/
noncomputable def model : Exercise Bool Event Bool Scenario where
  groups := groups
  bearer := fun a => Event.rec false false true true a
  occurs := fun s a => Event.rec (s.1 = true) (s.2.1 = true)
    (s.2.2 = true) ((s.1 = true ∨ s.2.1 = true) ∧ s.2.2 = true) a
  allowed := fun _ => True
  actual := (true, true, true)
  exercised := fun _ => True

/-- Independence interpretation changes only effect occurrence: a fully
populated actual input record still exists, but the effect also occurs
without input. This shows why coverage is an additional obligation. -/
noncomputable def uncovered : Exercise Bool Event Bool Scenario :=
  { model with occurs := fun s a => if a = effect then True else model.occurs s a }

/-- Redundancy and coverage controls. Same-source alternatives preserve source
requirement while neither individual episode is indispensable across routes.
Changing one supplier's bearer defeats the cut. A receptive enabler is not a
productive source. Role/occurrence and cut alone do not give existential loss. -/
def Controls : Prop :=
  PopulatedCut model model.actual effect false ∧
  AvailableRecord model (true, false, true) effect ∧
  AvailableRecord model (false, true, true) effect ∧
  ¬ AvailableRecord model (true, true, false) effect ∧
  ¬ SourceCut model effect true ∧
  RecordCovered model effect ∧
  (let m := { model with bearer := fun a => if a = right then true else model.bearer a };
    ¬ SourceCut m effect false) ∧
  PopulatedCut uncovered uncovered.actual effect false ∧
  SourceInactive uncovered (false, false, true) false ∧
  uncovered.occurs (false, false, true) effect ∧
  ¬ RecordCovered uncovered effect
end Control
end TruthCore.Causality.PreservationMeaning
