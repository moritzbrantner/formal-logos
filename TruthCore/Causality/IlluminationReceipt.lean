module
public import TruthCore.Causality.PreservationMeaning

/-! Analyst forward model of the existing U/R/L illumination brief. The input
is emitted amount, a path gate transmits it, and a receptive region responds
to summed arriving amounts. None of these bodies refers to the output's loss.
This is a stipulated quantity circuit, not optics or a sourced definition of
production. The receiver is the same air region; the effect is its illumination,
never its substantial existence. Actual exercise remains separately supplied. -/
@[expose] public section
namespace TruthCore.Causality.IlluminationReceipt
open JointGroups PreservationMeaning

inductive Bearer | sun | air | lamp deriving DecidableEq
inductive Event | solarArrival | lampArrival | receptivity | illumination deriving DecidableEq

/-- Exogenous emissions, independently switched paths, and receiver receptivity.
Amounts are uncalibrated natural-number tokens, not physical radiometry. -/
structure Scenario where
  solarEmission : Nat
  solarPath : Bool
  lampEmission : Nat
  lampPath : Bool
  receptive : Bool

/-- An open path transmits the given amount; a closed path transmits none.
No reverse equation determines the emitter from the illumination. -/
def transmit (emission : Nat) (path : Bool) : Nat := if path then emission else 0

def solarInput (s : Scenario) : Nat := transmit s.solarEmission s.solarPath
def lampInput (s : Scenario) : Nat := transmit s.lampEmission s.lampPath

/-- Receiving response: sum arriving quantities only when receptive. The
receiver does not add a source term. This gives the role distinction content
inside this model, without deriving productive causation from an equation. -/
def response (s : Scenario) : Nat :=
  if s.receptive then solarInput s + lampInput s else 0

/-- False selects the solar record, true the independent lamp record.
Opening the alternative roster does not change the event L or its bearer. -/
def records (includeLamp : Bool) : Groups Event Bool where
  contributors := fun g => {e | if g then e = .lampArrival else e = .solarArrival}
  enablers := fun _ => {e | e = .receptivity}
  effect := fun _ => .illumination
  admitted := fun g => g = false ∨ includeLamp = true

/-- Distinct source and receiving bearers, stable in every scenario. -/
noncomputable def bearer : Event → Bearer :=
  Event.rec .sun .lamp .air .air

/-- U records received input, not bare sun existence or output success. R
records receptivity, while L is positive receiver response. -/
noncomputable def occurs (s : Scenario) (e : Event) : Prop :=
  Event.rec (0 < solarInput s) (0 < lampInput s) (s.receptive = true)
    (0 < response s) e

/-- Solar-only scope forbids arriving lamp input. This is an explicit domain
restriction, not a claim that sunlight is the only possible illumination. -/
def allowed (includeLamp : Bool) (s : Scenario) : Prop :=
  includeLamp = true ∨ lampInput s = 0

/-- The actual scenario and exercise assignment are independent inputs. An
available record or positive response does not set the exercise flag. -/
noncomputable def model (includeLamp : Bool) (actual : Scenario)
    (performed : Bool → Prop) : Exercise Bearer Event Bool Scenario where
  groups := records includeLamp
  bearer := bearer
  occurs := occurs
  allowed := allowed includeLamp
  actual := actual
  exercised := performed

/-- A quantitative mechanism result: positive receiver response has exactly
one or both arriving inputs and receptivity. No actual causal claim follows. -/
def ResponseLaw : Prop := ∀ s : Scenario,
  (0 < response s ↔ (0 < solarInput s ∨ 0 < lampInput s) ∧ s.receptive = true) ∧
  (s.solarEmission = 0 → solarInput s = 0) ∧
  (s.solarPath = false → solarInput s = 0) ∧
  (0 < solarInput s ↔ 0 < s.solarEmission ∧ s.solarPath = true)

/-- Source cuts and coverage for the existing U/R/L vocabulary. Exercise
coherence is conditional on its exact correspondence to admitted occurring
inputs; genuine productive interpretation is an application obligation. -/
def RecordAnalysis : Prop := ∀ (a : Scenario) (performed : Bool → Prop),
  (∀ includeLamp, RecordCovered (model includeLamp a performed) .illumination) ∧
  SourceCut (model false a performed) .illumination .sun ∧
  ¬ SourceCut (model true a performed) .illumination .sun ∧
  ¬ SourceCut (model false a performed) .illumination .air ∧
  (∀ includeLamp, allowed includeLamp a →
    (∀ g, performed g → (records includeLamp).admitted g ∧
      (if g then 0 < lampInput a else 0 < solarInput a) ∧ a.receptive = true) →
    (model includeLamp a performed).coherent) ∧
  (∀ includeLamp s g, (records includeLamp).admitted g →
    (∀ e, e ∈ (records includeLamp).members g → occurs s e) →
    occurs s .illumination)

def bright : Scenario := ⟨3, true, 0, true, true⟩
def withdrawn : Scenario := ⟨0, true, 0, true, true⟩
def blocked : Scenario := ⟨3, false, 0, true, true⟩
def nonreceptive : Scenario := ⟨3, true, 0, true, false⟩
def lampLit : Scenario := ⟨0, true, 5, true, true⟩
def bothLit : Scenario := ⟨3, true, 5, true, true⟩

/-- The same receiver and same illumination event throughout. Real-world
occurrence/exercise is not asserted by these declared numeric assignments. -/
def Controls : Prop :=
  (model false bright (fun g => g = false)).coherent ∧
  PopulatedCut (model false bright (fun g => g = false)) bright .illumination .sun ∧
  response bright = 3 ∧
  (allowed false withdrawn ∧ occurs withdrawn .receptivity ∧ response withdrawn = 0) ∧
  (occurs blocked .receptivity ∧ blocked.solarEmission = 3 ∧ response blocked = 0) ∧
  (solarInput nonreceptive = 3 ∧ response nonreceptive = 0) ∧
  (allowed true lampLit ∧ ¬ allowed false lampLit ∧ response lampLit = 5 ∧
    SourceInactive (model true bright (fun g => g = false)) lampLit .sun) ∧
  (response bothLit = 8 ∧ solarInput bothLit = 3 ∧ lampInput bothLit = 5 ∧
    (model true bothLit (fun _ => True)).coherent) ∧
  bearer .illumination = .air ∧ bearer .solarArrival ≠ bearer .illumination ∧
  (model false bright (fun _ => False)).coherent ∧
  AvailableRecord (model false bright (fun _ => False)) bright .illumination ∧
  (∀ g, ¬ (model false bright (fun _ => False)).exercised g)
end TruthCore.Causality.IlluminationReceipt
