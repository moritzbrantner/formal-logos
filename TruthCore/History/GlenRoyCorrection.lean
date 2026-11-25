module

public import TruthCore.Modal.RevisionUptake

/-!
# A finite comparison of the Glen Roy correction

The prior weights, ice configurations and reporting errors are stipulated.
The score measures changes in answer accuracy for a continuing recipient.
-/

@[expose] public section

namespace TruthCore.History.GlenRoyCorrection

inductive Origin | lake | sea deriving DecidableEq, BEq
inductive Action | omit | silent | transmit deriving DecidableEq, BEq
inductive Production | governed | independent

/-- Four terrain configurations and four equally weighted transmission states. -/
abbrev ReportLaw := Origin → Fin 4 → Fin 4 → Bool

def obstructionReport : ReportLaw := fun cause terrain noise =>
  let crosses := cause == .lake || terrain == 0
  crosses != (noise == 0)

def sample (law : ReportLaw) : List (Origin × Bool) :=
  let causes : List Origin := [.lake, .lake, .sea, .sea, .sea]
  causes.flatMap fun cause =>
    (List.finRange 4).flatMap fun terrain =>
      (List.finRange 4).map fun noise => (cause, law cause terrain noise)

def frequency (law : ReportLaw) (cause : Origin) (report : Bool) : Nat :=
  (sample law).count (cause, report)

/-- As in the model, ties retain the initial marine answer. -/
def favorsLake (law : ReportLaw) (report : Bool) : Bool :=
  decide (frequency law .lake report > frequency law .sea report)

def judgment (law : ReportLaw) (report : Bool) : Origin :=
  if favorsLake law report then .lake else .sea

/-- With support and a living recipient, the existing revision gate routes the report.
A supplied answer is copied directly and does not require use of that gate. -/
def episode (law : ReportLaw) (action : Action) (report : Bool)
    (alive : Bool := true) (supplied : Option Origin := none) : Option Origin :=
  if !alive || action == .omit then none
  else
    let useLake := TruthCore.Modal.RevisionUptake.revise false (favorsLake law report)
      (action == .transmit) false
    some (supplied.getD (if useLake then .lake else .sea))

def natural (upkeep transmission : Bool) : Action :=
  if !upkeep then .omit else if transmission then .transmit else .silent

def exercise (route : Production) (instruction : Action)
    (upkeep : Bool := true) (transmission : Bool := true) : Action :=
  match route with
  | .governed =>
    if instruction == .omit then .omit
    else natural upkeep (transmission && instruction == .transmit)
  | .independent => natural upkeep transmission

/-- Only a returned answer can repair an earlier marine answer or introduce an error. -/
def repairs (law : ReportLaw) (answer : Bool → Option Origin) : Nat :=
  (sample law).countP fun (cause, report) => cause == .lake && answer report == some .lake

def newErrors (law : ReportLaw) (answer : Bool → Option Origin) : Nat :=
  (sample law).countP fun (cause, report) => cause == .sea && answer report == some .lake

def gain (law : ReportLaw) (answer : Bool → Option Origin) : Int :=
  (repairs law answer : Int) - (newErrors law answer : Int)

def actionGain (law : ReportLaw) (a : Action) : Int :=
  gain law (fun report => episode law a report)

theorem reportCounts :
    (sample obstructionReport).length = 80 ∧
    frequency obstructionReport .lake true = 24 ∧ frequency obstructionReport .lake false = 8 ∧
    frequency obstructionReport .sea true = 18 ∧ frequency obstructionReport .sea false = 30 := by
  decide

theorem openingCorrections :
    let answer := fun r => episode obstructionReport .transmit r
    repairs obstructionReport answer = 24 ∧ newErrors obstructionReport answer = 18 := by
  decide

theorem actionScores :
    actionGain obstructionReport .omit = 0 ∧ actionGain obstructionReport .silent = 0 ∧
    actionGain obstructionReport .transmit = 6 := by decide

theorem transmissionUniquelyMaximizes (a : Action) :
    (∀ alternative, actionGain obstructionReport alternative ≤ actionGain obstructionReport a) ↔
      a = .transmit := by
  obtain ⟨omitted, silent, transmitted⟩ := actionScores
  constructor
  · intro best
    have h := best .transmit
    cases a <;> simp_all
  · rintro rfl alternative
    cases alternative <;> simp_all

/-- One control makes crossing equally frequent. The other makes the report
independent of terrain and origin while retaining both report outcomes. -/
def sameCrossing : ReportLaw := fun _ _ noise => noise != 0
def independentReport : ReportLaw := fun _ _ noise => noise.val < 2

theorem uninformativeControls (report : Bool) (action : Action) :
    judgment sameCrossing report = .sea ∧ actionGain sameCrossing action = 0 ∧
    judgment independentReport report = .sea ∧ actionGain independentReport action = 0 := by
  cases report <;> cases action <;> decide

theorem recipientInterventions (route : Production) :
    let law := obstructionReport
    let action := exercise route .transmit
    episode law action true = some .lake ∧ episode law action false = some .sea ∧
    episode law action true (supplied := some .lake) = some .lake ∧
    episode law action false (supplied := some .lake) = some .lake ∧
    episode law action true (alive := false) = none ∧
    episode law (exercise route .transmit (transmission := false)) true = some .sea ∧
    episode law (exercise route .transmit (upkeep := false)) true = none := by
  cases route <;> decide

theorem sourceIntervention :
    episode obstructionReport (exercise .governed .omit) true = none ∧
    episode obstructionReport (exercise .independent .omit) true = some .lake := by decide

/-- An external observer can supply the same verdict on every report. -/
theorem copiedVerdict (law : ReportLaw) (report : Bool) :
    episode law .transmit report (supplied := some (judgment law report)) =
    episode law .transmit report := rfl

theorem copiedAccuracy :
    gain obstructionReport (fun r =>
      episode obstructionReport .transmit r (supplied := some (judgment obstructionReport r))) = 6 := by
  simpa only [copiedVerdict, actionGain] using actionScores.2.2

end TruthCore.History.GlenRoyCorrection
