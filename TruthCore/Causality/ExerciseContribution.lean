module

public import TruthCore.Explanation.BorrowedExercise
public import TruthCore.Causality.GiverIndexedApplication

/-! Analyst interpretation of cause in a respect for one selected exercise.
Productive credit tracks actual exercised contributor paths. The interpretation
counts a mediated productive contribution, but neither a mere enabler nor the
identity of an event index, as a ground for such credit. Warrant for a record's
contributor classification and for this interpretation of CAUSE_2 remains open. -/

@[expose] public section
namespace TruthCore.Causality.ExerciseContribution
open TruthCore.Causality.JointGroups (Exercise Groups)
open TruthCore.Explanation.BorrowedExercise (Lent Secondary SelfExercising)
open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Case.Catholicism (UniversalCauseTransfersPerfections)

variable {B E G S R : Type}

/-- An actual record with an occurring productive contributor and effect.
Both occurrences are explicitly at the selected actual scenario. -/
def Step (m : Exercise B E G S) (u v : E) : Prop :=
  m.occurs m.actual u ∧ m.occurs m.actual v ∧
    ∃ g, m.exercisedGroups.admitted g ∧ m.groups.effect g = v ∧ u ∈ m.groups.contributors g

/-- An actual realization of this bearer and respect at the selected context. -/
def Realized (m : Exercise B E G S) (respect : E → R) (x : B) (r : R) : Prop :=
  ∃ v, m.occurs m.actual v ∧ m.bearer v = x ∧ respect v = r

/-- Selected interpretation of productive credit. A nonempty actual contributor
path joins an event of a to an event of x in respect r. Repeated realizations of
one respect are existentially projected; a selected token must be fixed for a
claim about this particular occurrence. No claim of independent sufficiency. -/
def Credit (m : Exercise B E G S) (respect : E → R) (a x : B) (r : R) : Prop :=
  ∃ u v, m.bearer u = a ∧ m.bearer v = x ∧ respect v = r ∧ Relation.TransGen (Step m) u v

/-- Candidate interpretation of giver-indexed application for the selected
stroke and result. The productive path reaches the secondary's very exercise,
which productively contributes to this result. Its intended present-tense
exercise interpretation must be defended; temporal order is not encoded. -/
def ThroughAt (m : Exercise B E G S) (stroke result : E) (a b x : B) : Prop :=
  m.bearer stroke = b ∧ m.bearer result = x ∧
  (∃ u, m.bearer u = a ∧ Relation.TransGen (Step m) u stroke) ∧ Step m stroke result

/-- A general path consequence at the respect of the specified result. The
same result event remains the endpoint of both paths before projection to
bearer/respect credit. -/
def ThroughYieldsJointCredit : Prop :=
  ∀ (B E G S R : Type) (m : Exercise B E G S) (respect : E → R) (stroke result : E)
    (a b x : B), ThroughAt m stroke result a b x →
    (∃ u, m.bearer u = a ∧ Relation.TransGen (Step m) u result) ∧
    Relation.TransGen (Step m) stroke result ∧
    Credit m respect a x (respect result) ∧ Credit m respect b x (respect result)

namespace Press

inductive Role | giver | agent | patient deriving DecidableEq
inductive Respect | esse | work | signal deriving DecidableEq
inductive Event
  | giverEsse | agentEsse | patientEsse | maintenance | drive | stroke | imprint | indicator
  deriving DecidableEq
inductive Row | conservation | cooperation | application deriving DecidableEq

def bearer : Event → Role
  | .agentEsse | .stroke => .agent
  | .patientEsse | .imprint | .indicator => .patient
  | _ => .giver

def respect : Event → Respect
  | .giverEsse | .agentEsse | .patientEsse => .esse
  | .indicator => .signal
  | _ => .work

/-- The two switches control the drive and the secondary's own stroke input.
All three bearers and maintenance are present throughout. In cooperation the
imprint needs both inputs. In application the drive brings the stroke into
exercise, and its imprint follows. All rows have the same on/on actual
occurrences. These are stipulated contrasts within this press profile. -/
def occurs (row : Row) (s : Bool × Bool) : Event → Prop
  | .drive | .indicator => s.1 = true
  | .stroke => if row = .application then s.1 = true else s.2 = true
  | .imprint => match row with
    | .conservation => s.2 = true
    | .cooperation => s.1 = true ∧ s.2 = true
    | .application => s.1 = true
  | _ => True

/-- Records use their output events as indices. Roots have no exercised
incoming record. In conservation and cooperation the secondary exercises
without a lender for its stroke in the recorded scheme. In the application
case the drive actually lends to the stroke. -/
def active (row : Row) : Event → Prop
  | .agentEsse | .patientEsse | .imprint | .indicator => True
  | .stroke => row = .application
  | _ => False

def contributor (row : Row) (g u : Event) : Prop :=
  match g with
  | .agentEsse | .patientEsse => u = .maintenance
  | .stroke | .indicator => u = .drive
  | .imprint => u = .stroke ∨ (row = .cooperation ∧ u = .drive)
  | _ => False

def enabler (g u : Event) : Prop :=
  match g with
  | .agentEsse | .patientEsse | .indicator => u = .giverEsse
  | .stroke => u = .agentEsse
  | .imprint => u = .patientEsse ∨ u = .agentEsse
  | _ => False

def exercise (row : Row) : Exercise Role Event Event (Bool × Bool) where
  groups := { contributors := contributor row, enablers := enabler, effect := id,
              admitted := fun g => g = .agentEsse ∨ g = .patientEsse ∨ g = .stroke ∨
                                   g = .imprint ∨ g = .indicator }
  bearer := bearer
  occurs := occurs row
  actual := (true, true)
  allowed := fun _ => True
  exercised := active row

/-- The q3 profile uses only realized respects and actual path credit. The
principle slots are irrelevant to the transfer test and have singleton values. -/
def profile (row : Row) : Profile Role Unit Respect where
  InAct := Realized (exercise row) respect
  CausesIn := Credit (exercise row) respect
  esse := .esse
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  essentialPrinciplesAloneSufficeForEsse := fun _ => False

def transfer (row : Row) : Prop :=
  UniversalCauseTransfersPerfections (profile row).InAct (profile row).CausesIn .esse

/-- Shared background. All actual bearers have esse; the giver causes the esse
of each other bearer, the secondary causes the particular mark, and the giver
causes a separate indicator. Coherence includes all exercised enablers. -/
def Background (row : Row) : Prop :=
  (exercise row).coherent ∧ (∀ b, (profile row).InAct b .esse) ∧
  CausesAllInGenus (profile row).InAct (profile row).CausesIn .esse .giver ∧
  Step (exercise row) .stroke .imprint ∧ Step (exercise row) .drive .indicator ∧
  (profile row).CausesIn .agent .patient .work ∧
  (profile row).CausesIn .giver .patient .signal

/-- Three actual contribution mechanisms on the same occurrences and bearers.
`Secondary` is the borrowed-exercise predicate: this agent actually exercises
under a lender while retaining a capacity at an allowed scenario without one.
The supplied capability predicate is constant true for this comparison.
`transfer` covers the actual respects in this finite profile only. -/
def Certificate : Prop :=
  (∀ row, Background row) ∧
  (SelfExercising (exercise .conservation) .stroke ∧
    ¬ (profile .conservation).CausesIn .giver .patient .work ∧
    ¬ ThroughAt (exercise .conservation) .stroke .imprint .giver .agent .patient ∧
    ¬ transfer .conservation) ∧
  (SelfExercising (exercise .cooperation) .stroke ∧
    (exercise .cooperation).jointlySufficient .imprint ∧
    (exercise .cooperation).indispensable .imprint .drive ∧
    (exercise .cooperation).indispensable .imprint .stroke ∧
    Step (exercise .cooperation) .drive .imprint ∧
    (profile .cooperation).CausesIn .giver .patient .work ∧
    ¬ ThroughAt (exercise .cooperation) .stroke .imprint .giver .agent .patient ∧
    ¬ (profile .cooperation).CausesIn .giver .agent .work ∧ ¬ transfer .cooperation) ∧
  (Secondary (exercise .application) (fun _ _ => True) .stroke ∧
    ¬ Step (exercise .application) .drive .imprint ∧
    ThroughAt (exercise .application) .stroke .imprint .giver .agent .patient ∧
    (profile .application).CausesIn .giver .patient .work ∧ transfer .application)

end Press
end TruthCore.Causality.ExerciseContribution
