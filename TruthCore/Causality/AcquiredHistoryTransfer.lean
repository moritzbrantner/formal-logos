module

public import TruthCore.Causality.ExerciseContribution

/-! A sufficient support route from independently charted histories.
The rank concerns selected productive contributors, not necessarily elapsed
time. One exercise model supplies the actual record; the target frame may
interpret real perfections more broadly. Its coverage and its interpretation
of productive credit are therefore separate open inputs. -/

@[expose] public section
namespace TruthCore.Causality.AcquiredHistoryTransfer
open TruthCore.Causality.JointGroups (Exercise)
open TruthCore.Causality.ExerciseContribution (Step Credit)
open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus)

variable {B E G S R : Type}

/-- Every covered token has either a productive input of the named source
or one productive input earlier in its covered history. Other contributors
need not be in the same history. In applications the coverage, stages and
actual contributor steps need warrant independent of the desired credit. -/
def RankedInputs (m : Exercise B E G S) (covered : B → E → Prop) (stage : E → Nat) : Prop :=
  ∀ a v, covered a v →
    (∃ u, m.bearer u = a ∧ Step m u v) ∨
    ∃ u, covered a u ∧ stage u < stage v ∧ Step m u v

/-- Nonempty productive ancestry from an event of the named source to this
very covered token. Indexed presence or identity alone incurs no Step. -/
def CoveredAncestry (m : Exercise B E G S) (covered : B → E → Prop) : Prop :=
  ∀ a v, covered a v → ∃ u, m.bearer u = a ∧ Relation.TransGen (Step m) u v

/-- Every actual respect tested by universal transfer is either esse itself
or is realized by an occurring covered event at the same bearer and respect.
This substantive scope premise is stronger than coverage of acquired
qualities alone. It postulates neither a source path nor its causal credit. -/
def TargetCoverage (m : Exercise B E G S) (covered : B → E → Prop) (tag : E → R)
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ a, CausesAllInGenus InAct CausesIn esse a →
    ∀ x r, x ≠ a → CausesIn a x esse → InAct x r →
      r = esse ∨ ∃ v, covered a v ∧ m.occurs m.actual v ∧ m.bearer v = x ∧ tag v = r

/-- Productive credit in the episode licenses responsibility in the external
frame on those same bearers and respect. This direction neither interprets
mere enabling as productive nor infers a path from the existence of a bearer. -/
def CreditWarrantsCause (m : Exercise B E G S) (tag : E → R)
    (CausesIn : B → B → R → Prop) : Prop :=
  ∀ a x r, Credit m tag a x r → CausesIn a x r

namespace PressWitness
open TruthCore.Causality.ExerciseContribution.Press

/-- Only the secondary stroke and the patient's two non-esse outcomes are
selected. The drive is a source event, not a selected output. -/
def covered (a : Role) (v : Event) : Prop :=
  a = .giver ∧ (v = .stroke ∨ v = .imprint ∨ v = .indicator)

def stage (v : Event) : Nat := if v = .imprint then 1 else 0

/-- The application row populates all three sufficient open interfaces,
including a selected actual non-esse target. No physical or metaphysical
generality follows from this finite witness. -/
def Populated : Prop :=
  let m := exercise .application
  let f := profile .application
  RankedInputs m covered stage ∧ TargetCoverage m covered respect f.InAct f.CausesIn f.esse ∧
    CreditWarrantsCause m respect f.CausesIn ∧
    CausesAllInGenus f.InAct f.CausesIn f.esse .giver ∧
    Role.patient ≠ Role.giver ∧ f.CausesIn .giver .patient f.esse ∧
    f.InAct .patient .work ∧ covered .giver .imprint

end PressWitness
end TruthCore.Causality.AcquiredHistoryTransfer
