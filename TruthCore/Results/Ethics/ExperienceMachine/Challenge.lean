import TruthCore.Ethics.ExperienceMachine

/-!
Results of the experience-machine test of ST I q.5 a.1's "each thing is desirable
insofar as it is perfect". Analyst formulations, attribution deferred. See
`docs/notes/experience-machine.md`.
-/

namespace TruthCore.Results.Ethics.ExperienceMachine

open TruthCore.Latin.Aquinas.SummaTheologiae TruthCore.Ethics.ExperienceMachine
open TruthCore.Logic.StrengthComparison

/-- Near-transcription (instantiation): the stay-out verdict on two lives with the
same experiential profile, with the transfer bridge, gives a respect in which one
is desirable and the other is not, which experientialism excludes. Conjunct 8 of
`ExperienceMachineComparison` shows that the premise bundle, with the lives and
the betterness relation existentially closed, is equivalent to the conclusion: the
verdict is exactly a counterexample to experientialism, and all evidential weight
lies in the verdict and the bridge. -/
theorem experientialismFailsFromStayOut {Being Perfection Profile : Type}
    (experience : Being → Profile) (DesirableIn : Being → Perfection → Prop)
    (BetterFor : Being → Being → Prop) (real machine : Being)
    (hSame : SameExperience experience real machine)
    (hVerdict : StayOutVerdict BetterFor real machine)
    (hBridge : BetterRequiresRespectDifference BetterFor DesirableIn) :
    ExperientialismFails experience DesirableIn := by
  sorry

/-- Strength registration: q.5's biconditional gives its forward half. -/
theorem perfectMakesDesirableOfInsofar {Being Perfection : Type}
    (DesirableIn PerfectIn : Being → Perfection → Prop)
    (hInsofar : DesirableInsofarAsPerfectReading DesirableIn PerfectIn) :
    PerfectMakesDesirableReading DesirableIn PerfectIn := by
  sorry

/-- Strength registration: q.5's biconditional gives its backward half. -/
theorem desirableOnlyIfPerfectOfInsofar {Being Perfection : Type}
    (DesirableIn PerfectIn : Being → Perfection → Prop)
    (hInsofar : DesirableInsofarAsPerfectReading DesirableIn PerfectIn) :
    DesirableOnlyIfPerfectReading DesirableIn PerfectIn := by
  sorry

theorem forwardExactDifference : ForwardExactDifference := by
  sorry

theorem backwardExactDifference : BackwardExactDifference := by
  sorry

theorem experienceMachineComparison : ExperienceMachineComparison := by
  sorry

open TruthCore.Ethics.ExperienceMachine.Carrier in
theorem experienceMachineControls : ExperienceMachineControls := by
  sorry

end TruthCore.Results.Ethics.ExperienceMachine
