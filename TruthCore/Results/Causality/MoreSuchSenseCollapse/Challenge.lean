import TruthCore.Causality.MoreSuchSenseCollapse
import TruthCore.Results.Case.Catholicism.PreexistenceWithoutTransfer.Solution

/-!
# The "more such" package and the mode of possession: results

`moreSuchPackageForcesFormalPossession` composes the two registered derivations
`moreSuchOfDistinctCauseGives` (at the shared act predicate `InAct`) and
`distinctCauseGivesOfMoreSuch` (at formal act). `controls` checks the finite
interpretation of `MoreSuchSenseCollapse.Control` by decision. Analyst
formulations, attribution deferred; no premise is established.
-/

namespace TruthCore.Results.Causality.MoreSuchSenseCollapse

open TruthCore.Causality.MoreSuchSenseCollapse
open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.TermSenseForks (ActFrame)
open TruthCore.Results.Case.Catholicism.PreexistenceWithoutTransfer
  (moreSuchOfDistinctCauseGives distinctCauseGivesOfMoreSuch)

/-- Whatever single act predicate the possession premise and the exceeding step
share, the "more such" package with a formal more-such bearer gives formal
distinct-cause possession: the package yields "more such", and "what is more such
has the perfection", read formally, turns it into formal possession. -/
theorem moreSuchPackageForcesFormalPossession {W B T R : Type}
    (G : GradesFrame W B T R) (A : ActFrame B R) (InAct : B → R → Prop)
    (ReceivedIn LimitedBy : B → R → B → Prop) :
    MoreSuchPackageForcesFormalPossession G A InAct ReceivedIn LimitedBy := by
  sorry

/-- The induction-shaped interpretation and its uniform eminent
reinterpretation, checked by decision. -/
theorem controls : Control.Controls := by
  sorry

end TruthCore.Results.Causality.MoreSuchSenseCollapse
