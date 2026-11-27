module

public import TruthCore.Causality.MoreSuchSenseCollapse
public import TruthCore.Results.Case.Catholicism.PreexistenceWithoutTransfer.Solution

/-!
# The "more such" package and the mode of possession: results

`moreSuchPackageForcesFormalPossession` composes the two registered derivations
`moreSuchOfDistinctCauseGives` (at the shared act predicate `InAct`) and
`distinctCauseGivesOfMoreSuch` (at formal act). `controls` checks the finite
interpretation of `MoreSuchSenseCollapse.Control` by decision. Analyst
formulations, attribution deferred; no premise is established.
-/

@[expose] public section

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
  intro hHas hRecv hLim hOnly hNot hExceed hBearer
  exact distinctCauseGivesOfMoreSuch G.CausesIn A.InActFormally G.MoreIn
    (moreSuchOfDistinctCauseGives G.CausesIn InAct ReceivedIn LimitedBy G.MoreIn
      hHas hRecv hLim hOnly hNot hExceed)
    hBearer

/-- The induction-shaped interpretation and its uniform eminent
reinterpretation, checked by decision. -/
theorem controls : Control.Controls := by
  dsimp [Control.Controls, FormalPossessionGap, FormalDistinctCausePossession,
    TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives,
    TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect,
    TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient,
    TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception,
    TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect,
    TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited,
    TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading,
    TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading,
    Control.formalGrades, Control.eminentGrades, Control.act,
    TruthCore.Causality.CartesianAdequacy.gradesOf, Control.causes, Control.formal,
    Control.virtual, Control.received, Control.limited, Control.moreFormal,
    Control.moreEminent, TruthCore.Causality.TermSenseForks.ActFrame.InActFormallyOrVirtually]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The degree-indexed interpretation, checked by decision. The larger instance
budget only lets instance search assemble the `Decidable` instance of the
negated three-variable quantifier. -/
theorem ordinaryControls : Control.OrdinaryControls := by
  dsimp [Control.OrdinaryControls, FormalPossessionGap, OrdinaryComparativeGap,
    OrdinaryMoreSuch, OrdinaryComparative, EminentComparative,
    TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading,
    Control.grades3, Control.act3, TruthCore.Causality.CartesianAdequacy.gradesOf,
    Control.causes3, Control.formal3, Control.virtual3, Control.temp, Control.surpasses,
    TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading,
    TruthCore.Causality.TermSenseForks.ActFrame.InActFormallyOrVirtually]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end TruthCore.Results.Causality.MoreSuchSenseCollapse
