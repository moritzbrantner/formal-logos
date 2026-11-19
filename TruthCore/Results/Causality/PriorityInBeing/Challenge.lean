import TruthCore.Causality.PriorityInBeing
import TruthCore.Causality.Round2PerfectionPrimacy
import TruthCore.Causality.Round5Worklist
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsFirstBeing.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency

/-!
# Priority in being: per-sense arguments for spine III (#1751, slice 2)

Each argument uses one sense of PRIOR, except the pure-act argument, whose only
passage from PRIOR_4 to PRIOR_1 is the explicit bridge
`FirstInBeingMoverIsFirstInActPriority`. Existing results are composed, not
restated (`firstMoverIsFirstBeing`, `firstMoverPureAct`).
-/

namespace TruthCore.Results.Causality.PriorityInBeing

open TruthCore.Causality.PriorityInBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct MaximeEnsIsGod)
open TruthCore.Causality.Round2PerfectionPrimacy
  (DependenceExcludesBeingWithout IndependenceAllowsBeingWithout)
open TruthCore.Causality.Round5Worklist (DependenceForBeingIsCausedBeing)

/-- The n. 15 criterion gives PRIOR_4 by definition. -/
theorem beingWithoutCriterion {B : Type} (CanBeWithout : B → B → Prop) :
    BeingWithoutCriterionGivesPriorityInBeing CanBeWithout := by
  sorry

/-- PRIOR_4 requires nonmutual dependence, from the two being-without bridges
and excluded middle. If `y` is prior in being to `x`: `y` can be without `x`, so
by 000e1f65 `y` does not depend on `x`; `x` cannot be without `y`, so by
8ab3d114 it is not the case that `x` does not depend on `y`, and excluded middle
gives that `x` depends on `y`. -/
theorem priorityInBeingRequiresNonmutualDependence {B : Type}
    (DependsForBeing CanBeWithout : B → B → Prop)
    (hExcludes : DependenceExcludesBeingWithout DependsForBeing CanBeWithout)
    (hAllows : IndependenceAllowsBeingWithout DependsForBeing CanBeWithout)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    PriorityInBeingRequiresNonmutualDependence CanBeWithout DependsForBeing := by
  sorry

/-- What is prior in being to a thing is a cause of its being: the PRIOR_4
sibling of result `da2bbf20` (argument 1cb656a0). -/
theorem priorInBeingCausesBeing {B R : Type}
    (CanBeWithout DependsForBeing : B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hRequires : PriorityInBeingRequiresNonmutualDependence CanBeWithout DependsForBeing)
    (hCaused : DependenceForBeingIsCausedBeing DependsForBeing CausesIn esse) :
    PriorInBeingIsCauseOfBeing CanBeWithout CausesIn esse := by
  sorry

/-- Every first mover moved by none is first in being: the PRIOR_4 sibling of
argument f8992ef7, by the existing theorem `firstMoverIsFirstBeing` applied to
the relation `PriorInBeing CanBeWithout`. -/
theorem firstMoverIsFirstInBeing {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (CanBeWithout : Being → Being → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect) (God : Being → Prop)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hGod : MaximeEnsIsGod InAct MoreIn esse God)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God)
    (hPriorCause : PriorInBeingIsCauseOfBeing CanBeWithout CausesIn esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    FirstUnmovedMoverIsFirstInBeing MovedIn MovesIn CanBeWithout := by
  sorry

/-- Pure act from first-in-being, through the explicit PRIOR_4 → PRIOR_1 bridge
at first unmoved movers and act's simple priority (a4d3261a, PRIOR_1), under
adopted POTENCY_1 (`InPotency x r := CanBe x r ∧ ¬ InAct x r`), where
non-overlap is definitional (`AdoptedPotency.nonOverlapByConservativeAnalysis`).
These are the premises of argument 3e2366b5 with its first-being premise
replaced by the PRIOR_4 sibling plus the bridge, and its non-overlap premise
(c6d6379b, which carries POTENCY_2) discharged by the adopted sense. -/
theorem firstMoverPureActFromFirstInBeing {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct CanBe : Being → Respect → Prop)
    (CanBeWithout PriorSimply : Being → Being → Prop)
    (hFirstInBeing : FirstUnmovedMoverIsFirstInBeing MovedIn MovesIn CanBeWithout)
    (hBridge : FirstInBeingMoverIsFirstInActPriority MovedIn MovesIn CanBeWithout PriorSimply)
    (hPrior : ActSimplyPriorToPotencyReading InAct
      (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)
      PriorSimply) :
    FirstUnmovedMoverIsPureAct MovedIn MovesIn
      (PureAct (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)) := by
  sorry

/-- Sense-mixing control: with PRIOR_4 in the role of 6ca87431's priority, a
reciprocal cross-respect moving case gives `PriorInBeing y x` and
`PriorInBeing x y`, which the definition's asymmetry excludes. -/
theorem moverPriorityAsPriorityInBeingExcludesReciprocity :
    MoverPriorityAsPriorityInBeingExcludesReciprocity := by
  sorry

end TruthCore.Results.Causality.PriorityInBeing
