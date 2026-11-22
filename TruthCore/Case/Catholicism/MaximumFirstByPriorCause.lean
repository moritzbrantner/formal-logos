module

public import TruthCore.Case.Catholicism.StageOneQuartaVia
public import TruthCore.Case.Catholicism.MaximalBeingCauseExclusion

/-!
# The maximum in being is first, from prior causes of being (#1832)

Finite controls for the composition
`Results.Case.Catholicism.MaximumFirstByPriorCause.maximumInBeingIsFirstBeingOfPriorCause`:
what is simply prior to a thing causes its being (`SimplyPriorIsCauseOfBeing`,
OPEN) and no maximum in being has a distinct cause of its being
(`MaximumHasNoDistinctEsseCause`, derived from *Metaphysics* II.1's causal
comparison) give `MaximumInBeingIsFirstBeing` under excluded middle. Analyst
formulation, attribution deferred. Found by the agent-guided discovery pilot
(#1832): the baseline `truth discover` run did not retrieve
`SimplyPriorIsCauseOfBeing` as a candidate for this target.

The controls are statements about these finite interpretations only. They
show that both premises do work in the composition and that the premises are
jointly satisfiable with a maximum in being and a real priority edge; they do
not say that any premise is true or false of reality.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.MaximumFirstByPriorCause
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- Three finite interpretations on two beings (`Bool`) and one respect
(`Unit`, read as `esse`):

1. nonvacuity: both premises hold, `true` is maximal in being, `true` is simply
   prior to `false`, and the conclusion holds;
2. without `MaximumHasNoDistinctEsseCause`: what is simply prior causes being,
   yet `false` (maximal, since nothing is more a being than anything) has the
   distinct `true` simply prior to it;
3. without `SimplyPriorIsCauseOfBeing`: nothing causes anything, so no maximum
   has a distinct cause, yet the maximal `false` has `true` simply prior to it. -/
def Controls : Prop :=
  (∃ (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (PriorSimply : Bool → Bool → Prop),
    SimplyPriorIsCauseOfBeing PriorSimply CausesIn () ∧
    MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn () ∧
    IsMaximumIn InAct MoreIn () true ∧ PriorSimply true false ∧
    MaximumInBeingIsFirstBeing InAct MoreIn () PriorSimply) ∧
  (∃ (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (PriorSimply : Bool → Bool → Prop),
    SimplyPriorIsCauseOfBeing PriorSimply CausesIn () ∧
    ¬ MaximumInBeingIsFirstBeing InAct MoreIn () PriorSimply) ∧
  (∃ (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (PriorSimply : Bool → Bool → Prop),
    MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn () ∧
    ¬ MaximumInBeingIsFirstBeing InAct MoreIn () PriorSimply)

end TruthCore.Case.Catholicism.MaximumFirstByPriorCause
