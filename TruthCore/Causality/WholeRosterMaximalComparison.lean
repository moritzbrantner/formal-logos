module

public import TruthCore.Causality.MaximalGroundingAsymmetry
public import TruthCore.Causality.WholeRosterFoundation

/-! Exact conditional comparison for the selected existence-only bundle.
This does not repeat whole-roster/root equivalence or assert either policy.
The retained comparative/causal prefix is essential to the comparison, and
its real existential interpretation remains open. -/

@[expose] public section

namespace TruthCore.Causality.WholeRosterMaximalComparison
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.MaximalGroundingAsymmetry
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete

/-- On the SAME dictionaries, six existing inputs of the twelve-input
existence-only bundle make whole-roster nontrapping equivalent to nonreciprocity
at maximal targets. This is no unconditional equivalence and no independent
foundation argument. Other actual pairs may remain reciprocal or unfounded. -/
def Comparison : Prop := ∀ (W B R : Type) (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R),
  InhabitedConcreteAt m.ontic m.concrete w →
  ExistingInActAt m.ontic InAct esse w →
  EsseCauseIsActualConcreteGround m w CausesIn esse →
  MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
  GradesByApproachToAMaximumReading InAct MoreIn →
  ExcludedMiddle →
  (WholeRosterNotTrapped m w ↔ AtMaximalTarget m w InAct MoreIn esse)

end TruthCore.Causality.WholeRosterMaximalComparison
