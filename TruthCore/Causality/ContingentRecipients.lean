module

public import TruthCore.Causality.ActualAncestralSource

@[expose] public section
namespace TruthCore.Causality.ContingentRecipients
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.PrussPowerPremises.Model (allC)
open TruthCore.Causality.NarDerivation.Model (chainG chainGrounds)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.WillVersusChance.Model (onlyG)
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)

/-- The earlier fixed profile has a necessary intermediary giving to every
actual contingent concretum and an underived source upstream of that giver.
The naming predicate selects the intermediary solely to test its reach. -/
def CoverageControl : Prop :=
  let m := groundProfile chainG allC chainGrounds
  ActualRoot m false .d ∧ NecessaryAt m.ontic false .g ∧
    ContingentAt m.ontic false .c ∧ ActualConcrete m false .c ∧
    ActualConcreteGround m false .d .g ∧
    (∀ x, ActualConcrete m false x → ContingentAt m.ontic false x →
      ActualConcreteGround m false .g x ∧ chainG.GivesAt false .g x ()) ∧
    ¬ GodReachesActualConcreta m false onlyG

end TruthCore.Causality.ContingentRecipients
