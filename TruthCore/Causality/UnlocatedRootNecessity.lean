module

public import TruthCore.Causality.GroundedOccupantRegress

@[expose] public section

namespace TruthCore.Causality.UnlocatedRootNecessity

open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt NecessaryConcreteAt)
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Ontology.Spatiotemporal (Frame)

/-- On a singleton candidate roster with no actual concreta, both local
hypotheses hold at every actual concrete recipient vacuously. This does not
supply a recipient for either local hypothesis. -/
def EmptyPopulationOmission : Prop :=
  ∃ (m : Profile Unit Unit) (F : Frame Unit),
    ¬ ActualConcrete m () () ∧
    (∀ x, UnlocatedRootOrRegress m () F x) ∧
    (∀ x, NoAnchoredConcreteGroundingRegress m () x) ∧
    EveryContingentGroundedAt m () ∧
    ¬ NecessaryConcreteAt m ()

end TruthCore.Causality.UnlocatedRootNecessity
