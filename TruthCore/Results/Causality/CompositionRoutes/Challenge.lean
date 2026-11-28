import TruthCore.Causality.ContingentBeingNode
import TruthCore.Logic.CogitoEsse
import TruthCore.Mereology.FusionNoNecessaryParts

namespace TruthCore.Results.Causality.CompositionRoutes

open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.German.Kant.CosmologicalInference (NecessaryBeing)
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)
open TruthCore.Mereology.FusionNoNecessaryParts (NoNecessaryPartsAt)

theorem necessaryConcreteOfCalibratedExistence {W B : Type}
    (m : Profile W B) (w : W)
    (hNecessary : NecessaryBeing m.ontic w)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w) :
    NecessaryConcreteAt m w := by
  sorry

theorem actualContingentOfNoNecessaryParts {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (x : B)
    (hActual : ActualConcrete m w x)
    (hParts : NoNecessaryPartsAt m.ontic w x) :
    SomeActualContingentAt m w := by
  sorry

end TruthCore.Results.Causality.CompositionRoutes
