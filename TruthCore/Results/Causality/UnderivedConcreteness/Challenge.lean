import TruthCore.Causality.NecessaryConcreteUnderived
import TruthCore.Logic.CogitoEsse

namespace TruthCore.Results.Causality.UnderivedConcreteness

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessarilyUnderived (NecessarilyUnderived)
open TruthCore.Causality.NecessaryConcreteUnderived (NecessaryConcreteUnderivedAt)
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)

theorem underivedConcreteOfCalibration {W B : Type} (m : Profile W B) (w : W)
    (hUnderived : NecessarilyUnderived m.ontic m.grounds w)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

open TruthCore.Causality.NecessaryConcreteUnderived (witnessProfile)

theorem jointlySatisfied :
    NecessarilyUnderived witnessProfile.ontic witnessProfile.grounds false ∧
      EveryExistentConcreteAt witnessProfile.ontic witnessProfile.concrete false := by
  sorry

theorem calibrationOmission :
    let m : Profile Bool Bool := { witnessProfile with concrete := (· = true) }
    NecessarilyUnderived m.ontic m.grounds false ∧
      m.concrete true ∧ m.ontic.ExistsAt false true ∧
      ¬ NecessaryConcreteUnderivedAt m false := by
  sorry

end TruthCore.Results.Causality.UnderivedConcreteness
