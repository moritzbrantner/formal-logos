import TruthCore.Causality.NecessaryConcreteRouteBridge

namespace TruthCore.Results.Causality.NecessaryRootUniqueMaximum

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteRouteBridge (NecessaryRootIsMaximumAt)
open TruthCore.Case.Catholicism (AtMostOneMaximeEns)

/-- The necessary-root bundle `d6549981` identifies every maximum in being with
its one actual necessary root `n`; two maxima are therefore both `n`. Only the
identity clause is used: rootness, necessity at accessible worlds and per se
necessity of `n` are not needed for this step. -/
theorem atMostOneMaximumOfNecessaryRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (esse : Respect)
    (hRoot : NecessaryRootIsMaximumAt m w CausesNecessityOf InAct MoreIn esse) :
    AtMostOneMaximeEns InAct MoreIn esse := by
  sorry

end TruthCore.Results.Causality.NecessaryRootUniqueMaximum
