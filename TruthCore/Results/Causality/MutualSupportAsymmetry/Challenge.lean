import TruthCore.Causality.MutualSupportAsymmetry

namespace TruthCore.Results.Causality.MutualSupportAsymmetry

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.GradedSupportFoundation
  (NecessarySupportAscendsInEsse NoInfiniteAscentAmongNecessaryConcreta)
open TruthCore.Causality.MutualSupportAsymmetry
open TruthCore.Causality.NecessarySupportCoverage (NoNecessaryConcretaMutualSupport)

theorem noMutualSupport {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hAscend : NecessarySupportAscendsInEsse m w MoreIn esse)
    (hAsymm : NecessaryGradeAsymmetric m w MoreIn esse) :
    NoNecessaryConcretaMutualSupport m w := by
  sorry

theorem asymmetricOfWellFounded {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hWF : NoInfiniteAscentAmongNecessaryConcreta m w MoreIn esse) :
    NecessaryGradeAsymmetric m w MoreIn esse := by
  sorry

theorem asymmetricGradeWithoutFoundation : AsymmetryWithoutFoundation := by
  sorry

end TruthCore.Results.Causality.MutualSupportAsymmetry
