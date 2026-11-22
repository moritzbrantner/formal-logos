import TruthCore.Causality.ExistenceAccountIntegration

/-! Weaker sibling of the same-witness underived argument
(`TruthCore.Results.Causality.ExistenceAccountIntegration.sameWitnessUnderived`):
the two bridges `NoContingentGroundOfNecessary` and `NoNovelNecessarySupport`
replace `NecessaryPredecessorLifting`, with no actual reflexivity. The
identification of the necessary supporter with the actual exemplar supplies
the supporter's actual existence, which lifting supplied in the original.
Found in review of #1825; the proof follows the reviewer's sketch. -/

namespace TruthCore.Results.Causality.SameWitnessWeak

open TruthCore.Causality.ExistenceAccountIntegration
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived

/-- The actual concrete profile exemplar is necessary and underived, from the
two weaker bridges. A putative supporter is necessary (no contingent ground),
hence most real and identical with the exemplar; the exemplar exists actually,
and no novel necessary support moves the self-support edge to the actual world,
contradicting well-founded actual support. -/
theorem sameWitnessUnderivedFromBridges {W B : Type} (m : Profile W B) (p : RealityProfile B)
    (support : W → B → B → Prop) (w : W)
    (hActual : ActualConcreteProfile m p w)
    (hPopulation : NecessaryProfilePopulation m p w)
    (hUnique : MostRealUnique p)
    (hIdentify : NecessaryIsMostReal m.ontic p w)
    (hWF : WellFoundedPresentEsseSupport m.ontic support w)
    (hNoContingent : NoContingentGroundOfNecessary m.ontic support w)
    (hNoNovel : NoNovelNecessarySupport m.ontic support w) :
    UnderivedConcreteProfile m p support w := by
  sorry

/-- Omission controls: each bridge is needed by this argument, given the other
inputs. -/
theorem weakSiblingOmissions : WeakSiblingOmissions := by
  sorry

end TruthCore.Results.Causality.SameWitnessWeak
