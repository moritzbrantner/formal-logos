import TruthCore.Causality.SustainingDependence

namespace TruthCore.Results.Causality.SustainingDependence

open TruthCore.Causality.SustainingDependence
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.Round2Grounding (EsseEffectDependsOnItsCause)
open TruthCore.Modal.TemporalHistory (History BeginsAt)

/-- The sustaining sibling from contact and the co-presence bridge. If `c`,
distinct from `x`, causes `x`'s esse and sustains `x` in every history in which
`x` is present, then at each moment at which `x` is present `c` gives `x` being,
so by contact `c` is present then; the co-presence bridge gives dependence. -/
theorem sustainingSiblingOfCoPresence {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (DependsForBeing : B → B → Prop)
    (hContact : GiverPresentWhenGiving h G)
    (hBridge : CoPresentEsseCauseIsDependedOn h CausesIn esse DependsForBeing) :
    SustainingEsseCauseIsDependedOn h G CausesIn esse DependsForBeing := by
  sorry

/-- The esse-dependence premise `2068f91c` from the weak sustaining reading
`ce55210c` and the sustaining sibling: a distinct cause of `x`'s esse sustains
`x` in every history in which `x` is present, so the sibling applies. -/
theorem esseDependenceOfSustaining {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (DependsForBeing : B → B → Prop)
    (hSustaining : CausingAnothersBeingIsSustaining h G CausesIn esse)
    (hSibling : SustainingEsseCauseIsDependedOn h G CausesIn esse DependsForBeing) :
    EsseEffectDependsOnItsCause CausesIn esse DependsForBeing := by
  sorry

/-- Strength order: `2068f91c` entails its sustaining sibling. -/
theorem sustainingSiblingOfEsseDependence {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (DependsForBeing : B → B → Prop)
    (hDep : EsseEffectDependsOnItsCause CausesIn esse DependsForBeing) :
    SustainingEsseCauseIsDependedOn h G CausesIn esse DependsForBeing := by
  sorry

/-- Onset and parity give concurrent actualization for begun things. -/
theorem onceBegunOfOnsetParity {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop)
    (hOnset : ReceivedOnsetIsGiven h G EsseReceivedIn)
    (hParity : PersistenceParity h G EsseReceivedIn) :
    ConcurrentlyActualizedOnceBegun h G EsseReceivedIn := by
  sorry

/-- Strength order: the weak concurrent actualization `40a97664` entails
concurrent actualization for begun things. -/
theorem onceBegunOfConcurrentlyActualized {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop)
    (hActualized : ConcurrentlyActualized h G EsseReceivedIn) :
    ConcurrentlyActualizedOnceBegun h G EsseReceivedIn := by
  sorry

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control
open TruthCore.Causality.SustainingDependence.Control

/-- Omission, rival-reading, strictness and nonvacuity controls
(`Control.Certificate`). -/
theorem controls : TruthCore.Causality.SustainingDependence.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.SustainingDependence
