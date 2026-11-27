import TruthCore.Causality.DependenceToActOfBeing

/-!
# The "unde" inference from dependence to the act of being: results

Analyst formulations, attribution deferred; no premise is established.
-/

namespace TruthCore.Results.Causality.DependenceToActOfBeing

open TruthCore.Causality.DependenceToActOfBeing
open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.ModeOfBeingMiddleTerm
  (FiniteEsseReceivedAndLimited IntensiveEsseFrame IntensiveEsse)
open TruthCore.Latin.Aquinas.SummaTheologiae (ActualityOnlyInsofarAsBeingReading)
open TruthCore.Causality.ReceptionLimitation (ReceivedEsseIsLimited)
open TruthCore.Causality.Round2PerfectionPrimacy (CreatureEsseIsReceived)

/-- R-act₁ from dependence: q.4 a.1 ad 3's two "unde" steps, with the nature in
act and received esse limited. -/
theorem ractOneFromDependence {W B T R : Type} (F : GradesFrame W B T R)
    (A : ActualizationFrame B R) (EsseReceivedIn : B → R → Prop) (EsseLimited : B → Prop)
    (hDep : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hFirst : DependenceIsActualization F A)
    (hSecond : ActualizedQuiddityReceivesEsse F A EsseReceivedIn)
    (hNature : QuiddityInAct F A)
    (hLimit : ReceivedEsseIsLimited EsseLimited EsseReceivedIn) :
    FiniteEsseReceivedAndLimited (OwnBeingByQuiddity F A) EsseReceivedIn EsseLimited := by
  sorry

/-- R-act₂ from dependence: the first "unde", a witness for each pure
perfection, and inclusion. -/
theorem ractTwoFromDependence {W B T R : Type} (F : GradesFrame W B T R)
    (A : ActualizationFrame B R) (I : IntensiveEsseFrame R) (Pure : R → Prop)
    (hDep : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hFirst : DependenceIsActualization F A)
    (hWitness : PurePerfectionsActualSomewhere F Pure)
    (hInclusion : ActualizedPureIsOfEsse F A I Pure) :
    IntensiveEsse I Pure := by
  sorry

/-- Creature reception from R-act₁ and q.7 a.2 ad 1. -/
theorem creatureReceptionFromActOfBeing {B P : Type} (Creature OwnBeing : B → Prop)
    (EsseReceivedIn : B → P → Prop) (EsseLimited : B → Prop)
    (hAct : FiniteEsseReceivedAndLimited OwnBeing EsseReceivedIn EsseLimited)
    (hMade : NoCreatureIsOwnBeing Creature OwnBeing) :
    CreatureEsseIsReceived Creature EsseReceivedIn := by
  sorry

/-- Given R-dep, each bridge is equivalent to what it delivers; the first is
analytic on the dependence reading. -/
theorem undeLoadMap : UndeLoadMap := by
  sorry

/-- Both accounts of finitude need the nature premise; reception factors
through the essence-only account. -/
theorem limitationComparison : LimitationComparison := by
  sorry

/-- The finite profiles, checked by decision. -/
theorem controls : Control.Controls := by
  sorry

end TruthCore.Results.Causality.DependenceToActOfBeing
