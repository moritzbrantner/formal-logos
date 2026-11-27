module

public import TruthCore.Causality.DependenceToActOfBeing

/-!
# The "unde" inference from dependence to the act of being: results

Analyst formulations, attribution deferred; no premise is established.
-/

@[expose] public section

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
  intro x hNotOwn
  have hAct : F.InAct x (A.quiddity x) := hNature x
  have hRecv : EsseReceivedIn x (A.quiddity x) :=
    hSecond x (hFirst x _ hAct (hDep x _ hAct)) hNotOwn
  exact ⟨⟨A.quiddity x, hRecv⟩, hLimit x _ hRecv⟩

/-- R-act₂ from dependence: the first "unde", a witness for each pure
perfection, and inclusion. -/
theorem ractTwoFromDependence {W B T R : Type} (F : GradesFrame W B T R)
    (A : ActualizationFrame B R) (I : IntensiveEsseFrame R) (Pure : R → Prop)
    (hDep : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hFirst : DependenceIsActualization F A)
    (hWitness : PurePerfectionsActualSomewhere F Pure)
    (hInclusion : ActualizedPureIsOfEsse F A I Pure) :
    IntensiveEsse I Pure := by
  intro d hd
  obtain ⟨x, hx⟩ := hWitness d hd
  exact hInclusion x d (hFirst x d hx (hDep x d hx)) hd

/-- Creature reception from R-act₁ and q.7 a.2 ad 1. -/
theorem creatureReceptionFromActOfBeing {B P : Type} (Creature OwnBeing : B → Prop)
    (EsseReceivedIn : B → P → Prop) (EsseLimited : B → Prop)
    (hAct : FiniteEsseReceivedAndLimited OwnBeing EsseReceivedIn EsseLimited)
    (hMade : NoCreatureIsOwnBeing Creature OwnBeing) :
    CreatureEsseIsReceived Creature EsseReceivedIn := by
  intro x hx
  exact (hAct x (hMade x hx)).1

/-- Given R-dep, each bridge is equivalent to what it delivers; the first is
analytic on the dependence reading. -/
theorem undeLoadMap : UndeLoadMap := by
  intro W B T R F A EsseReceivedIn I Pure
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hDep
    constructor
    · intro hFirst x r hx
      exact hFirst x r hx (hDep x r hx)
    · intro hEvery x r hx _
      exact hEvery x r hx
  · intro hDep hFirst hNature
    constructor
    · intro hSecond x hNotOwn
      exact hSecond x (hFirst x _ (hNature x) (hDep x _ (hNature x))) hNotOwn
    · intro hRecv x _ hNe
      exact hRecv x hNe
  · intro hDep hFirst hWitness
    constructor
    · intro hInclusion
      exact ractTwoFromDependence F A I Pure hDep hFirst hWitness hInclusion
    · intro hIntensive x d _ hd
      exact hIntensive d hd
  · intro x r hx hEsse
    exact ⟨hx, hEsse⟩

/-- Both accounts of finitude need the nature premise; reception factors
through the essence-only account. -/
theorem limitationComparison : LimitationComparison := by
  intro W B T R F A C EsseReceivedIn Pure
  refine ⟨?_, ?_, ?_⟩
  · intro hOnly hExcl x hNotOwn
    obtain ⟨d, hd, hNot⟩ := hExcl x hNotOwn
    exact ⟨d, hd, fun hx => hNot (hOnly x d hx)⟩
  · intro hRecv hCap hExcl x hNotOwn
    obtain ⟨d, hd, hNot⟩ := hExcl x hNotOwn
    exact ⟨d, hd, fun hx => hNot (hCap x d (hRecv x hNotOwn) hx)⟩
  · intro hRecv hCap x hNotOwn d hx
    exact hCap x d (hRecv x hNotOwn) hx

/-- The finite profiles, checked by decision. -/
theorem controls : Control.Controls := by
  dsimp [Control.Controls, Control.gframe, Control.act1, Control.act2, Control.act3,
    Control.nature, Control.thomist, Control.idle, Control.received, Control.limited,
    Control.noReceived, Control.noLimited, Control.pure, Control.admitsNotWisdom,
    Control.admitsAll, ActualityOnlyInsofarAsBeingReading, DependenceIsActualization,
    ActualizedQuiddityReceivesEsse, QuiddityInAct, ReceivedEsseIsLimited,
    FiniteEsseReceivedAndLimited, OwnBeingByQuiddity, DeflatedActualizedBy,
    HasOnlyWhatNatureAdmits, NatureOtherThanBeingExcludesSomePure, FiniteInPerfection,
    ReceivedEsseOnlyToCapacity, PurePerfectionsActualSomewhere, ActualizedPureIsOfEsse,
    IntensiveEsse]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- The q.7 a.1 bridge: own being receives nothing, so its esse is unlimited, so it
has every pure perfection; on the measure reading the last step is analytic. -/
theorem q7BridgeLoadMap : Q7BridgeLoadMap := by
  intro B P D OwnBeing EsseReceivedIn EsseLimited Has Pure
  refine ⟨?_, ?_⟩
  · intro hNoRecipient hOnly hUnlimited x hx d hd
    refine hUnlimited x ?_ d hd
    intro hLimited
    exact hNoRecipient x hx (hOnly x hLimited)
  · intro x hNotLimited d hd
    exact Classical.byContradiction fun hNot => hNotLimited ⟨d, hd, hNot⟩

/-- The q.7 a.1 bridge on a source that has only being, checked by decision. -/
theorem q7Controls : Control.Q7Controls := by
  dsimp [Control.Q7Controls, Control.own, Control.recv, Control.hasOnlyBeing,
    Control.allPure, Control.limitedRole, TruthCore.Causality.ReceptionLimitation.OwnBeingIsNoRecipient,
    TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading,
    UnlimitedEsseHasEveryPure, LimitedByMeasure,
    TruthCore.Causality.ModeOfBeingMiddleTerm.OwnBeingHasEveryPurePerfection]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end TruthCore.Results.Causality.DependenceToActOfBeing
