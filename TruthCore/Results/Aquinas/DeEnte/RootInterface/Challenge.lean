import TruthCore.Latin.Aquinas.DeEnte.RootInterface
import TruthCore.Results.Aquinas.DeEnte.EsseSource.Solution
import TruthCore.Results.Causality.WholeRosterFoundation.Solution

/-!
# De ente: the first source at the root interface, and a per se regress (#1635)

* `uniqueActualRootFromDeEnte`: root existence from population and
  whole-roster nontrapping (`WholeRosterFoundation.actualRootExists`) composed
  with the #1628 uniqueness `atMostOneActualRootFromDeEnte` gives the
  root-uniqueness interface `UniqueActualRootAt`.
* `deEnteFirstSourceIsActualRoot`: the De ente first source is an actual
  concrete root at `w`, from the two OPEN bridges of `RootInterface`,
  existing-in-act and no self-causation of being.
* `uniqueActualRootFromDeEnteSource`: that root with at most one actual root
  gives `UniqueActualRootAt` without whole-roster nontrapping.
* `perSeRegressOfUnrestricted`: the unrestricted regress premise implies its
  per se version (strength order).
* `unrestrictedRegressFromPerSe`: the per se regress and the per se bridge
  give the unrestricted regress premise.

Nothing here supplies efficiency, conservation, modal necessity or God
identification.
-/

namespace TruthCore.Results.Aquinas.DeEnte.RootInterface

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Interface 1: an actual root exists (population, whole-roster nontrapping,
excluded middle) and, by De ente's other-cause step and at most one being
whose esse is its essence, every actual root equals it. -/
theorem uniqueActualRootFromDeEnte {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hOne : AtMostOneEsseIsEssence p) : UniqueActualRootAt m w := by
  sorry

/-- Interface 2: the De ente first source is an actual concrete root at `w`.
It is concrete and exists at `w` by the concreteness bridge; an actual
concrete ground y of it would cause its esse (ground bridge), be in act
(existing-in-act) and differ from it (no self-causation), so y would be an
actual cause of its esse, which the first source has none of. -/
theorem deEnteFirstSourceIsActualRoot {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R)
    (hSource : CommonEsseIsEssenceSource p)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hConcrete : ActualEsseIsEssenceIsActualConcreteAt m w p)
    (hGround : GroundOfEsseIsEssenceBeingCausesItsEsse m w p)
    (hNoSelf : NothingCausesItsOwnBeing p.CausesIn p.esse) :
    DeEnteFirstSourceIsActualRootAt m w p := by
  sorry

/-- The De ente first source as an actual root, with at most one actual root,
is the unique actual root at `w`. -/
theorem uniqueActualRootFromDeEnteSource {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R)
    (hRoot : DeEnteFirstSourceIsActualRootAt m w p)
    (hAtMost : AtMostOneActualRootAt m w) : UniqueActualRootAt m w := by
  sorry

/-- Strength order: no infinite chain of actual causes of being gives no
infinite chain of per se actual causes of being, for any per se link. -/
theorem perSeRegressOfUnrestricted (p : Profile B P R) (AsCaused : B → B → Prop)
    (hRegress : NoInfiniteActualEsseCauseRegress p) :
    NoInfinitePerSeActualEsseCauseRegress p AsCaused := by
  sorry

/-- The per se regress and the per se bridge give the unrestricted regress.
By per se induction on x: an actual cause c of x that has an actual cause d
causes x per se (bridge), so the induction hypothesis covers c; an actual
cause with no actual cause is accessible outright. -/
theorem unrestrictedRegressFromPerSe (p : Profile B P R) (AsCaused : B → B → Prop)
    (hPerSe : NoInfinitePerSeActualEsseCauseRegress p AsCaused)
    (hBridge : CausedEsseCauseCausesAsCaused p AsCaused) :
    NoInfiniteActualEsseCauseRegress p := by
  sorry

/-! ## Controls -/

open TruthCore.Results.Aquinas.DeEnte.EsseSource (regressProfile)

theorem rootInterfaceControls : RootInterfaceControls := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.RootInterface
