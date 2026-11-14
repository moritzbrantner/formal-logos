import TruthCore.Latin.Aquinas.DeEnte.EsseSource
import TruthCore.Causality.RootPurity

/-!
# De ente: one first being whose esse is its essence (#1628)

Conditional derivations for the three stages of *De ente* c.3 [69874]
(Baur/Koch numbering; Leonine c.4) and their reconnection to the root routes.

* `atMostOneEsseIsEssenceFromPlurification`: the multiplication inventory, the
  exclusion of an added difference and of matter, the existing esse-reception
  premises and the OPEN shared-nature premise give at most one actual being
  whose esse is its essence.
* `distinctEsseHasEsseIsEssenceSource`: the #1629 step (another actual cause of
  being, mode unspecified), no infinite regress of actual causes of being and
  excluded middle give every actual distinct esse a chain of actual causes of
  being headed by a being whose esse is its essence.
* `commonEsseIsEssenceSource`: with at most one such being, two actual beings
  and no infinite regress, one and the same being whose esse is its essence
  has no actual cause of its esse and heads a chain to every other actual
  being. Distinct represented esse and essence (a real distinction only if
  equality of represented principles is read as real identity) for every
  other being is derived here from at-most-one, as in the passage's order.
* `rootPurityFromDeEnte`: sibling of the root-purity route in which the #1629
  step replaces the q.3 a.4 efficient-read dichotomy pair.
* `atMostOneActualRootFromDeEnte`: any two actual concrete roots are the same,
  from the #1629 step and at-most-one (the uniqueness half of the
  root-uniqueness route, in place of its genus principle and grades).

Nothing here supplies efficiency, conservation, necessity or God
identification.
-/

namespace TruthCore.Results.Aquinas.DeEnte.EsseSource

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.EsseReception
  (EsseReceivedOnlyInOwnEssence NothingInReceptivePotencyToItself)
open TruthCore.Logic (ExcludedMiddle)

/-- Stage (b): at most one actual being has its esse identical with its
essence. -/
theorem atMostOneEsseIsEssenceFromPlurification (p : Profile B P R) (q : Plurification B)
    (EsseReceivedIn : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (hModes : PlurificationOnlyByThreeModesReading p q EsseReceivedIn)
    (hShare : EsseIsEssenceBeingsShareNature p q)
    (hDiff : EsseTantumReceivesNoDifferenceReading p q)
    (hMatter : EsseTantumNotInMatterReading p q)
    (hOwn : EsseReceivedOnlyInOwnEssence p.essenceOf EsseReceivedIn)
    (hPotency : ReceiverInPotencyToReceivedEsseReading p.esseOf EsseReceivedIn ReceptivePotencyTo)
    (hNotSelf : NothingInReceptivePotencyToItself ReceptivePotencyTo) :
    AtMostOneEsseIsEssence p := by
  sorry

/-- Stage (c): every actual distinct esse goes back, through actual causes of
being, to an actual being whose esse is its essence. -/
theorem distinctEsseHasEsseIsEssenceSource (p : Profile B P R)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hRegress : NoInfiniteActualEsseCauseRegress p) (hEM : ExcludedMiddle) :
    EveryDistinctEsseHasEsseIsEssenceSource p := by
  sorry

/-- Stages (a)-(c) together: one being whose esse is its essence has no
actual cause of its esse and heads a chain of actual causes of being to every
other actual being. -/
theorem commonEsseIsEssenceSource (p : Profile B P R)
    (hSource : EveryDistinctEsseHasEsseIsEssenceSource p)
    (hOne : AtMostOneEsseIsEssence p) (hTwo : TwoActualBeings p)
    (hRegress : NoInfiniteActualEsseCauseRegress p)
    (hEM : ExcludedMiddle) : CommonEsseIsEssenceSource p := by
  sorry

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.RootPurity
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Stage (d), uniqueness: any two actual concrete roots are the same, from the
#1629 step and at-most-one, in place of the genus principle and grades of the
root-uniqueness route. -/
theorem atMostOneActualRootFromDeEnte {W : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hOne : AtMostOneEsseIsEssence p) : AtMostOneActualRootAt m w := by
  sorry

/-- Stage (d), purity: the root-purity route with the #1629 step in place of
the q.3 a.4 dichotomy pair. -/
theorem rootPurityFromDeEnte {W D : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hComponent : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hBridge : UnlimitedDeterminationsArePure Composite PriorSimply p.essenceOf p.esseOf Has Pure) :
    ActualRootDeterminationsArePure m w Has Pure := by
  sorry

/-! ## Controls -/

open Four

/-- All four controls. -/
theorem esseSourceControls : EsseSourceControls := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.EsseSource
