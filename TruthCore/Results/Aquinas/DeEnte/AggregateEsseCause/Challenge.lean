import TruthCore.Latin.Aquinas.DeEnte.AggregateEsseCause
import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution
import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
import TruthCore.Logic.ExcludedMiddle

/-! The totality-cause route to CCR and its controls (#1724). Constructive:
no excluded middle, well-foundedness, efficient cause or modal premise. -/

namespace TruthCore.Results.Aquinas.DeEnte.AggregateEsseCause

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.DeEnte.AggregateEsseCause
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing)
open TruthCore.Latin.Aquinas.SummaTheologiae (MaximumInBeingCausesAllBeingsReading)
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Logic (ExcludedMiddle)

/-- A cause of the totality of received actual being (A), which causes each
received member's esse (B), with no self-causation of esse, is one uncaused
actual bearer that is a distinct actual cause of every received bearer. -/
theorem commonOfAggregate (p : Profile B P R) (T : B → Prop)
    (hA : ReceivedTotalityHasAggregateCause p T)
    (hB : TotalityCauseCausesEachReceived p T)
    (hSelf : NothingCausesItsOwnBeing p.CausesIn p.esse) :
    CommonUncausedCauseOfReceived p := by
  sorry

/-- A common uncaused cause of every received actual bearer gives CCR: any
closed collection with a member contains that cause, which is a root. -/
theorem closedOfCommon (p : Profile B P R) (h : CommonUncausedCauseOfReceived p) :
    ClosedActualEsseCollectionsRooted p := by
  sorry

/-- The common uncaused cause, distinct-esse coverage, identity uniqueness,
causal ascent at esse and excluded middle give the fixed-esse maximum
principle consumed by the GOD_4 existence bundle. Unlike
`MaximalFromEsseSource.maximalCauses`, no CCR, population or esse-cause
composition premise is used: the common cause already causes every received
bearer, and uniqueness shows every other actual bearer is received. -/
theorem maximalCausesOfCommon (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (hCommon : CommonUncausedCauseOfReceived p)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hOne : AtMostOneEsseIsEssence p)
    (hAscent : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse)
    (hEM : ExcludedMiddle) :
    MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse := by
  sorry

namespace Control

end Control

/-- The seven interpretations together. -/
theorem controls : AggregateEsseCauseControls := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.AggregateEsseCause
