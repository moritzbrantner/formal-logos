import TruthCore.Causality.EsseCauseEfficiencyPriority
import TruthCore.Results.Causality.ActPriorityAtFirst.Solution

/-!
# Efficient priority of esse-causes at "no component is the first being" (#1633)

The participated component's other cause is efficient by hypothesis
(`ParticipatedHasOtherEfficientEsseCause`, derived from the efficient q.3 a.4
reading), and efficient-cause priority is applied to that efficient relation.
The sibling theorem composes the existing `noComponentFirstOfWeak` with the
cause relation instantiated as `EfficientlyCausesEsseIn q`, so it restates
nothing. No sibling of `noComponentFirst` is given: that argument's act-priority
and component-kinds inputs use two senses of "potency" (legacy allowlist).
-/

namespace TruthCore.Results.Causality.EsseCauseEfficiencyPriority

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.EsseCauseEfficiency
open TruthCore.Causality.EsseCauseEfficiencyPriority
open TruthCore.Causality.ComponentFirstness
open TruthCore.Causality.ActPriorityAtFirst (FirstBeingActPriority)
open TruthCore.Causality.TermSenseForks (ParticipatedHasDistinctEsse)

/-- Whatever has being by participation actually exists with distinct esse;
every such being has an external efficient cause of its esse; so whatever has
being by participation has an efficient cause of its esse other than itself. -/
theorem participatedEfficientCauseFromQ3A4 (q : EfficiencyProfile B P R)
    (CausesOrigin : B → B → Prop) (Participated : B → Prop)
    (hDistinct : ParticipatedHasDistinctEsse (participationFrame q CausesOrigin Participated))
    (hEfficient : DistinctEsseRequiresExternalEfficientCause q) :
    ParticipatedHasOtherEfficientEsseCause q Participated := by
  sorry

/-- Sibling of `noComponentFirstOfWeak` (act priority only at a first being),
with the efficient participation premise and efficient-cause priority applied
to the efficient relation only. -/
theorem noComponentFirstEfficientOfWeak (q : EfficiencyProfile B P R)
    (ComponentOf PriorSimply : B → B → Prop)
    (InAct InPotency : B → R → Prop) (Participated : B → Prop)
    (hKinds : ComponentIsPotentialOrParticipated ComponentOf InPotency Participated)
    (hWeak : FirstBeingActPriority InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hParticipated : ParticipatedHasOtherEfficientEsseCause q Participated)
    (hEfficient : EfficientCauseIsPriorToEffectReading (EfficientlyCausesEsseIn q) PriorSimply) :
    NoComponentIsFirstBeingReading ComponentOf PriorSimply := by
  sorry

/-- The two finite interpretations. Explicit proof terms. -/
theorem efficientPriorityControls : EfficientPriorityControls := by
  sorry

end TruthCore.Results.Causality.EsseCauseEfficiencyPriority
