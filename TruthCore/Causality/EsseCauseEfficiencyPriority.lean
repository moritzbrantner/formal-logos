module

public import TruthCore.Causality.EsseCauseEfficiency
public import TruthCore.Causality.ComponentFirstness
public import TruthCore.Causality.ActPriorityAtFirst
public import TruthCore.Causality.TermSenseForks2

/-!
# Efficient priority of esse-causes at "no component is the first being" (#1633)

ST I q.3 a.8's third reason, as typed in `ComponentFirstness`, excludes a
participated component from being first because it "has a cause of its being
other than itself" (`ParticipatedHasOtherCause`, over the mode-unspecified
`CausesIn`) and "an efficient cause is prior to what it causes"
(`EfficientCauseIsPriorToEffectReading`). The existing arguments instantiate
the latter's cause relation with `CausesIn`, so they read every cause of
being as an efficient cause. This module gives the step a typed sibling: the
participated component has an *efficient* cause of its esse other than itself
(`ParticipatedHasOtherEfficientEsseCause`, over the primitive
`EfficientlyCausesEsse` of `EsseCauseEfficiency`), and priority is a separate
OPEN premise about that tenseless relation (`EfficientEsseCauseIsPrior`), not
the secunda via statement, whose efficient causes are read here and now. The
secunda via priority yields it only through the OPEN tense bridge
`EfficientEsseCauseActsHereAndNow` (`TenseGapControl`). Efficiency is then a
hypothesis that can fail (`NonEfficientParticipationControl`) rather than a
reading of `CausesIn`.

No premise is asserted; the sibling routes keep every other input of the
existing arguments unchanged.
-/

@[expose] public section

namespace TruthCore.Causality.EsseCauseEfficiencyPriority

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.EsseCauseEfficiency
open TruthCore.Causality.ComponentFirstness
open TruthCore.Causality.ActPriorityAtFirst (FirstBeingActPriority)
open TruthCore.Causality.TermSenseForks (BecomingBeingFrame ParticipatedHasDistinctEsse)

variable {B P R : Type}

/-- The efficient cause-of-esse relation in the respect-indexed shape of the
secunda via vocabulary: `c` efficiently causes `x` in respect `r` exactly when
`r` is the esse respect and `c` is an efficient cause of `x`'s esse. It only
reshapes `EfficientlyCausesEsse`; no other respect is covered. -/
def EfficientlyCausesEsseIn (q : EfficiencyProfile B P R) : B → B → R → Prop :=
  fun c x r => r = q.esse ∧ q.EfficientlyCausesEsse c x

/-- Whatever has its being by participation has an efficient cause of its
esse other than itself. The efficient sibling of `ParticipatedHasOtherCause`
(q.44 a.1 ad 1 as typed), which does not fix the mode. -/
def ParticipatedHasOtherEfficientEsseCause (q : EfficiencyProfile B P R)
    (Participated : B → Prop) : Prop :=
  ∀ x, Participated x → ∃ c, c ≠ x ∧ q.EfficientlyCausesEsse c x

/-- OPEN analyst premise: an efficient cause of a thing's esse (tenseless:
originating or sustaining) is simply prior to that thing. The tenseless
counterpart of the secunda via's `EfficientCauseIsPriorToEffectReading`, whose
efficient causes are read here and now; it is not that statement. -/
def EfficientEsseCauseIsPrior (q : EfficiencyProfile B P R)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ c x, q.EfficientlyCausesEsse c x → PriorSimply c x

/-- OPEN tense bridge: every (tenseless) efficient cause of a thing's esse is,
here and now, an efficient cause of that thing at the esse respect in the
secunda via's sense (`EfficientlyCausesIn`, DEF-EFFICIENT-CAUSING). It says
that agent causes of esse are present (conserving) causes; merely
originating agents of esse falsify it. -/
def EfficientEsseCauseActsHereAndNow (q : EfficiencyProfile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) : Prop :=
  ∀ c x, q.EfficientlyCausesEsse c x → EfficientlyCausesIn c x q.esse

/-- The participation frame of `TermSenseForks2` on the profile underlying an
efficiency profile. -/
def participationFrame (q : EfficiencyProfile B P R) (CausesOrigin : B → B → Prop)
    (Participated : B → Prop) : BecomingBeingFrame B P R :=
  ⟨q.toProfile, CausesOrigin, Participated⟩

/-! ## Finite controls (existence claims on `Bool`) -/

/-- Non-efficient participation: in some interpretation, a participated
component (`false`, a component of `true`) actually exists with distinct
esse and is caused in being by another, and every mode-unspecified input of
the existing routes holds (participated distinct esse, the q.3 a.4
mode-unspecified conclusion, `ParticipatedHasOtherCause`, the component
kinds, both act-priority premises, non-overlap) together with efficient
priority of efficient causes of esse (`EfficientEsseCauseIsPrior`); yet priority fails for the
mode-unspecified `CausesIn`, the efficient q.3 a.4 reading and the efficient
participation premise fail, and the component is first. (Witness in the
proof: `true` causes `false`'s esse non-efficiently and nothing is prior to
anything.) -/
def NonEfficientParticipationControl : Prop :=
  ∃ (q : EfficiencyProfile Bool Bool Unit) (CausesOrigin : Bool → Bool → Prop)
    (Participated : Bool → Prop) (ComponentOf PriorSimply : Bool → Bool → Prop)
    (InAct InPotency : Bool → Unit → Prop),
    ParticipatedHasDistinctEsse (participationFrame q CausesOrigin Participated) ∧
    DistinctEsseRequiresExternalCauseReading q.toProfile ∧
    ParticipatedHasOtherCause Participated q.CausesIn q.esse ∧
    ComponentIsPotentialOrParticipated ComponentOf InPotency Participated ∧
    ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
    FirstBeingActPriority InAct InPotency PriorSimply ∧
    NotActAndPotencyInSameRespectReading InAct InPotency ∧
    EfficientEsseCauseIsPrior q PriorSimply ∧
    ¬ EfficientCauseIsPriorToEffectReading q.CausesIn PriorSimply ∧
    ¬ DistinctEsseRequiresExternalEfficientCause q ∧
    ¬ ParticipatedHasOtherEfficientEsseCause q Participated ∧
    ¬ NoComponentIsFirstBeingReading ComponentOf PriorSimply

/-- Nonvacuity: in some interpretation with a component, every input of the
efficient sibling routes holds (participated distinct esse, the efficient q.3
a.4 reading, the efficient participation premise, the component kinds, both
act-priority premises, non-overlap, efficient priority, the secunda via priority at a here-and-now relation and the tense bridge), and so does the
conclusion. -/
def EfficientParticipationNonvacuity : Prop :=
  ∃ (q : EfficiencyProfile Bool Bool Unit) (CausesOrigin : Bool → Bool → Prop)
    (Participated : Bool → Prop) (ComponentOf PriorSimply : Bool → Bool → Prop)
    (InAct InPotency : Bool → Unit → Prop) (HereAndNow : Bool → Bool → Unit → Prop),
    (∃ p x, ComponentOf p x) ∧
    EfficientCauseIsPriorToEffectReading HereAndNow PriorSimply ∧
    EfficientEsseCauseActsHereAndNow q HereAndNow ∧
    ParticipatedHasDistinctEsse (participationFrame q CausesOrigin Participated) ∧
    DistinctEsseRequiresExternalEfficientCause q ∧
    ParticipatedHasOtherEfficientEsseCause q Participated ∧
    ComponentIsPotentialOrParticipated ComponentOf InPotency Participated ∧
    ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
    FirstBeingActPriority InAct InPotency PriorSimply ∧
    NotActAndPotencyInSameRespectReading InAct InPotency ∧
    EfficientEsseCauseIsPrior q PriorSimply ∧
    NoComponentIsFirstBeingReading ComponentOf PriorSimply

/-- Tense gap: in some interpretation the secunda via priority holds for a
here-and-now efficient relation while the tense bridge and the priority of
tenseless efficient causes of esse both fail. (Witness in the proof: `true`
efficiently causes `false`'s esse, nothing causes here and now, nothing is
prior to anything.) -/
def TenseGapControl : Prop :=
  ∃ (q : EfficiencyProfile Bool Bool Unit) (HereAndNow : Bool → Bool → Unit → Prop)
    (PriorSimply : Bool → Bool → Prop),
    EfficientCauseIsPriorToEffectReading HereAndNow PriorSimply ∧
    ¬ EfficientEsseCauseActsHereAndNow q HereAndNow ∧
    ¬ EfficientEsseCauseIsPrior q PriorSimply

/-- The three controls. -/
def EfficientPriorityControls : Prop :=
  NonEfficientParticipationControl ∧ EfficientParticipationNonvacuity ∧ TenseGapControl

end TruthCore.Causality.EsseCauseEfficiencyPriority
