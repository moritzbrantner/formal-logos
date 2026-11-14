module

public import TruthCore.Causality.EsseCauseEfficiencyPriority
public import TruthCore.Results.Causality.ActPriorityAtFirst.Solution

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

@[expose] public section

namespace TruthCore.Results.Causality.EsseCauseEfficiencyPriority

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.EsseCauseEfficiency
open TruthCore.Causality.EsseCauseEfficiencyPriority
open TruthCore.Causality.ComponentFirstness
open TruthCore.Causality.ActPriorityAtFirst (FirstBeingActPriority)
open TruthCore.Causality.TermSenseForks (ParticipatedHasDistinctEsse)

variable {B P R : Type}

/-- Whatever has being by participation actually exists with distinct esse;
every such being has an external efficient cause of its esse; so whatever has
being by participation has an efficient cause of its esse other than itself. -/
theorem participatedEfficientCauseFromQ3A4 (q : EfficiencyProfile B P R)
    (CausesOrigin : B → B → Prop) (Participated : B → Prop)
    (hDistinct : ParticipatedHasDistinctEsse (participationFrame q CausesOrigin Participated))
    (hEfficient : DistinctEsseRequiresExternalEfficientCause q) :
    ParticipatedHasOtherEfficientEsseCause q Participated := by
  intro x hx
  obtain ⟨c, hne, _, _, hEff⟩ := hEfficient x (hDistinct x hx)
  exact ⟨c, hne, hEff⟩

/-- Sibling of `noComponentFirstOfWeak` (act priority only at a first being),
with the efficient participation premise and the priority of (tenseless)
efficient causes of esse. -/
theorem noComponentFirstEfficientEsseOfWeak (q : EfficiencyProfile B P R)
    (ComponentOf PriorSimply : B → B → Prop)
    (InAct InPotency : B → R → Prop) (Participated : B → Prop)
    (hKinds : ComponentIsPotentialOrParticipated ComponentOf InPotency Participated)
    (hWeak : FirstBeingActPriority InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hParticipated : ParticipatedHasOtherEfficientEsseCause q Participated)
    (hPrior : EfficientEsseCauseIsPrior q PriorSimply) :
    NoComponentIsFirstBeingReading ComponentOf PriorSimply :=
  TruthCore.Results.Causality.ActPriorityAtFirst.noComponentFirstOfWeak ComponentOf PriorSimply
    InAct InPotency Participated (EfficientlyCausesEsseIn q) q.esse hKinds hWeak hNotBoth
    (fun x hx => let ⟨c, hne, hEff⟩ := hParticipated x hx; ⟨c, hne, rfl, hEff⟩)
    (fun c x _ h => hPrior c x h.2)

/-- The secunda via priority of here-and-now efficient causes, with the tense
bridge (every efficient cause of esse causes it here and now), gives the
priority of tenseless efficient causes of esse. -/
theorem efficientEsseCausePriorityFromHereAndNow (q : EfficiencyProfile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (hSecunda : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
    (hTense : EfficientEsseCauseActsHereAndNow q EfficientlyCausesIn) :
    EfficientEsseCauseIsPrior q PriorSimply :=
  fun c x h => hSecunda c x q.esse (hTense c x h)

/-- In the control profiles only `false` has distinct esse. -/
private theorem onlyFalseDistinct (q : EfficiencyProfile Bool Bool Unit)
    (hEssence : q.essenceOf = fun _ => false) (hEsse : q.esseOf = Bool.not) :
    ∀ x, DistinctEsseAt q.toProfile x → x = false := by
  intro x hx
  cases x with
  | false => rfl
  | true =>
    have h : q.esseOf true = q.essenceOf true := by rw [hEssence, hEsse]; rfl
    exact absurd h hx.2

/-- The three finite interpretations. Explicit proof terms. -/
theorem efficientPriorityControls : EfficientPriorityControls := by
  refine ⟨?nonEfficient, ?nonvacuity, ?tenseGap⟩
  · let q : EfficiencyProfile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun c x _ => c = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := ()
      EfficientlyCausesEsse := fun _ _ => False }
    have hOnly := onlyFalseDistinct q rfl rfl
    have hd : DistinctEsseAt q.toProfile false := ⟨True.intro, Bool.noConfusion⟩
    have hTF : (true : Bool) ≠ false := Bool.noConfusion
    have hExt : DistinctEsseRequiresExternalCauseReading q.toProfile := by
      intro x hx
      have hx' : x = false := hOnly x hx
      subst hx'
      exact ⟨true, hTF, True.intro, rfl, rfl⟩
    exact ⟨q, fun _ _ => False, fun x => x = false,
      fun p x => p = false ∧ x = true, fun _ _ => False,
      fun _ _ => False, fun _ _ => False,
      (fun x hx => by subst hx; exact hd),
      hExt,
      (fun x hx => ⟨true, fun h => hTF (h.trans hx), rfl, hx⟩),
      (fun p _ hc => Or.inr hc.1),
      (fun _ _ h => h.elim),
      (fun _ _ _ h => h.elim),
      (fun _ _ h => h.1.elim),
      (fun _ _ h => h.elim),
      (fun h => h true false () ⟨rfl, rfl⟩),
      (fun h => let ⟨_, _, _, _, hE⟩ := h false hd; hE),
      (fun h => let ⟨_, _, hE⟩ := h false rfl; hE),
      (fun h => h false true ⟨rfl, rfl⟩ (fun _ hp => hp.elim))⟩
  · let q : EfficiencyProfile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun c x _ => c = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := ()
      EfficientlyCausesEsse := fun c x => c = true ∧ x = false }
    have hOnly := onlyFalseDistinct q rfl rfl
    have hd : DistinctEsseAt q.toProfile false := ⟨True.intro, Bool.noConfusion⟩
    have hTF : (true : Bool) ≠ false := Bool.noConfusion
    have hEffExt : DistinctEsseRequiresExternalEfficientCause q := by
      intro x hx
      have hx' : x = false := hOnly x hx
      subst hx'
      exact ⟨true, hTF, True.intro, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact ⟨q, fun _ _ => False, fun x => x = false,
      fun p x => p = false ∧ x = true, fun y x => y = true ∧ x = false,
      fun _ _ => False, fun _ _ => False, fun c x _ => c = true ∧ x = false,
      ⟨false, true, rfl, rfl⟩, (fun _ _ _ h => h), (fun _ _ h => h),
      (fun x hx => by subst hx; exact hd),
      hEffExt,
      (fun x hx => ⟨true, fun h => hTF (h.trans hx), rfl, hx⟩),
      (fun p _ hc => Or.inr hc.1),
      (fun _ _ h => h.elim),
      (fun _ _ _ h => h.elim),
      (fun _ _ h => h.1.elim),
      (fun _ _ h => h),
      (fun _ _ hc hFirst => hTF ((hFirst true ⟨rfl, hc.1⟩).trans hc.1))⟩
  · let q : EfficiencyProfile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun c x _ => c = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := ()
      EfficientlyCausesEsse := fun c x => c = true ∧ x = false }
    exact ⟨q, fun _ _ _ => False, fun _ _ => False,
      (fun _ _ _ h => h.elim),
      (fun h => h true false ⟨rfl, rfl⟩),
      (fun h => h true false ⟨rfl, rfl⟩)⟩

end TruthCore.Results.Causality.EsseCauseEfficiencyPriority
