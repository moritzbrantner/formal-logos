module

public import TruthCore.Causality.EsseCauseEfficiency
public import TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.Solution

/-!
# Efficiency of causes of esse: derivations and controls (#1633)

The efficient reading of q.3 a.4's conclusion
(`DistinctEsseRequiresExternalEfficientCause`) follows, through the OPEN
bridge `DistinctActualEsseCauseIsEfficient`, from the mode-unspecified De ente
conclusion `DistinctEsseHasOtherActualCause` and from the q.3 a.4 dichotomy
with its no-self-sufficiency premise. It strengthens the mode-unspecified q.3
a.4 conclusion by projection, and the unrestricted bridge strengthens the
restricted one. The controls show that the bridge is needed and that the
strength orders are strict. No premise is proved here.
-/

@[expose] public section

namespace TruthCore.Results.Causality.EsseCauseEfficiency

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Latin.Aquinas.DeEnte (DistinctEsseHasOtherActualCause)
open TruthCore.Causality.EsseCauseEfficiency
open TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause
  (distinctEsseExternalFromExhaustion)

variable {B P R : Type}

/-- De ente's mode-unspecified other actual cause of a distinct esse, with the
efficiency bridge, is an external efficient cause. -/
theorem externalEfficientEsseCauseFromDeEnte (q : EfficiencyProfile B P R)
    (hOther : DistinctEsseHasOtherActualCause q.toProfile)
    (hBridge : DistinctActualEsseCauseIsEfficient q) :
    DistinctEsseRequiresExternalEfficientCause q := by
  intro x hDistinct
  obtain ⟨c, hne, hAct, hCause⟩ := hOther x hDistinct
  exact ⟨c, hne, hAct, hCause, hBridge x hDistinct c hne hAct hCause⟩

/-- The q.3 a.4 dichotomy and no-self-sufficiency (through the existing
transcription `distinctEsseExternalFromExhaustion`), with the efficiency
bridge, give the external efficient cause. -/
theorem externalEfficientEsseCauseFromQ3A4 (q : EfficiencyProfile B P R)
    (hExhaustive : DistinctEsseCauseDichotomyReading q.toProfile)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading q.toProfile)
    (hBridge : DistinctActualEsseCauseIsEfficient q) :
    DistinctEsseRequiresExternalEfficientCause q := by
  intro x hDistinct
  obtain ⟨c, hne, hAct, hCause⟩ :=
    distinctEsseExternalFromExhaustion q.toProfile hExhaustive hNoSelfCause x hDistinct
  exact ⟨c, hne, hAct, hCause, hBridge x hDistinct c hne hAct hCause⟩

/-- Strength order: an external efficient cause of esse is an external cause
of esse (the efficiency conjunct is dropped). -/
theorem externalCauseFromExternalEfficientCause (q : EfficiencyProfile B P R)
    (hEfficient : DistinctEsseRequiresExternalEfficientCause q) :
    DistinctEsseRequiresExternalCauseReading q.toProfile := by
  intro x hDistinct
  obtain ⟨c, hne, hAct, hCause, _⟩ := hEfficient x hDistinct
  exact ⟨c, hne, hAct, hCause⟩

/-- Strength order: the unrestricted bridge gives the restricted one. -/
theorem distinctActualEsseCauseEfficientFromUnrestricted (q : EfficiencyProfile B P R)
    (hAll : CausingAnothersEsseIsEfficient q) :
    DistinctActualEsseCauseIsEfficient q :=
  fun x _ y hne _ hCause => hAll y x hne hCause

/-- The De ente step and the mode-unspecified q.3 a.4 conclusion are the same
proposition on the same profile: each unfolds to "every actual distinct-esse
x has some y other than x, in act as to being, that causes x's esse". -/
theorem otherActualCauseIffExternalCause (p : Profile B P R) :
    DistinctEsseHasOtherActualCause p ↔ DistinctEsseRequiresExternalCauseReading p :=
  Iff.rfl

/-- In the three control profiles, `true`'s esse is its essence, so only
`false` is an actual distinct-esse being. -/
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
theorem esseCauseEfficiencyControls : EsseCauseEfficiencyControls := by
  refine ⟨?nonEfficient, ?restricted, ?nonvacuity⟩
  · -- Non-efficient cause: true causes false's esse, nothing is efficient.
    let q : EfficiencyProfile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun c x _ => c = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := ()
      EfficientlyCausesEsse := fun _ _ => False }
    have hOnly := onlyFalseDistinct q rfl rfl
    have hd : DistinctEsseAt q.toProfile false := ⟨True.intro, Bool.noConfusion⟩
    have hExt : ∀ x, DistinctEsseAt q.toProfile x → HasExternalEsseCause q.toProfile x := by
      intro x hx
      have hx' : x = false := hOnly x hx
      subst hx'
      exact ⟨true, Bool.noConfusion, True.intro, rfl, rfl⟩
    have hTrueFalse : (true : Bool) ≠ false := Bool.noConfusion
    exact ⟨q, hd,
      (fun x hx => Or.inr (hExt x hx)),
      (fun _ _ h => h),
      (fun x h => Bool.noConfusion (h.1.symm.trans h.2)),
      (fun _ _ _ => True.intro),
      hExt,
      hExt,
      (fun h => h false hd true hTrueFalse True.intro ⟨rfl, rfl⟩),
      (fun h => h true false hTrueFalse ⟨rfl, rfl⟩),
      (fun h => let ⟨_, _, _, _, hE⟩ := h false hd; hE)⟩
  · -- Restricted bridge only: false causes true's esse non-efficiently.
    let q : EfficiencyProfile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun c x _ => c ≠ x
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := ()
      EfficientlyCausesEsse := fun c x => c = true ∧ x = false }
    have hOnly := onlyFalseDistinct q rfl rfl
    have hd : DistinctEsseAt q.toProfile false := ⟨True.intro, Bool.noConfusion⟩
    have hBridge : DistinctActualEsseCauseIsEfficient q := by
      intro x hx y hne _ _
      have hx' : x = false := hOnly x hx
      subst hx'
      cases y with
      | false => exact absurd rfl hne
      | true => exact ⟨rfl, rfl⟩
    have hFalseTrue : (false : Bool) ≠ true := Bool.noConfusion
    exact ⟨q, hd, hBridge,
      (fun h => Bool.noConfusion (h false true hFalseTrue hFalseTrue).1)⟩
  · -- Nonvacuity: true efficiently causes false's esse.
    let q : EfficiencyProfile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun c x _ => c = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := ()
      EfficientlyCausesEsse := fun c x => c = true ∧ x = false }
    have hOnly := onlyFalseDistinct q rfl rfl
    have hd : DistinctEsseAt q.toProfile false := ⟨True.intro, Bool.noConfusion⟩
    have hExt : ∀ x, DistinctEsseAt q.toProfile x → HasExternalEsseCause q.toProfile x := by
      intro x hx
      have hx' : x = false := hOnly x hx
      subst hx'
      exact ⟨true, Bool.noConfusion, True.intro, rfl, rfl⟩
    have hAll : CausingAnothersEsseIsEfficient q := fun _ _ _ h => h
    exact ⟨q, hd,
      (fun x hx => Or.inr (hExt x hx)),
      (fun _ _ h => h),
      hExt,
      hAll,
      distinctActualEsseCauseEfficientFromUnrestricted q hAll,
      externalEfficientEsseCauseFromDeEnte q hExt
        (distinctActualEsseCauseEfficientFromUnrestricted q hAll)⟩

end TruthCore.Results.Causality.EsseCauseEfficiency
