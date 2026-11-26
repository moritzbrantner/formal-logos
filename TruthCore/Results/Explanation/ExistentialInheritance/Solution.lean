module

public import TruthCore.Explanation.ExistentialInheritance
public import TruthCore.Explanation.BruteContingencyParity
public import TruthCore.Results.Causality.DerivativeJointPower.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.ExistentialInheritance

open TruthCore.Explanation.ExistentialInheritance
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Explanation.EssenceReasonSeparation
open TruthCore.Explanation.PSRStrength
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Explanation.ExplanatoryClosure

variable {W B : Type}

theorem absence_transfer (p : Profile W B) (w : W) (x b : B)
    (hx : p.explanation.ontic.ExistsAt w x) (hr : ModalRequiresExistence p w x b)
    (hb : ContingentAt p.explanation.ontic w b) :
    ContingentAt p.explanation.ontic w x := by
  obtain ⟨_, v, hv, hnot⟩ := hb
  exact ⟨hx, v, hv, fun hxv => hnot (hr v hv hxv)⟩

theorem absenceInheritance : AbsenceInheritance := by
  refine ⟨fun _ _ => absence_transfer, ?_, ?_, ?_⟩
  · intro W B p w x y b hxy hyb v hv hx
    exact hyb v hv (hxy v hv hx)
  · intro W B p w x b hbridge he hx hb
    exact absence_transfer p w x b hx (hbridge x b he) hb
  · intro W B p w b D hD hb
    refine ⟨fun x hx => absence_transfer p w x b (hD x hx).1 (hD x hx).2 hb, ?_⟩
    obtain ⟨_, v, hv, hn⟩ := hb
    exact ⟨v, hv, fun x hx hxx => hn ((hD x hx).2 v hv hxx)⟩

namespace ContainedProof

open Contained

theorem parent_present (k w : Bool) (n : Nat) (h : enabled k w) :
    (ontic k).ExistsAt w (parent n) := by
  cases n with
  | zero => exact h
  | succ n => exact h

theorem parent_distinct (n : Nat) : parent n ≠ Being.derivative n := by
  cases n with
  | zero => intro h; cases h
  | succ n =>
    intro h
    have hn : n = n + 1 := Being.derivative.inj h
    exact Nat.ne_of_lt (Nat.lt_succ_self n) hn

theorem factive (k : Bool) : Factive (arena k) := by
  intro w r f h
  obtain ⟨hen, n, hr, hf⟩ := h
  subst r
  subst f
  exact ⟨parent_present k w n hen, hen⟩

theorem actual (k : Bool) : ActualResources (arena k) false records := by
  intro n _
  refine ⟨Or.inl rfl, ?_⟩
  intro f hf
  cases hf with
  | inl he =>
    subst f
    exact parent_present k false n (Or.inl rfl)
  | inr he => subst f; trivial

theorem rules (k : Bool) : RulesPreserveTruth (arena k) false records := by
  intro n _ v _ hm
  have hp := hm (.exists (parent n)) (Or.inl rfl)
  cases n with
  | zero => exact hp
  | succ n => exact hp

theorem base_unexplained (k : Bool) : ¬ Explained (arena k) false (.exists .base) := by
  rintro ⟨r, _, n, _, hn⟩
  cases hn

theorem derivative_explained (k : Bool) (n : Nat) :
    Explained (arena k) false (.exists (.derivative n)) :=
  ⟨.exists (parent n), Or.inl rfl, n, rfl, rfl⟩

theorem fixed_trap : Trap (allMembers records) fixedResources baseDependent := by
  constructor
  · intro f hd hf
    cases hd with
    | inl hb =>
      subst f
      cases hf with
      | inl hl => cases hl
      | inr hh => cases hh
    | inr hn =>
      obtain ⟨n, hn⟩ := hn
      subst f
      cases hf with
      | inl hl => cases hl
      | inr hh => cases hh
  · intro n _ _
    refine ⟨.exists (parent n), Or.inl rfl, ?_⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, rfl⟩

/-- Exact reuse of the existing trap theorem. This is a helper, not a new
registered philosophical implication or an independent defense of its policy. -/
theorem no_fixed_supply (n : Nat) :
    ¬ FullSupply records fixedResources (.exists (.derivative n)) :=
  TruthCore.Results.Causality.DerivativeJointPower.trap_obstruction
    (allMembers records) fixedResources baseDependent fixed_trap
    (.exists (.derivative n)) (Or.inr ⟨n, rfl⟩)

theorem supply_with_base (n : Nat) :
    FullSupply records withBase (.exists (.derivative n)) := by
  have hl : FullSupply records withBase .law := .intrinsic _ (Or.inl (Or.inl rfl))
  have hb : FullSupply records withBase (.exists .base) := .intrinsic _ (Or.inr rfl)
  induction n with
  | zero =>
    apply Supply.joint 0 trivial
    intro f hf
    cases hf with
    | inl he => subst f; exact hb
    | inr he => subst f; exact hl
  | succ n ih =>
    apply Supply.joint (n + 1) trivial
    intro f hf
    cases hf with
    | inl he => subst f; exact ih
    | inr he => subst f; exact hl

/-- Induction follows the submitted derivation itself. A law cannot seed a
base existence, and each derivative rule needs a predecessor and the law. -/
theorem resources_of_derivation (S : Fact → Prop)
    (hno : ∀ n, ¬ S (.exists (.derivative n))) (f : Fact)
    (h : FullSupply records S f) :
    (f = .exists .base → S (.exists .base)) ∧
    (f = .law → S .law) ∧
    (∀ n, f = .exists (.derivative n) → S (.exists .base) ∧ S .law) := by
  induction h with
  | intrinsic e hs =>
    refine ⟨fun he => he ▸ hs, fun he => he ▸ hs, ?_⟩
    intro n he
    exact False.elim (hno n (he ▸ hs))
  | joint g _ _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro he; cases he
    · intro he; cases he
    · intro _ _
      have hb : S (.exists .base) := by
        cases g with
        | zero => exact (ih (.exists .base) (Or.inl rfl)).1 rfl
        | succ n => exact ((ih (.exists (.derivative n)) (Or.inl rfl)).2.2 n rfl).1
      exact ⟨hb, (ih .law (Or.inr rfl)).2.1 rfl⟩

theorem essential_bridge : EssenceAbsenceBridge (profile false) false := by
  intro x b h
  obtain ⟨⟨n, hx⟩, hb⟩ := h
  subst x
  have hb' : b = .base := TruthCore.Explanation.ExistencePSR.ExistenceFact.fact.inj hb
  subst b
  intro v _ hv
  exact hv

theorem false_overlay_absent : ¬ enabled false true := by
  intro h
  cases h with
  | inl h => cases h
  | inr h => cases h

end ContainedProof

theorem resourceInheritance : ResourceInheritance := by
  open ContainedProof in
    refine ⟨?_, fixed_trap, no_fixed_supply, supply_with_base, ?_,
      essential_bridge, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨fun _ => ⟨trivial, trivial⟩, fun _ _ => Iff.rfl,
      ContainedProof.factive k, ?_, ContainedProof.actual k, ContainedProof.rules k,
      ContainedProof.base_unexplained k, ContainedProof.derivative_explained k, ?_⟩
    · intro w v h b
      cases b with
      | background => exact Iff.rfl
      | base => exact h
      | derivative n => exact h
    · intro w n h
      exact ⟨Contained.parent n, ContainedProof.parent_present k w n h,
        ContainedProof.parent_distinct n, h, n, rfl, rfl⟩
  · intro S hno n hs
    exact (ContainedProof.resources_of_derivation S hno _ hs).2.2 n rfl
  · exact ⟨Or.inl rfl, true, trivial, ContainedProof.false_overlay_absent⟩
  · intro n
    exact ⟨Or.inl rfl, true, trivial, ContainedProof.false_overlay_absent⟩
  · intro n
    exact ContainedProof.false_overlay_absent
  · intro v _
    exact Or.inr rfl
  · intro n v _
    exact Or.inr rfl

theorem replacementBoundary : ReplacementBoundary := by
  refine ⟨⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun _ _ => trivial, ?_, ?_, ?_, ?_,
    ⟨rfl, rfl⟩, ?_⟩
  · intro w
    refine ⟨trivial, Replacement.source w, ?_, ?_, rfl, rfl⟩
    · cases w <;> rfl
    · cases w <;> intro h <;> cases h
  · intro h
    exact Bool.noConfusion (h true trivial trivial)
  · exact modal_requirement_of_necessary directedNature false false true (fun _ _ => trivial)
  · exact modal_requirement_of_necessary directedNature false true false (fun _ _ => trivial)
  · intro h
    exact Bool.noConfusion h.1

/-! ## Contingent-existence demand pilot (#750, #1007)

Reuse the actual existence-reason model and the ontic stance, not a score or a
new notion of adequacy. A selected reason is a token admitted for the target;
the step tracks the being the token is about. Its selection and the norm
requiring an explanation of that being's existence are distinct commitments.
-/
namespace DemandPilot

open TruthCore.Explanation.ExistencePSR (Model Reason ExistenceFact)
open TruthCore.Explanation.BruteContingencyParity
  (WhyStance WhyHonors NoBruteContingentExistenceAt)

/-- A chosen admitted reason for x is about a contingent being y. This is
not yet a proof that y is an indispensable productive cause of x. -/
def SelectedContingentReason (m : Model W B) (w : W)
    (selected : B → Reason B → Prop) (x y : B) : Prop :=
  ∃ r, selected x r ∧ m.explains w r (.fact x) ∧
    TruthCore.Explanation.BruteContingencyParity.source r = y ∧
    ContingentAt m.ontic w y

/-- OPEN norm: the demand to explain the existence of a target extends to
the existence of a contingent bearer of its chosen reason. Only chosen
admitted reasons are tested; no universal PSR is a definition here. -/
def DemandPropagates (m : Model W B) (w : W)
    (selected : B → Reason B → Prop)
    (S : WhyStance (ExistenceFact B ⊕ Reason B)) : Prop :=
  ∀ x y, SelectedContingentReason m w selected x y →
    S.requiresWhy ((ofModel m).exist x) →
    S.requiresWhy ((ofModel m).exist y)

/-- An honored, accepted existence-demand supplies a #312 reason token, not
merely a reason for belief or a bare fact in another arena. -/
theorem reasonOfHonoredDemand (m : Model W B) (w : W)
    (S : WhyStance (ExistenceFact B ⊕ Reason B)) (x : B)
    (hHonors : WhyHonors S (ofModel m) w)
    (hReq : S.requiresWhy ((ofModel m).exist x))
    (hAccept : S.accepts ((ofModel m).exist x)) :
    ∃ r, m.explains w r (.fact x) := by
  obtain ⟨r, hr⟩ := hHonors _ hReq hAccept
  cases r with
  | inl f =>
    exact False.elim hr
  | inr r =>
    exact ⟨r, hr⟩

/-- Finite reach transports the demand, not the truth of the target. -/
theorem demandAlongSelectedReasons (m : Model W B) (w : W)
    (selected : B → Reason B → Prop)
    (S : WhyStance (ExistenceFact B ⊕ Reason B)) {x y : B}
    (hProp : DemandPropagates m w selected S)
    (hPath : Relation.ReflTransGen (SelectedContingentReason m w selected) x y)
    (hReq : S.requiresWhy ((ofModel m).exist x)) :
    S.requiresWhy ((ofModel m).exist y) := by
  induction hPath with
  | refl => exact hReq
  | tail _ hStep ih => exact hProp _ _ hStep ih

/-- The actual target of this pilot, 608a262d. Coverage by finite paths from
demanded existences is a separate open hypothesis. Neither path coverage nor
demand propagation is claimed to follow merely from undertaking inquiry. -/
theorem psrFromDemandCoverage (m : Model W B) (w : W)
    (selected : B → Reason B → Prop)
    (S : WhyStance (ExistenceFact B ⊕ Reason B))
    (hHonors : WhyHonors S (ofModel m) w)
    (hAccept : ∀ x, ContingentAt m.ontic w x → S.accepts ((ofModel m).exist x))
    (hProp : DemandPropagates m w selected S)
    (hCover : ∀ x, ContingentAt m.ontic w x → ∃ t,
      S.requiresWhy ((ofModel m).exist t) ∧
      Relation.ReflTransGen (SelectedContingentReason m w selected) t x) :
    NoBruteContingentExistenceAt m w := by
  intro x hx
  obtain ⟨t, ht, hPath⟩ := hCover x hx
  exact reasonOfHonoredDemand m w S x hHonors
    (demandAlongSelectedReasons m w selected S hProp hPath ht) (hAccept x hx)

/-- Local test of the rival: an accepted unexplained bearer reached from a
demanded existence forces a failure of the propagation norm if the stance
honors its own demands. It does not entail a contradiction without that norm. -/
theorem bruteForcesDemandBreak (m : Model W B) (w : W)
    (selected : B → Reason B → Prop)
    (S : WhyStance (ExistenceFact B ⊕ Reason B)) {x y : B}
    (hHonors : WhyHonors S (ofModel m) w)
    (hPath : Relation.ReflTransGen (SelectedContingentReason m w selected) x y)
    (hReq : S.requiresWhy ((ofModel m).exist x))
    (hAccept : S.accepts ((ofModel m).exist y))
    (hNone : ¬ ∃ r, m.explains w r (.fact y)) :
    ¬ DemandPropagates m w selected S := by
  intro hProp
  exact hNone (reasonOfHonoredDemand m w S y hHonors
    (demandAlongSelectedReasons m w selected S hProp hPath hReq) hAccept)

/-- Same existing contained-bruteness model: no alteration to its ontology
or reason tokens. The stance accepts actual truths but demands a reason for
the first derivative only. -/
def containedModel : Model Bool Contained.Being :=
  (Contained.profile false).explanation

def containedStance : WhyStance (ExistenceFact Contained.Being ⊕ Reason Contained.Being) where
  accepts := fun f => (ofModel containedModel).holds false f
  core := fun _ => False
  demands := fun _ => False
  requiresWhy := fun f => f = (ofModel containedModel).exist (.derivative 0)

def allSelected (_ : Contained.Being) (_ : Reason Contained.Being) : Prop := True

/-- The rival really honors its restricted local demand and denies the exact
PSR. Its selected reason for the derivative is about the same accepted
contingent base that it exempts. The exemption violates propagation, not
logical consistency by itself. -/
theorem containedExemption :
    WhyHonors containedStance (ofModel containedModel) false ∧
    ¬ NoBruteContingentExistenceAt containedModel false ∧
    SelectedContingentReason containedModel false allSelected (.derivative 0) .base ∧
    containedStance.requiresWhy ((ofModel containedModel).exist (.derivative 0)) ∧
    containedStance.accepts ((ofModel containedModel).exist .base) ∧
    ¬ containedStance.requiresWhy ((ofModel containedModel).exist .base) ∧
    ¬ DemandPropagates containedModel false allSelected containedStance := by
  have hBase : ContingentAt containedModel.ontic false .base :=
    ⟨Or.inl rfl, true, trivial, ContainedProof.false_overlay_absent⟩
  have hNone : ¬ ∃ r, containedModel.explains false r (.fact .base) := by
    rintro ⟨r, hr⟩
    change Contained.enabled false false ∧ ∃ n,
      r = .circumstance (Contained.parent n) ∧
        ExistenceFact.fact Contained.Being.base = .fact (.derivative n) at hr
    obtain ⟨_, n, _, hn⟩ := hr
    cases hn
  have hHonors : WhyHonors containedStance (ofModel containedModel) false := by
    intro f hf _
    change f = (ofModel containedModel).exist (.derivative 0) at hf
    subst f
    exact ⟨Sum.inr (.circumstance .base), ⟨Or.inl rfl, 0, rfl, rfl⟩⟩
  have hStep : SelectedContingentReason containedModel false allSelected
      (.derivative 0) .base :=
    ⟨.circumstance .base, trivial, ⟨Or.inl rfl, 0, rfl, rfl⟩, rfl, hBase⟩
  have hReq : containedStance.requiresWhy ((ofModel containedModel).exist (.derivative 0)) := rfl
  have hAccept : containedStance.accepts ((ofModel containedModel).exist .base) := hBase.1
  have hNot : ¬ containedStance.requiresWhy ((ofModel containedModel).exist .base) :=
    fun h => hNone (reasonOfHonoredDemand containedModel false containedStance .base hHonors h hAccept)
  exact ⟨hHonors, fun h => hNone (h .base hBase), hStep, hReq, hAccept,
    hNot, fun h => hNot (h _ _ hStep hReq)⟩

end DemandPilot

end TruthCore.Results.Explanation.ExistentialInheritance
