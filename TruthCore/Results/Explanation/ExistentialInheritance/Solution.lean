module

public import TruthCore.Explanation.ExistentialInheritance
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

end TruthCore.Results.Explanation.ExistentialInheritance
