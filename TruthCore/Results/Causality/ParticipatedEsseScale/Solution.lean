module

public import TruthCore.Causality.ParticipatedEsseScale

@[expose] public section
namespace TruthCore.Results.Causality.ParticipatedEsseScale

open TruthCore.Causality.ParticipatedEsseScale
open TruthCore.Causality.SoleEsseGiver
open TruthCore.Causality.EsseCauseEfficiency (EfficiencyProfile)

theorem boundFromRealizedLevels {B P R A D : Type} [Preorder D] (q : EfficiencyProfile B P R)
    (Participated OwnBeing : B → Prop) (s : B) (Total : B → B → R → Prop)
    (Pure : A → Prop) (Has : B → A → Prop) (level : A → D) (degree : R → B → D)
    (hSource : SoleEssentialGiver q.toProfile Participated OwnBeing s)
    (hGiving : EssentialGivingIsEfficientAndTotal q Participated OwnBeing Total)
    (hPreserve : GivingPreservesDeterminations q Participated Total Pure Has)
    (hScale : OwnDegreeFromRealizedLevels q.toProfile Pure Has level degree) :
    BoundsParticipatedEsse q.toProfile Participated degree s := by
  obtain ⟨w, hw, hp⟩ := hSource.1
  have hs := (hSource.2 w hw hp).1.2.1
  refine ⟨hs, ?_⟩
  intro x ha hx
  obtain ⟨hne, _, ho, hc⟩ := (hSource.2 x ha hx).1
  obtain ⟨he, ht⟩ := hGiving s x ha hx hne hs ho hc
  apply (hScale x ha).mono (hScale s hs)
  rintro v ⟨a, hpure, hhas, hv⟩
  exact ⟨a, hpure, hPreserve s x ha hx he ht a hpure hhas, hv⟩

theorem channelControl : ChannelControl := by
  intro n hn
  have inputLub : IsLUB {k | detected (n, n) k} n := by
    exact ⟨fun _ h => h.elim id id, fun _ h => h (Or.inl (le_refl n))⟩
  have combinedLub : IsLUB {k | detected (n + n, 0) k} (n + n) := by
    refine ⟨?_, fun _ h => h (Or.inl (le_refl _))⟩
    intro k hk
    exact hk.elim id (fun h => le_trans h (Nat.zero_le _))
  have addBound (a k : Nat) : a ≤ a + k := by
    induction k with
    | zero => exact Nat.le_refl a
    | succ _ ih => exact Nat.le.step ih
  have hlt : n < n + n := by
    cases n with
    | zero => exact hn
    | succ k => exact Nat.succ_le_succ (addBound (k + 1) k)
  exact ⟨rfl, rfl, fun _ => Iff.rfl, inputLub, inputLub, combinedLub, hlt,
    Or.inl le_rfl, fun h => (Nat.not_le_of_lt hlt) (h.elim id id)⟩

end TruthCore.Results.Causality.ParticipatedEsseScale
