module

public import TruthCore.Causality.ProductiveDeletion

@[expose] public section
namespace TruthCore.Results.Causality.ProductiveDeletion
open TruthCore.Causality.ProductiveDeletion
open TruthCore.Causality.JointGroups (Groups Exercise)
open TruthCore.Causality.DerivativeJointPower (Supply)
open TruthCore.Causality.AcquiredHistoryTransfer (CoveredAncestry)
open TruthCore.Causality.ExerciseContribution (Step)

variable {B E G S : Type}

/-- Transport the derivation unless it already contains a positive-length
selected branch. At a joint node the other inputs have original supply even
when only one of them continues the selected branch. -/
theorem pathOfLoss {h : Groups E G} {I : E → Prop} {selected : Set E} {v : E}
    (original : Supply h I v) (loss : ¬ Supply (withoutInputs h selected) I v) :
    ∃ u ∈ selected, Relation.TransGen (SuppliedStep h I) u v := by
  classical
  by_contra noPath
  apply loss
  clear loss
  induction original with
  | intrinsic e he => exact .intrinsic e he
  | joint g admitted inputs ih =>
    have step (e) (he : e ∈ h.contributors g) : SuppliedStep h I e (h.effect g) :=
      ⟨g, admitted, rfl, he, inputs⟩
    apply Supply.joint g
    · exact ⟨admitted, fun e he hs => noPath ⟨e, hs, .single (step e he)⟩⟩
    · intro e he
      exact ih e he fun ⟨u, hu, p⟩ => noPath ⟨u, hu, p.tail (step e he)⟩

theorem selfInputSurvives {h : Groups E G} {I : E → Prop} {v : E}
    (original : Supply h I v) : Supply (withoutInputs h {v}) I v := by
  classical
  let cut := withoutInputs h {v}
  by_contra lost
  have transport {e} (supplied : Supply h I e) : Supply cut I e := by
    induction supplied with
    | intrinsic e hi => exact .intrinsic e hi
    | joint g hg _ ih =>
      refine Supply.joint (h := cut) g ⟨hg, ?_⟩ ih
      intro u hu same
      obtain rfl : u = v := same
      exact lost (ih u hu)
  exact lost (transport original)

theorem ancestryFromLosses (m : Exercise B E G S) (covered : B → E → Prop)
    (I : E → Prop) (selected : B → E → Set E)
    (cuts : CoveredLosses m covered I selected) : CoveredAncestry m covered := by
  intro a v hv
  obtain ⟨owned, original, loss⟩ := cuts.2 a v hv
  obtain ⟨u, hu, path⟩ := pathOfLoss original loss
  have actualStep {p q} (s : SuppliedStep m.exercisedGroups I p q) : Step m p q := by
    obtain ⟨g, hg, rfl, hp, _⟩ := s
    obtain ⟨_, members, effect⟩ := cuts.1.2 g hg.2
    exact ⟨members p (Or.inl hp), effect, g, hg, rfl, hp⟩
  exact ⟨u, owned u hu, Relation.TransGen.mono (fun p q => @actualStep p q) u v path⟩

open TruthCore.Causality.ExerciseContribution.Press

theorem pressLoss : PressLoss := by
  let h := (exercise .application).exercisedGroups
  let cut := withoutInputs h {.drive}
  have stroke : Supply h pressSeed .stroke := by
    apply Supply.joint (h := h) .stroke ⟨by simp [exercise], rfl⟩
    intro e he
    obtain rfl : e = .drive := he
    exact .intrinsic _ (Or.inr (Or.inl rfl))
  have mark : Supply h pressSeed .imprint := by
    apply Supply.joint (h := h) .imprint ⟨by simp [exercise], trivial⟩
    intro e he
    rcases he with same | ⟨bad, _⟩
    · exact same ▸ stroke
    · contradiction
  have surviving {e} (hs : Supply cut pressSeed e) : e ≠ .stroke ∧ e ≠ .imprint := by
    induction hs with
    | intrinsic e he =>
      rcases he with rfl | rfl | rfl <;> decide
    | joint g admitted _ ih =>
      cases g <;> try exact ⟨by decide, by decide⟩
      · exact (admitted.2 .drive rfl rfl).elim
      · exact ((ih .stroke (Or.inl rfl)).1 rfl).elim
  have maintenance : Supply cut pressSeed .maintenance := .intrinsic _ (Or.inl rfl)
  have kept (e : Event) (he : e = .agentEsse ∨ e = .patientEsse) : Supply cut pressSeed e := by
    refine Supply.joint (h := cut) e ⟨?_, ?_⟩ ?_
    · rcases he with rfl | rfl <;> exact ⟨by simp [exercise], trivial⟩
    · intro u hu
      have hm : u = .maintenance := by rcases he with rfl | rfl <;> exact hu
      subst u
      decide
    · intro u hu
      have hm : u = .maintenance := by rcases he with rfl | rfl <;> exact hu
      exact hm ▸ maintenance
  exact ⟨mark, fun hs => (surviving hs).2 rfl, .intrinsic _ (Or.inr (Or.inr rfl)),
    kept _ (Or.inl rfl), kept _ (Or.inr rfl)⟩

end TruthCore.Results.Causality.ProductiveDeletion
