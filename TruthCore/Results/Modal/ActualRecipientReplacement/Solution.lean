module

public import TruthCore.Modal.ActualRecipientReplacement

@[expose] public section

namespace TruthCore.Results.Modal.ActualRecipientReplacement

open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.ModalGrounding (NoActualContingentConcreteIn)
open TruthCore.Modal.PrussPowerPremises
open TruthCore.Modal.PrussPowerPremises.Model
open TruthCore.Modal.ActualRecipientReplacement

private theorem contingentRecipient (v : Bool) :
    ∃ x, ContingentAt frame.history.ontic v x ∧ GivesTo frame v .g x := by
  cases v
  · exact ⟨.c, ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), true, trivial, by
      simp [frame, gFrame, replEx]⟩, (), Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨.d, ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), false, trivial, by
      simp [frame, gFrame, replEx]⟩, (), Or.inr ⟨rfl, rfl, rfl⟩⟩

private theorem actualContingent (x : Bg)
    (contingent : ContingentAt frame.history.ontic false x) : x = .c := by
  cases x with
  | g =>
    obtain ⟨_, _, absent⟩ := contingent.2
    exact (absent (Or.inl rfl)).elim
  | c => rfl
  | d => exact ((by simp [replEx] : ¬ replEx false .d) contingent.1).elim

theorem boundary : Boundary := by
  refine ⟨fun _ _ => Or.inl rfl, ?_, contingentRecipient, ?_, ?_⟩
  · intro v y x gave
    obtain ⟨_, gave⟩ := gave
    rcases gave with ⟨_, same, world⟩ | ⟨_, same, world⟩
    · exact Or.inr (Or.inl ⟨same, world⟩)
    · exact Or.inr (Or.inr ⟨same, world⟩)
  · refine ⟨.g, Or.inl rfl, ⟨rfl, ?_⟩, true, trivial, ?_, Or.inl rfl, ?_⟩
    · intro v _
      obtain ⟨x, _, _, gave⟩ := contingentRecipient v
      exact ⟨x, gave⟩
    · intro x _ contingent
      rw [actualContingent x contingent]
      simp [frame, gFrame, replEx]
    · intro x _ contingent
      rw [actualContingent x contingent]
      exact ⟨⟨(), Or.inl ⟨rfl, rfl, rfl⟩⟩, by
        simp [GivesTo, frame, gFrame, giving, givesCHere, givesDThere]⟩
  · intro v none
    obtain ⟨x, contingent, _⟩ := contingentRecipient v
    exact none x trivial contingent

end TruthCore.Results.Modal.ActualRecipientReplacement
