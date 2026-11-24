module

public import TruthCore.Causality.GiverIndexedApplication
public import TruthCore.Logic.ExcludedMiddle

@[expose] public section
namespace TruthCore.Results.Causality.GiverIndexedApplication
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Causality.Q44SourceSupply (ActualEsseCauseComposes)
open TruthCore.Causality.GiverIndexedApplication
open TruthCore.Logic (ExcludedMiddle)

theorem composeOfPerSe {B P R : Type} (f : Profile B P R) (AsCaused : B → B → Prop)
    (hEM : ExcludedMiddle) (hBridge : CausedEsseCauseCausesAsCaused f AsCaused)
    (hPerSe : PerSeComposition f AsCaused) : ActualEsseCauseComposes f := by
  intro a b c actualA givesAB linkBC
  rcases hEM (a = b) with eq | distinct
  · subst a
    exact linkBC.2.2.2
  · have linkAB : ActualEsseCause f a b := ⟨distinct, actualA, linkBC.2.1, givesAB⟩
    exact hPerSe a b c linkAB ⟨linkBC, hBridge b c linkBC ⟨a, linkAB⟩⟩

theorem perSeOfApplication {B P R : Type} (f : Profile B P R) (AsCaused : B → B → Prop)
    (Through : B → B → B → Prop) (hCredit : AppliedGiverComposes f Through)
    (hAlign : EachGiverApplies f AsCaused Through) : PerSeComposition f AsCaused := by
  intro a b c hab hbc
  exact hCredit a b c hab hbc.1 (hAlign a b c hab hbc)

open TruthCore.Case.Catholicism (TransferRole transferFourForallDecidable)
attribute [local instance] transferFourForallDecidable

private instance (p : TransferRole → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .source ∨ p .supporter ∨ p .producer ∨ p .recipient)
    ⟨fun h => by
      rcases h with h | h | h | h
      · exact ⟨.source, h⟩
      · exact ⟨.supporter, h⟩
      · exact ⟨.producer, h⟩
      · exact ⟨.recipient, h⟩,
    fun ⟨x, hx⟩ => by
      cases x with
      | source => exact Or.inl hx
      | supporter => exact Or.inr (Or.inl hx)
      | producer => exact Or.inr (Or.inr (Or.inl hx))
      | recipient => exact Or.inr (Or.inr (Or.inr hx))⟩

theorem controls : Control.Certificate := by
  unfold Control.Certificate Control.Background CausedEsseCauseCausesAsCaused
    AppliedGiverComposes EachGiverApplies PerSeComposition ActualEsseCauseComposes
    PerSeActualEsseCause ActualEsseCause Control.through Control.asCaused
  dsimp only [Control.profile, Control.cause]
  repeat' apply And.intro
  all_goals first
    | decide
    | (intro a b c; cases a <;> cases b <;> cases c <;> decide)
    | (intro h; specialize h .source .producer .recipient; revert h; decide)

end TruthCore.Results.Causality.GiverIndexedApplication
