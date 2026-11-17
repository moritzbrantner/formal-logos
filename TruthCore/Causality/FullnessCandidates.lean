module

public import Mathlib.Data.Set.Lattice.Order
public import TruthCore.Causality.TermSenseForks2
public import TruthCore.Causality.Q44SourceSupply
public import TruthCore.Logic.ExcludedMiddle

/-! Independently specified candidate degrees. Neither construction consults
Limited, MoreIn, Godhood or the comparison it is used to test. They measure
inclusive perfection coverage and actual esse-causal reach, respectively; no
identification of either with esse fullness is built in. -/

@[expose] public section
namespace TruthCore.Causality.FullnessCandidates
open TruthCore.Causality.TermSenseForks (ActFrame)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause CommonEsseIsEssenceSource)
open TruthCore.Causality.Q44SourceSupply (ActualEsseCauseComposes)

/-- Coverage of independently classified pure perfections, with the existing
inclusive formal-or-virtual act sense. The frame retains the two modes;
coverage does not order formal possession against virtual possession. -/
def possessionContent {B R : Type} (F : ActFrame B R) (Pure : R → Prop)
    (x : B) : Set R := {r | Pure r ∧ F.InActFormallyOrVirtually x r}

/-- Actual distinct esse effects of c in the existing source dictionary.
This is esse-causal scope, not a perfection-content or esse-grade definition. -/
def actualEsseEffects {B P R : Type} (p : Profile B P R) (c : B) : Set B :=
  {x | ActualEsseCause p c x}

/-- A complete inclusive repertoire gives weak coverage; strict coverage has an
exact missing-perfection witness, while a complete recipient ties the source. -/
def ContentAudit : Prop := ∀ (B R : Type) (F : ActFrame B R) (Pure : R → Prop)
    (c x : B), TruthCore.Logic.ExcludedMiddle →
    (∀ r, Pure r → F.InActFormallyOrVirtually c r) →
    possessionContent F Pure x ⊆ possessionContent F Pure c ∧
    ((possessionContent F Pure x < possessionContent F Pure c) ↔
      ∃ r, Pure r ∧ ¬ F.InActFormallyOrVirtually x r) ∧
    ((possessionContent F Pure x = possessionContent F Pure c) ↔
      ∀ r, Pure r → F.InActFormallyOrVirtually x r)

/-- The same actual common ancestor strictly dominates each other actual being
in actual causal footprint, without any premise comparing degrees of esse. -/
def FootprintAudit : Prop := ∀ (B P R : Type) (p : Profile B P R),
    CommonEsseIsEssenceSource p → ActualEsseCauseComposes p →
    ∃ n, p.InAct n p.esse ∧ p.esseOf n = p.essenceOf n ∧
      ∀ x, p.InAct x p.esse → x ≠ n → actualEsseEffects p x < actualEsseEffects p n

end TruthCore.Causality.FullnessCandidates
