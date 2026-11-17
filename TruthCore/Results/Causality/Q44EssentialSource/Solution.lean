module

public import TruthCore.Causality.Q44EssentialSource

@[expose] public section
namespace TruthCore.Results.Causality.Q44EssentialSource
open TruthCore.Causality.Q44EssentialSource
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte (AtMostOneEsseIsEssence)
open TruthCore.Causality.Round2PerfectionPrimacy (OthersThanPrimaryParticipateEsse)
open TruthCore.Causality.CreatureSenses (IsCreatureOfUniversalCause)
open TruthCore.Latin.Aquinas.SummaTheologiae (OthersAreCreaturesReading CausesAllInGenus)

/-- Source selection through the existing De ente at-most-one statement,
with its identity dictionary and one selected actual identity witness explicit. -/
theorem sourcesSelected {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (p : B)
    (hIdentity : RelevantEssentialSourceHasIdentity f Participated OwnBeing)
    (hOne : AtMostOneEsseIsEssence f)
    (hSelected : SelectedActualIdentity f p) :
    RelevantEssentialSourcesSelected f Participated OwnBeing p := by
  intro c x hx _ hc ho he
  exact hOne c p hc hSelected.1 (hIdentity c x hx ‹c ≠ x› hc ho he) hSelected.2

/-- Each other thing has a selected own-being source of esse. That same p
therefore causes every other actual being and makes each other thing CREATURE_1.
No GOD_4 dictionary, maximality or claim of efficiency is used. -/
theorem othersAreCreatures {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (p : B)
    (hOthers : OthersThanPrimaryParticipateEsse Participated p)
    (hSource : ParticipatedHasEssentialSource f Participated OwnBeing)
    (hSelection : RelevantEssentialSourcesSelected f Participated OwnBeing p) :
    OthersAreCreaturesReading
      (IsCreatureOfUniversalCause f.InAct f.CausesIn f.esse) p := by
  have causes : ∀ x, x ≠ p → f.CausesIn p x f.esse := by
    intro x hx
    obtain ⟨c, hne, hc, ho, he⟩ := hSource x (hOthers x hx)
    have hcp := hSelection c x (hOthers x hx) hne hc ho he
    exact hcp ▸ he
  have all : CausesAllInGenus f.InAct f.CausesIn f.esse p :=
    fun x hx _ => causes x hx
  exact fun x hx => ⟨p, all, hx, causes x hx⟩

open Control.Three in
private theorem forallThree (Q : Control.Three → Prop) :
    (Q primary ∧ Q source ∧ Q effect) ↔ ∀ x, Q x := by
  constructor
  · intro h x
    cases x with
    | primary => exact h.1
    | source => exact h.2.1
    | effect => exact h.2.2
  · intro h
    exact ⟨h primary, h source, h effect⟩

open Control.Three in
private theorem existsThree (Q : Control.Three → Prop) :
    (Q primary ∨ Q source ∨ Q effect) ↔ ∃ x, Q x := by
  constructor
  · intro h
    rcases h with h | h | h
    · exact ⟨primary, h⟩
    · exact ⟨source, h⟩
    · exact ⟨effect, h⟩
  · rintro ⟨x, hx⟩
    cases x with
    | primary => exact Or.inl hx
    | source => exact Or.inr (Or.inl hx)
    | effect => exact Or.inr (Or.inr hx)

open Control.Three in
private instance (priority := 2000) (Q : Control.Three → Prop) [DecidablePred Q] :
    Decidable (∀ x, Q x) :=
  decidable_of_iff (Q primary ∧ Q source ∧ Q effect) (forallThree Q)

open Control.Three in
private instance (priority := 2000) (Q : Control.Three → Prop) [DecidablePred Q] :
    Decidable (∃ x, Q x) :=
  decidable_of_iff (Q primary ∨ Q source ∨ Q effect) (existsThree Q)

open Control in
/-- Closed finite interpretations, not metaphysical possibility claims. -/
theorem controls : Certificate := by
  unfold Certificate SelectedActualIdentity AtMostOneEsseIsEssence
    ParticipatedHasEssentialSource RelevantEssentialSourceHasIdentity
    RelevantEssentialSourcesSelected OthersAreCreaturesReading IsCreatureOfUniversalCause
    CausesAllInGenus
  dsimp [primaryOnly, twoIdentities, sourceOnly, positive, profile,
    participant, own, localCause, other, ownPrimary]
  repeat' apply And.intro
  all_goals decide

end TruthCore.Results.Causality.Q44EssentialSource
