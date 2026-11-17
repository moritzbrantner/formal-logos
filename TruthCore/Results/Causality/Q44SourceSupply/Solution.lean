module

public import TruthCore.Causality.Q44SourceSupply

@[expose] public section
namespace TruthCore.Results.Causality.Q44SourceSupply
open TruthCore.Causality.Q44SourceSupply
open TruthCore.Causality.Q44EssentialSource (SelectedActualIdentity ParticipatedHasEssentialSource)
open TruthCore.Causality.TermSenseForks (BecomingBeingFrame ParticipatedHasDistinctEsse)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte
  (ActualEsseCause CommonEsseIsEssenceSource EveryDistinctEsseHasEsseIsEssenceSource AtMostOneEsseIsEssence
   ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Causality.EsseReception
  (EsseReceivedOnlyInOwnEssence NothingInReceptivePotencyToItself)
open TruthCore.Causality.ReceptionLimitation (UnreceivedEsseIsOwnBeing)
open TruthCore.Causality.Round2PerfectionPrimacy (OthersThanPrimaryParticipateEsse)
open TruthCore.Causality.CreatureSenses (IsCreatureOfUniversalCause)
open TruthCore.Latin.Aquinas.SummaTheologiae (OthersAreCreaturesReading CausesAllInGenus)

/-- Collapse a nonempty actual esse-cause chain using the stated composition
premise. The source's actuality is not inferred from mere representation. -/
theorem causeOfChain {B P R : Type} (f : Profile B P R)
    (hCompose : ActualEsseCauseComposes f) {n x : B}
    (hn : f.InAct n f.esse) (h : Relation.TransGen (ActualEsseCause f) n x) :
    f.CausesIn n x f.esse := by
  induction h with
  | single h => exact h.2.2.2
  | tail _ h ih => exact hCompose _ _ _ hn ih h

/-- Identity passes through an explicit reception argument: a supposed receiver
would be in receptive potency to itself; no reception then gives OwnBeing
through its separately stated interpretation bridge. -/
theorem ownBeingOfIdentity {B P R : Type} (f : Profile B P R)
    (Received : B → P → Prop) (Potency : P → P → Prop) (OwnBeing : B → Prop)
    (hOwn : EsseReceivedOnlyInOwnEssence f.essenceOf Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading f.esseOf Received Potency)
    (hIrreflexive : NothingInReceptivePotencyToItself Potency)
    (hUnreceived : UnreceivedEsseIsOwnBeing Received OwnBeing)
    {n : B} (hIdentity : f.esseOf n = f.essenceOf n) : OwnBeing n := by
  apply hUnreceived n
  intro r hr
  have hp := hPotency n r hr
  rw [hOwn n r hr, ← hIdentity] at hp
  exact hIrreflexive _ hp

/-- Actual identity-bearing ancestry plus participant actuality/distinction,
composition and the explicit reception premises supply de05072a. -/
theorem sourceSupply {B P R : Type} (F : BecomingBeingFrame B P R)
    (Received : B → P → Prop) (Potency : P → P → Prop) (OwnBeing : B → Prop)
    (hParticipant : ParticipatedHasDistinctEsse F)
    (hAncestor : EveryDistinctEsseHasEsseIsEssenceSource F.profile)
    (hCompose : ActualEsseCauseComposes F.profile)
    (hOwn : EsseReceivedOnlyInOwnEssence F.profile.essenceOf Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading F.profile.esseOf Received Potency)
    (hIrreflexive : NothingInReceptivePotencyToItself Potency)
    (hUnreceived : UnreceivedEsseIsOwnBeing Received OwnBeing) :
    ParticipatedHasEssentialSource F.profile F.Participated OwnBeing := by
  intro x hx
  have hd := hParticipant x hx
  obtain ⟨n, hn, hIdentity, hPath⟩ := hAncestor x hd
  have hnx : n ≠ x := by
    intro e
    subst x
    exact hd.2 hIdentity
  exact ⟨n, hnx, hn,
    ownBeingOfIdentity F.profile Received Potency OwnBeing hOwn hPotency hIrreflexive
      hUnreceived hIdentity,
    causeOfChain F.profile hCompose hn hPath⟩

/-- The existing common source supplies the weaker per-participant ancestry
interface. This uses actuality and represented distinction, not a naming rule. -/
theorem ancestryOfCommonSource {B P R : Type} (f : Profile B P R)
    (hCommon : CommonEsseIsEssenceSource f) : EveryDistinctEsseHasEsseIsEssenceSource f := by
  obtain ⟨n, hn, hIdentity, _, hPaths⟩ := hCommon
  intro x hx
  have hxn : x ≠ n := by
    intro e
    subst x
    exact hx.2 hIdentity
  exact ⟨n, hn, hIdentity, hPaths x hx.1 hxn⟩

/-- A sibling retaining the existing common-source premise as a direct support
option; no common-source existence is inferred from local external causes. -/
theorem sourceSupplyFromCommon {B P R : Type} (F : BecomingBeingFrame B P R)
    (Received : B → P → Prop) (Potency : P → P → Prop) (OwnBeing : B → Prop)
    (hParticipant : ParticipatedHasDistinctEsse F)
    (hCommon : CommonEsseIsEssenceSource F.profile)
    (hCompose : ActualEsseCauseComposes F.profile)
    (hOwn : EsseReceivedOnlyInOwnEssence F.profile.essenceOf Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading F.profile.esseOf Received Potency)
    (hIrreflexive : NothingInReceptivePotencyToItself Potency)
    (hUnreceived : UnreceivedEsseIsOwnBeing Received OwnBeing) :
    ParticipatedHasEssentialSource F.profile F.Participated OwnBeing :=
  sourceSupply F Received Potency OwnBeing hParticipant
    (ancestryOfCommonSource F.profile hCommon) hCompose hOwn hPotency hIrreflexive hUnreceived

/-- Align the existential common ancestor with the selected p using the SAME
profile's at-most-one and actual identity witness. No IsGod uniqueness is used. -/
theorem selectedSourceSupply {B P R : Type} (F : BecomingBeingFrame B P R)
    (Received : B → P → Prop) (Potency : P → P → Prop) (OwnBeing : B → Prop) (p : B)
    (hParticipant : ParticipatedHasDistinctEsse F)
    (hAncestor : EveryDistinctEsseHasEsseIsEssenceSource F.profile)
    (hCompose : ActualEsseCauseComposes F.profile)
    (hOwn : EsseReceivedOnlyInOwnEssence F.profile.essenceOf Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading F.profile.esseOf Received Potency)
    (hIrreflexive : NothingInReceptivePotencyToItself Potency)
    (hUnreceived : UnreceivedEsseIsOwnBeing Received OwnBeing)
    (hOne : AtMostOneEsseIsEssence F.profile)
    (hSelected : SelectedActualIdentity F.profile p) :
    SelectedEssentialSourceSupply F.profile F.Participated OwnBeing p := by
  intro x hx
  have hd := hParticipant x hx
  obtain ⟨n, hn, hIdentity, hPath⟩ := hAncestor x hd
  have hnp : n = p := hOne n p hn hSelected.1 hIdentity hSelected.2
  subst n
  have hpx : p ≠ x := by
    intro e
    subst x
    exact hd.2 hIdentity
  exact ⟨hpx, hn,
    ownBeingOfIdentity F.profile Received Potency OwnBeing hOwn hPotency hIrreflexive
      hUnreceived hIdentity,
    causeOfChain F.profile hCompose hn hPath⟩

/-- A selected witness for each participant suffices for the existing root
consumer; this does not require all possible own-being causes to equal p. -/
theorem othersAreCreatures {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (p : B)
    (hOthers : OthersThanPrimaryParticipateEsse Participated p)
    (hSupply : SelectedEssentialSourceSupply f Participated OwnBeing p) :
    OthersAreCreaturesReading
      (IsCreatureOfUniversalCause f.InAct f.CausesIn f.esse) p := by
  have causes : ∀ x, x ≠ p → f.CausesIn p x f.esse :=
    fun x hx => (hSupply x (hOthers x hx)).2.2.2
  have all : CausesAllInGenus f.InAct f.CausesIn f.esse p := fun x hx _ => causes x hx
  exact fun x hx => ⟨p, all, hx, causes x hx⟩

open TruthCore.Causality.Q44EssentialSource.Control.Three

private theorem commonStar (identity : Control.Being → Bool) (hi : identity primary = false) :
    CommonEsseIsEssenceSource (Control.profile (fun _ => True) identity Control.starCause) := by
  refine ⟨primary, trivial, hi, ?_, ?_⟩
  · intro c hc
    exact hc.2.2.2.2 rfl
  · intro x _ hx
    exact .single ⟨Ne.symm hx, trivial, trivial, rfl, hx⟩

private theorem commonAbsent : CommonEsseIsEssenceSource Control.absent := by
  refine ⟨primary, (by decide : primary ≠ effect), rfl, ?_, ?_⟩
  · intro c hc
    exact (by decide : primary ≠ source) hc.2.2.2.2
  · intro x hx hne
    cases x with
    | primary => exact (hne rfl).elim
    | source => exact .single ⟨by decide, (by decide : primary ≠ effect), (by decide : source ≠ effect), rfl, rfl⟩
    | effect => exact (hx rfl).elim

private theorem commonChain : CommonEsseIsEssenceSource Control.chain := by
  refine ⟨primary, trivial, rfl, ?_, ?_⟩
  · intro c hc
    rcases hc.2.2.2 with h | h
    · exact (by decide : primary ≠ source) h.2
    · exact (by decide : primary ≠ effect) h.2
  · intro x _ hne
    cases x with
    | primary => exact (hne rfl).elim
    | source => exact .single ⟨by decide, trivial, trivial, Or.inl ⟨rfl, rfl⟩⟩
    | effect =>
      exact .tail (.single ⟨by decide, trivial, trivial, Or.inl ⟨rfl, rfl⟩⟩)
        ⟨by decide, trivial, trivial, Or.inr ⟨rfl, rfl⟩⟩

private theorem commonFull : CommonEsseIsEssenceSource Control.full := by
  refine ⟨primary, trivial, rfl, ?_, ?_⟩
  · intro c hc
    rcases hc.2.2.2 with h | h
    · exact h.2 rfl
    · exact (by decide : primary ≠ effect) h.2
  · intro x _ hx
    exact .single ⟨Ne.symm hx, trivial, trivial, Or.inl ⟨rfl, hx⟩⟩

private theorem forallThree (Q : Control.Being → Prop) :
    (Q primary ∧ Q source ∧ Q effect) ↔ ∀ x, Q x := by
  constructor
  · intro h x
    cases x with
    | primary => exact h.1
    | source => exact h.2.1
    | effect => exact h.2.2
  · intro h
    exact ⟨h primary, h source, h effect⟩

private theorem existsThree (Q : Control.Being → Prop) :
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

private instance (priority := 2000) (Q : Control.Being → Prop) [DecidablePred Q] :
    Decidable (∀ x, Q x) :=
  decidable_of_iff (Q primary ∧ Q source ∧ Q effect) (forallThree Q)

private instance (priority := 2000) (Q : Control.Being → Prop) [DecidablePred Q] :
    Decidable (∃ x, Q x) :=
  decidable_of_iff (Q primary ∨ Q source ∨ Q effect) (existsThree Q)

/-- Closed finite controls of the precise interfaces, not metaphysical rivals. -/
theorem controls : Control.Certificate := by
  unfold Control.Certificate
  refine ⟨⟨commonAbsent, ?_⟩, ⟨commonStar Control.oneIdentity rfl, ?_⟩,
    ⟨commonChain, ?_⟩, ⟨commonStar Control.oneIdentity rfl, ?_⟩,
    ⟨commonStar Control.oneIdentity rfl, ?_⟩, ⟨commonStar Control.twoIdentity rfl, ?_⟩,
    ⟨commonFull, ?_⟩⟩
  all_goals dsimp only [Control.ReceptionInputs, ParticipatedHasDistinctEsse,
    ActualEsseCauseComposes, ActualEsseCause, ParticipatedHasEssentialSource,
    SelectedEssentialSourceSupply, SelectedActualIdentity, AtMostOneEsseIsEssence,
    EsseReceivedOnlyInOwnEssence, ReceiverInPotencyToReceivedEsseReading,
    NothingInReceptivePotencyToItself, UnreceivedEsseIsOwnBeing,
    OthersAreCreaturesReading, IsCreatureOfUniversalCause, CausesAllInGenus,
    TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.DistinctEsseAt,
    Control.frame, Control.star, Control.absent, Control.chain, Control.full,
    Control.two, Control.profile, Control.own, Control.received,
    Control.potency, Control.justEffect, Control.justPrimary, Control.other,
    Control.oneIdentity, Control.twoIdentity, Control.starCause, Control.chainCause,
    Control.fullCause]
  all_goals repeat' apply And.intro
  all_goals decide

end TruthCore.Results.Causality.Q44SourceSupply
