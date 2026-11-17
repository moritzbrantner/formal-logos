module

public import TruthCore.Causality.SourceScopedAscent
public import TruthCore.Results.Causality.MaximalFromEsseSource.Solution

@[expose] public section
namespace TruthCore.Results.Causality.SourceScopedAscent
open TruthCore.Causality.SourceScopedAscent
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Latin.Aquinas.DeEnte
  (CommonEsseIsEssenceSource ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Causality.EsseReception
  (EsseReceivedOnlyInOwnEssence NothingInReceptivePotencyToItself)
open TruthCore.Causality.ReceptionLimitation (ReceivedEsseIsLimited)
open TruthCore.Causality.Round2PerfectionPrimacy (LimitedEsseApproachesLess GreaterDegreeIsMore)
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception
  (EsseLimitedOnlyThroughReceptionReading)
open TruthCore.Causality.Q44SourceSupply (ActualEsseCauseComposes)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

theorem restrictAscent {B P R : Type} (p : Profile B P R)
    (MoreIn : R → B → B → Prop)
    (h : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse) :
    IdentityCauseAscent p MoreIn := by
  intro c x _ _ _ hne hc
  exact h c x hne hc

/-- Absolute nonlimitation is obtained through the explicit reception premises,
not through freedom from this one target's capacity. All comparisons are at esse. -/
theorem identityAscentFromReception {B P R D : Type} [Preorder D]
    (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (Received : B → P → Prop) (Potency : P → P → Prop)
    (Limited : B → Prop) (degree : B → D)
    (hOwn : EsseReceivedOnlyInOwnEssence p.essenceOf Received)
    (hPotency : ReceiverInPotencyToReceivedEsseReading p.esseOf Received Potency)
    (hNotSelf : NothingInReceptivePotencyToItself Potency)
    (hReceived : CausedEsseIsReceived p.CausesIn p.esse Received)
    (hLimited : ReceivedEsseIsLimited Limited Received)
    (hOnly : EsseLimitedOnlyThroughReceptionReading Limited Received)
    (hLess : LimitedEsseApproachesLess Limited degree)
    (hMore : GreaterDegreeIsMore (fun (_ : Unit) => MoreIn p.esse)
      (fun x (_ : Unit) => degree x)) :
    IdentityCauseAscent p MoreIn := by
  intro c x _ _ hid hne hc
  have hNoRec : ∀ z, ¬ Received c z := by
    intro z hz
    have hp := hPotency c z hz
    rw [hOwn c z hz, ← hid] at hp
    exact hNotSelf _ hp
  have hNoLim : ¬ Limited c := by
    intro hl
    obtain ⟨z, hz⟩ := hOnly c hl
    exact hNoRec z hz
  obtain ⟨z, hz⟩ := hReceived c x hne hc
  exact hMore () c x (hLess x c (hLimited x z hz) hNoLim)

/-- Consume the weaker source-scoped input in the accepted same-witness route. -/
theorem maximalCausesFromIdentityAscent {B P R : Type} (p : Profile B P R)
    (MoreIn : R → B → B → Prop)
    (hSource : CommonEsseIsEssenceSource p)
    (hCompose : ActualEsseCauseComposes p)
    (hAscent : IdentityCauseAscent p MoreIn)
    (hEM : ExcludedMiddle) :
    MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse := by
  obtain ⟨n, hn, hid, _, hPaths⟩ := hSource
  have hScope : ∀ x, p.InAct x p.esse → x ≠ n → p.CausesIn n x p.esse := by
    intro x hx hxn
    exact TruthCore.Results.Causality.Q44SourceSupply.causeOfChain p hCompose hn
      (hPaths x hx hxn)
  intro m hm
  have hmn : m = n := by
    rcases hEM (m = n) with heq | hne
    · exact heq
    · exact (hm.2 n (hAscent n m hn hm.1 hid (fun h => hne h.symm)
        (hScope m hm.1 hne))).elim
  subst m
  intro x hxn hx
  exact hScope x hx hxn

private theorem crossReceptionCore : RelativeStepForcesCrossReception := by
  intro B R InAct ReceivedIn LimitedBy MoreIn hExceed hOnly hAsym hEM a b r ha hb haa hbb
  rcases hEM (ReceivedIn a r b) with hab | hab
  · exact Or.inl hab
  rcases hEM (ReceivedIn b r a) with hba | hba
  · exact Or.inr hba
  have hna : ¬ LimitedBy a r b := fun h => hab (hOnly a r b h)
  have hnb : ¬ LimitedBy b r a := fun h => hba (hOnly b r a h)
  exact (hAsym r a b (hExceed a b r ha hbb hna)
    (hExceed b a r hb haa hnb)).elim

theorem crossReception : RelativeStepAudit := by
  constructor
  · exact crossReceptionCore
  intro B P R p Received LimitedBy MoreIn hOwn hExceed hOnly hAsym hEM a b ha hb haa hbb
  have hPair := crossReceptionCore B Unit
    (fun x _ => p.InAct x p.esse) (fun x _ y => Received x (p.essenceOf y))
    (fun x _ y => LimitedBy x y) (fun _ => MoreIn p.esse)
    hExceed hOnly hAsym hEM a b () ha hb haa hbb
  rcases hPair with hab | hba
  · exact (hOwn a _ hab).symm
  · exact hOwn b _ hba

end TruthCore.Results.Causality.SourceScopedAscent
