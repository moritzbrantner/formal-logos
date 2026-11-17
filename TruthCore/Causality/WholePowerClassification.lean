module

public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Causality.ReceptionLimitation
public import TruthCore.Causality.DeiFiliusUnifiedRoute
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder

/-! A consequence of combining the retained whole-power and strict-purity
interfaces on one OwnBeing witness. No no-defect clause, mode alignment,
source existence or degree comparison is supplied by this audit. -/

@[expose] public section
namespace TruthCore.Causality.WholePowerClassification
open TruthCore.Causality.WholePowerPerfection
open TruthCore.Causality.ReceptionLimitation

def ScopeCost : Prop := ∀ (B D : Type)
    (OwnBeing Recipient : B → Prop) (Has : B → D → Prop) (Pure OfBeing : D → Prop),
    OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing →
    PurePerfectionsPertainToBeing Pure OfBeing →
    OwnBeingIsNoRecipient OwnBeing Recipient →
    NonRecipientDeterminationsArePure Recipient Has Pure →
    ∀ n, OwnBeing n → ∀ d, OfBeing d ↔ Pure d

/-- The positive whole-power clause is preserved when real possession is
extended. It therefore does not encode the separate exclusion of defects. -/
def PositiveClauseExtensionStable : Prop := ∀ (B D : Type)
    (OwnBeing : B → Prop) (Has Has' : B → D → Prop) (OfBeing : D → Prop),
    OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing →
    (∀ x d, Has x d → Has' x d) →
    OwnBeingLacksNoPerfectionOfBeing OwnBeing Has' OfBeing

def ClassificationAudit : Prop := ScopeCost ∧ PositiveClauseExtensionStable

/-- A real subsistence-mode contrast for a supplied actual universal esse source.
The source's OwnBeing is an explicit premise, not a represented-equality
unfolding; receipt, limitation and infinity interfaces remain separate. -/
def ModeAudit : Prop := ∀ (B P R : Type)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (OwnBeing : B → Prop) (Received : B → P → Prop)
    (Limited Infinite : B → Prop) (n : B),
    p.InAct n p.esse → OwnBeing n →
    TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus p.InAct p.CausesIn p.esse n →
    TruthCore.Causality.DeiFiliusUnifiedRoute.CausedEsseIsReceived p.CausesIn p.esse Received →
    ReceivedEsseIsLimited Limited Received →
    OwnBeingIsInfinite OwnBeing Infinite → InfiniteEsseIsUnlimited Limited Infinite →
    p.InAct n p.esse ∧ OwnBeing n ∧ Infinite n ∧ ¬ Limited n ∧
      ∀ x, p.InAct x p.esse → x ≠ n → Limited x ∧ ¬ Infinite x ∧ ¬ OwnBeing x

end TruthCore.Causality.WholePowerClassification
