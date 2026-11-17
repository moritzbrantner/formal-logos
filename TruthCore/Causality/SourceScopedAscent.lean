module

public import TruthCore.Causality.Q44SourceSupply
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Causality.DeiFiliusUnifiedRoute

/-! A scope restriction of the existing esse-causal ascent principle. No new
causal, receiving, limiting or comparative relation is introduced. -/

@[expose] public section
namespace TruthCore.Causality.SourceScopedAscent
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

/-- OPEN: actual identity bearers exceed the actual others whose esse they cause.
The identities are represented essence/esse identities, not God identification.
No assertion about received intermediate causes is made. -/
def IdentityCauseAscent {B P R : Type} (p : Profile B P R)
    (MoreIn : R → B → B → Prop) : Prop :=
  ∀ c x, p.InAct c p.esse → p.InAct x p.esse →
    p.esseOf c = p.essenceOf c → c ≠ x → p.CausesIn c x p.esse → MoreIn p.esse c x

/-- Audit consequence, not a new metaphysical premise: the old relative law,
its limitation-to-reception bridge and asymmetric comparison force a reception
in one direction between any two actual self-limited possessors. -/
def RelativeStepForcesCrossReception : Prop :=
  ∀ (B R : Type) (InAct : B → R → Prop)
    (ReceivedIn LimitedBy : B → R → B → Prop) (MoreIn : R → B → B → Prop),
    TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited
      InAct LimitedBy MoreIn →
    TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception
      ReceivedIn LimitedBy →
    TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric MoreIn →
    TruthCore.Logic.ExcludedMiddle →
    ∀ a b r, InAct a r → InAct b r → LimitedBy a r a → LimitedBy b r b →
      ReceivedIn a r b ∨ ReceivedIn b r a

/-- Apply the same audit when a recipient-being represents its essence as the
receiving principle. It forces equality of the receiving essences of any two
actual self-limited beings; that dictionary is explicit, not a changed definition. -/
def RelativeStepForcesSharedReceivingEssence : Prop :=
  ∀ (B P R : Type) (p : Profile B P R) (Received : B → P → Prop)
    (LimitedBy : B → B → Prop) (MoreIn : R → B → B → Prop),
    TruthCore.Causality.EsseReception.EsseReceivedOnlyInOwnEssence p.essenceOf Received →
    TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited
      (fun x (_ : Unit) => p.InAct x p.esse)
      (fun x (_ : Unit) y => LimitedBy x y) (fun (_ : Unit) => MoreIn p.esse) →
    TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception
      (fun x (_ : Unit) y => Received x (p.essenceOf y))
      (fun x (_ : Unit) y => LimitedBy x y) →
    TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric
      (fun (_ : Unit) => MoreIn p.esse) →
    TruthCore.Logic.ExcludedMiddle →
    ∀ a b, p.InAct a p.esse → p.InAct b p.esse → LimitedBy a a → LimitedBy b b →
      p.essenceOf a = p.essenceOf b

/-- Two linked consequences of the same recipient-relative inference. -/
def RelativeStepAudit : Prop :=
  RelativeStepForcesCrossReception ∧ RelativeStepForcesSharedReceivingEssence

end TruthCore.Causality.SourceScopedAscent
