module

public import TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived

/-! A control comparing represented essence values with identity-bearer tokens. -/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.IdentitySupplierSingleton

open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
open TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit (EveryActualEsseBearerHasFiniteRootAudit)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (DistinctEsseAt Profile)

/-- One successor relation supplies an infinite ancestry to the distinct-esse
recipient at zero. Every actual identity bearer has the same represented
essence value, and no actual identity bearer lies on a cycle. This profile
supplies identity ancestry to every distinct recipient without a finite root
audit or common source. The singleton concerns values of the profile's
`essenceOf` field. -/
def SingletonEssenceValueWithInfiniteIdentitySuppliers : Prop :=
  ∃ p : Profile Nat Bool Unit,
    (∀ x, p.InAct x p.esse) ∧ DistinctEsseAt p 0 ∧
    (∀ c x, ActualEsseCause p c x ↔ c = x + 1) ∧
    (∃ e : Bool, { v | ∃ x, p.InAct x p.esse ∧ p.esseOf x = p.essenceOf x ∧
      p.essenceOf x = v } = {e}) ∧
    (actualIdentityAncestors p 0).Infinite ∧ ActualIdentityAncestryAcyclic p ∧
    EveryDistinctEsseHasEsseIsEssenceSource p ∧
    ¬ EveryActualEsseBearerHasFiniteRootAudit p ∧ ¬ CommonEsseIsEssenceSource p

end TruthCore.Latin.Aquinas.DeEnte.IdentitySupplierSingleton
