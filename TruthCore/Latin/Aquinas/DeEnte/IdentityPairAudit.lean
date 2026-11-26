module

public import TruthCore.Causality.SupplierPairAudit
public import TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.IdentityPairAudit

open TruthCore.Causality.SupplierPairAudit (AdmissibleRelation CertifiesRoot)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile DistinctEsseAt)

variable {B P R : Type}

/-- A possible gift goes from a distinct actual donor to an actual recipient
whose represented esse differs from its essence. The use of this restriction
for actual or possible gifts requires the underived-identity premise. -/
def eligible (p : Profile B P R) (y x : B) : Prop :=
  y ≠ x ∧ p.InAct y p.esse ∧ DistinctEsseAt p x

/-- The particular identity ancestor and the finite queries may vary with the
recipient. The entirety of the eligible class is fixed across queries. -/
def FiniteIdentityPairAudits (p : Profile B P R) : Prop :=
  ∃ valid : ∀ y x, ActualEsseCause p y x → eligible p y x,
    ∀ x, p.InAct x p.esse → ∃ s, p.InAct s p.esse ∧ p.esseOf s = p.essenceOf s ∧
      ∃ tested : Set (B × B), tested.Finite ∧
        CertifiesRoot (⟨ActualEsseCause p, valid⟩ : AdmissibleRelation (eligible p)) s x tested

end TruthCore.Latin.Aquinas.DeEnte.IdentityPairAudit
