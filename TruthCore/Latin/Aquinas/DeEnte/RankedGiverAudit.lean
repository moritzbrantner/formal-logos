module

public import TruthCore.Causality.SupplierPairAudit
public import TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.RankedGiverAudit

open TruthCore.Causality.SupplierPairAudit (AdmissibleRelation CertifiesRoot)
open TruthCore.Latin.Aquinas.SummaTheologiae
open PrimaPars.Question3.Article4 (Profile)

variable {B P R : Type}

/-- The bearer identities, actuality, and comparative at esse are held fixed
throughout the audit. Only a distinct actual higher bearer may supply esse. -/
def eligible (p : Profile B P R) (MoreIn : R → B → B → Prop) (y x : B) : Prop :=
  y ≠ x ∧ p.InAct y p.esse ∧ p.InAct x p.esse ∧ MoreIn p.esse y x

/-- A self comparison uses no observations. Every other comparison checks
only the proposed direct gift from the same source to its recipient. -/
def giftQuestion (s x : B) : Set (B × B) :=
  {pair | pair = (s, x) ∧ s ≠ x}

/-- One fixed actual maximum has a certificate for every actual recipient.
The actual relation must respect the fixed ranking. Each alternative may use
any subset of the eligible edges that matches the queried answers. -/
def RankedGiverCertificates (p : Profile B P R) (MoreIn : R → B → B → Prop) : Prop :=
  ∃ valid : ∀ y x, ActualEsseCause p y x → eligible p MoreIn y x,
    ∃ s, IsMaximumIn p.InAct MoreIn p.esse s ∧ ∀ x, p.InAct x p.esse →
      CertifiesRoot (⟨ActualEsseCause p, valid⟩ : AdmissibleRelation (eligible p MoreIn))
        s x (giftQuestion s x)

end TruthCore.Latin.Aquinas.DeEnte.RankedGiverAudit
