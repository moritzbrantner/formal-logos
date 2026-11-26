module

public import TruthCore.Causality.SupplierAuditCertificates
public import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource

/-! Finite root certificates on the fixed actual esse-cause relation. -/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit

open TruthCore.Causality.SupplierAudit (auditFrame)
open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Logic.JustificationIntrospection (Knows)

/-- For each actual bearer, a particular actual root and a finite set of
complete incoming lists suffice to certify its root status and its finite
path to that bearer across all agreeing relations on the fixed roster.
This expresses availability of a certificate. -/
def EveryActualEsseBearerHasFiniteRootAudit {B P R : Type} (p : Profile B P R) : Prop :=
  ∀ x, p.InAct x p.esse →
    ∃ r, p.InAct r p.esse ∧
      ∃ audited : Set B, audited.Finite ∧
        Knows (auditFrame id audited) (RootAncestor r x) (ActualEsseCause p)

end TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit
