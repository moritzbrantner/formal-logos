import TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit
import TruthCore.Results.Causality.ConcreteRootAccess.Solution
import TruthCore.Results.Causality.SupplierAuditCertificates.Solution

/-! Convert finite audit certificates to root access in the actual esse order. -/

namespace TruthCore.Results.Aquinas.DeEnte.FiniteEsseRootAudit

open TruthCore.Causality.ConcreteRootAccess (RootAccess)
open TruthCore.Causality.SupplierAudit (auditFrameReflexive)
open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Results.Causality.ConcreteRootAccess (accessOfClosed closedOfAccess)
open TruthCore.Results.Causality.SupplierAuditCertificates (positiveCertificate)

/-- Each audit is factive at the actual supply relation. Finite root access
then places the root in every supplier-closed collection containing its target. -/
theorem closedOfFiniteRootAudits (p : Profile B P R)
    (audits : EveryActualEsseBearerHasFiniteRootAudit p) :
    ClosedActualEsseCollectionsRooted p := by
  sorry

/-- Closed-collection rootedness with explicit excluded middle yields the
structural availability of an audit for each actual bearer. -/
theorem finiteRootAuditsOfClosed (p : Profile B P R)
    (closed : ClosedActualEsseCollectionsRooted p) (em : ExcludedMiddle) :
    EveryActualEsseBearerHasFiniteRootAudit p := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.FiniteEsseRootAudit
