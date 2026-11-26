module

public import TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit
public import TruthCore.Results.Causality.ConcreteRootAccess.Solution
public import TruthCore.Results.Causality.SupplierAuditCertificates.Solution

/-! Convert finite audit certificates to root access in the actual esse order. -/

@[expose] public section

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

variable {B P R : Type}

private theorem accessOfAncestor (p : Profile B P R) {r x : B}
    (actualRoot : p.InAct r p.esse)
    (ancestor : RootAncestor r x (ActualEsseCause p)) :
    RootAccess (esseCauseGraph p) () x := by
  obtain ⟨path, root⟩ := ancestor
  induction path with
  | refl =>
    exact .root ⟨⟨actualRoot, actualRoot⟩, fun c edge => root c edge.2.2⟩
  | tail _ edge access =>
    exact .step access ⟨edge.2.2.1, edge.2.2.1⟩ ⟨edge.2.1, edge.2.1, edge⟩

private theorem ancestorOfAccess (p : Profile B P R) {x : B}
    (access : RootAccess (esseCauseGraph p) () x) :
    ∃ r, p.InAct r p.esse ∧ RootAncestor r x (ActualEsseCause p) := by
  induction access with
  | @root r h =>
    exact ⟨r, h.1.1, .refl, fun c edge => h.2 c ⟨edge.2.1, edge.2.1, edge⟩⟩
  | step _ _ edge ih =>
    obtain ⟨r, actualRoot, path, root⟩ := ih
    exact ⟨r, actualRoot, path.tail edge.2.2, root⟩

/-- Each audit is factive at the actual supply relation. Finite root access
then places the root in every supplier-closed collection containing its target. -/
theorem closedOfFiniteRootAudits (p : Profile B P R)
    (audits : EveryActualEsseBearerHasFiniteRootAudit p) :
    ClosedActualEsseCollectionsRooted p := by
  apply closedOfAccess (esseCauseGraph p) ()
  intro x actual
  obtain ⟨r, actualRoot, audited, _, knows⟩ := audits x actual.1
  have ancestor := knows (ActualEsseCause p) (auditFrameReflexive id audited (ActualEsseCause p))
  exact accessOfAncestor p actualRoot ancestor

/-- Closed-collection rootedness with explicit excluded middle yields the
structural availability of an audit for each actual bearer. -/
theorem finiteRootAuditsOfClosed (p : Profile B P R)
    (closed : ClosedActualEsseCollectionsRooted p) (em : ExcludedMiddle) :
    EveryActualEsseBearerHasFiniteRootAudit p := by
  intro x actual
  have access := accessOfClosed (esseCauseGraph p) () closed em x ⟨actual, actual⟩
  obtain ⟨r, actualRoot, ancestor⟩ := ancestorOfAccess p access
  exact ⟨r, actualRoot, (positiveCertificate (ActualEsseCause p) r x).mp ancestor⟩

end TruthCore.Results.Aquinas.DeEnte.FiniteEsseRootAudit
