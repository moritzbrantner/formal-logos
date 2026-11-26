import TruthCore.Causality.SupplierPairAudit

/-! Exact positive root certificates from individual supplier-pair queries.
Analyst formulations, attribution deferred. -/

namespace TruthCore.Results.Causality.SupplierPairAudit

open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Causality.SupplierPairAudit

/-- A pair audit certifies the stated root ancestor exactly when it tests all
allowed incoming pairs at the root, finds no incoming edge, and observes every
edge on some path from the root to the target. The zero-edge path is allowed. -/
theorem certificateAt {B : Type} {allowed : B → B → Prop}
    (actual : AdmissibleRelation allowed) (root target : B)
    (tested : Set (B × B)) :
    CertifiesRoot actual root target tested ↔
      (∀ y, allowed y root → (y, root) ∈ tested) ∧
      (∀ y, ¬ actual.val y root) ∧
      Relation.ReflTransGen (fun y x => actual.val y x ∧ (y, x) ∈ tested) root target := by
  sorry

/-- A finite pair certificate exists exactly for an actual root ancestor with
finitely many allowed incoming suppliers at that root. -/
theorem finiteCertificate {B : Type} {allowed : B → B → Prop}
    (actual : AdmissibleRelation allowed) (root target : B) :
    FiniteCertificateCriterion actual root target := by
  sorry

/-- On an infinite roster with all pairs allowed, no finite pair audit
certifies a specified supplierless ancestor. -/
theorem unrestrictedInfiniteRoster {B : Type} [Infinite B]
    (actual : AdmissibleRelation (fun (_ _ : B) => True)) (root target : B) :
    ¬ ∃ tested : Set (B × B), tested.Finite ∧ CertifiesRoot actual root target tested := by
  sorry

/-- On the infinite natural-number roster, one negative root query and one
positive path query suffice, although every bearer is allowed to supply the
target. The actual relation consists of the edge from zero to one. -/
theorem boundedRootMaskControl :
    ∃ actual : AdmissibleRelation (fun (y x : Nat) => y = 2 ∨ x ≠ 0),
      (∀ y x, actual.val y x ↔ y = 0 ∧ x = 1) ∧
        CertifiesRoot actual 0 1 ({(2, 0), (0, 1)} : Set (Nat × Nat)) := by
  sorry

/-- A matching-pair certificate gives a root in the actual relation. The
complete-list theorem then supplies a finite row audit for the same two bearers. -/
theorem completeListAuditOfPairCertificate {B : Type} {allowed : B → B → Prop}
    (actual : AdmissibleRelation allowed)
    {root target : B} {tested : Set (B × B)} (cert : CertifiesRoot actual root target tested) :
    ∃ audited : Set B, audited.Finite ∧
      TruthCore.Logic.JustificationIntrospection.Knows
        (TruthCore.Causality.SupplierAudit.auditFrame id audited)
        (RootAncestor root target) actual.val := by
  sorry

end TruthCore.Results.Causality.SupplierPairAudit
