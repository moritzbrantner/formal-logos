import TruthCore.Causality.SupplierAuditCertificates
import Mathlib.Data.Fintype.Card

/-! Sharp finite certificates for local supplier ancestry. Analyst formulations,
attribution deferred. -/

namespace TruthCore.Results.Causality.SupplierAuditCertificates

open TruthCore.Causality.SupplierAudit (auditFrame auditFrameReflexive HasRootIn)
open TruthCore.Causality.SupplierAuditCertificates
open TruthCore.Logic.JustificationIntrospection (Knows)

/-- An audit certifies the same root identity exactly when it reads an empty
incoming list there and records every edge along some actual path to the target. -/
theorem positiveCertificateAt {B : Type} (actual : B → B → Prop) (root target : B)
    (audited : Set B) :
    Knows (auditFrame id audited) (RootAncestor root target) actual ↔
      root ∈ audited ∧ (∀ y, ¬ actual y root) ∧
        Relation.ReflTransGen (fun y x => actual y x ∧ x ∈ audited) root target := by
  sorry

/-- An actual fixed root ancestor has a finite certificate, by auditing the root
and the recipients on one path. The actual relation itself tests the converse. -/
theorem positiveCertificate {B : Type} (actual : B → B → Prop) (root target : B) :
    PositiveCertificateCriterion actual root target := by
  sorry

/-- Excluding every root ancestor requires auditing the entire actual cone.
Each unaudited ancestor can be made supplierless while remaining an ancestor. -/
theorem negativeCertificateAt {B : Type} (actual : B → B → Prop) (target : B)
    (audited : Set B) :
    Knows (auditFrame id audited) (fun r => ¬ HasRootIn (predecessorCone r target) r) actual ↔
      predecessorCone actual target ⊆ audited ∧
        ¬ HasRootIn (predecessorCone actual target) actual := by
  sorry

/-- A finite certificate excluding every root ancestor exists exactly for a
finite actual cone whose members all have suppliers. -/
theorem negativeCertificate {B : Type} (actual : B → B → Prop) (target : B) :
    NegativeCertificateCriterion actual target := by
  sorry

/-- If there is no directed cycle in the actual cone, no finite audit can
certify that it has no root. -/
theorem acyclicConeCannotHaveNegativeCertificate {B : Type} (actual : B → B → Prop)
    (target : B) (acyclic : ∀ x ∈ predecessorCone actual target, ¬ Relation.TransGen actual x x) :
    ¬ ∃ audited : Set B, audited.Finite ∧
      Knows (auditFrame id audited) (fun r => ¬ HasRootIn (predecessorCone r target) r) actual := by
  sorry

end TruthCore.Results.Causality.SupplierAuditCertificates
