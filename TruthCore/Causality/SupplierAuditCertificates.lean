module

public import TruthCore.Causality.SupplierAudit

/-! Local supplier audit criteria on one fixed bearer type. -/

@[expose] public section

namespace TruthCore.Causality.SupplierAuditCertificates

open TruthCore.Causality.SupplierAudit (auditFrame HasRootIn)
open TruthCore.Logic.JustificationIntrospection (Knows)

variable {B : Type}

/-- The full finite-path predecessor cone, including the target via the empty path. -/
def predecessorCone (supplies : B → B → Prop) (target : B) : Set B :=
  {x | Relation.ReflTransGen supplies x target}

/-- This very bearer reaches the target and has no supplier in the relation. -/
def RootAncestor (root target : B) (supplies : B → B → Prop) : Prop :=
  root ∈ predecessorCone supplies target ∧ ∀ y, ¬ supplies y root

/-- A finite audit can certify that the fixed identity is a root ancestor exactly
when it is a root ancestor in the actual relation. -/
def PositiveCertificateCriterion (actual : B → B → Prop) (root target : B) : Prop :=
  RootAncestor root target actual ↔
    ∃ audited : Set B, audited.Finite ∧
      Knows (auditFrame id audited) (RootAncestor root target) actual

/-- A finite audit can exclude all root ancestors exactly when the actual cone
is finite and rootless. The cone at an alternative is computed in that alternative. -/
def NegativeCertificateCriterion (actual : B → B → Prop) (target : B) : Prop :=
  (∃ audited : Set B, audited.Finite ∧
    Knows (auditFrame id audited) (fun r => ¬ HasRootIn (predecessorCone r target) r) actual) ↔
    (predecessorCone actual target).Finite ∧ ¬ HasRootIn (predecessorCone actual target) actual

end TruthCore.Causality.SupplierAuditCertificates
