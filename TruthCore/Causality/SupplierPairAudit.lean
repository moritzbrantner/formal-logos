module

public import TruthCore.Causality.SupplierAuditCertificates

/-! Exact certificates from yes/no queries about individual supplier pairs. -/

@[expose] public section

namespace TruthCore.Causality.SupplierPairAudit

open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Logic.JustificationIntrospection (Knows)
open TruthCore.Modal (Frame)

variable {B : Type}

/-- An admissible supplier relation uses only the independently allowed pairs.
The class of worlds includes every subrelation of the allowed relation. -/
def AdmissibleRelation (allowed : B → B → Prop) :=
  {supplies : B → B → Prop // ∀ y x, supplies y x → allowed y x}

/-- The audit records a yes or no answer for each tested ordered pair
`(supplier, recipient)`. An alternative agrees on exactly those pairs. -/
def pairAuditFrame (allowed : B → B → Prop) (tested : Set (B × B)) :
    Frame (AdmissibleRelation allowed) where
  access actual alternative :=
    ∀ y x, (y, x) ∈ tested → (actual.val y x ↔ alternative.val y x)

/-- Every matching admissible relation makes the fixed bearer a supplierless
ancestor of the fixed target. -/
def CertifiesRoot {allowed : B → B → Prop} (actual : AdmissibleRelation allowed)
    (root target : B) (tested : Set (B × B)) : Prop :=
  Knows (pairAuditFrame allowed tested) (fun alternative => RootAncestor root target alternative.val)
    actual

/-- The local finiteness condition for certification by finitely many queries.
Only the allowed incoming suppliers at the specified root must form a finite set. -/
def FiniteCertificateCriterion {allowed : B → B → Prop}
    (actual : AdmissibleRelation allowed) (root target : B) : Prop :=
  (∃ tested : Set (B × B), tested.Finite ∧ CertifiesRoot actual root target tested) ↔
    RootAncestor root target actual.val ∧ ({y | allowed y root} : Set B).Finite

end TruthCore.Causality.SupplierPairAudit
