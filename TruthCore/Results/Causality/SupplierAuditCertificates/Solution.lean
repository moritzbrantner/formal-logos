module

public import TruthCore.Causality.SupplierAuditCertificates
public import Mathlib.Data.Fintype.Card

/-! Sharp finite certificates for local supplier ancestry. Analyst formulations,
attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Causality.SupplierAuditCertificates

open TruthCore.Causality.SupplierAudit (auditFrame auditFrameReflexive HasRootIn)
open TruthCore.Causality.SupplierAuditCertificates
open TruthCore.Logic.JustificationIntrospection (Knows)

private theorem transferRootAncestor {B : Type} {actual alternative : B → B → Prop}
    {root target : B} {audited : Set B}
    (agreement : (auditFrame id audited).access actual alternative)
    (rootAudited : root ∈ audited) (rootEmpty : ∀ y, ¬ actual y root)
    (path : Relation.ReflTransGen (fun y x => actual y x ∧ x ∈ audited) root target) :
    RootAncestor root target alternative := by
  refine ⟨?_, fun y edge => rootEmpty y ((agreement root rootAudited y).mpr edge)⟩
  change Relation.ReflTransGen alternative root target
  exact Relation.ReflTransGen.mono
    (fun y x edge => (agreement x edge.2 y).mp edge.1) root target path

/-- An audit certifies the same root identity exactly when it reads an empty
incoming list there and records every edge along some actual path to the target. -/
theorem positiveCertificateAt {B : Type} (actual : B → B → Prop) (root target : B)
    (audited : Set B) :
    Knows (auditFrame id audited) (RootAncestor root target) actual ↔
      root ∈ audited ∧ (∀ y, ¬ actual y root) ∧
        Relation.ReflTransGen (fun y x => actual y x ∧ x ∈ audited) root target := by
  constructor
  · intro knows
    have rootAudited : root ∈ audited := by
      by_contra notAudited
      let alternative (y x : B) := actual y x ∨ (x = root ∧ y = root)
      have agreement : (auditFrame id audited).access actual alternative := by
        intro x hx y
        exact ⟨Or.inl, fun edge => edge.elim id fun h => (notAudited (h.1 ▸ hx)).elim⟩
      exact (knows alternative agreement).2 root (.inr ⟨rfl, rfl⟩)
    have rootEmpty := (knows actual (auditFrameReflexive id audited actual)).2
    have listsAgree :
        (auditFrame id audited).access actual (fun y x => actual y x ∧ x ∈ audited) :=
      fun _ hx _ => ⟨fun edge => ⟨edge, hx⟩, And.left⟩
    exact ⟨rootAudited, rootEmpty, (knows _ listsAgree).1⟩
  · rintro ⟨rootAudited, rootEmpty, path⟩ alternative agrees
    exact transferRootAncestor agrees rootAudited rootEmpty path

private theorem finitePathAudit {B : Type} {actual : B → B → Prop} {root target : B}
    (path : Relation.ReflTransGen actual root target) :
    ∃ audited : Set B, audited.Finite ∧ root ∈ audited ∧
      Relation.ReflTransGen (fun y x => actual y x ∧ x ∈ audited) root target := by
  induction path with
  | refl => exact ⟨{root}, Set.finite_singleton root, Set.mem_singleton root, .refl⟩
  | @tail x t _ edge ih =>
    obtain ⟨audited, finite, rootAudited, observedPath⟩ := ih
    refine ⟨insert t audited, finite.insert t, Set.mem_insert_of_mem t rootAudited, ?_⟩
    have extendedAudit : Relation.ReflTransGen (fun y x => actual y x ∧ x ∈ insert t audited)
        root x :=
      Relation.ReflTransGen.mono
        (fun _ _ step => ⟨step.1, Set.mem_insert_of_mem t step.2⟩) root x observedPath
    exact extendedAudit.tail ⟨edge, Set.mem_insert t audited⟩

/-- An actual fixed root ancestor has a finite certificate, by auditing the root
and the recipients on one path. The actual relation itself tests the converse. -/
theorem positiveCertificate {B : Type} (actual : B → B → Prop) (root target : B) :
    PositiveCertificateCriterion actual root target := by
  constructor
  · rintro ⟨path, rootEmpty⟩
    obtain ⟨audited, finite, rootAudited, observedPath⟩ := finitePathAudit path
    exact ⟨audited, finite, fun _ agrees =>
      transferRootAncestor agrees rootAudited rootEmpty observedPath⟩
  · rintro ⟨audited, _, knows⟩
    exact knows actual (auditFrameReflexive id audited actual)

private theorem pathAfterDeletingIncoming {B : Type} {actual : B → B → Prop}
    {root target : B} (path : Relation.ReflTransGen actual root target) :
    Relation.ReflTransGen (fun y x => actual y x ∧ x ≠ root) root target := by
  induction path with
  | refl => exact .refl
  | @tail _ x _ edge ih =>
    by_cases returnsToRoot : x = root
    · subst x
      exact .refl
    · exact ih.tail ⟨edge, returnsToRoot⟩

/-- Excluding every root ancestor requires auditing the entire actual cone.
Each unaudited ancestor can be made supplierless while remaining an ancestor. -/
theorem negativeCertificateAt {B : Type} (actual : B → B → Prop) (target : B)
    (audited : Set B) :
    Knows (auditFrame id audited) (fun r => ¬ HasRootIn (predecessorCone r target) r) actual ↔
      predecessorCone actual target ⊆ audited ∧
        ¬ HasRootIn (predecessorCone actual target) actual := by
  constructor
  · intro knows
    refine ⟨?_, knows actual (auditFrameReflexive id audited actual)⟩
    intro root reaches
    by_contra notAudited
    let alternative (y x : B) := actual y x ∧ x ≠ root
    have agrees : (auditFrame id audited).access actual alternative := by
      intro x hx y
      exact ⟨fun edge => ⟨edge, fun h => notAudited (h ▸ hx)⟩, And.left⟩
    exact knows alternative agrees ⟨root, pathAfterDeletingIncoming reaches, fun _ edge =>
      edge.2 rfl⟩
  · rintro ⟨covers, noRoot⟩ alternative agrees ⟨root, reaches, rootEmpty⟩
    have actualPath {x : B} (path : Relation.ReflTransGen alternative x target) :
        Relation.ReflTransGen actual x target := by
      induction path using Relation.ReflTransGen.head_induction_on with
      | refl => exact .refl
      | @head x next edge _ ih => exact ih.head ((agrees next (covers ih) x).mpr edge)
    have rootReaches := actualPath reaches
    exact noRoot ⟨root, rootReaches, fun y edge =>
      rootEmpty y ((agrees root (covers rootReaches) y).mp edge)⟩

/-- A finite certificate excluding every root ancestor exists exactly for a
finite actual cone whose members all have suppliers. -/
theorem negativeCertificate {B : Type} (actual : B → B → Prop) (target : B) :
    NegativeCertificateCriterion actual target := by
  constructor
  · rintro ⟨audited, finite, knows⟩
    obtain ⟨covers, noRoot⟩ := (negativeCertificateAt actual target audited).mp knows
    exact ⟨finite.subset covers, noRoot⟩
  · rintro ⟨finite, noRoot⟩
    exact ⟨predecessorCone actual target, finite,
      (negativeCertificateAt actual target _).mpr ⟨Set.Subset.rfl, noRoot⟩⟩

/-- If there is no directed cycle in the actual cone, no finite audit can
certify that it has no root. -/
theorem acyclicConeCannotHaveNegativeCertificate {B : Type} (actual : B → B → Prop)
    (target : B) (acyclic : ∀ x ∈ predecessorCone actual target, ¬ Relation.TransGen actual x x) :
    ¬ ∃ audited : Set B, audited.Finite ∧
      Knows (auditFrame id audited) (fun r => ¬ HasRootIn (predecessorCone r target) r) actual := by
  intro certificate
  obtain ⟨finite, noRoot⟩ := (negativeCertificate actual target).mp certificate
  let Cone := ↥(predecessorCone actual target)
  let precedes (x y : Cone) := Relation.TransGen actual x.val y.val
  have : Finite Cone := finite
  have : IsTrans Cone precedes := ⟨fun _ _ _ first second => first.trans second⟩
  have : Std.Irrefl precedes := ⟨fun x => acyclic x.val x.property⟩
  have founded := Finite.wellFounded_of_trans_of_irrefl precedes
  have inhabitedCone : (Set.univ : Set Cone).Nonempty := ⟨⟨target, .refl⟩, Set.mem_univ _⟩
  obtain ⟨root, _, minimal⟩ := founded.has_min Set.univ inhabitedCone
  refine noRoot ⟨root.val, root.property, fun y edge => ?_⟩
  have reaches : Relation.ReflTransGen actual root.val target := root.property
  exact minimal ⟨y, reaches.head edge⟩ (Set.mem_univ _) (.single edge)

end TruthCore.Results.Causality.SupplierAuditCertificates
