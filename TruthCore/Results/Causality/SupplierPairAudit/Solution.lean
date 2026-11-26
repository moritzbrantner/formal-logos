module

public import TruthCore.Results.Causality.SupplierAuditCertificates.Solution
public import TruthCore.Causality.SupplierPairAudit

/-! Exact positive root certificates from individual supplier-pair queries.
Analyst formulations, attribution deferred. -/

@[expose] public section

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
  constructor
  · intro known
    let greatest : AdmissibleRelation allowed :=
      ⟨fun y x => allowed y x ∧ ((y, x) ∈ tested → actual.val y x), fun _ _ edge => edge.1⟩
    have agreesGreatest : (pairAuditFrame allowed tested).access actual greatest :=
      fun y x testedPair =>
        ⟨fun edge => ⟨actual.property y x edge, fun _ => edge⟩, fun edge => edge.2 testedPair⟩
    have covers (y : B) (possible : allowed y root) : (y, root) ∈ tested := by
      by_contra missing
      exact (known greatest agreesGreatest).2 y ⟨possible, fun testedPair =>
        (missing testedPair).elim⟩
    let least : AdmissibleRelation allowed :=
      ⟨fun y x => actual.val y x ∧ (y, x) ∈ tested, fun y x edge => actual.property y x edge.1⟩
    have agreesLeast : (pairAuditFrame allowed tested).access actual least :=
      fun _ _ testedPair => ⟨fun edge => ⟨edge, testedPair⟩, And.left⟩
    exact ⟨covers, (known actual (fun _ _ _ => Iff.rfl)).2, (known least agreesLeast).1⟩
  · rintro ⟨covers, empty, path⟩ alternative agrees
    constructor
    · change Relation.ReflTransGen alternative.val root target
      exact Relation.ReflTransGen.mono
        (fun y x edge => (agrees y x edge.2).mp edge.1) root target path
    · intro y edge
      have testedPair := covers y (alternative.property y root edge)
      exact empty y ((agrees y root testedPair).mpr edge)

private theorem finitePathAudit {B : Type} {supplies : B → B → Prop} {root target : B}
    (path : Relation.ReflTransGen supplies root target) :
    ∃ tested : Set (B × B), tested.Finite ∧
      Relation.ReflTransGen (fun y x => supplies y x ∧ (y, x) ∈ tested) root target := by
  induction path with
  | refl => exact ⟨∅, Set.finite_empty, .refl⟩
  | @tail x t _ edge ih =>
    obtain ⟨tested, finite, observed⟩ := ih
    refine ⟨insert (x, t) tested, finite.insert (x, t), ?_⟩
    have extended : Relation.ReflTransGen
        (fun y z => supplies y z ∧ (y, z) ∈ insert (x, t) tested) root x :=
      Relation.ReflTransGen.mono
        (fun _ _ step => ⟨step.1, Set.mem_insert_of_mem (x, t) step.2⟩) root x observed
    exact extended.tail ⟨edge, Set.mem_insert (x, t) tested⟩

/-- A finite pair certificate exists exactly for an actual root ancestor with
finitely many allowed incoming suppliers at that root. -/
theorem finiteCertificate {B : Type} {allowed : B → B → Prop}
    (actual : AdmissibleRelation allowed) (root target : B) :
    FiniteCertificateCriterion actual root target := by
  constructor
  · rintro ⟨tested, finite, known⟩
    obtain ⟨covers, empty, observed⟩ := (certificateAt actual root target tested).mp known
    exact ⟨⟨Relation.ReflTransGen.mono (fun _ _ step => step.1) root target observed, empty⟩,
      (finite.image Prod.fst).subset (fun y possible => ⟨(y, root), covers y possible, rfl⟩)⟩
  · rintro ⟨⟨path, empty⟩, finiteIncoming⟩
    obtain ⟨pathPairs, finitePathPairs, observed⟩ := finitePathAudit path
    let incomingPairs := (fun y => (y, root)) '' {y | allowed y root}
    refine ⟨incomingPairs ∪ pathPairs, (finiteIncoming.image _).union finitePathPairs,
      (certificateAt actual root target _).mpr ⟨?_, empty, ?_⟩⟩
    · exact fun y possible => Or.inl ⟨y, possible, rfl⟩
    · exact Relation.ReflTransGen.mono
        (fun _ _ step => ⟨step.1, Or.inr step.2⟩) root target observed

/-- On an infinite roster with all pairs allowed, no finite pair audit
certifies a specified supplierless ancestor. -/
theorem unrestrictedInfiniteRoster {B : Type} [Infinite B]
    (actual : AdmissibleRelation (fun (_ _ : B) => True)) (root target : B) :
    ¬ ∃ tested : Set (B × B), tested.Finite ∧ CertifiesRoot actual root target tested := by
  intro certificate
  have finite := ((finiteCertificate actual root target).mp certificate).2
  exact Set.infinite_univ (by simpa using finite)

/-- On the infinite natural-number roster, one negative root query and one
positive path query suffice, although every bearer is allowed to supply the
target. The actual relation consists of the edge from zero to one. -/
theorem boundedRootMaskControl :
    ∃ actual : AdmissibleRelation (fun (y x : Nat) => y = 2 ∨ x ≠ 0),
      (∀ y x, actual.val y x ↔ y = 0 ∧ x = 1) ∧
        CertifiesRoot actual 0 1 ({(2, 0), (0, 1)} : Set (Nat × Nat)) := by
  let actual : AdmissibleRelation (fun (y x : Nat) => y = 2 ∨ x ≠ 0) :=
    ⟨fun y x => y = 0 ∧ x = 1, fun _ _ edge => Or.inr (edge.2 ▸ Nat.one_ne_zero)⟩
  refine ⟨actual, fun _ _ => Iff.rfl, (certificateAt actual _ _ _).mpr ⟨?_, ?_, ?_⟩⟩
  · rintro y (rfl | impossible)
    · exact Set.mem_insert _ _
    · exact (impossible rfl).elim
  · exact fun _ edge => Nat.one_ne_zero edge.2.symm
  · exact .single ⟨⟨rfl, rfl⟩, Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩

/-- A matching-pair certificate gives a root in the actual relation. The
complete-list theorem then supplies a finite row audit for the same two bearers. -/
theorem completeListAuditOfPairCertificate {B : Type} {allowed : B → B → Prop}
    (actual : AdmissibleRelation allowed)
    {root target : B} {tested : Set (B × B)} (cert : CertifiesRoot actual root target tested) :
    ∃ audited : Set B, audited.Finite ∧
      TruthCore.Logic.JustificationIntrospection.Knows
        (TruthCore.Causality.SupplierAudit.auditFrame id audited)
        (RootAncestor root target) actual.val := by
  exact (TruthCore.Results.Causality.SupplierAuditCertificates.positiveCertificate
    actual.val root target).mp (cert actual (fun _ _ _ => Iff.rfl))

end TruthCore.Results.Causality.SupplierPairAudit
