module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.Lemmas
public import TruthCore.Logic.JustificationIntrospection

/-! Finite observations of supplier chains and a sufficient condition on a closed finite roster. -/

@[expose] public section

namespace TruthCore.Causality.SupplierAudit

open TruthCore.Modal
open TruthCore.Logic.JustificationIntrospection (Knows)

def endless (y x : Nat) := y = x + 1

def sourced (n y x : Nat) := (x < n ∧ y = x + 1) ∨ (n < x ∧ y = n)

theorem sameLists (n x y : Nat) (seen : x < n) :
    sourced n y x ↔ endless y x := by unfold sourced endless; omega

theorem endlessBorrower (x : Nat) : ∃ y, endless y x := ⟨x + 1, rfl⟩

theorem oneRoot (n x : Nat) : (∀ y, ¬ sourced n y x) ↔ x = n := by
  constructor
  · intro h
    by_cases lt : x < n
    · exact False.elim (h (x + 1) (Or.inl ⟨lt, rfl⟩))
    · by_contra ne
      exact h n (Or.inr ⟨by omega, rfl⟩)
  · rintro rfl y
    unfold sourced
    omega

-- Integer labels permit infinite descent on the full roster.
theorem finiteAudit {B : Type} (S : Set B) (r : B → B → Prop) (level : B → Int)
    (finite : S.Finite) (present : S.Nonempty)
    (closed : ∀ x ∈ S, ∀ y, r y x → y ∈ S)
    (drop : ∀ x ∈ S, ∀ y, r y x → level y < level x) :
    ∃ x ∈ S, ∀ y, ¬ r y x := by
  obtain ⟨x, hx, least⟩ := S.exists_min_image level finite present
  exact ⟨x, hx, fun y hy => (not_lt_of_ge (least y (closed x hx y hy))) (drop x hx y hy)⟩

/-- Worlds agree on exactly the evidence recorded by the audit: the full
incoming supplier list at every audited recipient, with fixed bearer identities. -/
def auditFrame {W B : Type} (supplies : W → B → B → Prop) (audited : Set B) :
    Frame W where
  access w v := ∀ x ∈ audited, ∀ y, supplies w y x ↔ supplies v y x

theorem auditFrameReflexive {W B : Type} (supplies : W → B → B → Prop)
    (audited : Set B) : Reflexive (auditFrame supplies audited) := by
  intro w x hx y
  exact Iff.rfl

/-- Some member of the indicated collection has no supplier anywhere in the
selected relation. Closure of a roster is a separate hypothesis. -/
def HasRootIn {B : Type} (S : Set B) (supplies : B → B → Prop) : Prop :=
  ∃ x ∈ S, ∀ y, ¬ supplies y x

/-- The sourced model's sole root is an ancestor of each recipient, counting
the zero-edge path from the root to itself. -/
theorem sourcedReaches (n x : Nat) : Relation.ReflTransGen (sourced n) n x := by
  by_cases before : x < n
  · exact (sourcedReaches n (x + 1)).tail (Or.inl ⟨before, rfl⟩)
  · by_cases equal : x = n
    · subst x
      exact .refl
    · exact .single (Or.inr ⟨by omega, rfl⟩)
termination_by n - x
decreasing_by omega

/-- The same populated Nat roster admits both completions at every finite
audit, including non-prefix audits. -/
theorem sameFiniteLists (audited : Set Nat) (finite : audited.Finite) :
    ∃ n, (∀ x ∈ audited, x < n) ∧ (auditFrame id audited).access endless (sourced n) := by
  obtain ⟨bound, upper⟩ := finite.bddAbove
  have below x (hx : x ∈ audited) : x < bound + 1 := Nat.lt_succ_of_le (upper hx)
  exact ⟨bound + 1, below, fun x hx y => (sameLists (bound + 1) x y (below x hx)).symm⟩

/-- Complete incoming lists with the endless record decide neither root verdict.
This holds for the whole roster and for the predecessor cone of any traced
bearer. The candidate worlds in this model range over all supplier assignments. -/
theorem finiteAuditRootUndecided (audited : Set Nat) (finite : audited.Finite)
    (actual : Nat → Nat → Prop) (record : (auditFrame id audited).access actual endless) :
    (¬ Knows (auditFrame id audited) (HasRootIn Set.univ) actual ∧
      ¬ Knows (auditFrame id audited) (fun r => ¬ HasRootIn Set.univ r) actual) ∧
    ∀ traced,
      (¬ Knows (auditFrame id audited)
        (fun r => HasRootIn {x | Relation.ReflTransGen r x traced} r) actual) ∧
      (¬ Knows (auditFrame id audited)
        (fun r => ¬ HasRootIn {x | Relation.ReflTransGen r x traced} r) actual) := by
  obtain ⟨n, _, agrees⟩ := sameFiniteLists audited finite
  have seesSourced : (auditFrame id audited).access actual (sourced n) :=
    fun x hx y => (record x hx y).trans (agrees x hx y)
  have noEndlessRoot (S : Set Nat) : ¬ HasRootIn S endless := by
    rintro ⟨x, _, unreceived⟩
    obtain ⟨y, supplies⟩ := endlessBorrower x
    exact unreceived y supplies
  have rootAtN := (oneRoot n n).mpr rfl
  refine ⟨⟨?_, ?_⟩, fun traced => ⟨?_, ?_⟩⟩
  · exact fun knows => noEndlessRoot Set.univ (knows endless record)
  · exact fun knows => knows (sourced n) seesSourced ⟨n, Set.mem_univ _, rootAtN⟩
  · exact fun knows => noEndlessRoot _ (knows endless record)
  · exact fun knows => knows (sourced n) seesSourced ⟨n, sourcedReaches n traced, rootAtN⟩

/-- Each alternative must have a genuinely finite nonempty supplier-closed
collection and a strict integer ranking toward the suppliers. The collection
can select a cone or the whole roster. Its root and ranking can vary by world. -/
theorem knowsRootFromFiniteRank {W B : Type} (F : Frame W) (actual : W)
    (supplies : W → B → B → Prop) (S : W → Set B)
    (certificate : ∀ v, F.access actual v →
      (S v).Finite ∧ (S v).Nonempty ∧
        (∀ x ∈ S v, ∀ y, supplies v y x → y ∈ S v) ∧
        ∃ level : B → Int, ∀ x ∈ S v, ∀ y, supplies v y x → level y < level x) :
    Knows F (fun v => HasRootIn (S v) (supplies v)) actual := by
  intro v access
  obtain ⟨finite, present, closed, level, drop⟩ := certificate v access
  exact finiteAudit (S v) (supplies v) level finite present closed drop

/-- A known existence result in a fixed audited roster yields a known particular
root. Factivity supplies a root at the actual world, whose empty incoming list
is then shared by every alternative. -/
theorem knownRootFromAuditedRoster {W B : Type} (actual : W)
    (supplies : W → B → B → Prop) (audited S : Set B) (covered : S ⊆ audited)
    (known : Knows (auditFrame supplies audited) (fun v => HasRootIn S (supplies v)) actual) :
    ∃ x ∈ S, Knows (auditFrame supplies audited) (fun v => ∀ y, ¬ supplies v y x) actual := by
  have actualRoot := axiomT_valid (auditFrame supplies audited)
    (auditFrameReflexive supplies audited) (Formula.atom ())
    (fun v (_ : Unit) => HasRootIn S (supplies v)) actual known
  obtain ⟨x, member, root⟩ := actualRoot
  exact ⟨x, member, fun v agrees y edge => root y ((agrees x (covered member) y).mpr edge)⟩

private theorem sourcedClosedRank (n bound : Nat) (inRoster : n ≤ bound) :
    (∀ x ∈ Set.Iic bound, ∀ y, sourced n y x → y ∈ Set.Iic bound) ∧
      ∃ level : Nat → Int, ∀ x ∈ Set.Iic bound, ∀ y,
        sourced n y x → level y < level x := by
  constructor
  · intro x _ y edge
    rcases edge with ⟨before, rfl⟩ | ⟨_, rfl⟩
    · exact (Nat.succ_le_of_lt before).trans inRoster
    · exact inRoster
  · refine ⟨fun x => if x < n then (n : Int) - x else (x : Int) - n, ?_⟩
    intro x _ y edge
    dsimp only
    rcases edge with ⟨before, edge⟩ | ⟨after, edge⟩ <;> subst y
    · rw [ite_eq_left before]
      split <;> omega
    · rw [ite_eq_right (Nat.not_lt.mpr after.le), ite_eq_right (Nat.lt_irrefl n)]
      omega

/-- Two sourced completions agree on recipient zero and both have a root in
the closed roster {0, 1, 2}. The roots differ, so the observer knows that this
roster has a root without knowing a particular bearer to be unreceived. -/
theorem knownExistenceWithoutKnownBearer :
    let supplies (v : Bool) := sourced (if v then 2 else 1)
    let F := auditFrame supplies ({0} : Set Nat)
    let S := Set.Iic (2 : Nat)
    Knows F (fun v => HasRootIn S (supplies v)) false ∧
      ¬ ∃ x, Knows F (fun v => ∀ y, ¬ supplies v y x) false := by
  dsimp only
  have agrees : (auditFrame (fun v : Bool => sourced (if v then 2 else 1))
      ({0} : Set Nat)).access false true := by
    intro x hx y
    have hx0 : x = 0 := hx
    subst x
    exact (sameLists 1 0 y (by decide)).trans (sameLists 2 0 y (by decide)).symm
  constructor
  · refine knowsRootFromFiniteRank _ _ _ _ ?_
    intro v _
    refine ⟨Set.finite_le_nat 2, ⟨0, by decide⟩, ?_⟩
    cases v
    · exact sourcedClosedRank 1 2 (by decide)
    · exact sourcedClosedRank 2 2 (by decide)
  · rintro ⟨x, knows⟩
    have atOne : x = 1 := (oneRoot 1 x).mp (knows false (fun _ _ _ => Iff.rfl))
    have atTwo : x = 2 := (oneRoot 2 x).mp (knows true agrees)
    omega

end TruthCore.Causality.SupplierAudit
