module

public import TruthCore.Causality.FiniteThroughput

@[expose] public section
open scoped ENNReal
open Relation
namespace TruthCore.Results.Causality.FiniteThroughput
open TruthCore.Causality
open TruthCore.Causality.FiniteThroughput

theorem returnOrNetExport : ReturnOrNetExport := by
  intro V flow finite a b edge
  classical
  let upstream (x : V) := ReflTransGen (fun i j => 0 < flow i j) x a
  change upstream b ∨ ∃ u, upstream u ∧ (∑' x, flow x u) < ∑' y, flow u y
  by_contra! h
  obtain ⟨outside, budget⟩ := h
  let incoming (p : V × V) := if upstream p.2 then flow p.1 p.2 else 0
  let outgoing (p : V × V) := if upstream p.1 then flow p.1 p.2 else 0
  have bounded : ∀ p, incoming p ≤ flow p.1 p.2 := by
    intro p
    by_cases h : upstream p.2 <;> simp [incoming, h]
  have included : ∀ p, incoming p ≤ outgoing p := by
    rintro ⟨i,j⟩
    by_cases hj : upstream j
    · by_cases pos : 0 < flow i j
      · have hi : upstream i := hj.head pos
        simp [incoming, outgoing, hi, hj]
      · simp [incoming, outgoing, le_antisymm (le_of_not_gt pos) bot_le]
    · simp [incoming, outgoing, hj]
  have crosses : incoming (a,b) < outgoing (a,b) := by
    have ha : upstream a := .refl
    simpa [incoming, outgoing, ha, outside] using edge
  have cut := ENNReal.tsum_lt_tsum
    (ne_top_of_le_ne_top finite (ENNReal.tsum_le_tsum bounded)) included crosses
  apply (not_le_of_gt cut)
  calc
    (∑' p, outgoing p) = ∑' i, ∑' j, outgoing (i,j) := ENNReal.tsum_prod'
    _ ≤ ∑' i, ∑' j, incoming (j,i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : upstream i
      · simpa [incoming, outgoing, hi] using budget i hi
      · simp [incoming, outgoing, hi]
    _ = ∑' i, ∑' j, incoming (i,j) := ENNReal.tsum_comm
    _ = ∑' p, incoming p := ENNReal.tsum_prod'.symm

theorem groundedExerciseAtTransfer (cut : ReturnOrNetExport) : GroundedExerciseAtTransfer := by
  intro V flow transmits intrinsic finite step supply a b edge noReturn
  obtain ⟨u, path, excess⟩ := (cut flow finite edge).resolve_left noReturn
  apply FinitelyGroundedPower.borrowed (step a b edge)
  clear edge noReturn
  induction path with
  | refl => exact .intrinsic u (supply u excess)
  | tail _ transfer ih => exact .borrowed (step _ _ transfer) ih

open BruteFoundationBoundary (Profile)
open NecessaryRootFork (ActualConcrete ActualRoot)
open RootPositiveIntellectWill (ActualRootExistsAt)

theorem actualRootOfLedger {W B : Type} (m : Profile W B) (w : W)
    (flow : {x // ActualConcrete m w x} → {x // ActualConcrete m w x} → ℝ≥0∞)
    (cut : ReturnOrNetExport) (oneWay : FiniteOneWayTransfer flow)
    (covered : GroundedExportCovered m w flow) : ActualRootExistsAt m w := by
  obtain ⟨finite, a, b, edge, noReturn⟩ := oneWay
  obtain ⟨u, _, excess⟩ := (cut flow finite edge).resolve_left noReturn
  exact ⟨u, u.property, fun y hy => (not_le_of_gt excess) (covered u ⟨y, hy⟩)⟩

theorem ledgerExistenceCriterion (cut : ReturnOrNetExport) : LedgerExistenceCriterion := by
  classical
  intro W B m w
  let V := {x // ActualConcrete m w x}
  constructor
  · rintro ⟨flow, oneWay, covered⟩
    obtain ⟨u, root⟩ := actualRootOfLedger m w flow cut oneWay covered
    obtain ⟨_, a, b, _, noReturn⟩ := oneWay
    by_cases hua : u = a.val
    · refine ⟨u, b, root, b.property, ?_⟩
      intro hub
      exact noReturn (Subtype.ext (hub.symm.trans hua) ▸ ReflTransGen.refl)
    · exact ⟨u, a, root, a.property, hua⟩
  · rintro ⟨u, v, root, actual, distinct⟩
    let a : V := ⟨u, root.1⟩
    let b : V := ⟨v, actual⟩
    have ab : a ≠ b := fun eq => distinct (congrArg Subtype.val eq)
    let flow (i j : V) : ℝ≥0∞ := if i = a then (if j = b then 1 else 0) else 0
    have support {i j} (pos : 0 < flow i j) : i = a ∧ j = b := by
      by_cases hi : i = a <;> by_cases hj : j = b <;> simp_all [flow]
    have stays {x} (h : ReflTransGen (fun i j => 0 < flow i j) b x) : x = b := by
      induction h with
      | refl => rfl
      | tail _ pos _ => exact (support pos).2
    refine ⟨flow, ⟨?_, a, b, by simp [flow], fun h => ab (stays h)⟩, ?_⟩
    · rw [ENNReal.tsum_prod']
      have row (i : V) : (∑' j, flow i j) = if i = a then 1 else 0 := by
        by_cases hi : i = a
        · simpa only [flow, hi, ite_true] using (tsum_ite_eq b (fun _ => (1 : ℝ≥0∞)))
        · simp [flow, hi]
      change (∑' i : V, ∑' j : V, flow i j) ≠ ⊤
      simp_rw [row]
      rw [tsum_ite_eq a (fun _ => (1 : ℝ≥0∞))]
      exact ENNReal.one_ne_top
    · intro z hasGround
      have za : z ≠ a := by
        rintro rfl
        obtain ⟨y, hy⟩ := hasGround
        exact root.2 y hy
      simp [flow, za]

end TruthCore.Results.Causality.FiniteThroughput
