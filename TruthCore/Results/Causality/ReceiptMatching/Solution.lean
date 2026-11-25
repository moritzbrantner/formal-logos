module

public import TruthCore.Causality.ReceiptMatching
public import Mathlib.Tactic

@[expose] public section
namespace TruthCore.Results.Causality.ReceiptMatching
open TruthCore.Causality
open TruthCore.Causality.ReceiptMatching
open BruteFoundationBoundary (Profile)
open NecessaryRootFork (ActualConcrete)
open RootPositiveIntellectWill (ActualRootExistsAt)

theorem unmatchedUpstream : UnmatchedUpstream := by
  classical
  intro E V sender receiver marked noReturn finite
  by_contra! allMatch
  let Up (x : V) := Reaches sender receiver x (sender marked)
  let Out := {p : E // Up (sender p)}
  let _ : Finite Out := finite
  let matchAt (u : V) (hu : Up u) := (allMatch u hu).some
  let prior (p : Out) := matchAt (sender p.val) p.property ⟨p.val, rfl⟩
  have received (p : Out) : receiver (prior p).val = sender p.val := (prior p).property
  let previous (p : Out) : Out :=
    ⟨(prior p).val, p.property.head ⟨(prior p).val, rfl, received p⟩⟩
  have unique : Function.Injective previous := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ eq
    have sameReceipt := congrArg Subtype.val eq
    have sameSender : sender p = sender q :=
      (received ⟨p,hp⟩).symm.trans ((congrArg receiver sameReceipt).trans (received ⟨q,hq⟩))
    have fibers {x y : V} (hx : Up x) (hy : Up y)
        (i : {e // sender e = x}) (j : {e // sender e = y})
        (xy : x = y) (equal : (matchAt x hx i).val = (matchAt y hy j).val) :
        i.val = j.val := by
      subst y
      exact congrArg Subtype.val ((matchAt x hx).injective (Subtype.ext equal))
    exact Subtype.ext (fibers hp hq ⟨p,rfl⟩ ⟨q,rfl⟩ sameSender sameReceipt)
  obtain ⟨p, preimage⟩ := (Finite.surjective_of_injective unique) (⟨marked, .refl⟩ : Out)
  have hit : (prior p).val = marked := congrArg Subtype.val preimage
  apply noReturn
  have start : receiver marked = sender p.val := (congrArg receiver hit).symm.trans (received p)
  exact start.symm ▸ p.property

theorem actualRootOfReceiptMatching {W B E : Type} (m : Profile W B) (w : W)
    (sender receiver : E → {x // ActualConcrete m w x})
    (obstruction : UnmatchedUpstream) (boundary : OneWayFiniteAncestry sender receiver)
    (covered : GroundedCanMatch m w sender receiver) : ActualRootExistsAt m w := by
  obtain ⟨marked, noReturn, finite⟩ := boundary
  obtain ⟨u, _, mismatch⟩ := obstruction sender receiver marked noReturn finite
  exact ⟨u, u.property, fun y h => mismatch (covered u ⟨y,h⟩)⟩

open scoped BigOperators
open ParticipatedEsseScale (realizedLevels)

private theorem layers {n : Nat} (count gap : Fin n → Nat) :
    amount count gap = ∑ k, atLeast count k * gap k := by
  unfold amount atLeast
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : k ≤ j <;> simp [h]

/-- With multiplicities and the zero point fixed, all positive integer
spacings give a covered output iff every upper-grade count is covered. -/
theorem allCalibrations : CoverageUnderRegrading := by
  intro n outgoing incoming
  constructor
  · intro covered k
    let bump := (∑ j, atLeast incoming j) + 1
    let gap (j : Fin n) := 1 + if j = k then bump else 0
    have positive (j : Fin n) : 0 < gap j := by simp [gap]
    have expand (c : Fin n → Nat) :
        amount c gap = (∑ j, atLeast c j) + atLeast c k * bump := by
      rw [layers]
      simp [gap, Nat.mul_add, Finset.sum_add_distrib, mul_ite]
    have h := covered gap positive
    rw [expand, expand] at h
    by_contra! excess
    have step := Nat.mul_le_mul_right bump (Nat.succ_le_of_lt excess)
    rw [Nat.succ_mul] at step
    dsimp [bump] at h step
    omega
  · intro counts gap _
    rw [layers, layers]
    exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right _ (counts j))

private theorem preserves {giver recipient : Bearer} (h : gives giver recipient) :
    ∀ feature, has recipient feature → has giver feature := by
  cases giver <;> cases recipient <;> simp_all [gives, has]

/-- Both numerical readings calibrate the degree as the least upper bound of
all levels actually realized, on the existing definition of realizedLevels. -/
private theorem calibrated (high : Nat) (h : 2 ≤ high) (b : Bearer) :
    IsLUB (realizedLevels (fun _ => True) has (level high) b) (degree high b) := by
  apply IsGreatest.isLUB
  constructor
  · cases b with
    | principal | relay => exact ⟨true, trivial, trivial, rfl⟩
    | left | right => exact ⟨false, trivial, rfl, rfl⟩
  · rintro v ⟨f, _, hf, rfl⟩
    cases b <;> cases f <;> simp_all [has, degree, level]

theorem relayCalibrationControl : RelayCalibrationControl := by
  refine ⟨fun _ _ h => preserves h, calibrated, ?_⟩
  decide

end TruthCore.Results.Causality.ReceiptMatching
