module

public import Mathlib.Order.Setoid.Basic
public import TruthCore.Modal.ChoiceContext
public import TruthCore.Modal.DeonticFutureBoundary

/-! Local choice semantics on supplied moment/history incidence. The laws use
arbitrary carriers; the controls use finite branching frames. A choice is a
setoid class of histories through the moment. Tree and interaction conditions
are stated separately from this local semantics. -/

@[expose] public section

namespace TruthCore.Modal.STIT

open TruthCore.Modal.DeonticFutureBoundary (Ought Can compatibility)

structure BranchingFrame (M H A : Type) where
  /-- The supplied histories containing each moment. -/
  traverses : M → H → Prop
  /-- Two histories are related when they represent outcomes of the same
  available choice for the indicated agent at the moment. -/
  choice : (m : M) → A → Setoid {h : H // traverses m h}

variable {M H A : Type}

abbrev BranchingFrame.Through (F : BranchingFrame M H A) (m : M) := {h : H // F.traverses m h}

variable {F : BranchingFrame M H A} {m : M}

def Necessary (p : F.Through m → Prop) : Prop := ∀ h, p h

def Cstit (a : A) (h : F.Through m) (p : F.Through m → Prop) : Prop :=
  ∀ k, (F.choice m a).r h k → p k

def Dstit (a : A) (h : F.Through m) (p : F.Through m → Prop) : Prop :=
  Cstit a h p ∧ ¬ Necessary p

/-- Agent-indexed choices are jointly realizable if every selection of cell
representatives has a common history in their respective cells. -/
def Independent (F : BranchingFrame M H A) (m : M) : Prop :=
  ∀ selected : A → F.Through m, ∃ h, ∀ a, (F.choice m a).r (selected a) h

/-- A shared strictly later moment prevents the histories being separated
by a present choice. The supplied order can be taken from a branching tree. -/
def NoChoiceBetweenUndivided [LT M] (F : BranchingFrame M H A) (m : M) : Prop :=
  ∀ (a : A) (h k : F.Through m), (∃ n, m < n ∧ F.traverses n h ∧ F.traverses n k) →
    (F.choice m a).r h k

theorem cstit_actual {a : A} {h : F.Through m} {p : F.Through m → Prop} (hp : Cstit a h p) : p h :=
  hp h ((F.choice m a).iseqv.refl h)

theorem cstit_sameCell {a : A} {h k : F.Through m} {p : F.Through m → Prop}
    (hk : (F.choice m a).r h k) : Cstit a h p ↔ Cstit a k p :=
  ⟨fun hp j hj => hp j ((F.choice m a).iseqv.trans hk hj),
   fun hp j hj => hp j ((F.choice m a).iseqv.trans ((F.choice m a).iseqv.symm hk) hj)⟩

theorem cstit_and {a : A} {h : F.Through m} {p q : F.Through m → Prop} :
    Cstit a h (fun k => p k ∧ q k) ↔ Cstit a h p ∧ Cstit a h q :=
  ⟨fun hp => ⟨fun k hk => (hp k hk).1, fun k hk => (hp k hk).2⟩,
    fun hp k hk => ⟨hp.1 k hk, hp.2 k hk⟩⟩

theorem necessary_cstit {a : A} {h : F.Through m} {p : F.Through m → Prop} (hp : Necessary p) :
    Cstit a h p := fun k _ => hp k

theorem necessary_not_dstit {a : A} {h : F.Through m} {p : F.Through m → Prop} (hp : Necessary p) :
    ¬ Dstit a h p := fun hd => hd.2 hp

/-- Any history is historically possible from any other at this moment. -/
def historical (F : BranchingFrame M H A) (m : M) : Frame (F.Through m) :=
  ⟨fun _ _ => True⟩

/-- Feasible successors are supplied independently of ideal successors.
When feasibility is imposed at the cell level its successor sets should be
unions of cells. Ensuring still quantifies over the full chosen cell. -/
def CanEnsure (available : Frame (F.Through m)) (a : A) (h : F.Through m)
    (p : F.Through m → Prop) : Prop :=
  Can available h (fun k => Cstit a k p)

theorem canEnsure_can {available : Frame (F.Through m)} {a : A} {h : F.Through m} {p : F.Through m → Prop}
    (hp : CanEnsure available a h p) : Can available h p := by
  obtain ⟨k, hk, hc⟩ := hp
  exact ⟨k, hk, cstit_actual hc⟩

theorem ought_can_iff (ideal available : Frame (F.Through m)) (h : F.Through m) :
    (∀ p, Ought ideal h p → Can available h p) ↔
      ∃ k, ideal.access h k ∧ available.access h k :=
  compatibility ideal available h

/-- An available contrary cell supplies an actual counterhistory. The
reverse inference fails when outcomes vary within a cell. -/
theorem dstit_of_canEnsure_not {available : Frame (F.Through m)}
    {a : A} {h : F.Through m} {p : F.Through m → Prop} (hp : Cstit a h p)
    (hn : CanEnsure available a h (fun k => ¬ p k)) : Dstit a h p := by
  obtain ⟨k, _, hk⟩ := canEnsure_can hn
  exact ⟨hp, fun settled => hk (settled k)⟩

/-- If the deterministic decision table supplies each history's response
from the same law and input, historical variation of its action is excluded. -/
theorem choiceContext_settled (h : F.Through m)
    (table : F.Through m → ChoiceContext.History)
    (same : ∀ k, ChoiceContext.SameContext (table h) (table k)) :
    Necessary (fun k => ChoiceContext.action (table k) = ChoiceContext.action (table h)) := by
  intro k
  obtain ⟨law, input⟩ := same k
  simp only [ChoiceContext.action, ← law, ← input]

end TruthCore.Modal.STIT
