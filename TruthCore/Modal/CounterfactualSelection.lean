module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs
public import TruthCore.Modal.Kripke

/-!
World-indexed, extensional selection. These are analyst profiles. Accessibility
determines normal possibility; it need not supply an ordering or admit repairs.
-/

@[expose] public section

namespace TruthCore.Modal.CounterfactualSelection

abbrev Selector (W : Type*) := W → Set W → Set W

variable {W Rank : Type*}

/-- The universal truth clause validates both consequents of opposite polarity
when selection is empty. `HasSelection` makes this boundary explicit. -/
def Would (select : Selector W) (w : W) (A Q : Set W) : Prop :=
  select w A ⊆ Q

def HasSelection (select : Selector W) (w : W) (A : Set W) : Prop :=
  (select w A).Nonempty

def Success (select : Selector W) : Prop :=
  ∀ w A, select w A ⊆ A

def Centered (select : Selector W) : Prop :=
  ∀ w A, w ∈ A → w ∈ select w A

def NormallyPossible (frame : Frame W) (w : W) (A : Set W) : Prop :=
  ∃ v ∈ A, frame.access w v

def NonemptyForPossible (frame : Frame W) (select : Selector W) : Prop :=
  ∀ w A, NormallyPossible frame w A → HasSelection select w A

def NormalFirst (frame : Frame W) (select : Selector W) : Prop :=
  ∀ w A, NormallyPossible frame w A → ∀ v ∈ select w A, frame.access w v

/-- All accessible antecedent worlds. A normally impossible antecedent has
empty selection, whether or not there are inaccessible antecedent worlds. -/
def accessibleSelection (frame : Frame W) : Selector W :=
  fun w A v => frame.access w v ∧ v ∈ A

theorem accessible_success (frame : Frame W) : Success (accessibleSelection frame) :=
  fun _ _ _ hv => hv.2

theorem accessible_centered (frame : Frame W) (h : Reflexive frame) :
    Centered (accessibleSelection frame) :=
  fun w _ hw => ⟨h w, hw⟩

theorem accessible_nonempty (frame : Frame W) :
    NonemptyForPossible frame (accessibleSelection frame) :=
  fun _ _ ⟨v, hA, hAccess⟩ => ⟨v, hAccess, hA⟩

theorem accessible_normalFirst (frame : Frame W) :
    NormalFirst frame (accessibleSelection frame) :=
  fun _ _ _ _ hv => hv.1

theorem accessible_vacuity (frame : Frame W) (w : W) (A Q : Set W)
    (h : ¬ NormallyPossible frame w A) : Would (accessibleSelection frame) w A Q :=
  fun v hv => (h ⟨v, hv.2, hv.1⟩).elim

theorem identity {select : Selector W} (h : Success select) (w : W) (A : Set W) :
    Would select w A A :=
  h w A

theorem modus_ponens {select : Selector W} (h : Centered select) {w : W} {A Q : Set W}
    (hA : w ∈ A) (hQ : Would select w A Q) : w ∈ Q :=
  hQ (h w A hA)

theorem conjunction {select : Selector W} {w : W} {A Q R : Set W} :
    Would select w A (Q ∩ R) ↔ Would select w A Q ∧ Would select w A R :=
  ⟨fun h => ⟨fun _ hv => (h hv).1, fun _ hv => (h hv).2⟩,
    fun ⟨hQ, hR⟩ _ hv => ⟨hQ hv, hR hv⟩⟩

theorem weaken_consequent {select : Selector W} {w : W} {A Q R : Set W}
    (h : Would select w A Q) (hQR : Q ⊆ R) : Would select w A R :=
  fun _ hv => hQR (h hv)

theorem excludes_opposite {select : Selector W} {w : W} {A Q : Set W}
    (h : HasSelection select w A) (hQ : Would select w A Q) :
    ¬ Would select w A Qᶜ :=
  fun hNot => let ⟨_, hv⟩ := h; hNot hv (hQ hv)

/-- A supplied Stalnaker-style choice may leave an antecedent without a
representative. A successful, nonempty instance must choose an A-world. -/
def singleSelection (choose : W → Set W → Option W) : Selector W :=
  fun w A v => choose w A = some v

theorem single_would_iff {choose : W → Set W → Option W} {w v : W} {A Q : Set W}
    (h : choose w A = some v) : Would (singleSelection choose) w A Q ↔ v ∈ Q :=
  ⟨fun hQ => hQ h, fun hQ _ hv => Option.some.inj (hv.symm.trans h) ▸ hQ⟩

theorem single_conditional_excluded_middle (choose : W → Set W → Option W)
    (w : W) (A Q : Set W) :
    Would (singleSelection choose) w A Q ∨ Would (singleSelection choose) w A Qᶜ := by
  cases he : choose w A with
  | none =>
    exact Or.inl (fun _ hv => by
      change choose w A = some _ at hv
      rw [he] at hv
      cases hv)
  | some v =>
    rcases Classical.em (v ∈ Q) with h | h
    · exact Or.inl ((single_would_iff he).mpr h)
    · exact Or.inr ((single_would_iff he).mpr h)

/-- All A-worlds tied at the least rank. Lower ranks mean closer worlds.
No least rank is presumed to exist. -/
def leastSelection [Preorder Rank] (rank : W → W → Rank) : Selector W :=
  fun w A v => v ∈ A ∧ IsLeast (rank w '' A) (rank w v)

theorem least_success [Preorder Rank] (rank : W → W → Rank) :
    Success (leastSelection rank) :=
  fun _ _ _ hv => hv.1

/-- Lewis-style ordering clause without a limit assumption. Either A has
no worlds in the evaluation domain, or some A-world is strictly closer than
every A-world that falsifies Q. Restrict A first if using an accessible domain. -/
def LewisWould [Preorder Rank] (rank : W → W → Rank) (w : W) (A Q : Set W) : Prop :=
  (∀ v, v ∉ A) ∨ ∃ v ∈ A, ∀ u ∈ A, u ∉ Q → rank w v < rank w u

theorem lewis_iff_least_of_hasSelection [Preorder Rank] (rank : W → W → Rank)
    (w : W) (A Q : Set W) (hLeast : HasSelection (leastSelection rank) w A) :
    LewisWould rank w A Q ↔ Would (leastSelection rank) w A Q := by
  constructor
  · intro h v hv
    apply Classical.byContradiction
    intro hNot
    rcases h with hEmpty | ⟨u, hu, hCloser⟩
    · exact hEmpty v hv.1
    · exact (not_lt_of_ge (hv.2.2 ⟨u, hu, rfl⟩)) (hCloser v hv.1 hNot)
  · intro h
    obtain ⟨v, hv⟩ := hLeast
    refine Or.inr ⟨v, hv.1, fun u hu hNot => ?_⟩
    refine lt_of_le_not_ge (hv.2.2 ⟨u, hu, rfl⟩) fun hBack => ?_
    apply hNot (h (a := u) ⟨hu, ⟨⟨u, hu, rfl⟩, ?_⟩⟩)
    exact fun _ hz => le_trans hBack (hv.2.2 hz)

end TruthCore.Modal.CounterfactualSelection
