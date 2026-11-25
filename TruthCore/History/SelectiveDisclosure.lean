module

/-!
# Inferring absence from a historical record

A truthful selection can omit an event that occurred. The absence inference
uses completeness for the specified reporting domain.
-/

@[expose] public section

namespace TruthCore.History.SelectiveDisclosure

abbrev Event := Fin 3
def occurred (e : Event) : Prop := e.val < 2
def selected : List Event := [1]
def full : List Event := [0, 1]
def sound (rows : List Event) : Prop :=
  ∀ e, e ∈ rows → occurred e
def complete (rows : List Event) : Prop :=
  ∀ e, occurred e → e ∈ rows
def inferAbsent (rows : List Event) (e : Event) : Bool :=
  decide (e ∉ rows)

theorem absence_of_complete {E : Type} (actual : E → Prop)
    (rows : List E) (covers : ∀ e, actual e → e ∈ rows)
    (e : E) (missing : e ∉ rows) : ¬ actual e :=
  fun happened => missing (covers e happened)

theorem selectiveTruthControl :
    selected ≠ [] ∧ sound selected ∧
    inferAbsent selected 0 = true ∧ occurred 0 ∧
    ¬ complete selected ∧ sound full ∧ complete full ∧
    inferAbsent full 0 = false ∧
    inferAbsent full 2 = true ∧ ¬ occurred 2 := by
  simp [sound, complete, Fin.forall_fin_succ,
    occurred, selected, full, inferAbsent]

end TruthCore.History.SelectiveDisclosure
