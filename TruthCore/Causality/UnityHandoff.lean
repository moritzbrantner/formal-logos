module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause

/-! A composite has a distinct uniting cause in each phase while its uniter can change from a jig to a collar. -/

@[expose] public section

namespace TruthCore.Causality.UnityHandoff

open TruthCore.Latin.Aquinas.SummaTheologiae

inductive Role | whole | collar | jig deriving DecidableEq

open Role

def holds (late jigAvailable collarAvailable : Bool) :=
  if late then collarAvailable else jigAvailable

def composite (x : Role) := x = whole

abbrev supplies (late : Bool) (c x : Role) (_ : Unit) : Prop :=
  x = whole ∧ holds late true true = true ∧
  holds late (decide (c ≠ jig)) (decide (c ≠ collar)) = false

theorem pointwise (late : Bool) :
    CompositeHasAUnitingCauseReading composite (supplies late) () := by
  rintro x rfl
  cases late
  · exact ⟨jig, by decide, by decide⟩
  · exact ⟨collar, by decide, by decide⟩

theorem noFixed : ¬ ∃ c, ∀ late, supplies late c whole () := by
  rintro ⟨c, h⟩
  cases c with
  | whole => exact (by decide : ¬ supplies false whole whole ()) (h false)
  | collar => exact (by decide : ¬ supplies false collar whole ()) (h false)
  | jig => exact (by decide : ¬ supplies true jig whole ()) (h true)

theorem latePart (c : Role) (h : supplies true c whole ()) : c = collar := by
  cases c with
  | collar => rfl
  | whole => exact False.elim ((by decide : ¬ supplies true whole whole ()) h)
  | jig => exact False.elim ((by decide : ¬ supplies true jig whole ()) h)

end TruthCore.Causality.UnityHandoff
