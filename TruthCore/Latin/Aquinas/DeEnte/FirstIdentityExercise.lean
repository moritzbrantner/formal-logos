module

public import TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

/-- For each actual identity bearer, some eligible exercise has no nonempty
path into it from any exercise of that same bearer, including itself. -/
def ActualIdentityHasMinimalExercise {B P R E : Type} (p : Profile B P R)
    (bearer : E → B) (C : E → E → Prop) : Prop :=
  ∀ r, p.InAct r p.esse → p.esseOf r = p.essenceOf r →
    ∃ f, bearer f = r ∧ ∀ e, bearer e = r → ¬ Relation.TransGen C e f

end TruthCore.Latin.Aquinas.DeEnte.FirstIdentityExercise
