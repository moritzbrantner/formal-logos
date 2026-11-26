module

public import Mathlib.Data.Fintype.Basic

/-! Material-conditional token recommendation. Acceptance and truth are
separate inputs. Absence means no recommendation by this route. -/

@[expose] public section
namespace TruthCore.Logic.MatchedRecommendation

def recommend {Atom : Type} [DecidableEq Atom] (p a b : Atom)
    (atomicAccepted conditionalAccepted : Bool) : Option Atom :=
  if atomicAccepted = true ∧ conditionalAccepted = true ∧ p = a then some b else none

theorem truthPreserved {Atom : Type} [DecidableEq Atom] (truth : Atom → Bool)
    {p a b r : Atom} {pa ca : Bool} (generated : recommend p a b pa ca = some r)
    (atomTrue : truth p = true) (conditionalTrue : (!truth a || truth b) = true) :
    truth r = true := by
  unfold recommend at generated
  split at generated
  · rename_i matched
    have rEq : b = r := Option.some.inj generated
    simpa [← rEq, ← matched.2.2, atomTrue] using conditionalTrue
  · contradiction

theorem renamed {Atom Other : Type} [DecidableEq Atom] [DecidableEq Other]
    (rename : Atom → Other) (injective : Function.Injective rename)
    (p a b : Atom) (pa ca : Bool) :
    (recommend p a b pa ca).map rename =
      recommend (rename p) (rename a) (rename b) pa ca := by
  simp [recommend, injective.eq_iff]

theorem scopeSize : 3 ^ 3 * 2 ^ 2 = 108 ∧ 108 * 2 ^ 3 = 864 ∧ 108 * 6 = 648 := by
  decide

def truth (a : Fin 3) : Bool := a == 0

def fixedOutput (p a : Fin 3) : Option (Fin 3) :=
  if (recommend p a (0 : Fin 3) true true).isSome then some 2 else none

def unmatched (_ _ b : Fin 3) : Option (Fin 3) := some b

theorem mutationControls :
    recommend (0 : Fin 3) 0 0 true true = some 0 ∧
    truth 0 = true ∧ fixedOutput 0 0 = some 2 ∧ truth 2 = false ∧
    recommend (0 : Fin 3) 1 1 true true = none ∧
    (!truth 1 || truth 1) = true ∧ unmatched 0 1 1 = some 1 ∧ truth 1 = false := by
  decide +kernel

end TruthCore.Logic.MatchedRecommendation
