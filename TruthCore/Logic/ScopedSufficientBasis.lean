module

/-! The two-content basis split treats sufficiency as a stipulated relation.
Having an observationally sufficient basis may coexist with another basis. -/

@[expose] public section
namespace TruthCore.Logic.ScopedSufficientBasis

/-- False denotes L or D, true denotes Q or O. -/
def sufficient (lo qd content empirical : Bool) : Bool :=
  match content, empirical with
  | false, false | true, true => true
  | false, true => lo
  | true, false => qd

def scope (global content : Bool) : Bool := global || content

def someEmpirical (S : Bool → Bool → Bool) (included : Bool → Bool) : Prop :=
  ∀ c, included c = true → (∃ b, S c b = true) → S c true = true

def onlyEmpirical (S : Bool → Bool → Bool) (included : Bool → Bool) : Prop :=
  ∀ c, included c = true → ∀ b, S c b = true → b = true

theorem rows : ∀ lo qd global,
    (someEmpirical (sufficient lo qd) (scope global) ↔ (if global then lo else true) = true) ∧
    (onlyEmpirical (sufficient lo qd) (scope global) ↔
      (if global then false else !qd) = true) := by
  unfold someEmpirical onlyEmpirical
  decide +kernel

end TruthCore.Logic.ScopedSufficientBasis
