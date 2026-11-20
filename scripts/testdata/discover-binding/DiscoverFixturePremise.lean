/-! Fixture for `scripts/test_discover_binding_lean.py`: a premise in another
module whose relation binder `Causes` carries the same tag as the target's
`CausesIn`. -/
namespace TruthCore.DiscoverFixturePremise

def Premise (B : Type) (Causes : B → B → Nat → Prop) (a : B) : Prop := Causes a a 1

end TruthCore.DiscoverFixturePremise

namespace TruthCore.DiscoverFixturePremise

/-- A trivial premise whose element binder `x : B` the target lacks. -/
def HasElement (B : Type) (x : B) : Prop := x = x

end TruthCore.DiscoverFixturePremise

namespace TruthCore.DiscoverFixturePremise

/-- Refutable only given an element of `B`: satisfiable over an empty `B`. -/
def EverywhereBoth (B : Type) (R : B → Prop) : Prop := ∀ y, R y ∧ ¬ R y

end TruthCore.DiscoverFixturePremise

namespace TruthCore.DiscoverFixturePremise

/-- Every element has `P`: holds vacuously over an empty `B`. -/
def AllP (B : Type) (P : B → Prop) : Prop := ∀ y, P y

/-- A content-free candidate that only introduces an element `x : B`. -/
def Marker (B : Type) (x : B) : Prop := True

end TruthCore.DiscoverFixturePremise
