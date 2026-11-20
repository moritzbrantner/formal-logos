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
