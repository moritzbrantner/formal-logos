/-! Fixture for `scripts/test_discover_binding_lean.py`: a target whose relation
binder `CausesIn` is tagged (by the test) either as a whole binder or only at
the partial application `CausesIn _ _ 0`, while the target itself needs the
relation at another respect (`1`). -/
namespace TruthCore.DiscoverFixtureTarget

def Target (B : Type) (CausesIn : B → B → Nat → Prop) (a : B) : Prop := CausesIn a a 1

end TruthCore.DiscoverFixtureTarget
