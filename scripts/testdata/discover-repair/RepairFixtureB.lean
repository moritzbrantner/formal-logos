/-! Fixture for `scripts/test_discover_repair.py` (#1833): a declaration in
another module whose carrier has the same name `B` as the target's. Only the
cross-module by-name fallback identifies the two carriers; nothing records
that they are one domain. Imports only Init. -/
namespace TruthCore.RepairFixtureB

/-- The carrier `B` (of this module) is empty. -/
def NoElement (B : Type) : Prop := ∀ _x : B, False

end TruthCore.RepairFixtureB
