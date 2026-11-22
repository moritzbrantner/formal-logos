/-! Fixture for `scripts/test_discover_binding_lean.py`: a target whose relation
binder `CausesIn` is tagged (by the test) either as a whole binder or only at
the partial application `CausesIn _ _ 0`, while the target itself needs the
relation at another respect (`1`). -/
namespace TruthCore.DiscoverFixtureTarget

def Target (B : Type) (CausesIn : B → B → Nat → Prop) (a : B) : Prop := CausesIn a a 1

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-- A target that holds only for a nonempty carrier: not a theorem of its
vocabulary (Codex P1 on #1796, premise-free check). -/
def Inhabited' (B : Type) : Prop := ∃ y : B, y = y

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-- A target that introduces an element `x : B` its premise lacks. -/
def HoldsAt (B : Type) (R : B → Prop) (x : B) : Prop := R x

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-- Some element has `Q`: needs a nonempty `B`, which `AllP` does not give
(Codex P1 on #1796, bridge search). -/
def SomeQ (B : Type) (Q : B → Prop) : Prop := ∃ y, Q y

/-- `SomeQ` with the target's own element `x : B` (the control). -/
def SomeQAt (B : Type) (Q : B → Prop) (x : B) : Prop := ∃ y, Q y

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-- An opaque proposition whose only proof is an axiom outside the allowance
(standing in for an imported `sorry`-dependent simp lemma; Codex P2 on #1796,
witness axioms). -/
opaque Hard : Prop

@[simp] axiom hard_holds : Hard

def NeedsHard (B : Type) (R : B → Prop) : Prop := Hard ∧ ∀ y, R y → R y

def GivesHard (B : Type) (R : B → Prop) : Prop := Hard

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-- The goal of the domain-provenance fixture. -/
def DomGoal (Q : Prop) : Prop := Q

/-- Shares `C` with the premise module's `DomMarker` only by name. -/
def DomWitness (C : Type) (P : C → Prop) : Prop := ∃ c, P c

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-- Some `y` has `Q y d` for every `d`. -/
def BTarget (B D : Type) (Q : B → D → Prop) : Prop := ∃ y, ∀ d, Q y d

/-- Everything has `P`. -/
def BAll (B D : Type) (P : B → D → Prop) : Prop := ∀ y d, P y d

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-- An unrelated target: only an inconsistent premise set proves it. -/
def Unrelated (Q : Prop) : Prop := Q

/-- A conjunctive antecedent: whatever is `A1` and `A2` is `Q` (#1819). -/
def ConjGoal (B : Type) (A1 A2 Q : B → Prop) : Prop := ∀ g, A1 g → A2 g → Q g

/-- A single antecedent: the control for the conjunctive-bridge fixture. -/
def SingleGoal (B : Type) (A1 Q : B → Prop) : Prop := ∀ g, A1 g → Q g

/-- A structure with a field of the carrier's type (projection binding). -/
structure Box (B : Type) where
  val : B

/-- The target binds an element `x : B`. -/
def ProjTarget (B : Type) (P : B → Prop) (x : B) : Prop := P x

/-- The premise speaks of `b.val` for a structure binder `b : Box B`. -/
def ProjPremise (B : Type) (P : B → Prop) (b : Box B) : Prop := P b.val

/-- A premise whose projection choice does not help. -/
def ProjWrong (B : Type) (P : B → Prop) (b : Box B) : Prop := ¬ P b.val

end TruthCore.DiscoverFixtureTarget
