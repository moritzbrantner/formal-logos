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

namespace TruthCore.DiscoverFixturePremise

/-- An unused candidate that introduces the carrier `C` (Codex P1 on #1796,
domain provenance through same-module aliases). -/
def DomMarker (C : Type) : Prop := True

/-- Shares `C` with `DomMarker` by the same-module convention. -/
def DomRule (C : Type) (P : C → Prop) (Q : Prop) : Prop := (∃ c, P c) → Q

end TruthCore.DiscoverFixturePremise

namespace TruthCore.DiscoverFixturePremise

/-- A tautology whose only role is to put an element `x : B` next to `P`; its
carriers match the target's by name only (bridge domain provenance). -/
def BMark (B D : Type) (P : B → D → Prop) (x : B) : Prop := ∀ d, P x d ∨ ¬ P x d

end TruthCore.DiscoverFixturePremise

namespace TruthCore.DiscoverFixturePremise

/-- Every element has `S` (one half of a literal P/¬P pair, #1819). -/
def LitP (C : Type) (S : C → Prop) : Prop := ∀ y, S y

/-- The literal negation of `LitP`: it unfolds to `¬ LitP C S`, as
`ActNotPriorInTime F := ¬ ActPriorInTime F` does. -/
def LitNotP (C : Type) (S : C → Prop) : Prop := ¬ LitP C S

/-- Some element lacks `S`: incompatible with `LitP`, but not its definitional
negation (the negative control: a genuine incompatibility). -/
def GenSome (C : Type) (S : C → Prop) : Prop := ∃ y, ¬ S y

/-- Whatever is `R` is `Q` (the premise of the conjunctive-bridge fixture). -/
def ConjRule (B : Type) (R Q : B → Prop) : Prop := ∀ g, R g → Q g

end TruthCore.DiscoverFixturePremise

namespace TruthCore.DiscoverFixturePremise

/-- Two premises of one module over one world `w` (renamed on entry, since
the target already has a `w`): they must share it (#1926). -/
def HoldsHere (W : Type) (P : W → Prop) (w : W) : Prop := P w

/-- The second premise over the same `w`. -/
def AlsoHere (W : Type) (P : W → Prop) (w : W) : Prop := P w → P w

end TruthCore.DiscoverFixturePremise
