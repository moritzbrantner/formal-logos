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

namespace TruthCore.DiscoverFixtureTarget

/-- A structure with a predicate field and an element field. -/
structure PBox (B : Type) where
  Q : B → Prop
  val : B

/-- The target's predicate `R` has the type of `PBox.Q`: binding `R := b.Q`
would equate unrelated relations by type alone, so it is never tried. -/
def PredTarget (B : Type) (R : B → Prop) (x : B) : Prop := R x

/-- Everything is `b.Q`. -/
def PredPremise (B : Type) (b : PBox B) : Prop := ∀ y, b.Q y

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-- A predicate through a definitional alias (as Mathlib's `Set B`). -/
def Pred (B : Type) : Type := B → Prop

/-- A structure with an aliased-predicate field and an element field. -/
structure PABox (B : Type) where
  Q : Pred B
  val : B

/-- The target's `R : Pred B` is a predicate behind an alias: never projected. -/
def AliasTarget (B : Type) (R : Pred B) (x : B) : Prop := R x

/-- Everything is `b.Q`. -/
def AliasPremise (B : Type) (b : PABox B) : Prop := ∀ y, b.Q y

/-- A structure with two fields of the carrier's type. -/
structure Two (B : Type) where
  fst : B
  snd : B

/-- `P` holds at both fields: either projection of `x` closes the goal. -/
def TwoPremise (B : Type) (P : B → Prop) (t : Two B) : Prop := P t.fst ∧ P t.snd

/-- A box with a second field, so that no box is built from a value alone. -/
structure Tagged (B T : Type) where
  val : B
  tag : T

/-- `P` holds at every tagged value: proves `P b.val` for any `b`, without the
premise that introduced `b`. -/
def EveryBox (B T : Type) (P : B → Prop) : Prop := ∀ c : Tagged B T, P c.val

/-- A content-free premise that only introduces a tagged box `b`. -/
def OwnsBox (B T : Type) (b : Tagged B T) : Prop := True

/-- A conjunctive antecedent over two elements of one type: the conjunctive
builder applies `R` to the first element `g`, but `Q` is asked of `h`, so only
the single-conjunct bridge `∀ a, A2 a → R a` unlocks it. -/
def ConjSkew (B : Type) (A1 A2 Q : B → Prop) : Prop := ∀ g h, A1 g → A2 h → Q h

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-! Computed formulas (#1845): a small modal language whose schema is built by
recursion, as `TruthCore.Modal.convergenceFormula` is. Delta-expansion leaves
`conv 1 0 1 1` and the recursive `Sat` unevaluated; their equations evaluate
them to constructor form before Duper runs. -/

inductive Fm where
  | atom : Fm
  | imp : Fm → Fm → Fm
  | box : Fm → Fm
  | dia : Fm → Fm

/-- A relational frame (standing in for a Kripke frame). -/
structure Fr (W : Type) where
  acc : W → W → Prop

/-- Truth at a world, by structural recursion on the formula. -/
def Sat {W : Type} (F : Fr W) (V : W → Prop) (w : W) : Fm → Prop
  | .atom => V w
  | .imp p q => Sat F V w p → Sat F V w q
  | .box p => ∀ v, F.acc w v → Sat F V v p
  | .dia p => ∃ v, F.acc w v ∧ Sat F V v p

/-- Validity on a frame. -/
def Val {W : Type} (F : Fr W) (p : Fm) : Prop := ∀ V w, Sat F V w p

def iterB : Nat → Fm → Fm
  | 0, p => p
  | n + 1, p => .box (iterB n p)

def iterD : Nat → Fm → Fm
  | 0, p => p
  | n + 1, p => .dia (iterD n p)

/-- The Lemmon-Scott schema `◇ʰ□ⁱp → □ʲ◇ᵏp`, built by recursion. -/
def conv (h i j k : Nat) : Fm := .imp (iterD h (iterB i .atom)) (iterB j (iterD k .atom))

/-- The 5 schema `◇p → □◇p` is valid on `F` (a computed formula). -/
def FiveValid (W : Type) (F : Fr W) : Prop := Val F (conv 1 0 1 1)

/-- `F` is Euclidean: the frame condition that validates the 5 schema. -/
def EuclFrame (W : Type) (F : Fr W) : Prop := ∀ w a b, F.acc w a → F.acc w b → F.acc a b

/-- The same schema validity under another name: proved from `FiveValid`
treating `conv 1 0 1 1` as an opaque term (the plain prover suffices). -/
def FiveValidCopy (W : Type) (F : Fr W) : Prop := Val F (conv 1 0 1 1)

/-- `F` is reflexive: it does not validate the 5 schema (negative control). -/
def ReflFrame (W : Type) (F : Fr W) : Prop := ∀ w, F.acc w w

/-- A profile bundling a frame with another field (projection-only uses). -/
structure Prof (W : Type) where
  frame : Fr W
  other : W → Prop

/-- Uses `m` only through `m.frame : Fr W`. -/
def FrameOnly (W : Type) (m : Prof W) : Prop := EuclFrame W m.frame

/-- Uses `m` through `m.frame` and `m.other`. -/
def FrameAndOther (W : Type) (m : Prof W) : Prop := EuclFrame W m.frame ∧ ∀ w, m.other w

/-- Uses `m` whole. -/
def Whole (W : Type) (m : Prof W) : Prop := m = m

end TruthCore.DiscoverFixtureTarget

namespace TruthCore.DiscoverFixtureTarget

/-! The `truth prove-sweep` portfolio inside `truth discover`. `PlusOne` needs
an arithmetic fact (`n < n + 1`) that `duper [*]` has no premise for, while
`simp_all` and `grind` close it from `Keeps`. -/

/-- The target: `Q` with a successor fact. -/
def PlusOne (P Q : Nat → Prop) : Prop := ∀ n, P n → Q n ∧ n < n + 1

/-- The premise the portfolio needs. -/
def Keeps (P Q : Nat → Prop) : Prop := ∀ n, P n → Q n

/-- Doubling by recursion: `double n = 2 * n` needs induction. -/
def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

/-- A library theorem, tagged for `simp` and `grind`: a premise outside any
bundle. A portfolio proof that rests on it must be rejected. -/
@[simp, grind =] theorem double_eq (n : Nat) : double n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [double, ih]; omega

/-- Follows from no premise only through `double_eq`. -/
def DoubleTarget (P : Nat → Prop) : Prop := ∀ n, P (2 * n) → P (double n)

/-- An unrelated premise of the same vocabulary. -/
def DoubleKeeps (P : Nat → Prop) : Prop := ∀ n, P n → P n

/-- A proof through `double_eq`, for `#discover_external`. -/
theorem usesDoubleEq (P : Nat → Prop) (n : Nat) (h : P (2 * n)) : P (double n) := by
  rw [double_eq]; exact h

/-- A proof through `double`'s equation lemmas only (generated, not premises). -/
theorem usesEquations (P : Nat → Prop) (h : P 2) : P (double 1) := by
  simp only [double]; exact h

end TruthCore.DiscoverFixtureTarget
