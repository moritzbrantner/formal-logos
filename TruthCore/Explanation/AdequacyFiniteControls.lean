module

public import Mathlib.Data.Rat.Defs
public import TruthCore.Explanation.ExistentialInheritance

/-! Finite explanatory controls with stipulated facts, edges, scopes and
resources. They test the displayed assignments and leave their adequacy open. -/

@[expose] public section
namespace TruthCore.Explanation.AdequacyFiniteControls

namespace Occupant

abbrev Being := Bool × Bool
def worlds : List Bool := [false, true]
def occupants : List Being := [(false, false), (false, true), (true, false), (true, true)]

def identity (changes w : Bool) : Bool := changes && w
def present (changes w : Bool) (b : Being) : Bool := b.2 == identity changes w

def edge (changes w : Bool) (s t : Being) : Bool :=
  s == (false, identity changes w) && t == (true, identity changes w)

theorem assignment : ∀ changes : Bool,
    (∀ w : Bool,
      (occupants.filter (fun b => !b.1 && present changes w b)).length = 1 ∧
      (occupants.filter (fun b => b.1 && present changes w b)).length = 1 ∧
      (∀ i : Bool, present changes w (false, i) = present changes w (true, i)) ∧
      (∀ s ∈ occupants, ∀ t ∈ occupants,
        edge changes w s t → present changes w s ∧ present changes w t) ∧
      (∀ i : Bool, present changes w (true, i) → edge changes w (false, i) (true, i)) ∧
      ∀ s ∈ occupants, ∀ i : Bool, ¬ edge changes w s (false, i)) ∧
    (present changes false (false, false) &&
      worlds.any (fun w => !present changes w (false, false))) = changes ∧
    (changes = false → ∀ w, identity changes w = false) := by
  decide +kernel

theorem identification :
    (∀ w : Bool, ∀ b ∈ occupants, present true w b →
      ∃ v, present true v b = false) ∧
    (worlds.filter (fun w => present true w (true, false))) = [false] ∧
    (∀ w i : Bool, present true w (true, i) → identity true w = i) := by
  decide +kernel

def weight (p : ℚ) (w : Bool) : ℚ := if w then 1 - p else p

def posteriorActual (p : ℚ) (observed : Bool → Bool) : ℚ :=
  weight p false / (((worlds.filter observed).map (weight p)).sum)

theorem samplePriors :
    ∀ p ∈ ([1/10, 1/2, 9/10] : List ℚ),
      posteriorActual p (fun _ => true) = p ∧
      posteriorActual p (fun w => present true w (true, false)) = 1 := by
  decide +kernel

abbrev Performance := Bool → Bool
def channels : List Bool := [false, true]
def queries : List Performance := [fun _ => false, (· == false), (· == true), fun _ => true]
def available (limited w channel : Bool) : Bool := !(limited && !w && channel)
def response (q : Performance) (limited w channel : Bool) : Bool :=
  q channel && available limited w channel

theorem localRestriction :
    (∀ limited : Bool,
      (!channels.all (available limited false)) = limited ∧
      ∀ q ∈ queries, ∀ c : Bool, response q limited false c =
        (q c && available limited false c)) ∧
    (∀ q ∈ queries, ∀ c : Bool,
      (q c && true && (c == false)) = (q c && (c == false))) ∧
    (∃ q ∈ queries, ∃ c : Bool, (q c && true && true) ≠ (q c && (c == false))) := by
  decide +kernel

end Occupant

namespace Direction

abbrev Fact := Fin 4
abbrev Edge := Fact × Fact

def existsB (w : Bool) : Bool := !w
def edgeSound (e : Bool → Bool) : Bool := decide (∀ w, e w = true → existsB w = true)

theorem edgeTables :
    ([false, true].flatMap fun a => [false, true].map (a, ·)).filter
      (fun (a, b) => edgeSound (fun w => if w then b else a) && a) = [(true, false)] ∧
    ∀ rigid : Bool, edgeSound (fun _ => rigid) = !rigid ∧
      edgeSound (fun w => rigid && existsB w) ∧ (rigid && existsB false) = rigid := by
  decide +kernel

def holds (w : Bool) (f : Fact) : Bool := !w || f == 0 || f == 3

def cases : List (List Edge × Bool × Bool × Bool × Bool) :=
  [([], false, false, false, true), ([(2, 1), (1, 2)], true, true, true, true),
    ([(1, 2)], true, false, false, true), ([(0, 2)], true, false, false, false),
    ([(0, 1), (1, 2)], true, true, false, false)]

def path (edges : List Edge) : Nat → Fact → Fact → Bool
  | 0, _, _ => false
  | n + 1, x, y => edges.contains (x, y) ||
    edges.any (fun e => e.1 == x && path edges n e.2 y)

/-- Positive cycles in a four-fact graph have a witness of length at most four. -/
def cyclic (edges : List Edge) : Bool := (List.finRange 4).any fun x => path edges 4 x x

theorem explanansRows :
    cases.all (fun (edges, b, a, cycle, necessitating) => decide (
      (∀ e ∈ edges, holds false e.1 ∧ holds false e.2) ∧
      edges.any (fun e => e.2 == 2) = b ∧ edges.any (fun e => e.2 == 1) = a ∧
      cyclic edges = cycle ∧
      edges.all (fun e => decide (∀ w, holds w e.1 = true → holds w e.2 = true)) =
        necessitating)) = true := by
  decide +kernel

end Direction

namespace SameBase

open TruthCore.Explanation.ExistentialInheritance.Contained (Being present parent Step)

def derivatives : List Being := (List.range 4).map Being.derivative
def beings : List Being := [.background, .base] ++ derivatives

def derivativeEdges : List (Being × Being) :=
  (List.range 4).map fun n => (parent n, .derivative n)

theorem derivativeEdge_iff (s t : Being) :
    (s, t) ∈ derivativeEdges ↔ Step s t ∧ t ∈ derivatives := by
  simp only [derivativeEdges, derivatives, List.mem_map, Prod.mk.injEq, Step]
  constructor
  · rintro ⟨n, hn, h1, h2⟩
    exact ⟨⟨n, h1.symm, h2.symm⟩, n, hn, h2⟩
  · rintro ⟨⟨n, h1, h2⟩, m, hm, h3⟩
    have same : m = n := Being.derivative.inj (h3.trans h2)
    subst m
    exact ⟨n, hm, h1.symm, h2.symm⟩

def edges (active w : Bool) : List (Being × Being) :=
  if w then [] else derivativeEdges ++ (if active then [(.background, .base)] else [])

def existsAt (w : Bool) : Being → Bool
  | .background => true
  | _ => !w

theorem existsAt_iff (w : Bool) (b : Being) :
    existsAt w b = true ↔ present false w b := by
  cases w <;> cases b <;>
    simp [existsAt, present, TruthCore.Explanation.ExistentialInheritance.Contained.enabled]

inductive Fact where
  | law | exercise | exists (b : Being)
  deriving DecidableEq

def truths (w withExercise : Bool) : Fact → Bool
  | .law => true
  | .exercise => withExercise && !w
  | .exists b => existsAt w b

abbrev Rule := List Fact × Fact

def oldRules : List Rule := derivativeEdges.map fun (s, t) => ([.law, .exists s], .exists t)
def activated : List Rule := oldRules ++ [([.law, .exists .background, .exercise], .exists .base)]
def necessarySeed : List Fact := [.law, .exists .background]
def dependent : List Fact := (.exists .base) :: derivatives.map Fact.exists

def close (rules : List Rule) (seed : List Fact) : List Fact :=
  let step (known : List Fact) := known ++
    (rules.filter fun r => r.1.all known.contains && !known.contains r.2).map Prod.snd
  (step^[6]) seed

def preserves (w withExercise : Bool) (r : Rule) : Bool :=
  !(r.1.all (truths w withExercise)) || truths w withExercise r.2

def trace (w : Bool) (n : Nat) : List Nat :=
  if existsAt w (.derivative n) then (List.range 6).map (fun t => (n + t) % 3) else []

def readoutChecks (w : Bool) (n : Nat) : Bool :=
  let clock := trace w n
  (clock == if w then [] else (List.range 6).map (fun t => (n + t) % 3)) &&
    (clock.zip clock.tail).all (fun (a, b) => b == (a + 1) % 3)

def admittedReasonFacts (active w : Bool) : List (Fact × Fact) :=
  (edges active w).map fun (s, t) => (.exists s, .exists t)

theorem fixedDerivativeRows :
    (∀ active w : Bool,
      (edges active w).all (fun (s, t) => existsAt w s && existsAt w t && s != t) ∧
      (admittedReasonFacts active w).all (fun (r, f) => truths w false r && truths w false f) ∧
      (edges active w).filter (fun (_, t) => derivatives.contains t) = edges false w ∧
      derivatives.all (fun d => !existsAt w d || (edges active w).any (fun e => e.2 == d)) ∧
      oldRules.all (preserves w false) ∧
      (List.range 4).all (readoutChecks w)) ∧
    beings.filter (fun b => existsAt false b && !existsAt true b) = .base :: derivatives := by
  decide +kernel

def unexplained (active : Bool) : List Being :=
  beings.filter fun b => existsAt false b && !existsAt true b &&
    !(admittedReasonFacts active false).any (fun e => e.2 == .exists b)

theorem sourceAndResources :
    unexplained false = [.base] ∧ unexplained true = [] ∧
    (∀ w : Bool, existsAt w .background) ∧
    (∀ active : Bool, !(admittedReasonFacts active false).any (fun e => e.2 == .exists .background)) ∧
    (Fact.exists .background, Fact.exists .base) ∈ admittedReasonFacts true false ∧
    necessarySeed.all (truths true false) ∧ ¬ truths true false (.exists .base) ∧
    (∀ w : Bool, activated.all (preserves w true)) ∧
    dependent.all (fun f => !(close activated necessarySeed).contains f) ∧
    dependent.all (close activated (Fact.exercise :: necessarySeed)).contains ∧
    (derivatives.map Fact.exists).all (close oldRules (Fact.exists .base :: necessarySeed)).contains ∧
    !(activated.any fun r => r.2 == .exercise) := by
  decide +kernel

end SameBase

namespace Replacement

abbrev Being := Fin 4

def roster (dependentPersistent w : Bool) : List Being :=
  if dependentPersistent then
    if w then [2] else [0, 2]
  else if w then [2, 3] else [0, 1]

def links (dependentPersistent w : Bool) : List (Being × Being) :=
  if dependentPersistent then
    if w then [] else [(0, 2)]
  else if w then [(2, 3)] else [(0, 1)]

def roots (persistent w : Bool) : List Being :=
  (roster persistent w).filter (fun b => !(links persistent w).any (fun e => e.2 == b))

theorem replacementRows :
    (∀ p w : Bool, (roots p w).length = 1 ∧ (roots p w).all (roster p w).contains) ∧
    (∀ p : Bool, roots p false = [0] ∧ roots p true = [2] ∧ 0 ∉ roster p true) ∧
    (∀ w : Bool, 2 ∈ roster true w) := by
  decide +kernel

end Replacement

end TruthCore.Explanation.AdequacyFiniteControls
