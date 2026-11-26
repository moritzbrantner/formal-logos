module

public import TruthCore.Causality.Round5Worklist

/-!
# Finite controls from the causal-perfection transfer investigation

Structural surrogates for `docs/notes/causal-perfection-transfer.md`. Each
model fixes a small stipulated signature. The operation and life rules are the
corpus definitions `BeingInActHasOperation`, `OperationFromSelfOrAsMoved`,
`SelfOperatingUnmovedLives` and `PureAct`; the remaining relations are local
analyst slots. No ontology of actions, modal frame, grounding theory or
metaphysical possibility is certified by these models.
-/

@[expose] public section

set_option synthInstance.maxSize 4096

namespace TruthCore.Causality.PerfectionTransferControls

open TruthCore.Causality.Round5Worklist
open TruthCore.Causality.SelfOperationLife (SelfOperatingUnmovedLives)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

/-! ## 1. Operation, external determination and life (eight assignments)

Bearers `g` (source) and `x` (effect); respects esse and motion; operations
give, receive and immanent. The effect receives esse from `g`; only the
effect is moved and in potency. Three switches add an immanent operation of
`g`, life at `g`, and an external determination of `g`'s giving by `x`. -/

namespace Operation

abbrev g : Fin 2 := 0
abbrev x : Fin 2 := 1
abbrev esse : Fin 2 := 0
abbrev motion : Fin 2 := 1
abbrev give : Fin 3 := 0
abbrev receive : Fin 3 := 1
abbrev immanent : Fin 3 := 2

def actual (_ : Fin 2) (_ : Fin 2) : Prop := True
def grounds (c b : Fin 2) : Prop := c = g ∧ b = x
def causes (c b r : Fin 2) : Prop := c = g ∧ b = x ∧ r = esse
def potency (b r : Fin 2) : Prop := b = x ∧ r = motion
def moved (b r : Fin 2) : Prop := potency b r

def operationOf (i : Bool) (o : Fin 3) (b : Fin 2) : Prop :=
  (o = give ∧ b = g) ∨ (o = receive ∧ b = x) ∨ (i = true ∧ o = immanent ∧ b = g)
def terminus (o : Fin 3) : Fin 2 := if o = immanent then g else x
/-- The act reference of each operation; giving shares the source's esse-act. -/
def actRef (o : Fin 3) : Fin 2 := if o = receive then x else g
/-- Self-operation: an immanent operation whose terminus is its own bearer. -/
def operates (i : Bool) (b : Fin 2) : Prop :=
  ∃ o, operationOf i o b ∧ terminus o = b ∧ o = immanent
def lives (l : Bool) (b : Fin 2) (_ : Unit) : Prop := b = x ∨ (l = true ∧ b = g)
def externallyActualized (e : Bool) (c : Fin 2) (o : Fin 3) : Prop :=
  e = true ∧ c = x ∧ o = give
/-- An external actualizer of an operation identical with `g`'s esse-act must ground `g`. -/
def adapter (i e : Bool) : Prop :=
  ∀ c o, externallyActualized e c o → ¬ (operationOf i o g ∧ actRef o = g) ∨ grounds c g
/-- Broad first agency: no external actualizer of the giving. -/
def broad (e : Bool) : Prop := ¬ ∃ c, externallyActualized e c give
def root (b : Fin 2) : Prop := ∀ c, ¬ grounds c b

def Dichotomy (i : Bool) : Prop := OperationFromSelfOrAsMoved (operationOf i) (operates i) moved
def LifeRule (i l : Bool) : Prop := SelfOperatingUnmovedLives (operates i) moved (lives l)

/-- The background shared by all eight assignments. -/
theorem background (i : Bool) :
    root g ∧ ¬ root x ∧ PureAct potency g ∧ ¬ PureAct potency x ∧
    BeingInActHasOperation actual (operationOf i) esse ∧ (∀ b r, moved b r → potency b r) ∧
    operationOf i give g ∧ causes g x esse ∧ actRef give = g ∧ terminus give = x := by
  unfold root PureAct BeingInActHasOperation actual moved grounds potency operationOf causes
    actRef terminus
  revert i; decide

/-- The dichotomy and the life rule jointly force life at the unmoved source,
and the act-ground adapter excludes the external determination. -/
theorem forced (i l e : Bool) :
    (Dichotomy i → LifeRule i l → lives l g ()) ∧ (adapter i e → e = false) := by
  unfold Dichotomy LifeRule adapter OperationFromSelfOrAsMoved SelfOperatingUnmovedLives operates
    externallyActualized operationOf terminus moved potency lives actRef grounds
  revert i l e; decide

/-- Positive witness, two omission controls and the adapter control. -/
theorem controls :
    (adapter false false ∧ broad false ∧ ¬ Dichotomy false ∧ LifeRule false false) ∧
    (Dichotomy true ∧ ¬ LifeRule true false) ∧
    (adapter true false ∧ broad false ∧ Dichotomy true ∧ LifeRule true true) ∧
    (¬ adapter false true ∧ ¬ broad true) := by
  unfold Dichotomy LifeRule adapter broad OperationFromSelfOrAsMoved SelfOperatingUnmovedLives
    operates externallyActualized operationOf terminus moved potency lives actRef grounds
  decide

end Operation

/-! ## 2. External denomination versus incoming ground (sixteen configurations)

Carriers `g`, `x`, `y`. Each configuration has two local rosters: `g` with the
actual effect `x`, and `g` with the actual effect `y`. Four switches vary
act/esse identity, completion of the operative act by the effect, transport of
that completion into a ground of `g`, and an immanent operation of `g`. -/

namespace Denomination

abbrev g : Fin 3 := 0
abbrev x : Fin 3 := 1
abbrev y : Fin 3 := 2
abbrev give : Fin 3 := 0
abbrev secondary : Fin 3 := 1
abbrev inward : Fin 3 := 2

structure Config where
  identity : Bool
  completion : Bool
  transport : Bool
  immanent : Bool

variable (k : Config) (effect : Fin 3)

def actual (b : Fin 3) : Prop := b = g ∨ b = effect
instance (b : Fin 3) : Decidable (actual effect b) := inferInstanceAs (Decidable (_ ∨ _))

inductive ActReference where
  | esseAct | operationAct
  deriving DecidableEq

def actRef (_ : Fin 3) : ActReference := if k.identity then .esseAct else .operationAct
def terminus : Fin 3 := effect
def ground (c b : Fin 3) : Prop :=
  (c = g ∧ b = effect) ∨ (k.identity ∧ k.completion ∧ k.transport ∧ c = effect ∧ b = g)
def actGround : Prop := k.completion = true
def root : Prop := actual effect g ∧ ∀ c, ¬ ground k effect c g
def effects (c b : Fin 3) (r : Unit) : Prop := c = g ∧ b = effect ∧ r = ()
instance (c b : Fin 3) (r : Unit) : Decidable (effects effect c b r) :=
  inferInstanceAs (Decidable (_ ∧ _))
def operationOf (o : Fin 3) (b : Fin 3) : Prop :=
  (o = give ∧ b = g) ∨ (o = secondary ∧ b = effect) ∨ (k.immanent ∧ o = inward ∧ b = g)
def intrinsic (b : Fin 3) : Prop := k.immanent ∧ b = g
def potency (b : Fin 3) : Prop := b = effect
def moved (b : Fin 3) (_ : Unit) : Prop := b = effect
def bridge : Prop := ¬ k.identity ∨ ¬ actGround k ∨ ground k effect effect g
def givesX : Prop := ∃ r, effects effect g x r

def Dichotomy : Prop := OperationFromSelfOrAsMoved (operationOf k effect) (intrinsic k) (moved effect)

def configs : List Config :=
  [false, true].flatMap fun i => [false, true].flatMap fun c =>
    [false, true].flatMap fun t => [false, true].map fun m => ⟨i, c, t, m⟩

/-- Checked in every configuration and both rosters (`effect = 1` and `2`): the
dichotomy holds exactly with immanence, and a root satisfying identity and the
bridge excludes completion. Across the rosters the act is fixed while the
productive description "g gives x" changes truth. -/
theorem invariants :
    configs.length = 16 ∧ ∀ k ∈ configs,
      (∀ effect ∈ [x, y],
        (Finset.univ.filter (actual effect)).card = 2 ∧ effect ≠ g ∧
        (∃ c b, effects effect c b () ∧ ∀ c' b' r,
          effects effect c' b' r → c' = c ∧ b' = b ∧ r = ()) ∧
        operationOf k effect give g ∧
        ¬ moved effect g () ∧ ¬ potency effect g ∧
        moved effect effect () ∧ potency effect effect ∧
        (∀ b, actual effect b → ∃ o, operationOf k effect o b) ∧
        (givesX effect ↔ actual effect x) ∧
        (Dichotomy k effect ↔ k.immanent = true) ∧
        (root k effect ∧ k.identity = true ∧ bridge k effect → ¬ actGround k)) ∧
      actRef k x = actRef k y ∧ terminus x ≠ terminus y ∧ givesX x ∧ ¬ givesX y := by
  unfold Dichotomy OperationFromSelfOrAsMoved operationOf intrinsic moved bridge root ground
    actGround givesX terminus potency
  unfold actual effects
  decide

/-- The five selected controls, in both rosters. -/
theorem controls : ∀ effect ∈ [(1 : Fin 3), 2],
    (root ⟨true, false, true, false⟩ effect ∧ bridge ⟨true, false, true, false⟩ effect) ∧
    (root ⟨true, false, true, true⟩ effect ∧ bridge ⟨true, false, true, true⟩ effect) ∧
    (¬ root ⟨true, true, true, false⟩ effect ∧ bridge ⟨true, true, true, false⟩ effect) ∧
    (root ⟨true, true, false, false⟩ effect ∧ ¬ bridge ⟨true, true, false, false⟩ effect) ∧
    (root ⟨false, true, true, false⟩ effect ∧ bridge ⟨false, true, true, false⟩ effect) := by
  unfold bridge root ground actGround actual
  decide

end Denomination

/-! ## 3. Fixed due scope (four variants)

Determinations esse, active efficacy and life, all pure and all of being
(`Pure = OfBeing` is stipulated). The source has esse and active efficacy;
the switches say whether it has life and whether life is due to it. -/

namespace DueScope

/-- If every due determination is possessed and every pure determination is
due, every pure determination is possessed. The converse needs the separate
premise that possessed pure determinations are due. -/
theorem fullFromDue {D : Type} (Pure Has Due : D → Prop)
    (hDue : ∀ d, Due d → Has d) (hPure : ∀ d, Pure d → Due d) : ∀ d, Pure d → Has d :=
  fun d hd => hDue d (hPure d hd)

def has (hasLife : Bool) (d : Fin 3) : Bool := d != 2 || hasLife
def due (dueLife : Bool) (d : Fin 3) : Bool := d != 2 || dueLife
def all (p : Fin 3 → Bool) : Bool := (List.finRange 3).all p

abbrev g : Fin 2 := 0
abbrev x : Fin 2 := 1

def actual : List (Fin 2) := [g, x]
def ground (a b : Fin 2) : Prop := a = g ∧ b = x
def ownBeing (b : Fin 2) : Prop := b = g
def passivePotency (b : Fin 2) : Prop := b = x
def hasX (_ : Fin 3) : Bool := true
def produces (a b : Fin 2) (_ : Fin 3) : Prop := a = g ∧ b = x
def pureInventory (_ : Fin 3) : Bool := true
def ofBeing (_ : Fin 3) : Bool := true

def noDueMissing (h u : Bool) : Bool := all fun d => !due u d || has h d
def pureDue (u : Bool) : Bool := all fun d => !pureInventory d || due u d
def full (h : Bool) : Bool := all fun d => !pureInventory d || has h d
def wholePower (h : Bool) : Bool := all fun d => !ofBeing d || has h d
def possessedPureDue (h u : Bool) : Bool :=
  all fun d => !(pureInventory d && has h d) || due u d

theorem variants :
    (g ∈ actual ∧ x ∈ actual ∧ g ≠ x ∧ actual.length = 2 ∧
      ground g x ∧ (∀ a, ¬ ground a g) ∧ ownBeing g ∧
      ¬ passivePotency g ∧ passivePotency x ∧
      ∀ d, hasX d = true ∧ produces g x d ∧
        ∀ a b, produces a b d → a ∈ actual ∧ b ∈ actual ∧ b = x ∧ hasX d = true) ∧
    (∀ h u : Bool,
      (∀ d, (has h d → pureInventory d) ∧ (pureInventory d → ofBeing d)) ∧
      full h = wholePower h ∧
      (!(noDueMissing h u && pureDue u) || full h) = true ∧
      (!(noDueMissing h u && possessedPureDue h u) || full h == pureDue u) = true) ∧
    (noDueMissing false false ∧ !full false) = true ∧
    (!noDueMissing false true ∧ !full false) = true ∧
    (noDueMissing true true ∧ full true) = true ∧
    (full true ∧ !pureDue false) = true := by
  unfold actual ground ownBeing passivePotency produces
  decide

end DueScope

/-! ## 4. Ancestral coverage versus joint explanatory completeness

Projected reachability fires a support group when any input is reached;
full closure fires it only when all inputs are. Nodes: N, E (seeds); A, C
agents; X organization; H circumstances; O operating procedure; I intellect;
T original standing; D directed obligation; U rational uptake; P joint target;
K, J the cognitive and normative grounds. -/

namespace Coverage

inductive Node | N | E | A | C | X | H | O | I | T | D | U | P | K | J
  deriving DecidableEq

open Node

abbrev Group := List Node × Node

def fires (conjunctive : Bool) (seen : List Node) (inputs : List Node) : Bool :=
  if conjunctive then inputs.all seen.contains else inputs.any seen.contains

def step (conjunctive : Bool) (groups : List Group) (seen : List Node) : List Node :=
  seen ++ (groups.filter fun (xs, y) => fires conjunctive seen xs && !seen.contains y).map (·.2)

/-- Fourteen rounds saturate, since each unsaturated round adds a node. -/
def closure (conjunctive : Bool) (groups : List Group) (seeds : List Node) : List Node :=
  (step conjunctive groups)^[14] seeds

def common : List Group :=
  [A, C, X, H, O].map (fun y => ([N, E], y)) ++
    [([A, X, K], I), ([C, J], T), ([A, C, H, T, J], D), ([A, I, K, O], U), ([U, D], P)]

/-- `k`, `j`: the cognitive and normative grounds are source-based. -/
def groups (k j : Bool) : List Group :=
  common ++ (if k then [([N], K)] else []) ++ (if j then [([N], J)] else [])
def external (k j : Bool) : List Node := (if k then [] else [K]) ++ (if j then [] else [J])

def reach (k j : Bool) := closure false (groups k j) [N, E]
def full (k j : Bool) := closure true (groups k j) [N, E]
def total (k j : Bool) := closure true (groups k j) ([N, E] ++ external k j)

/-- Projected paths reach the joint target in all four rows, and adding the
external grounds restores the complete account; full source support of the
joint target holds iff both grounds are source-based. -/
theorem rows : ∀ k j : Bool,
    [A, C, I, T, D, U, P].all (reach k j).contains ∧
    [A, C, I, T, D, U, P].all (total k j).contains ∧
    (full k j).contains I = k ∧ (full k j).contains U = k ∧
    (full k j).contains T = j ∧ (full k j).contains D = j ∧
    (full k j).contains P = (k && j) := by
  decide +kernel

end Coverage

end TruthCore.Causality.PerfectionTransferControls
