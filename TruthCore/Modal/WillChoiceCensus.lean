module

public import TruthCore.Modal.OptimalCreationChoice

/-!
# Finite complete-output quality controls

The eight outputs are subsets of three recipients, encoded by three bits
in order d, a, b. The rank assignments are base-three tables. These ranks
are stipulated structural data for the will-versus-chance comparison.
-/

@[expose] public section

namespace TruthCore.Modal.WillChoiceCensus

open TruthCore.Modal.OptimalCreationChoice (Optimal)

abbrev Output := Fin 8

def includes (s : Output) (recipient : Fin 3) : Bool := s.val.testBit recipient.val

def quality (s : Output) : Nat :=
  2 * (includes s 0).toNat + (includes s 1 != includes s 2).toNat

def outputs : List Output := List.finRange 8

def optimal (q : Output → Nat) (s : Output) : Bool :=
  outputs.all fun t => decide (q t ≤ q s)

theorem optimal_iff (q : Output → Nat) (s : Output) :
    optimal q s = true ↔ Optimal Set.univ q s := by
  simp [optimal, outputs, Optimal, IsGreatest, upperBounds]

def improvement (q : Output → Nat) : Bool :=
  outputs.all fun s => includes s 0 || outputs.any fun t => decide (q s < q t)

def core (q : Output → Nat) : Bool :=
  outputs.all fun s => !optimal q s || includes s 0

theorem tiedOptima :
    outputs.filter (optimal quality) = [3, 5] ∧
    improvement quality = true ∧ core quality = true ∧
    (outputs.filter (optimal quality)).any (fun s => !includes s 1) = true ∧
    0 ∈ outputs ∧ 2 ∈ outputs := by
  decide +kernel

def ranking (n : Nat) (s : Output) : Nat := n / (3 ^ s.val) % 3

def censusCounts : Nat × Nat :=
  (List.range 81).foldl (fun total block =>
    (List.range 81).foldl (fun (agreed, triggered) i =>
      let q := ranking (block * 81 + i)
      let improves := improvement q
      (agreed + (improves == core q).toNat, triggered + improves.toNat))
      total) (0, 0)

set_option maxRecDepth 4096 in
theorem census : 81 * 81 = 6561 ∧ censusCounts = (6561, 1055) := by
  decide +kernel

/-- The same permission table admits both exercises. Only the latter exercises
omit d at one of the two accessible positions. -/
theorem omission :
    let permitted := outputs
    let bothGive : List Output := [3, 5]
    let omission : List Output := [3, 2]
    (0 ∈ permitted ∧ 2 ∈ permitted) ∧
    bothGive.all (permitted.contains) = true ∧ omission.all (permitted.contains) = true ∧
    bothGive.all (fun s => includes s 0) = true ∧
    omission.all (fun s => includes s 0) = false ∧
    bothGive.all (optimal quality) = true ∧ omission.all (optimal quality) = false := by
  decide +kernel

end TruthCore.Modal.WillChoiceCensus
