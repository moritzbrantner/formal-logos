module

public import TruthCore.Logic.FixedPointSelection

/-! Two-element controls for fixed points, classification, uniform witnesses,
restricted fibers and the distinction between factivity and modal sufficiency. -/

@[expose] public section
namespace TruthCore.Logic.InterfaceFiniteControls

abbrev Table := Bool → Bool

def maps : List Table :=
  (List.range 4).map fun mask s => mask.testBit s.toNat

def relations : List (Bool → Bool → Bool) :=
  (List.range 16).map fun mask i x => mask.testBit (2 * i.toNat + x.toNat)

def fixedCases : List (Table × Table × Table × Bool) :=
  maps.flatMap fun tr => maps.flatMap fun mv => maps.flatMap fun sel =>
    [false, true].map fun e => (tr, mv, sel, e)

def fixedEligible (tr mv sel : Table) (e : Bool) : Bool :=
  tr e == e && sel (tr e) == mv (sel e)

theorem fixedSelector :
    (fixedCases.filter fun (tr, mv, sel, e) => fixedEligible tr mv sel e).length = 32 ∧
    ∀ tr mv sel : Table, ∀ e, fixedEligible tr mv sel e = true → mv (sel e) = sel e := by
  refine ⟨by decide +kernel, ?_⟩
  intro tr mv sel e h
  simp only [fixedEligible, Bool.and_eq_true, beq_iff_eq] at h
  exact FixedPointSelection.fixed_output sel mv h.1 h.2

def uniqueCases : List (Table × Table × Bool) :=
  maps.flatMap fun mv => maps.flatMap fun p => [false, true].map fun h => (mv, p, h)

def uniqueEligible (mv p : Table) (h : Bool) : Bool :=
  p h && decide (∀ x, p x = true → x = h) && decide (∀ x, p x = true → p (mv x) = true)

theorem uniqueClosed :
    (uniqueCases.filter fun (mv, p, h) => uniqueEligible mv p h).length = 4 ∧
    ∀ mv p : Table, ∀ h, uniqueEligible mv p h = true → mv h = h := by
  refine ⟨by decide +kernel, ?_⟩
  intro mv p h eligible
  simp only [uniqueEligible, Bool.and_eq_true, decide_eq_true_eq] at eligible
  exact FixedPointSelection.unique_closed_fixed (fun x => p x = true) mv h
    eligible.1.1 eligible.1.2 eligible.2

def mapPairs : List (Table × Table) := maps.flatMap fun a => maps.map (a, ·)

def invariant (obs p : Table) : Bool :=
  decide (∀ a b, obs a = obs b → p a = p b)

def factors (obs p : Table) : Bool :=
  maps.any fun c => decide (∀ s, c (obs s) = p s)

theorem classification :
    mapPairs.length = 16 ∧
    (mapPairs.filter fun (obs, p) => !invariant obs p).length = 4 ∧
    mapPairs.all (fun (obs, p) => invariant obs p == factors obs p) = true := by
  decide +kernel

def localWitness (r : Bool → Bool → Bool) : Bool := decide (∀ i, ∃ x, r i x = true)
def uniformWitness (r : Bool → Bool → Bool) : Bool := decide (∃ x, ∀ i, r i x = true)

theorem witnessScope :
    relations.length = 16 ∧
    (relations.filter fun r => localWitness r && !uniformWitness r).length = 2 ∧
    relations.all (fun r => !uniformWitness r || localWitness r) = true ∧
    localWitness (fun i x => i == x) ∧ ¬ uniformWitness (fun i x => i == x) ∧
    localWitness (fun i x => i != x) ∧ ¬ uniformWitness (fun i x => i != x) := by
  decide +kernel

def fiberCases : List (Table × Table × Table × (Bool → Bool → Bool)) :=
  maps.flatMap fun allow => maps.flatMap fun obs => maps.flatMap fun pos =>
    relations.map fun truth => (allow, obs, pos, truth)

def fiberTest (allow obs pos : Table) (truth : Bool → Bool → Bool) : Bool :=
  let inside := fun i => allow i && pos (obs i)
  let holds := fun i => truth (obs i) i
  let sound := decide (∀ i, inside i = true → holds i = true)
  let uniform := decide (∀ i j, inside i = true → inside j = true →
    obs i = obs j → holds i = holds j)
  let witnesses := decide (∀ i, inside i = true →
    ∃ j, inside j = true ∧ obs i = obs j ∧ holds j = true)
  sound == (uniform && witnesses)

theorem restrictedFibers :
    fiberCases.length = 1024 ∧
    fiberCases.all (fun (allow, obs, pos, truth) => fiberTest allow obs pos truth) = true := by
  decide +kernel

def sufficient (a b : Table) : Bool := decide (∀ v, a v = true → b v = true)
def always (a : Table) : Bool := a false && a true

theorem modalScope :
    mapPairs.all (fun (a, b) => !(always a && sufficient a b) || always b) = true ∧
    (mapPairs.filter fun (a, b) => a false && b false && !sufficient a b).length = 1 := by
  decide +kernel

end TruthCore.Logic.InterfaceFiniteControls
