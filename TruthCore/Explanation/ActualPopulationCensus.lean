module

public import TruthCore.Explanation.ActualPopulationApplications

/-!
# Finite censuses of the actual-population applications

Finite diagnostics for `docs/notes/unconditional-corpus-closure.md`. The
evaluated world is `0`; there are two world labels. The Boolean evaluators
are proved to coincide with the corpus predicates, so the censuses count
models of those predicates. The general results are
`ActualPopulationApplications.possibleFromActual` and
`ActualPopulationApplications.necessaryOrContingentFromActual`.
-/

@[expose] public section

namespace TruthCore.Explanation.ActualPopulationCensus

open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Explanation.EmptyHistoryCausalAvailability (PossiblyInhabitedConcreteAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)

def worlds : List (Fin 2) := List.finRange 2

/-- Existence and accessibility tables, with no causal edges. -/
def ontic {E : Type} (exists_ : Fin 2 → E → Bool) (access : Fin 2 → Fin 2 → Bool) :
    Ontic (Fin 2) E :=
  ⟨⟨fun w v => access w v = true⟩, fun v x => exists_ v x = true, fun _ _ _ => False⟩

/-! ## One candidate: actual population supplies possible population -/

/-- A concreteness bit, existence at the two worlds, and four access edges. -/
structure Single where
  concrete : Bool
  exists_ : Fin 2 → Bool
  access : Fin 2 → Fin 2 → Bool

namespace Single

variable (s : Single)

def model : Ontic (Fin 2) Unit := ontic (fun v _ => s.exists_ v) s.access
def arena : Arena (Fin 2) Unit Unit :=
  ⟨s.model, fun _ _ => True, fun _ => (), fun _ _ _ => False, fun _ _ => False⟩
def Concrete (_ : Unit) : Prop := s.concrete = true
def profile : Profile (Fin 2) Unit := ⟨s.model, s.Concrete, fun _ _ _ => False⟩

def actual : Bool := s.concrete && s.exists_ 0
def reflexive : Bool := s.access 0 0
def possible : Bool := worlds.any fun v => s.access 0 v && s.concrete && s.exists_ v
def contingent : Bool := s.actual && worlds.any fun v => s.access 0 v && !s.exists_ v
def necessary : Bool := worlds.all fun v => !s.access 0 v || s.exists_ v

theorem actual_iff : s.actual = true ↔ InhabitedConcreteAt s.model s.Concrete 0 := by
  simp [actual, InhabitedConcreteAt, Concrete, model, ontic]

theorem reflexive_iff : s.reflexive = true ↔ ActualReflexive s.model 0 := by
  simp [reflexive, ActualReflexive, model, ontic]

theorem possible_iff : s.possible = true ↔ PossiblyInhabitedConcreteAt s.arena s.Concrete 0 := by
  simp [possible, worlds, PossiblyInhabitedConcreteAt, InhabitedConcreteAt, Concrete, arena,
    model, ontic, and_assoc]

theorem contingent_iff : s.contingent = true ↔ SomeActualContingentAt s.profile 0 := by
  simp [contingent, actual, worlds, SomeActualContingentAt, ContingentAt, Concrete, profile,
    model, ontic, and_assoc]

theorem necessary_iff : s.necessary = true ↔ NecessaryAt s.model 0 () := by
  simp only [necessary, worlds, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', NecessaryAt, model, ontic]
  constructor
  · intro h v hv
    exact (h v).resolve_left (by simp [hv])
  · intro h v
    cases hv : s.access 0 v
    · exact Or.inl rfl
    · exact Or.inr (h v hv)

end Single

def bitLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitLists n).flatMap fun bs => [false :: bs, true :: bs]

def vector (bs : List Bool) : Fin 2 → Bool := fun x => bs.getD x.val false
def table (bs : List Bool) : Fin 2 → Fin 2 → Bool := fun w v => bs.getD (2 * w.val + v.val) false

/-- All 128 single-candidate assignments. -/
def singles : List Single :=
  [false, true].flatMap fun c => (bitLists 2).flatMap fun e =>
    (bitLists 4).map fun a => ⟨c, vector e, table a⟩

/-- Every forward implication holds and all four separation controls occur:
reflexivity cannot be omitted, actual population cannot be omitted, possible
population does not give actual population back, and actual reflexive
population with necessity does not give contingency. -/
theorem singleCensus :
    singles.length = 128 ∧
    singles.all (fun s => !(s.actual && s.reflexive) || s.possible) ∧
    singles.all (fun s => !s.contingent || s.actual) ∧
    singles.all (fun s => !(s.contingent && s.necessary)) ∧
    singles.any (fun s => s.actual && !s.reflexive && !s.possible) ∧
    singles.any (fun s => s.reflexive && !s.actual && !s.possible) ∧
    singles.any (fun s => s.possible && s.reflexive && !s.actual) ∧
    singles.any (fun s => s.actual && s.reflexive && s.necessary && !s.contingent) := by
  decide +kernel

/-! ## Two candidates: population is necessary or contingent population -/

structure Pair where
  concrete : Fin 2 → Bool
  /-- `exists_ v x`: candidate `x` exists at world `v`. -/
  exists_ : Fin 2 → Fin 2 → Bool
  access : Fin 2 → Fin 2 → Bool

namespace Pair

variable (s : Pair)

def profile : Profile (Fin 2) (Fin 2) :=
  ⟨ontic s.exists_ s.access, fun x => s.concrete x = true, fun _ _ _ => False⟩

def present (x : Fin 2) : Bool := s.concrete x && s.exists_ 0 x
def population : Bool := worlds.any s.present
def necessaryPopulation : Bool :=
  worlds.any fun x => s.present x && worlds.all fun v => !s.access 0 v || s.exists_ v x
def contingentPopulation : Bool :=
  worlds.any fun x => s.present x && worlds.any fun v => s.access 0 v && !s.exists_ v x

theorem population_iff :
    s.population = true ↔ InhabitedConcreteAt s.profile.ontic s.profile.concrete 0 := by
  simp [population, present, worlds, InhabitedConcreteAt, profile, ontic]

theorem necessaryPopulation_iff : s.necessaryPopulation = true ↔ NecessaryConcreteAt s.profile 0 := by
  simp only [necessaryPopulation, present, worlds, List.any_eq_true, List.all_eq_true,
    List.mem_finRange, true_and, true_implies, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', NecessaryConcreteAt, NecessaryAt, profile, ontic, and_assoc]
  constructor
  · rintro ⟨x, hc, he, h⟩
    exact ⟨x, hc, he, fun v hv => (h v).resolve_left (by simp [hv])⟩
  · rintro ⟨x, hc, he, h⟩
    refine ⟨x, hc, he, fun v => ?_⟩
    cases hv : s.access 0 v
    · exact Or.inl rfl
    · exact Or.inr (h v hv)

theorem contingentPopulation_iff :
    s.contingentPopulation = true ↔ SomeActualContingentAt s.profile 0 := by
  simp [contingentPopulation, present, worlds, SomeActualContingentAt, ContingentAt, profile,
    ontic, and_assoc]

end Pair

/-- All 1,024 two-candidate profiles. -/
def pairs : List Pair :=
  (bitLists 2).flatMap fun c => (bitLists 4).flatMap fun e =>
    (bitLists 4).map fun a => ⟨vector c, table e, table a⟩

/-- Population is equivalent to necessary-or-contingent population. Among
populated profiles both exclusive horns and their coexistence occur, and
population without a necessary individual always supplies contingency. -/
theorem pairCensus :
    pairs.length = 1024 ∧
    pairs.all (fun s => s.population == (s.necessaryPopulation || s.contingentPopulation)) ∧
    pairs.all (fun s => !(s.population && !s.necessaryPopulation) || s.contingentPopulation) ∧
    pairs.any (fun s => s.population && s.necessaryPopulation && !s.contingentPopulation) ∧
    pairs.any (fun s => s.population && !s.necessaryPopulation && s.contingentPopulation) ∧
    pairs.any (fun s => s.population && s.necessaryPopulation && s.contingentPopulation) := by
  decide +kernel

end TruthCore.Explanation.ActualPopulationCensus
