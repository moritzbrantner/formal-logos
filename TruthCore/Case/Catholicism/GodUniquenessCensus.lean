module

public import TruthCore.Case.Catholicism.MaximalBeingCauseExclusion
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
public import TruthCore.Causality.GodMaximalCausal
public import TruthCore.Causality.TermSenseForks3

/-!
# Exhaustive two-carrier census of the genus-free uniqueness bundles

Finite diagnostics for `docs/notes/root-route-modal-load.md` §§1, 3 and 5.
Every structure enumerated in §§1 and 5 has two carriers and one respect (esse). A structure fixes
which carriers are God and actual, and the `MoreIn` and `CausesIn` tables;
`more y x` reads "`y` is more in being than `x`". The Boolean evaluators below
are proved to coincide with the corpus definitions, so the counts are counts
of models of those definitions, not of a separate encoding.

The counts describe this small encoding. The general §1 entailment is
`GodIsOneFromEsse.oneFromWitness`; the named omission controls are
`GodIsOneFromEsse.controls`. In §5, `fifthCensus` checks the conjunction of
uniqueness and actual-bearer God-causality at finite scope.
`AttributesFromEsse.oneFromSource` gives general uniqueness under all-respects
causal ascent and excluded middle.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.GodUniquenessCensus

open TruthCore.Case.Catholicism
open TruthCore.Causality.GodMaximalCausal (GodCausesBeingOfAllOthers)
open TruthCore.Causality.TermSenseForks (SomeBeingMaximalInBeing)
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- A two-carrier structure at the single respect esse. -/
structure Two where
  god : Fin 2 → Bool
  act : Fin 2 → Bool
  more : Fin 2 → Fin 2 → Bool
  causes : Fin 2 → Fin 2 → Bool

namespace Two

variable (s : Two)

def IsGod (x : Fin 2) : Prop := s.god x = true
def InAct (x : Fin 2) (_ : Unit) : Prop := s.act x = true
def MoreIn (_ : Unit) (y x : Fin 2) : Prop := s.more y x = true
def CausesIn (c x : Fin 2) (_ : Unit) : Prop := s.causes c x = true

def carriers : List (Fin 2) := List.finRange 2

def maximal (m : Fin 2) : Bool := s.act m && carriers.all fun y => !s.more y m
/-- `U(m)`: `m` causes the being of every distinct actual carrier. -/
def universal (m : Fin 2) : Bool :=
  carriers.all fun x => x == m || !s.act x || s.causes m x

def exclusion : Bool :=
  carriers.all fun m => !s.maximal m || carriers.all fun c => c == m || !s.causes c m
def maximumExists : Bool := carriers.any s.maximal
def converse : Bool :=
  carriers.all fun g => !s.god g || carriers.all fun y => y == g || s.causes g y
def someGod : Bool := carriers.any s.god
def atMostOneGod : Bool :=
  carriers.all fun g => carriers.all fun k => !s.god g || !s.god k || k == g
def twoMaxima : Bool := (carriers.filter s.maximal).length == 2

def sourceExists : Bool := carriers.any fun m => s.maximal m && s.universal m
def ascent : Bool :=
  carriers.all fun c => carriers.all fun x => c == x || !s.causes c x || s.more c x
def godsMaximal : Bool := carriers.all fun g => !s.god g || s.maximal g
def godsUniversal : Bool := carriers.all fun g => !s.god g || s.universal g

/-! ### The evaluators are the corpus definitions -/

theorem maximal_iff (m : Fin 2) :
    s.maximal m = true ↔ IsMaximumIn s.InAct s.MoreIn () m := by
  simp [maximal, carriers, IsMaximumIn, InAct, MoreIn, List.all_eq_true]

theorem universal_iff (m : Fin 2) :
    s.universal m = true ↔ CausesAllInGenus s.InAct s.CausesIn () m := by
  simp only [universal, carriers, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', CausesAllInGenus, InAct, CausesIn]
  constructor
  · intro h x hx ha
    rcases h x with (h | h) | h
    · exact absurd h hx
    · simp [ha] at h
    · exact h
  · intro h x
    by_cases hx : x = m
    · exact Or.inl (Or.inl hx)
    · cases ha : s.act x
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (h x hx ha)

theorem exclusion_iff :
    s.exclusion = true ↔ MaximumHasNoDistinctEsseCause s.InAct s.MoreIn s.CausesIn () := by
  simp only [exclusion, carriers, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', MaximumHasNoDistinctEsseCause, ← maximal_iff,
    CausesIn]
  constructor
  · intro h m hm c hc hcause
    rcases h m with h | h
    · simp [hm] at h
    · rcases h c with h | h
      · exact hc h
      · simp [hcause] at h
  · intro h m
    cases hm : s.maximal m
    · exact Or.inl rfl
    · exact Or.inr fun c => by
        by_cases hc : c = m
        · exact Or.inl hc
        · exact Or.inr (Bool.eq_false_iff.mpr (h m hm c hc))

theorem maximumExists_iff :
    s.maximumExists = true ↔ SomeBeingMaximalInBeing s.InAct s.MoreIn () := by
  simp [maximumExists, carriers, SomeBeingMaximalInBeing, IsMaximalIn, ← maximal_iff]

theorem converse_iff : s.converse = true ↔ GodCausesBeingOfAllOthers s.IsGod s.CausesIn () := by
  simp only [converse, carriers, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', GodCausesBeingOfAllOthers, IsGod, CausesIn]
  constructor
  · intro h g y hg hy
    rcases h g with h | h
    · simp [hg] at h
    · exact (h y).resolve_left hy
  · intro h g
    cases hg : s.god g
    · exact Or.inl rfl
    · exact Or.inr fun y => by
        by_cases hy : y = g
        · exact Or.inl hy
        · exact Or.inr (h g y hg hy)

theorem atMostOneGod_iff : s.atMostOneGod = true ↔ GodIsOne s.IsGod := by
  simp only [atMostOneGod, carriers, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', GodIsOne, IsTheOneGod, IsGod]
  constructor
  · intro h g hg k hk
    rcases h g k with (h | h) | h
    · simp [hg] at h
    · simp [hk] at h
    · exact h
  · intro h g k
    cases hg : s.god g
    · exact Or.inl (Or.inl rfl)
    · cases hk : s.god k
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (h g hg k hk)

theorem sourceExists_iff :
    s.sourceExists = true ↔ MaximeEnsCausesBeingOfAllReading s.InAct s.MoreIn s.CausesIn () := by
  simp [sourceExists, carriers, MaximeEnsCausesBeingOfAllReading, ← maximal_iff, ← universal_iff]

theorem ascent_iff : s.ascent = true ↔ CauseOfBeingIsMoreInBeing s.CausesIn s.MoreIn () := by
  simp only [ascent, carriers, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', CauseOfBeingIsMoreInBeing, CausesIn, MoreIn]
  constructor
  · intro h c x hcx hc
    rcases h c x with (h | h) | h
    · exact absurd h hcx
    · simp [hc] at h
    · exact h
  · intro h c x
    by_cases hcx : c = x
    · exact Or.inl (Or.inl hcx)
    · cases hc : s.causes c x
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (h c x hcx hc)

theorem godsMaximal_iff :
    s.godsMaximal = true ↔ GodIsMaximalInBeing s.IsGod s.InAct s.MoreIn () := by
  simp only [godsMaximal, carriers, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', GodIsMaximalInBeing, IsGod, ← maximal_iff]
  constructor
  · intro h g hg
    exact (h g).resolve_left (by simp [hg])
  · intro h g
    cases hg : s.god g
    · exact Or.inl rfl
    · exact Or.inr (h g hg)

theorem godsUniversal_iff :
    s.godsUniversal = true ↔ ∀ g, s.IsGod g → CausesAllInGenus s.InAct s.CausesIn () g := by
  simp only [godsUniversal, carriers, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', IsGod, ← universal_iff]
  constructor
  · intro h g hg
    exact (h g).resolve_left (by simp [hg])
  · intro h g
    cases hg : s.god g
    · exact Or.inl rfl
    · exact Or.inr (h g hg)

end Two

/-! ### Enumeration -/

def bitLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitLists n).flatMap fun bs => [false :: bs, true :: bs]

def vector (bs : List Bool) : Fin 2 → Bool := fun x => bs.getD x.val false
def table (bs : List Bool) : Fin 2 → Fin 2 → Bool := fun y x => bs.getD (2 * y.val + x.val) false

/-- All 4096 structures: two God bits, two actuality bits and two 2×2 tables. -/
def structures : List Two :=
  (bitLists 2).flatMap fun g => (bitLists 2).flatMap fun a =>
    (bitLists 4).flatMap fun m => (bitLists 4).map fun c =>
      ⟨vector g, vector a, table m, table c⟩

/-! ### §1. Exclusion, maximal existence and the carrier-wide converse -/

def firstJoint (s : Two) : Bool := s.exclusion && s.maximumExists && s.converse

/-- Two Gods while every premise except the `i`th holds (exclusion, maximal
existence, causal converse). -/
def firstOmission (i : Fin 3) (s : Two) : Bool :=
  let premises := [s.exclusion, s.maximumExists, s.converse]
  !s.atMostOneGod && !premises[i]! &&
    (List.finRange 3).all fun j => j == i || premises[j]!

/-- The §1 census: 172 joint models, 56 with a God, none with two Gods or with a
God and two maxima. Dropping one premise admits 60, 196 and 116 two-God models. -/
theorem firstCensus :
    structures.length = 4096 ∧
    (structures.filter firstJoint).length = 172 ∧
    (structures.filter fun s => firstJoint s && s.someGod).length = 56 ∧
    (structures.filter fun s => firstJoint s && !s.atMostOneGod).length = 0 ∧
    (structures.filter fun s => firstJoint s && s.someGod && s.twoMaxima).length = 0 ∧
    (structures.filter (firstOmission 0)).length = 60 ∧
    (structures.filter (firstOmission 1)).length = 196 ∧
    (structures.filter (firstOmission 2)).length = 116 := by
  decide +kernel

/-! ### §5. Actual universal source, causal ascent at esse and God-maximality -/

def fifthJoint (s : Two) : Bool := s.sourceExists && s.ascent && s.godsMaximal
def fifthConclusion (s : Two) : Bool := s.atMostOneGod && s.godsUniversal

/-- The joint conclusion fails while every premise except the `i`th holds
(actual universal source, ascent, God-maximality). -/
def fifthOmission (i : Fin 3) (s : Two) : Bool :=
  let premises := [s.sourceExists, s.ascent, s.godsMaximal]
  !fifthConclusion s && !premises[i]! &&
    (List.finRange 3).all fun j => j == i || premises[j]!

/-- The §5 census: all 128 joint models satisfy at-most-one-God together with
actual-recipient God causality; 64 have a God. The omission counts refer to the
joint conclusion. The carrier-wide converse fails in 32 joint models. -/
theorem fifthCensus :
    (structures.filter fifthJoint).length = 128 ∧
    (structures.filter fun s => fifthJoint s && s.someGod).length = 64 ∧
    (structures.filter fun s => fifthJoint s && !fifthConclusion s).length = 0 ∧
    (structures.filter (fifthOmission 0)).length = 36 ∧
    (structures.filter (fifthOmission 1)).length = 20 ∧
    (structures.filter (fifthOmission 2)).length = 128 ∧
    (structures.filter fun s => fifthJoint s && !s.converse).length = 32 := by
  decide +kernel

/-! ### §3. Genus causality and the God-specific converse are independent

Two carriers and two respects (`true` is esse). God is carrier `true`. -/

def godTrue (x : Bool) : Prop := x = true
def noRelation (_ : Bool) (_ _ : Bool) : Prop := False
def noCause (_ _ : Bool) (_ : Bool) : Prop := False

/-- Only the God is actual, and only at esse. Genus causality holds vacuously
for distinct actual bearers and God is maximal with causal superiority, but the
God-specific converse fails at the nonactual carrier `false`. -/
def actualGodOnly (x r : Bool) : Prop := x = true ∧ r = true

/-- Both carriers are actual at both respects. At esse the God is more and
causes the other; at the second respect nothing is more and nothing causes.
The converse, God-maximality and causal superiority hold; genus causality fails
at the second respect, where both actual carriers are maxima with no causes. -/
def allActual (_ _ : Bool) : Prop := True
def aboveAtEsse (r c x : Bool) : Prop := r = true ∧ c = true ∧ x = false
def causesAtEsse (c x r : Bool) : Prop := aboveAtEsse r c x

def Independence : Prop :=
  (MaximumInGenusCausesAllInGenusReading actualGodOnly noRelation noCause ∧
    GodIsMaximalInBeing godTrue actualGodOnly noRelation true ∧
    CauseOfQualityInAnotherIsMoreSuchReading noCause noRelation ∧ godTrue true ∧
    ¬ GodCausesBeingOfAllOthers godTrue noCause true) ∧
  (GodCausesBeingOfAllOthers godTrue causesAtEsse true ∧
    GodIsMaximalInBeing godTrue allActual aboveAtEsse true ∧
    CauseOfQualityInAnotherIsMoreSuchReading causesAtEsse aboveAtEsse ∧ godTrue true ∧
    ¬ MaximumInGenusCausesAllInGenusReading allActual aboveAtEsse causesAtEsse)

theorem independence : Independence := by
  dsimp only [Independence, MaximumInGenusCausesAllInGenusReading, GodIsMaximalInBeing,
    CauseOfQualityInAnotherIsMoreSuchReading, GodCausesBeingOfAllOthers, CausesAllInGenus,
    IsMaximumIn, godTrue, noRelation, noCause, actualGodOnly, allActual, aboveAtEsse,
    causesAtEsse]
  and_intros <;> decide

end TruthCore.Case.Catholicism.GodUniquenessCensus
