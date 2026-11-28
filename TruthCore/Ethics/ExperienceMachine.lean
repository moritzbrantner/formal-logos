module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Basic
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
public import TruthCore.Logic.StrengthComparison

/-!
# The experience machine as a test of the q.5 desirability premise

Analyst formulations, attribution deferred (owner direction 2026-11-05 and the
exhibit map of 2026-11-28). The thought experiment is used as a concrete test of
implicit principles: two lives with the same experiential profile, one with real
perfections (achievement, friendship, knowledge of what is) and one without.

Vocabulary. `Being` is reused from ST I q.5 a.1
(`TruthCore.Latin.Aquinas.SummaTheologiae`); in the case its elements are lives,
a person living a life, so a perfection of the life is a perfection of the same
bearer whose desirability is assessed. `DesirableIn` and `PerfectIn` are the q.5
parameters, with `PerfectIn` in sense PERFECT_1. Three parameters are new:

* `experience : Being → Profile`: the experiential profile of a bearer, how its
  life is from the inside (DEF "Experiential profile of a life"). It is a
  primitive: nothing here says what a profile contains beyond the fact that two
  lives can share one.
* `BetterFor : Being → Being → Prop`: the life `x` is better for its subject than
  the life `y`, the person-level comparison that the stay-out verdict reports
  (DEF "Better for its subject"). It is distinct from `DesirableIn`; the two are
  related only by the explicit transfer statements below.

The rival is experientialism: desirability in each respect is fixed by the
bearer's experiential profile. It is encoded with Mathlib's
`Function.FactorsThrough` (the desirability profile `DesirableIn x` factors
through `experience`), and `experientialism_iff_factor` shows the positive form:
there is a valuation of profiles that fixes desirability in every respect.
Hedonism proper (only pleasantness counts) is one such valuation, not separately
encoded.

Nothing in this module asserts that any premise is true. The q.5 readings are
those of `Article1`; the case facts, the verdict and the transfer bridge are open
analyst premises.
-/

@[expose] public section

namespace TruthCore.Ethics.ExperienceMachine

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.StrengthComparison

/-- EXPERIENTIALISM (the experience requirement): a bearer's desirability in each
respect is fixed by its experiential profile, so two bearers with the same profile
are desirable in exactly the same respects. Encoded as Mathlib's
`Function.FactorsThrough`: the map `x ↦ DesirableIn x` factors through
`experience`. It is about the q.5 parameter `DesirableIn`, applied to lives of
experiencing subjects; it says nothing about how desirable any profile is. -/
def ExperientialismReading {Being Perfection Profile : Type}
    (experience : Being → Profile) (DesirableIn : Being → Perfection → Prop) : Prop :=
  Function.FactorsThrough DesirableIn experience

/-- The negation of experientialism for the given profile and desirability
relation: some two bearers with the same experiential profile differ in
desirability in some respect. -/
def ExperientialismFails {Being Perfection Profile : Type}
    (experience : Being → Profile) (DesirableIn : Being → Perfection → Prop) : Prop :=
  ¬ ExperientialismReading experience DesirableIn

/-- The perfections of bearers are fixed by their experiential profiles. Under
q.5's biconditional this is exactly what experientialism costs
(`ExperienceMachineComparison`, conjunct 2). -/
def PerfectionSupervenesOnExperience {Being Perfection Profile : Type}
    (experience : Being → Profile) (PerfectIn : Being → Perfection → Prop) : Prop :=
  Function.FactorsThrough PerfectIn experience

/-- Case fact: the real life and the machine life have the same experiential
profile. -/
def SameExperience {Being Profile : Type}
    (experience : Being → Profile) (real machine : Being) : Prop :=
  experience real = experience machine

/-- Case fact: the real life is perfect (PERFECT_1) in every respect in which the
machine life is, and in the respect `p` in which the machine life is not.
The machine life has no perfection the real life lacks; together with
`SameExperience` this isolates the difference to real perfections. -/
def RealPerfectionsExceed {Being Perfection : Type}
    (PerfectIn : Being → Perfection → Prop) (real machine : Being) (p : Perfection) : Prop :=
  (∀ q, PerfectIn machine q → PerfectIn real q) ∧ PerfectIn real p ∧ ¬ PerfectIn machine p

/-- The stay-out verdict: the real life is better for its subject than the machine
life. -/
def StayOutVerdict {Being : Type}
    (BetterFor : Being → Being → Prop) (real machine : Being) : Prop :=
  BetterFor real machine

/-- Transfer bridge from person-level welfare to the per-perfection reading: if a
life is better for its subject than another, there is a respect in which it is
desirable (q.5 `DesirableIn`) and the other is not. It identifies the respects
that ground person-level betterness with the q.5 respects of desirability, and it
leaves out betterness by degree within a shared respect. -/
def BetterRequiresRespectDifference {Being Perfection : Type}
    (BetterFor : Being → Being → Prop) (DesirableIn : Being → Perfection → Prop) : Prop :=
  ∀ x y, BetterFor x y → ∃ p, DesirableIn x p ∧ ¬ DesirableIn y p

/-- Converse transfer (respect dominance): a life desirable in every respect in
which another is, and in some respect in which the other is not, is better for its
subject. Used only inside `ExperienceMachineComparison`. -/
def RespectDominanceMakesBetter {Being Perfection : Type}
    (BetterFor : Being → Being → Prop) (DesirableIn : Being → Perfection → Prop) : Prop :=
  ∀ x y, (∀ q, DesirableIn y q → DesirableIn x q) →
    (∃ p, DesirableIn x p ∧ ¬ DesirableIn y p) → BetterFor x y

/-- Forward half of q.5's "desirable insofar as perfect" (PERFECT_1): whatever is
perfect in a respect is desirable in that respect. Aquinas' stated reason (*omnia
appetunt suam perfectionem*) bears on this half. -/
def PerfectMakesDesirableReading {Being Perfection : Type}
    (DesirableIn PerfectIn : Being → Perfection → Prop) : Prop :=
  ∀ x p, PerfectIn x p → DesirableIn x p

/-- Backward half of q.5's "desirable insofar as perfect" (PERFECT_1): whatever is
desirable in a respect is perfect in that respect. -/
def DesirableOnlyIfPerfectReading {Being Perfection : Type}
    (DesirableIn PerfectIn : Being → Perfection → Prop) : Prop :=
  ∀ x p, DesirableIn x p → PerfectIn x p

/-- Strength comparison: the biconditional against its forward half, with the
backward half as the proposed difference. No background. -/
def forwardComparison {Being Perfection : Type}
    (DesirableIn PerfectIn : Being → Perfection → Prop) : ComparisonSpec where
  stronger := DesirableInsofarAsPerfectReading DesirableIn PerfectIn
  weaker := PerfectMakesDesirableReading DesirableIn PerfectIn
  delta := DesirableOnlyIfPerfectReading DesirableIn PerfectIn

/-- Strength comparison: the biconditional against its backward half, with the
forward half as the proposed difference. No background. -/
def backwardComparison {Being Perfection : Type}
    (DesirableIn PerfectIn : Being → Perfection → Prop) : ComparisonSpec where
  stronger := DesirableInsofarAsPerfectReading DesirableIn PerfectIn
  weaker := DesirableOnlyIfPerfectReading DesirableIn PerfectIn
  delta := PerfectMakesDesirableReading DesirableIn PerfectIn

/-- The biconditional is exactly its forward half plus its backward half. -/
def ForwardExactDifference : Prop :=
  ∀ (Being Perfection : Type) (DesirableIn PerfectIn : Being → Perfection → Prop),
    Equivalence (forwardComparison DesirableIn PerfectIn)

/-- The biconditional is exactly its backward half plus its forward half. -/
def BackwardExactDifference : Prop :=
  ∀ (Being Perfection : Type) (DesirableIn PerfectIn : Being → Perfection → Prop),
    Equivalence (backwardComparison DesirableIn PerfectIn)

/-- Strict respect dominance, used as the betterness relation of the controls, so
that both transfer statements hold there by construction. -/
def Dominates {Being Perfection : Type}
    (DesirableIn : Being → Perfection → Prop) (x y : Being) : Prop :=
  (∀ q, DesirableIn y q → DesirableIn x q) ∧ ∃ p, DesirableIn x p ∧ ¬ DesirableIn y p

/-- Experientialism in pointwise form. -/
theorem experientialism_iff_pointwise {Being Perfection Profile : Type}
    (experience : Being → Profile) (DesirableIn : Being → Perfection → Prop) :
    ExperientialismReading experience DesirableIn ↔
      ∀ x y, experience x = experience y → ∀ p, (DesirableIn x p ↔ DesirableIn y p) := by
  constructor
  · intro h x y hxy p
    rw [h hxy]
  · intro h x y hxy
    funext p
    exact propext (h x y hxy p)

/-- Experientialism in positive form: some valuation of experiential profiles
fixes desirability in every respect. -/
theorem experientialism_iff_factor {Being Perfection Profile : Type}
    (experience : Being → Profile) (DesirableIn : Being → Perfection → Prop) :
    ExperientialismReading experience DesirableIn ↔
      ∃ value : Profile → Perfection → Prop, ∀ x p, DesirableIn x p ↔ value (experience x) p := by
  unfold ExperientialismReading
  rw [Function.factorsThrough_iff]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun x p => by rw [he]; rfl⟩
  · rintro ⟨e, he⟩
    exact ⟨e, funext fun x => funext fun p => propext (he x p)⟩

/-- The comparison certified by result "Experience-machine comparison of
experientialism and q.5 desirability". Every conjunct is quantified over arbitrary
types and relations.

1. Positive form of experientialism (`experientialism_iff_factor`).
2. Exact price: a desirability relation satisfying both q.5's biconditional and
   experientialism exists exactly when perfection supervenes on experience.
3. Contrariety under the case: with the machine case's facts, q.5's biconditional
   and experientialism are not jointly true.
4. Prediction: q.5's biconditional, the case's perfection facts and respect
   dominance give the stay-out verdict.
5. Prohibition: experientialism, same experience and the transfer bridge exclude
   the stay-out verdict.
6. Strength split: q.5's biconditional is the conjunction of its two halves.
7. Forward half with experientialism makes the machine life desirable in the
   respect it lacks; backward half with experientialism makes the real life not
   desirable in the respect it has.
8. Re-presentation probe for the refutation: some same-experience pair with the
   stay-out verdict and the transfer bridge exists exactly when experientialism
   fails. -/
def ExperienceMachineComparison : Prop :=
  (∀ (Being Perfection Profile : Type) (experience : Being → Profile)
      (DesirableIn : Being → Perfection → Prop),
    ExperientialismReading experience DesirableIn ↔
      ∃ value : Profile → Perfection → Prop, ∀ x p, DesirableIn x p ↔ value (experience x) p) ∧
  (∀ (Being Perfection Profile : Type) (experience : Being → Profile)
      (PerfectIn : Being → Perfection → Prop),
    (∃ DesirableIn : Being → Perfection → Prop,
        DesirableInsofarAsPerfectReading DesirableIn PerfectIn ∧
        ExperientialismReading experience DesirableIn) ↔
      PerfectionSupervenesOnExperience experience PerfectIn) ∧
  (∀ (Being Perfection Profile : Type) (experience : Being → Profile)
      (DesirableIn PerfectIn : Being → Perfection → Prop) (real machine : Being) (p : Perfection),
    SameExperience experience real machine → RealPerfectionsExceed PerfectIn real machine p →
      ¬ (DesirableInsofarAsPerfectReading DesirableIn PerfectIn ∧
          ExperientialismReading experience DesirableIn)) ∧
  (∀ (Being Perfection : Type) (DesirableIn PerfectIn : Being → Perfection → Prop)
      (BetterFor : Being → Being → Prop) (real machine : Being) (p : Perfection),
    DesirableInsofarAsPerfectReading DesirableIn PerfectIn →
    RealPerfectionsExceed PerfectIn real machine p →
    RespectDominanceMakesBetter BetterFor DesirableIn →
    StayOutVerdict BetterFor real machine) ∧
  (∀ (Being Perfection Profile : Type) (experience : Being → Profile)
      (DesirableIn : Being → Perfection → Prop) (BetterFor : Being → Being → Prop)
      (real machine : Being),
    ExperientialismReading experience DesirableIn →
    SameExperience experience real machine →
    BetterRequiresRespectDifference BetterFor DesirableIn →
    ¬ StayOutVerdict BetterFor real machine) ∧
  (∀ (Being Perfection : Type) (DesirableIn PerfectIn : Being → Perfection → Prop),
    DesirableInsofarAsPerfectReading DesirableIn PerfectIn ↔
      PerfectMakesDesirableReading DesirableIn PerfectIn ∧
      DesirableOnlyIfPerfectReading DesirableIn PerfectIn) ∧
  (∀ (Being Perfection Profile : Type) (experience : Being → Profile)
      (DesirableIn PerfectIn : Being → Perfection → Prop) (real machine : Being) (p : Perfection),
    ExperientialismReading experience DesirableIn →
    SameExperience experience real machine →
    RealPerfectionsExceed PerfectIn real machine p →
    (PerfectMakesDesirableReading DesirableIn PerfectIn →
        DesirableIn machine p ∧ ¬ PerfectIn machine p) ∧
    (DesirableOnlyIfPerfectReading DesirableIn PerfectIn →
        ¬ DesirableIn real p ∧ PerfectIn real p)) ∧
  (∀ (Being Perfection Profile : Type) (experience : Being → Profile)
      (DesirableIn : Being → Perfection → Prop),
    (∃ (real machine : Being) (BetterFor : Being → Being → Prop),
        SameExperience experience real machine ∧ StayOutVerdict BetterFor real machine ∧
        BetterRequiresRespectDifference BetterFor DesirableIn) ↔
      ExperientialismFails experience DesirableIn)

/-! ## A finite machine carrier

Three lives and four goods. `rich` is the profile of a life as of achieving,
having friends, knowing and enjoying; `dull` presents only knowing. The real life
actually has all four goods; the machine life has only the felt pleasure, an act of
its sensitive power, and lacks real achievement, friendship and knowledge of what
is; the drab life knows but has no achievement, friends or pleasure. These are
stipulations of the finite interpretation, not claims about any actual life. -/
namespace Carrier

inductive Life | real | machine | drab deriving DecidableEq
inductive Good | achievement | friendship | knowledge | pleasure deriving DecidableEq
inductive Profile | rich | dull deriving DecidableEq

instance : Fintype Life := ⟨{.real, .machine, .drab}, by intro x; cases x <;> decide⟩
instance : Fintype Good :=
  ⟨{.achievement, .friendship, .knowledge, .pleasure}, by intro x; cases x <;> decide⟩
instance : Fintype Profile := ⟨{.rich, .dull}, by intro x; cases x <;> decide⟩

/-- Experiential profiles: the real and machine lives are indistinguishable from
the inside. -/
def experience : Life → Profile
  | .real => .rich
  | .machine => .rich
  | .drab => .dull

/-- Actual possession of a good (in act). -/
def has : Life → Good → Bool
  | .real, _ => true
  | .machine, .pleasure => true
  | .machine, _ => false
  | .drab, .knowledge => true
  | .drab, _ => false

/-- The goods a profile presents as had. -/
def presents : Profile → Good → Bool
  | .rich, _ => true
  | .dull, .knowledge => true
  | .dull, _ => false

def Has (x : Life) (g : Good) : Prop := has x g = true

/-- Perfectionist desirability: desirable exactly in the goods actually had. -/
def perfectionist (x : Life) (g : Good) : Prop := has x g = true

/-- Hedonist desirability: desirable only in pleasure, and there exactly when the
profile presents pleasure. A function of the profile. -/
def hedonist (x : Life) (g : Good) : Prop := g = .pleasure ∧ presents (experience x) .pleasure = true

/-- Presentational experientialism: desirable in every good the profile presents.
A function of the profile. -/
def presentational (x : Life) (g : Good) : Prop := presents (experience x) g = true

/-- Partial experientialism: desirable in the goods actually had, and in
friendship whenever the profile presents friendship. -/
def partialExperiential (x : Life) (g : Good) : Prop :=
  has x g = true ∨ (g = .friendship ∧ presents (experience x) .friendship = true)

/-- A restricted desirability: desirable in the goods actually had, except
knowledge. A formal interpretation, not a recorded position. -/
def restricted (x : Life) (g : Good) : Prop := has x g = true ∧ g ≠ .knowledge

/-- An arbitrary betterness that relates only the real life to the machine life. -/
def bare (x y : Life) : Prop := x = .real ∧ y = .machine

instance (x : Life) (g : Good) : Decidable (Has x g) := inferInstanceAs (Decidable (_ = _))
instance (x : Life) (g : Good) : Decidable (perfectionist x g) := inferInstanceAs (Decidable (_ = _))
instance (x : Life) (g : Good) : Decidable (hedonist x g) := inferInstanceAs (Decidable (_ ∧ _))
instance (x : Life) (g : Good) : Decidable (presentational x g) := inferInstanceAs (Decidable (_ = _))
instance (x : Life) (g : Good) : Decidable (partialExperiential x g) := inferInstanceAs (Decidable (_ ∨ _))
instance (x : Life) (g : Good) : Decidable (restricted x g) := inferInstanceAs (Decidable (_ ∧ _))
instance (x y : Life) : Decidable (bare x y) := inferInstanceAs (Decidable (_ ∧ _))

end Carrier

open Carrier in
/-- Joint models and omission controls on the finite carrier, certified by result
"Experience-machine joint models and controls". `PerfectIn` is `Has` throughout,
and the betterness relation is strict respect dominance of the model's
desirability (so both transfer statements hold by construction) except in row 6.

1. Perfectionist side: q.5's biconditional, q.5's perfect-in-act reading, the case
   facts, both transfer statements and the stay-out verdict hold, experientialism
   fails.
2. Hedonist side: experientialism, the case facts and both transfer statements
   hold, the stay-out verdict fails; the backward half holds, the forward half and
   q.5's biconditional fail. The real life dominates the drab life, whose profile
   differs.
3. Presentational experientialism: experientialism, the forward half and the case
   facts hold; the backward half, q.5's biconditional and the stay-out verdict fail.
4. Partial experientialism: the forward half, the case facts and the stay-out
   verdict hold; the backward half and experientialism fail.
5. Restricted model: the backward half, the case facts and the stay-out verdict
   hold; the forward half and experientialism fail.
6. Bridge omission: with the hedonist desirability and a betterness relating only
   the real to the machine life, experientialism, same experience and the verdict
   hold and the transfer bridge fails. -/
def ExperienceMachineControls : Prop :=
  -- 1. perfectionist side
  (DesirableInsofarAsPerfectReading perfectionist Has ∧
    PerfectInsofarAsInActReading Has Has ∧
    SameExperience experience .real .machine ∧
    RealPerfectionsExceed Has .real .machine .achievement ∧
    RespectDominanceMakesBetter (Dominates perfectionist) perfectionist ∧
    BetterRequiresRespectDifference (Dominates perfectionist) perfectionist ∧
    StayOutVerdict (Dominates perfectionist) .real .machine ∧
    ¬ ExperientialismReading experience perfectionist) ∧
  -- 2. hedonist side
  (ExperientialismReading experience hedonist ∧
    SameExperience experience .real .machine ∧
    RealPerfectionsExceed Has .real .machine .achievement ∧
    RespectDominanceMakesBetter (Dominates hedonist) hedonist ∧
    BetterRequiresRespectDifference (Dominates hedonist) hedonist ∧
    ¬ StayOutVerdict (Dominates hedonist) .real .machine ∧
    DesirableOnlyIfPerfectReading hedonist Has ∧
    ¬ PerfectMakesDesirableReading hedonist Has ∧
    ¬ DesirableInsofarAsPerfectReading hedonist Has ∧
    Dominates hedonist .real .drab ∧ ¬ SameExperience experience .real .drab) ∧
  -- 3. presentational experientialism
  (ExperientialismReading experience presentational ∧
    PerfectMakesDesirableReading presentational Has ∧
    SameExperience experience .real .machine ∧
    RealPerfectionsExceed Has .real .machine .achievement ∧
    ¬ DesirableOnlyIfPerfectReading presentational Has ∧
    ¬ DesirableInsofarAsPerfectReading presentational Has ∧
    ¬ StayOutVerdict (Dominates presentational) .real .machine) ∧
  -- 4. partial experientialism
  (PerfectMakesDesirableReading partialExperiential Has ∧
    RealPerfectionsExceed Has .real .machine .achievement ∧
    SameExperience experience .real .machine ∧
    StayOutVerdict (Dominates partialExperiential) .real .machine ∧
    ¬ DesirableOnlyIfPerfectReading partialExperiential Has ∧
    ¬ ExperientialismReading experience partialExperiential) ∧
  -- 5. restricted model
  (DesirableOnlyIfPerfectReading restricted Has ∧
    RealPerfectionsExceed Has .real .machine .achievement ∧
    SameExperience experience .real .machine ∧
    StayOutVerdict (Dominates restricted) .real .machine ∧
    ¬ PerfectMakesDesirableReading restricted Has ∧
    ¬ ExperientialismReading experience restricted) ∧
  -- 6. bridge omission
  (ExperientialismReading experience hedonist ∧
    SameExperience experience .real .machine ∧
    StayOutVerdict bare .real .machine ∧
    ¬ BetterRequiresRespectDifference bare hedonist)

end TruthCore.Ethics.ExperienceMachine
