module

public import TruthCore.Causality.RootPerfectionIntellect
public import TruthCore.Explanation.TruthmakerTheories
public import TruthCore.Explanation.BruteContingencyParity

/-! # What could make a root's closure explained? Essence, carriage and truthmakers (#2145, premise lane E)

Analyst formulations, attribution deferred. The target is E,
`RootPerfectionExclusion.NoUnexplainedAbsenceAtRoots` (`9281317d`): no actual
root lacks a determination that some admissible profile has together with all
of the root's determinations. #2153 and #2162 found that no graph node supplies
E: the contingency-restricted PSRs do not reach a necessary root's necessary
profile, `FactPSR` is unbound, and truthmaker maximalism is met by a totality
fact. This module asks whether an essentialist account of modality supplies E
and exactly where the rival's escape must lie.

**Hyperintensional essence for profiles (ESSENCE_6).** `Ess y x C` reads "it
lies in the nature of `y` that `x`'s profile satisfies the condition `C`", for
a condition `C : Set D → Prop` on sets of real determinations. It is a
declared PRIMITIVE parameter. The existing ESSENCE_5 (`ModalGrounding.
EssentialTruth`) takes world-propositions, and that is too coarse here: a
world-proposition about `x`'s profile cannot say what the essential condition
demands of a profile that no world realizes, so "the condition excludes `k`"
would hold vacuously of every unrealized profile. A condition on profiles
states its content directly. No bridge to ESSENCE_5 is asserted.

**Four premises.**

* `RootAbsencesNecessary` (N): no accessible world gives an actual root a
  determination it lacks at `w`. The root's absences are necessary.
* `EssenceGroundedRootProfileModality` (EM): the essentialist account of the
  source of modality (Fine-style "necessitarian actualism", navigation only),
  restricted to root profiles: any set of determinations that satisfies every
  essential condition on an actual root's profile is had by that root at some
  accessible world. Necessity of a profile fact then needs an essential
  condition that excludes its contrary. It is the profile counterpart of the
  existing existence-level `ModalGrounding.EssentialExclusionAccount`.
* `RootEssentialConditionsPositive` (EP): every essential condition on an
  actual root's profile holds of every admissible profile that extends the
  root's actual profile. Natures constrain a root's profile only through the
  admissibility constraints and the presence of its determinations; no
  essential condition is a negative clause that cuts off an admissible
  extension.
* `RootEssentialConditionsCarried` (LE): an essential condition on an actual
  root's profile can fail at an admissible extension of that profile only where
  some determination of the root requires the lack of members of that
  extension (`RootPerfectionIntellect`'s primitive `RequiresLack`). Essential
  exclusions are carried by what the root is. It is weaker than EP.

The results module derives E from N, EM and EP, and EP from LE and the
necessity direction of member grounding (`AdmissibleIsExclusionFree`,
`89c988d9`). It also proves the converse that makes the first derivation a
relocation (E with factivity of essential conditions gives EP), that
under EM and EP an unexplained absence is a contingent one, that a carried
closure at an actual root contradicts root purity and the purity of
requirements, that truthmaker necessitation is met by any existent for a
necessary fact, and a finite scene for the selection tu quoque.
-/

@[expose] public section

namespace TruthCore.Causality.RootClosure

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPerfectionExclusion (ActualProfile)

variable {W B D : Type}

/-- ESSENCE_6, essential profile condition: it lies in the nature of `y` that
`x`'s profile (set of real determinations) satisfies `C`. A parameter wrapper
over the primitive `Ess`. Examples: it lies in the nature of a triangle that its
sides number three (a condition on its profile of sides); it lies in the nature
of a simple source that its profile contains no composition. Non-examples: that
`x`'s profile happens to be `P` at `w` (a fact, not a nature-relative truth);
that every accessible world has `x` with `P` (a modal fact, which EM relates to
essence only as a premise). -/
def ProfileEssentialCondition (Ess : B → B → (Set D → Prop) → Prop) (y x : B)
    (C : Set D → Prop) : Prop :=
  Ess y x C

/-- OPEN (N): no world accessible from `w` gives an actual root at `w` a
determination it lacks at `w`. The root's absences are necessary. It says
nothing about why they are. -/
def RootAbsencesNecessary (m : Profile W B) (w : W) (HasAt : W → B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ v, m.ontic.frame.access w v → ∀ d, HasAt v r d → HasAt w r d

/-- OPEN (EM): essence-grounded modality for root profiles. Every set `q` of
determinations that satisfies every essential condition (of any being) on an
actual root's profile is included in that root's profile at some accessible
world. Whatever no nature excludes is possible for the root. Powers-based,
Humean and primitivist accounts of modality deny it in different ways. -/
def EssenceGroundedRootProfileModality (m : Profile W B) (w : W)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ q : Set D,
    (∀ y C, ProfileEssentialCondition Ess y r C → C q) →
      ∃ v, m.ontic.frame.access w v ∧ q ⊆ ActualProfile (HasAt v) r

/-- OPEN (EP): every essential condition on an actual root's profile holds of
every admissible profile that contains the root's actual determinations. No
nature constrains a root's profile by a clause that cuts off an admissible
extension. -/
def RootEssentialConditionsPositive (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ y C, ProfileEssentialCondition Ess y r C →
    ∀ q, Admissible q → ActualProfile (HasAt w) r ⊆ q → C q

/-- OPEN (LE): essential exclusions at a root are carried by its determinations.
Every essential condition on an actual root's profile holds of every admissible
extension of the root's actual profile in which no determination of the root
requires the lack of some members of that extension. Equivalently
(classically): such a condition fails at an admissible extension only where a
determination of the root requires a lack within it. A closure determination
("being such as to have nothing beyond these") counts as a carrier. -/
def RootEssentialConditionsCarried (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RequiresLack : D → Set D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ y C, ProfileEssentialCondition Ess y r C →
    ∀ q, Admissible q → ActualProfile (HasAt w) r ⊆ q →
      (∀ t, HasAt w r t → ∀ S ⊆ q, ¬ RequiresLack t S) → C q

/-- Factivity of essential conditions on root profiles: each holds of the
root's actual profile. Used only in the converse lemma. It follows from
essence grounding necessity on a reflexive frame. -/
def RootEssentialConditionsFactive (m : Profile W B) (w : W)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ y C, ProfileEssentialCondition Ess y r C →
    C (ActualProfile (HasAt w) r)

/-! ## Finite controls

The carrier is the #2153 one: worlds and beings `Bool`, universal access, the
source `true` the only actual root at `true` (`rootProfile`), and the five
#1970 determinations. The admissible family is `openProfile` (contains `esse`,
lacks the nonpure `limiter`). The effect has `esse` and `noesis` at both worlds.
These are assignments of the stated relations only; they say nothing about
what essence, requirement or admissibility metaphysically are. -/
namespace Control

open TruthCore.Causality.SourceIntellectControls.ProfileControls (Determination effect openProfile)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootPerfectionExclusion (NoUnexplainedAbsenceAtRoots)

/-- The source's profile is `atTrue` at world `true` and `atFalse` at world
`false`; the effect always has `esse` and `noesis`. -/
def hasAt (atTrue atFalse : Set Determination) : Bool → Bool → Determination → Prop
  | true, true, d => d ∈ atTrue
  | false, true, d => d ∈ atFalse
  | _, false, d => d ∈ effect

/-- The condition "lacks `noesis`". -/
def noNoesis (q : Set Determination) : Prop := Determination.noesis ∉ q

/-- Only the source's nature constrains its profile, and only by admissibility. -/
def essOpen (y x : Bool) (C : Set Determination → Prop) : Prop :=
  y = true ∧ x = true ∧
    C = openProfile

/-- The source's nature also contains the negative clause "lacks `noesis`". -/
def essNeg (y x : Bool) (C : Set Determination → Prop) : Prop :=
  y = true ∧ x = true ∧
    (C = openProfile ∨
      C = noNoesis)

/-- No requirement of a lack. -/
def noReq (_ : Determination) (_ : Set Determination) : Prop := False

/-- The pure `a` requires the lack of `noesis` (a closure carrier). -/
def aExcludesNoesis (d : Determination) (S : Set Determination) : Prop :=
  d = Determination.a ∧ S = {Determination.noesis}

/-- N on the control carrier. -/
abbrev cN (s t : Set Determination) : Prop := RootAbsencesNecessary rootProfile true (hasAt s t)
/-- EM on the control carrier. -/
abbrev cEM (ess : Bool → Bool → (Set Determination → Prop) → Prop) (s t : Set Determination) :
    Prop := EssenceGroundedRootProfileModality rootProfile true ess (hasAt s t)
/-- EP on the control carrier, with the open family. -/
abbrev cEP (ess : Bool → Bool → (Set Determination → Prop) → Prop) (s t : Set Determination) :
    Prop := RootEssentialConditionsPositive rootProfile true openProfile ess (hasAt s t)
/-- LE on the control carrier, with the open family. -/
abbrev cLE (ess : Bool → Bool → (Set Determination → Prop) → Prop) (s t : Set Determination)
    (req : Determination → Set Determination → Prop) : Prop :=
  RootEssentialConditionsCarried rootProfile true openProfile ess (hasAt s t) req
/-- E on the control carrier, with the open family. -/
abbrev cE (s t : Set Determination) : Prop :=
  NoUnexplainedAbsenceAtRoots rootProfile true openProfile (hasAt s t true)

end Control

/-! ## The selection tu quoque: a finite scene

Facts: `select`, that one of several undominated outcomes is selected
(contingent); `power`, that an agent exercises its power over that range;
`lack`, that the root lacks `k` (necessary); `clause`, that the root's nature
contains the bare negative clause "without `k`". The scene asks what the two
existing `WhyStance` standards say when both explananda are required. -/
namespace Selection

open TruthCore.Explanation.PSRStrength (Arena basic everywhere)
open TruthCore.Explanation.BruteContingencyParity (WhyStance)

/-- The four facts of the scene. -/
inductive SFact | select | power | lack | clause
  deriving DecidableEq

/-- `select` holds only at the actual world `true`; the rest hold at both. -/
def holds : Bool → SFact → Prop
  | w, .select => w = true
  | _, _ => True

/-- The exercised power is a reason for the selection at `true`; the bare
clause is a reason for the lack at both worlds. -/
def explains (w : Bool) (r f : SFact) : Prop :=
  (r = .power ∧ f = .select ∧ w = true) ∨ (r = .clause ∧ f = .lack)

/-- The scene's arena: universal access, no beings. -/
def scene : Arena Bool Empty SFact :=
  basic everywhere holds explains (fun g f => g = f)

/-- A stance that accepts both explananda and requires a reason why each
obtains, uniformly. -/
def stance : WhyStance SFact where
  accepts f := f = .select ∨ f = .lack
  core _ := False
  demands _ := False
  requiresWhy f := f = .select ∨ f = .lack


open TruthCore.Explanation.PSRStrength (Contingent Explained Access)
open TruthCore.Explanation.BruteContingencyParity (WhyHonors WhyHonorsNecessitating)

/-- The selection tu quoque on one scene. The stance that requires a reason why
for the contingent selection and for the root's necessary lack is honored:
the exercised power is a reason for the selection and the bare negative clause
is a reason for the lack. The stronger necessitating standard fails, and it
fails at the selection, not at the lack: the clause necessitates the lack, the
power does not necessitate the selection. Neither existing standard counts
against the bare clause; only a constraint on what may serve as a reason for a
root's profile fact (LE) does. A finite scene, not a model of agency. -/
theorem selectionParity :
    Contingent scene true SFact.select ∧ ¬ Contingent scene true SFact.lack ∧
    WhyHonors stance scene true ∧ ¬ WhyHonorsNecessitating stance scene true ∧
    (∃ r, scene.explains true r SFact.lack ∧
      ∀ v, Access scene true v → scene.holds v r → scene.holds v SFact.lack) ∧
    (∀ r, scene.explains true r SFact.lack → r = SFact.clause) := by
  refine ⟨⟨rfl, false, trivial, by simp [scene, TruthCore.Explanation.PSRStrength.basic,
      holds]⟩, ?_, ?_, ?_, ⟨SFact.clause, Or.inr ⟨rfl, rfl⟩, fun _ _ _ => trivial⟩, ?_⟩
  · rintro ⟨_, v, _, hv⟩
    exact hv trivial
  · rintro f (rfl | rfl) _
    · exact ⟨SFact.power, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨SFact.clause, Or.inr ⟨rfl, rfl⟩⟩
  · intro h
    obtain ⟨r, hr, hnec⟩ := h SFact.select (Or.inl rfl) (Or.inl rfl)
    rcases hr with ⟨rfl, -, -⟩ | ⟨-, h⟩
    · exact absurd (hnec false trivial trivial) (by simp [scene,
        TruthCore.Explanation.PSRStrength.basic, holds])
    · cases h
  · rintro r (⟨-, h, -⟩ | ⟨rfl, -⟩)
    · cases h
    · rfl

end Selection

end TruthCore.Causality.RootClosure
