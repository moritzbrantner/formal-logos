module

public import TruthCore.German.Kant.CosmologicalInference
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Logic.StrengthComparison

/-!
# Necessary existence and cross-world existential dependence

This source-free investigation (#495) separates de re necessary existence from
the absence of direct support *for that being's existence*. Its primitive
`supportsEsse` is not identified with efficient causation, modal accessibility,
explanation of an existence fact, or the transmission of causal power.

The positive conditional results explicitly consume the existing excluded-
middle proposition. The constructive results below use no axioms. None of the
support hypotheses is asserted to hold in reality.
-/

@[expose] public section

namespace TruthCore.Causality.NecessarilyUnderived

open TruthCore.German.Kant.CosmologicalInference

variable {World Being : Type}

/-- An actual-world existential-support edge has a supporter which exists at
the actual world. No distinctness condition is imposed syntactically; a
well-founded instance of this relation rules out self-support. -/
def PresentEsseSupport (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (source target : Being) : Prop :=
  m.ExistsAt w₀ source ∧ supportsEsse w₀ source target

/-- No existing individual directly supports this target at the selected world.
This is the shared pointwise absence condition, not actual target existence,
modal necessity, uniqueness, or absence of support at other worlds. It is
exactly the negation of each incoming `PresentEsseSupport` edge, written with
the existence guard curried so existing theorem interfaces remain unchanged. -/
def NoExistingSupportAt (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w : World)
    (target : Being) : Prop :=
  ∀ source, m.ExistsAt w source → ¬ supportsEsse w source target

def WellFoundedPresentEsseSupport (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  WellFounded (PresentEsseSupport m supportsEsse w₀)

/-- A single, actually present, de re necessary individual has no direct
existential supporter among existent individuals at *any* admitted world.
This says neither that the individual is unique nor that it is God. -/
def NecessarilyUnderived (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  ∃ target, m.ExistsAt w₀ target ∧ NecessaryAt m w₀ target ∧
    ∀ w, NoExistingSupportAt m supportsEsse w target

def NonRefutableNecessarilyUnderived (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  ¬¬ NecessarilyUnderived m supportsEsse w₀

/-- Every possible-world incoming supporter of a necessary bearer lifts to
an *actually present and itself necessary* predecessor of that same bearer.
This exact transport property is an open metaphysical premise. -/
def NecessaryPredecessorLifting (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  ∀ w source target, NecessaryAt m w₀ target →
    m.ExistsAt w source → supportsEsse w source target →
      NecessaryAt m w₀ source ∧
      PresentEsseSupport m supportsEsse w₀ source target

/-- A direct supporter, where it exists, of a necessary individual must
itself be a necessary individual. This does not follow from modality alone. -/
def NoContingentGroundOfNecessary (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  ∀ w source target, m.ExistsAt w source → NecessaryAt m w₀ target →
    supportsEsse w source target → NecessaryAt m w₀ source

/-- Only one direction of the former proposed *invariance* axiom is needed:
an incoming support edge between necessary individuals at an admitted world
must already occur at the actual world. Actual edges may disappear elsewhere. -/
def NoNovelNecessarySupport (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  ∀ w source target, NecessaryAt m w₀ source → NecessaryAt m w₀ target →
    m.ExistsAt w source → supportsEsse w source target →
      supportsEsse w₀ source target

def ActualReflexive (m : Ontic World Being) (w₀ : World) : Prop :=
  m.frame.access w₀ w₀

/-- Union of the world-indexed direct existential-support edges, restricted
to rigidly necessary bearers. Well-foundedness here is a cross-world condition:
even if every world's edge relation is a DAG, their union need not be.
Each edge remains wholly within its witness world; a path in this overlay may
combine edges witnessed at different worlds and is not an actual causal path.
Requiring this overlay to be well-founded is an additional open constraint,
not ordinary worldwise causal or temporal coherence. -/
def UnionNecessarySupport (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (source target : Being) : Prop :=
  NecessaryAt m w₀ source ∧ NecessaryAt m w₀ target ∧
    ∃ w, m.ExistsAt w source ∧ supportsEsse w source target

def WellFoundedUnionNecessarySupport (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  WellFounded (UnionNecessarySupport m supportsEsse w₀)

/-- Minimal structural theorem: source-free necessity, well-founded actual
support, and lifted necessary predecessors refute the *denial* of an underived
necessary bearer. No modal frame axiom is needed: actual existence is tracked
explicitly throughout the well-founded induction. -/
theorem not_not_underived_of_lifting
    (m : Ontic World Being) (supportsEsse : World → Being → Being → Prop)
    (w₀ : World) (hNecessary : NecessaryBeing m w₀)
    (hWF : WellFoundedPresentEsseSupport m supportsEsse w₀)
    (hLift : NecessaryPredecessorLifting m supportsEsse w₀) :
    NonRefutableNecessarilyUnderived m supportsEsse w₀ := by
  intro hNone
  obtain ⟨initial, hInitialExists, hInitialNecessary⟩ := hNecessary
  have noActualNecessary : ∀ target,
      NecessaryAt m w₀ target → m.ExistsAt w₀ target → False := by
    intro target
    induction hWF.apply target with
    | intro target _ ih =>
        intro hNec hPresent
        apply hNone
        refine ⟨target, hPresent, hNec, ?_⟩
        intro w source hSource hEdge
        obtain ⟨hSourceNecessary, hActualEdge⟩ :=
          hLift w source target hNec hSource hEdge
        exact ih source hActualEdge hSourceNecessary hActualEdge.1
  exact noActualNecessary initial hInitialNecessary hInitialExists

/-- The older pair of independently disputable grounding bridges, plus
reflexivity *only at the selected actual world*, entails predecessor lifting.
Full S5 accessibility and biconditional edge invariance are not required. -/
theorem lifting_of_two_bridges
    (m : Ontic World Being) (supportsEsse : World → Being → Being → Prop)
    (w₀ : World) (hReflexive : ActualReflexive m w₀)
    (hNoContingent : NoContingentGroundOfNecessary m supportsEsse w₀)
    (hNoNovel : NoNovelNecessarySupport m supportsEsse w₀) :
    NecessaryPredecessorLifting m supportsEsse w₀ := by
  intro w source target hNecessaryTarget hSource hEdge
  have hNecessarySource :=
    hNoContingent w source target hSource hNecessaryTarget hEdge
  exact ⟨hNecessarySource, hNecessarySource w₀ hReflexive,
    hNoNovel w source target hNecessarySource hNecessaryTarget hSource hEdge⟩

/-- Alternative graph-theoretic bridge: with actual reflexivity and no
contingent supporters of necessary beings, a globally well-founded union of
necessary support edges rules out rotating roots without assuming that edges
are world-invariant. -/
theorem not_not_underived_of_union_wellFounded
    (m : Ontic World Being) (supportsEsse : World → Being → Being → Prop)
    (w₀ : World) (hNecessary : NecessaryBeing m w₀)
    (hReflexive : ActualReflexive m w₀)
    (hNoContingent : NoContingentGroundOfNecessary m supportsEsse w₀)
    (hUnionWF : WellFoundedUnionNecessarySupport m supportsEsse w₀) :
    NonRefutableNecessarilyUnderived m supportsEsse w₀ := by
  intro hNone
  obtain ⟨initial, _, hInitialNecessary⟩ := hNecessary
  have noNecessary : ∀ target, ¬ NecessaryAt m w₀ target := by
    intro target
    induction hUnionWF.apply target with
    | intro target _ ih =>
        intro hNec
        apply hNone
        refine ⟨target, hNec w₀ hReflexive, hNec, ?_⟩
        intro w source hSource hEdge
        have hSourceNec :=
          hNoContingent w source target hSource hNec hEdge
        exact ih source ⟨hSourceNec, hNec, ⟨w, hSource, hEdge⟩⟩ hSourceNec
  exact noNecessary initial hInitialNecessary

/-- The first bridge package entails the alternative union-WF package. The
reverse is not valid: a new edge in another world can remain globally acyclic. -/
theorem union_wellFounded_of_actual_wellFounded
    (m : Ontic World Being) (supportsEsse : World → Being → Being → Prop)
    (w₀ : World) (hReflexive : ActualReflexive m w₀)
    (hNoNovel : NoNovelNecessarySupport m supportsEsse w₀)
    (hActualWF : WellFoundedPresentEsseSupport m supportsEsse w₀) :
    WellFoundedUnionNecessarySupport m supportsEsse w₀ := by
  have hSub : ∀ source target,
      UnionNecessarySupport m supportsEsse w₀ source target →
      PresentEsseSupport m supportsEsse w₀ source target := by
    intro source target ⟨hSourceNec, hTargetNec, w, hPresent, hEdge⟩
    exact ⟨hSourceNec w₀ hReflexive,
      hNoNovel w source target hSourceNec hTargetNec hPresent hEdge⟩
  exact Subrelation.wf (fun {_ _} h => hSub _ _ h) hActualWF

/-- Classical existence is derived from the constructive result by reusing
the repository's explicit excluded-middle *proposition*, not a hidden axiom. -/
theorem underived_of_lifting_and_excludedMiddle
    (m : Ontic World Being) (supportsEsse : World → Being → Being → Prop)
    (w₀ : World) (hNecessary : NecessaryBeing m w₀)
    (hWF : WellFoundedPresentEsseSupport m supportsEsse w₀)
    (hLift : NecessaryPredecessorLifting m supportsEsse w₀)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    NecessarilyUnderived m supportsEsse w₀ := by
  have hNN := not_not_underived_of_lifting m supportsEsse w₀ hNecessary hWF hLift
  cases hEM (NecessarilyUnderived m supportsEsse w₀) with
  | inl h => exact h
  | inr h => exact False.elim (hNN h)

theorem underived_of_union_wellFounded_and_excludedMiddle
    (m : Ontic World Being) (supportsEsse : World → Being → Being → Prop)
    (w₀ : World) (hNecessary : NecessaryBeing m w₀)
    (hReflexive : ActualReflexive m w₀)
    (hNoContingent : NoContingentGroundOfNecessary m supportsEsse w₀)
    (hUnionWF : WellFoundedUnionNecessarySupport m supportsEsse w₀)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    NecessarilyUnderived m supportsEsse w₀ := by
  have hNN := not_not_underived_of_union_wellFounded m supportsEsse w₀
    hNecessary hReflexive hNoContingent hUnionWF
  cases hEM (NecessarilyUnderived m supportsEsse w₀) with
  | inl h => exact h
  | inr h => exact False.elim (hNN h)

/-! ## Strength orders of the lifting premise (#1017, #1598)

`NecessaryPredecessorLifting` entails `NoNovelNecessarySupport` (its third
conjunct; the extra necessity hypothesis of the weak version is unused) and
`NoContingentGroundOfNecessary` (its first conjunct). The deltas below state
what lifting adds to each, with no background; the converse
`lifting_of_two_bridges` instead needs `ActualReflexive`. -/

section LiftingStrength

open TruthCore.Logic.StrengthComparison

/-- Delta over `NoNovelNecessarySupport`: every existent direct supporter, at
any admitted world, of a necessary individual is itself necessary and exists
at the actual world `w₀`. It says nothing about the support edge at `w₀`. -/
def SupportersOfNecessaryNecessaryAndActual (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  ∀ w source target, NecessaryAt m w₀ target →
    m.ExistsAt w source → supportsEsse w source target →
      NecessaryAt m w₀ source ∧ m.ExistsAt w₀ source

/-- Delta over `NoContingentGroundOfNecessary`: every support edge, at any
admitted world, from an existent source into a necessary individual recurs at
the actual world `w₀` as a present support edge (the source exists at `w₀` and
supports the same target there). It says nothing about the source's necessity. -/
def SupportOfNecessaryRecursActually (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : Prop :=
  ∀ w source target, NecessaryAt m w₀ target →
    m.ExistsAt w source → supportsEsse w source target →
      PresentEsseSupport m supportsEsse w₀ source target

/-- Lifting over no novel necessary support; difference: supporters of
necessary individuals are necessary and actual. -/
def liftingOverNoNovel (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : ComparisonSpec where
  stronger := NecessaryPredecessorLifting m supportsEsse w₀
  weaker := NoNovelNecessarySupport m supportsEsse w₀
  delta := SupportersOfNecessaryNecessaryAndActual m supportsEsse w₀

/-- Lifting over no contingent ground of the necessary; difference: support
edges into necessary individuals recur actually. -/
def liftingOverNoContingent (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World) : ComparisonSpec where
  stronger := NecessaryPredecessorLifting m supportsEsse w₀
  weaker := NoContingentGroundOfNecessary m supportsEsse w₀
  delta := SupportOfNecessaryRecursActually m supportsEsse w₀

/-- Exact factorization: lifting holds iff no novel necessary support holds and
supporters of necessary individuals are necessary and actual. -/
def LiftingOverNoNovelExact : Prop :=
  ∀ {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World),
    NecessaryPredecessorLifting m supportsEsse w₀ ↔
      NoNovelNecessarySupport m supportsEsse w₀ ∧
        SupportersOfNecessaryNecessaryAndActual m supportsEsse w₀

/-- Exact factorization: lifting holds iff no contingent ground of the
necessary holds and support edges into necessary individuals recur actually. -/
def LiftingOverNoContingentExact : Prop :=
  ∀ {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World),
    NecessaryPredecessorLifting m supportsEsse w₀ ↔
      NoContingentGroundOfNecessary m supportsEsse w₀ ∧
        SupportOfNecessaryRecursActually m supportsEsse w₀

/-- Control model (a): worlds and individuals `Bool`, universal frame; `true`
exists at every world, `false` only at world `true`. A formal interpretation. -/
def contingentSourceOntic : Ontic Bool Bool :=
  ⟨⟨fun _ _ => True⟩, fun w x => x = true ∨ w = true, fun _ _ _ => False⟩

/-- Control model (b): both individuals exist at every world, universal frame. -/
def twoNecessaryOntic : Ontic Bool Bool :=
  ⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩

/-- Control support relation: `false` supports `true` at world `true` only. -/
def nonActualEdge (w source target : Bool) : Prop :=
  w = true ∧ source = false ∧ target = true

/-- Separating setting for lifting over no novel support: a contingent source
supports a necessary target at a non-actual world (actual world `false`). -/
def contingentSourceSetting : ComparisonSpec :=
  liftingOverNoNovel contingentSourceOntic nonActualEdge false

/-- Separating setting for lifting over no contingent ground: two necessary
individuals with a support edge only at a non-actual world. -/
def nonActualEdgeSetting : ComparisonSpec :=
  liftingOverNoContingent twoNecessaryOntic nonActualEdge false

/-- In model (a) no novel necessary support holds (vacuously: the only source
with an edge is contingent) and lifting fails. -/
def ContingentSourceSeparates : Prop := Separation contingentSourceSetting

/-- In model (b) no contingent ground holds (both individuals are necessary)
and lifting fails (the edge is absent at the actual world). -/
def NonActualEdgeSeparates : Prop := Separation nonActualEdgeSetting

end LiftingStrength

end TruthCore.Causality.NecessarilyUnderived
