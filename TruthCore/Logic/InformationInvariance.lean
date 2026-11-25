module

/-!
# Information invariance (#1926)

Constructive proof reuse for exact classification, agreement on a selected
relation class, and transfer from a representative with a true predicate.
These are logical conditions on supplied observations, relations and
predicates, not definitions of truth, evidence, knowledge, explanation or
reliability. No quotient, propositional extensionality, choice, or
computability assumption is required. Domain-specific scopes and witnesses
remain explicit in the callers.
-/

@[expose] public section

namespace TruthCore.Logic.InformationInvariance

universe u v

/-- Exact proposition-valued classification exists precisely when the
predicate is invariant on equal-observation fibers. No decidability or
surjectivity of the observation map is needed. -/
theorem factor_iff {S : Sort u} {O : Sort v} (observe : S → O)
    (P : S → Prop) :
    (∃ criterion : O → Prop, ∀ s, criterion (observe s) ↔ P s) ↔
      (∀ s t, observe s = observe t → (P s ↔ P t)) := by
  constructor
  · intro h s t same
    obtain ⟨criterion, exactC⟩ := h
    calc
      P s ↔ criterion (observe s) := (exactC s).symm
      _ ↔ criterion (observe t) := by rw [same]
      _ ↔ P t := exactC t
  · intro invariant
    refine ⟨(fun e => ∃ s, observe s = e ∧ P s), ?_⟩
    intro t
    exact ⟨fun ⟨s, same, holds⟩ => (invariant s t same).mp holds,
      fun holds => ⟨t, rfl, holds⟩⟩

/-- Related members of a symmetric, transitive relation agree on membership
in the class of a third member. The relation need not be reflexive everywhere. -/
theorem class_agreement {S : Sort u} (R : S → S → Prop)
    (symm : ∀ s t, R s t → R t s)
    (trans : ∀ s t a, R s t → R t a → R s a)
    {s t : S} (same : R s t) (a : S) : R s a ↔ R t a :=
  ⟨fun h => trans t s a (symm s t same) h,
    fun h => trans s t a same h⟩

/-- An invariant predicate holds at a selected member if it holds at one
related representative. The relation can include a restriction on admissible
representatives; no reflexivity, total coverage or truth of all classes is
inferred. -/
theorem of_representative {S : Sort u} (R : S → S → Prop)
    (P : S → Prop) (s : S)
    (invariant : ∀ t, R s t → (P s ↔ P t))
    (representative : ∃ t, R s t ∧ P t) : P s :=
  match representative with
  | ⟨t, related, holds⟩ => (invariant t related).mpr holds

end TruthCore.Logic.InformationInvariance
