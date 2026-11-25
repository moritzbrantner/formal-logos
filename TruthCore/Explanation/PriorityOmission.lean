module

public import Mathlib.Data.Set.Basic

/-!
# Strict explanatory priority and common omission

A row records eligible facts true in one target-absent interpretation of a
fixed background. The resulting truth consequence is relative to that class.
It does not furnish a metaphysically sufficient explanation or any priority
arrow. The modeled priority is between facts, independently of any relation
between bearers.
-/

@[expose] public section

namespace TruthCore.Explanation.PriorityOmission

variable {Fact Row : Type}

/-- An indispensable strict contributor is neither the target itself nor
posterior to it in the same transitive priority relation. -/
theorem priorExcludesSelfAndPosterior {priority : Fact → Fact → Prop}
    (hIrrefl : ∀ f, ¬ priority f f)
    (hTrans : ∀ ⦃a b c⦄, priority a b → priority b c → priority a c)
    {fact target : Fact} (hPrior : priority fact target) :
    fact ≠ target ∧ ¬ priority target fact := by
  refine ⟨?_, fun hBack => hIrrefl fact (hTrans hPrior hBack)⟩
  rintro rfl
  exact hIrrefl fact hPrior

/-- If an actual constituent's own actuality has the displayed priority to
instantiated constitution, that constitution cannot strictly explain the
whole's existence while the whole is also prior to that constituent. -/
theorem constitutionNotPriorOfWholeFirst {priority : Fact → Fact → Prop}
    (hIrrefl : ∀ f, ¬ priority f f)
    (hTrans : ∀ ⦃a b c⦄, priority a b → priority b c → priority a c)
    {whole part constitution : Fact}
    (hWhole : priority whole part) (hPart : priority part constitution) :
    ¬ priority constitution whole :=
  (priorExcludesSelfAndPosterior hIrrefl hTrans (hTrans hWhole hPart)).2

/-- In the presence of a target-absent row, the full eligible set is a
nonempty excluding record exactly when there is no common omission row
preserving every eligible fact. The proof allows infinite records and rows. -/
theorem excludingRecordIffNoCommonOmission {eligible : Set Fact}
    {holds : Row → Set Fact} (omission : Nonempty Row) :
    (∃ G : Set Fact, G.Nonempty ∧ G ⊆ eligible ∧ ∀ v, ¬ G ⊆ holds v) ↔
      ¬ ∃ v, eligible ⊆ holds v := by
  constructor
  · rintro ⟨G, _, hEligible, hExcludes⟩ ⟨v, hCommon⟩
    exact hExcludes v (hEligible.trans hCommon)
  · intro h
    refine ⟨eligible, ?_, Set.Subset.rfl, fun v hV => h ⟨v, hV⟩⟩
    obtain ⟨v⟩ := omission
    classical
    by_contra hn
    exact h ⟨v, fun f hf => (hn ⟨f, hf⟩).elim⟩

/-- The absence of singleton import cannot replace one common omission.
Each of two facts is preserved in some target-absent row, but the joint
record rules out both rows. -/
theorem individualOmissionsWithoutCommon :
    let holds : Bool → Set Bool := fun v => {f | f = v}
    (∀ f, ∃ v, f ∈ holds v) ∧ (∀ v, ¬ (Set.univ : Set Bool) ⊆ holds v) := by
  dsimp
  refine ⟨fun f => ⟨f, rfl⟩, ?_⟩
  intro v h
  cases v
  · exact Bool.noConfusion (h (Set.mem_univ true) : true = false)
  · exact Bool.noConfusion (h (Set.mem_univ false) : false = true)

end TruthCore.Explanation.PriorityOmission
