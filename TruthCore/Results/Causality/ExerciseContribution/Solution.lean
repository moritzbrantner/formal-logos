module

public import TruthCore.Causality.ExerciseContribution

@[expose] public section
namespace TruthCore.Results.Causality.ExerciseContribution
open TruthCore.Causality.ExerciseContribution

theorem jointCredit : ThroughYieldsJointCredit := by
  intro B E G S R m respect stroke result a b x through
  obtain ⟨hb, hx, ⟨u, ha, prior⟩, last⟩ := through
  exact ⟨⟨u, ha, prior.tail last⟩, .single last, ⟨u, result, ha, hx, rfl, prior.tail last⟩,
    ⟨stroke, result, hb, hx, rfl, .single last⟩⟩

open Press
open TruthCore.Causality.JointGroups (Exercise Groups)
open TruthCore.Explanation.BorrowedExercise (Lent Lender SelfExercising Retained Secondary)
open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus)
open TruthCore.Case.Catholicism (UniversalCauseTransfersPerfections)

private instance : Fintype Role := ⟨{.giver, .agent, .patient}, by intro x; cases x <;> decide⟩
private instance : Fintype Respect := ⟨{.esse, .work, .signal}, by intro x; cases x <;> decide⟩
private instance : Fintype Event := ⟨{.giverEsse, .agentEsse, .patientEsse, .maintenance,
  .drive, .stroke, .imprint, .indicator}, by intro x; cases x <;> decide⟩

private def direct (row : Row) (u v : Event) : Prop := active row v ∧ contributor row v u

private theorem stepIff (row : Row) (u v : Event) :
    Step (exercise row) u v ↔ direct row u v := by
  constructor
  · rintro ⟨_, _, g, hg, rfl, input⟩
    exact ⟨hg.2, input⟩
  · rintro ⟨ex, input⟩
    have occurred (e : Event) : occurs row (true, true) e := by
      cases row <;> cases e <;> simp [occurs]
    refine ⟨occurred u, occurred v, v, ⟨?_, ex⟩, rfl, input⟩
    cases v <;> simp_all [active, exercise]

/-- Every path in this particular acyclic episode has length at most two.
The only extra pair beyond a single edge is drive → stroke → imprint in the
application row. This table is proved from the exercised records. -/
private def table (row : Row) (u v : Event) : Prop :=
  direct row u v ∨ row = .application ∧ u = .drive ∧ v = .imprint

private theorem reachIff (row : Row) (u v : Event) :
    Relation.TransGen (Step (exercise row)) u v ↔ table row u v := by
  constructor
  · intro path
    induction path with
    | single edge => exact Or.inl ((stepIff _ _ _).1 edge)
    | @tail v w _ last prior =>
      have hd := (stepIff _ _ _).1 last
      cases v <;> cases w <;> simp_all [table, direct, active, contributor]
  · rintro (h | ⟨rfl, rfl, rfl⟩)
    · exact .single ((stepIff _ _ _).2 h)
    · have first : Step (exercise .application) .drive .stroke :=
        (stepIff _ _ _).2 ⟨rfl, rfl⟩
      exact (Relation.TransGen.single first).tail ((stepIff _ _ _).2 ⟨trivial, Or.inl rfl⟩)

private instance (row : Row) (e : Event) : Decidable (active row e) := by
  cases e <;> unfold active <;> infer_instance
private instance (row : Row) (g e : Event) : Decidable (contributor row g e) := by
  cases g <;> unfold contributor <;> infer_instance
private instance (g e : Event) : Decidable (enabler g e) := by
  cases g <;> unfold enabler <;> infer_instance
private instance (row : Row) (s : Bool × Bool) (e : Event) : Decidable (occurs row s e) := by
  cases row <;> cases e <;> unfold occurs <;> infer_instance
private instance (row : Row) (u v : Event) : Decidable (direct row u v) := by
  unfold direct; infer_instance
private instance (row : Row) (u v : Event) : Decidable (table row u v) := by
  unfold table; infer_instance
private instance (row : Row) (u v : Event) : Decidable (Step (exercise row) u v) :=
  decidable_of_iff _ (stepIff row u v).symm
private instance (row : Row) (u v : Event) : Decidable (Relation.TransGen (Step (exercise row)) u v) :=
  decidable_of_iff _ (reachIff row u v).symm
private instance (row : Row) (a x : Role) (r : Respect) :
    Decidable (Credit (exercise row) respect a x r) := by
  unfold Credit
  change Decidable (∃ u v, bearer u = a ∧ bearer v = x ∧ respect v = r ∧ _)
  infer_instance
private instance (row : Row) (a : Role) (r : Respect) :
    Decidable (Realized (exercise row) respect a r) := by
  unfold Realized
  change Decidable (∃ v, occurs row (true, true) v ∧ bearer v = a ∧ respect v = r)
  infer_instance
private instance (row : Row) (a b x : Role) :
    Decidable (ThroughAt (exercise row) .stroke .imprint a b x) := by
  unfold ThroughAt; infer_instance

private instance (row : Row) (x : Role) : Decidable
    (CausesAllInGenus (profile row).InAct (profile row).CausesIn .esse x) := by
  unfold CausesAllInGenus
  dsimp only [profile]
  infer_instance

private instance (row : Row) : Decidable (transfer row) := by
  unfold transfer UniversalCauseTransfersPerfections
  letI (a x : Role) (r : Respect) : Decidable
      (x ≠ a → (profile row).CausesIn a x .esse → (profile row).InAct x r →
        (profile row).CausesIn a x r) := by dsimp only [profile]; infer_instance
  letI (a x : Role) : Decidable (∀ r, x ≠ a → (profile row).CausesIn a x .esse →
      (profile row).InAct x r → (profile row).CausesIn a x r) := Fintype.decidableForallFintype
  letI (a : Role) : Decidable (∀ x r, x ≠ a → (profile row).CausesIn a x .esse →
      (profile row).InAct x r → (profile row).CausesIn a x r) := Fintype.decidableForallFintype
  infer_instance

private instance (row : Row) (s : Bool × Bool) (g : Event) : Decidable (Lender (exercise row) s g) := by
  change Decidable ((g = .agentEsse ∨ g = .patientEsse ∨ g = .stroke ∨ g = .imprint ∨ g = .indicator) ∧
    (s = (true, true) → active row g) ∧ (∃ e, contributor row g e) ∧
    ∀ e, contributor row g e → occurs row s e)
  infer_instance
private instance (row : Row) (s : Bool × Bool) (e : Event) : Decidable (Lent (exercise row) s e) := by
  unfold Lent; infer_instance

theorem controls : Press.Certificate := by
  unfold Certificate
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro row
    unfold Background
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have occurred (e : Event) : occurs row (true, true) e := by
        cases row <;> cases e <;> simp [occurs]
      refine ⟨trivial, fun g hg => ⟨?_, fun e _ => occurred e, occurred g⟩⟩
      cases g <;> simp_all [exercise, active]
    all_goals cases row <;> first | decide | (dsimp only [profile]; decide)
  · refine ⟨⟨by rfl, ?_⟩, ?_, ?_, ?_⟩ <;> first | decide | (dsimp only [profile]; decide)
  · refine ⟨⟨by rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide
    · intro s _ inputs
      exact ⟨inputs .drive (Or.inl (Or.inr ⟨rfl, rfl⟩)), inputs .stroke (Or.inl (Or.inl rfl))⟩
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      intro afterDeletion
      have impossible := afterDeletion (false, true) trivial (by
        intro e member
        change (contributor .cooperation .imprint e ∧ e ≠ .drive) ∨ enabler .imprint e at member
        cases e <;> simp_all [exercise, contributor, enabler, occurs])
      exact Bool.noConfusion impossible.1
    · refine ⟨Or.inl rfl, ?_⟩
      intro afterDeletion
      have impossible := afterDeletion (true, false) trivial (by
        intro e member
        change (contributor .cooperation .imprint e ∧ e ≠ .stroke) ∨ enabler .imprint e at member
        cases e <;> simp_all [exercise, contributor, enabler, occurs])
      exact Bool.noConfusion impossible.2
    all_goals first | decide | (dsimp only [profile]; decide)
  · refine ⟨⟨⟨(false, true), trivial, trivial, ?_⟩, by rfl, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      first | decide | (dsimp only [profile]; decide)

end TruthCore.Results.Causality.ExerciseContribution
