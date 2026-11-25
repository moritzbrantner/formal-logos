module

public import TruthCore.Explanation.ActualExerciseExplanation
public import TruthCore.Results.Causality.DerivativeJointPower.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.ActualExerciseExplanation

open TruthCore.Causality.JointGroups (Exercise Groups)
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Causality.ExerciseContribution
open TruthCore.Explanation.ActualExerciseExplanation
open TruthCore.German.Kant.CosmologicalInference

theorem productiveCut : ProductiveCut := by
  intro B E G W m I a x h
  let D : Set E := {e | e = a ∨ e = x}
  have ht : Trap m.exercisedGroups I D := by
    constructor
    · intro e he hi
      rcases he with rfl | rfl
      · exact h.adoptionNotIndependent hi
      · exact h.productNotIndependent hi
    · intro g hg he
      rcases he with ha | hx
      · exact ⟨x, h.adoptionNeedsProduct g hg ha, Or.inr rfl⟩
      · exact ⟨a, h.productNeedsAdoption g hg hx, Or.inl rfl⟩
  have obstruct := TruthCore.Results.Causality.DerivativeJointPower.trap_obstruction
    m.exercisedGroups I D ht
  exact ⟨obstruct a (Or.inl rfl), obstruct x (Or.inr rfl)⟩

open Matched

private theorem actual_occurs (route : Route) (e : Event) :
    (exercise route true).occurs true e := by
  cases e <;> trivial

private theorem adoption_record (route : Route) :
    (exercise route true).exercisedGroups.admitted .adoption := by
  simp [Exercise.exercisedGroups, exercise, groups]

private theorem product_record (route : Route) :
    (exercise route true).exercisedGroups.admitted .product := by
  simp [Exercise.exercisedGroups, exercise, groups]

private theorem direct_record :
    (exercise .exercised true).exercisedGroups.admitted .direct := by
  simp [Exercise.exercisedGroups, exercise, groups]

private theorem actual_coherent (route : Route) : (exercise route true).coherent := by
  refine ⟨trivial, ?_⟩
  intro g hg
  refine ⟨?_, fun e _ => actual_occurs route e, actual_occurs route _⟩
  cases route <;> cases g <;> simp_all [exercise, groups]

private theorem source_adoption (route : Route) :
    Step (exercise route true) .operation .adoption :=
  ⟨actual_occurs route _, actual_occurs route _,
    .adoption, adoption_record route, rfl, Or.inl rfl⟩

private theorem adoption_product (route : Route) :
    Step (exercise route true) .adoption .product :=
  ⟨actual_occurs route _, actual_occurs route _,
    .product, product_record route, rfl, rfl⟩

private theorem product_adoption (route : Route) :
    Step (exercise route true) .product .adoption :=
  ⟨actual_occurs route _, actual_occurs route _,
    .adoption, adoption_record route, rfl, Or.inr rfl⟩

private theorem source_credit (route : Route) :
    Credit (exercise route true) respect .source .recipient .esse :=
  ⟨.adoption, .product, rfl, rfl, rfl, .single (adoption_product route)⟩

private theorem source_cause (route : Route) :
    (ontic route).Causes true .source .recipient :=
  ⟨by decide, source_credit route⟩

private theorem only_recipient_contingent (route : Route) (b : Bearer)
    (h : ContingentAt (ontic route) true b) : b = .recipient := by
  cases b with
  | source =>
    obtain ⟨v, _, hn⟩ := h.2
    exact False.elim (hn (Or.inl rfl))
  | recipient => rfl

private theorem operation_not_sufficient (route : Route) (e : Event)
    (he : e ≠ .operation) : ¬ (exercise route true).suffices {.operation} e := by
  intro hs
  have bad := hs false trivial (by
    intro k hk
    have hk' : k = Event.operation := hk
    subst k
    trivial)
  cases e with
  | operation => exact he rfl
  | adoption => exact Bool.false_ne_true bad
  | product => exact Bool.false_ne_true bad

private theorem background (route : Route) : Background route := by
  refine ⟨actual_coherent route, ?_, ?_, ?_, rfl, rfl, rfl,
    source_adoption route, adoption_product route, product_adoption route,
    source_credit route, source_cause route, ?_, ?_,
    operation_not_sufficient route .adoption (by decide),
    operation_not_sufficient route .product (by decide)⟩
  · intro g _
    cases g with
    | adoption => exact ⟨.operation, Or.inl rfl⟩
    | product => exact ⟨.adoption, rfl⟩
    | direct => exact ⟨.operation, rfl⟩
  · intro v _
    exact Or.inl rfl
  · refine ⟨Or.inr rfl, false, trivial, ?_⟩
    simp [ontic]
  · intro b hb
    have h := only_recipient_contingent route b hb
    subst b
    exact ⟨.circumstance .source, source_cause route⟩
  · intro b hb
    have h := only_recipient_contingent route b hb
    subst b
    exact ⟨.source, by decide, source_credit route⟩

private theorem blocked_founded (route : Route) (h : route ≠ .exercised) :
    OutputFounded (exercise route true) sourceBasis .adoption .product := by
  refine ⟨by simp [sourceBasis], by simp [sourceBasis], ?_, ?_⟩
  · intro g hg he
    cases g <;> simp_all [Exercise.exercisedGroups, exercise, groups]
  · intro g hg he
    cases g <;> simp_all [Exercise.exercisedGroups, exercise, groups]

private theorem product_of_adoption (route : Route) (I : Event → Prop)
    (ha : Supply (exercise route true).exercisedGroups I .adoption) :
    Supply (exercise route true).exercisedGroups I .product := by
  refine Supply.joint (h := (exercise route true).exercisedGroups)
    (intrinsic := I) Record.product (product_record route) ?_
  intro e he
  have h : e = Event.adoption := he
  subst e
  exact ha

private theorem directly_supplied_adoption :
    Supply (exercise .exercised true).exercisedGroups sourceBasis .adoption := by
  refine Supply.joint (h := (exercise .exercised true).exercisedGroups)
    (intrinsic := sourceBasis) Record.direct direct_record ?_
  intro e he
  have h : e = Event.operation := he
  subst e
  exact .intrinsic _ rfl

theorem matchedComparison : Matched.Comparison := by
  have hc := blocked_founded .circular (by decide)
  have ha := blocked_founded .admitted (by decide)
  have nc := productiveCut _ _ _ _ _ _ _ _ hc
  have na := productiveCut _ _ _ _ _ _ _ _ ha
  refine ⟨background, hc, ha, by simp [groups], by simp [exercise],
    nc.1, nc.2, na.2, directly_supplied_adoption,
    product_of_adoption _ _ directly_supplied_adoption, ?_,
    product_of_adoption _ _ (.intrinsic _ (Or.inr rfl)), ?_, ?_⟩
  · intro h
    have bad : Event.product = .operation :=
      h.adoptionNeedsProduct .direct direct_record rfl
    cases bad
  · intro h
    exact h.adoptionNotIndependent (Or.inr rfl)
  · intro hs
    have bad := hs false trivial (by
      intro e he
      have he' : e = Event.operation := by
        simpa [Groups.members, exercise, groups] using he
      subst e
      trivial)
    exact Bool.false_ne_true bad

private theorem output_direct_record :
    (outputExercise true).exercisedGroups.admitted .direct := direct_record

private theorem output_adoption_record :
    (outputExercise true).exercisedGroups.admitted .adoption := adoption_record .exercised

private theorem output_supplied :
    Supply (outputExercise true).exercisedGroups sourceBasis .product := by
  refine Supply.joint (h := (outputExercise true).exercisedGroups)
    (intrinsic := sourceBasis) Record.direct output_direct_record ?_
  intro e he
  have h : e = Event.operation := he
  subst e
  exact .intrinsic _ rfl

theorem outputBypass : Matched.OutputBypass := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, output_supplied, ?_, ?_⟩
  · refine ⟨trivial, ?_⟩
    intro g hg
    refine ⟨(actual_coherent .exercised).2 g hg |>.1,
      fun e _ => actual_occurs .exercised e, ?_⟩
    exact actual_occurs .exercised _
  · intro g _ he
    cases g <;> simp_all [outputExercise, exercise, groups]
  · exact ⟨trivial, rfl,
      .direct, output_direct_record, rfl, rfl⟩
  · refine Supply.joint (h := (outputExercise true).exercisedGroups)
      (intrinsic := sourceBasis) Record.adoption output_adoption_record ?_
    intro e he
    have h : e = Event.operation ∨ e = .product := he
    rcases h with rfl | rfl
    · exact .intrinsic _ rfl
    · exact output_supplied
  · intro h
    have bad : Event.adoption = .operation :=
      h.productNeedsAdoption .direct output_direct_record rfl
    cases bad

end TruthCore.Results.Explanation.ActualExerciseExplanation
