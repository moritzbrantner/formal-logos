module

public import TruthCore.Causality.AcquiredHistoryTransfer
public import TruthCore.Results.Causality.ExerciseContribution.Solution

@[expose] public section
namespace TruthCore.Results.Causality.AcquiredHistoryTransfer
open TruthCore.Causality.AcquiredHistoryTransfer
open TruthCore.Causality.JointGroups (Exercise)
open TruthCore.Causality.ExerciseContribution (Step)
open TruthCore.Case.Catholicism (UniversalCauseTransfersPerfections)

variable {B E G S R : Type}

theorem ancestryFromRankedInputs (m : Exercise B E G S) (covered : B → E → Prop)
    (stage : E → Nat) (inputs : RankedInputs m covered stage) : CoveredAncestry m covered := by
  intro a v
  let reaches := fun e => ∃ u, m.bearer u = a ∧ Relation.TransGen (Step m) u e
  have walk (n : Nat) : ∀ e, stage e = n → covered a e → reaches e := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro e hn he
      rcases inputs a e he with ⟨u, hu, step⟩ | ⟨u, cu, earlier, step⟩
      · exact ⟨u, hu, .single step⟩
      · obtain ⟨start, hs, path⟩ := ih (stage u) (hn ▸ earlier) u rfl cu
        exact ⟨start, hs, path.tail step⟩
  exact walk (stage v) v rfl

theorem transferFromCoveredHistories (m : Exercise B E G S) (covered : B → E → Prop)
    (tag : E → R) (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (paths : CoveredAncestry m covered) (targets : TargetCoverage m covered tag InAct CausesIn esse)
    (credit : CreditWarrantsCause m tag CausesIn) :
    UniversalCauseTransfersPerfections InAct CausesIn esse := by
  intro a ha x r hxa hEsse hr
  rcases targets a ha x r hxa hEsse hr with rfl | ⟨v, cv, _, hv, ht⟩
  · exact hEsse
  · obtain ⟨u, hu, path⟩ := paths a v cv
    exact credit a x r ⟨u, v, hu, hv, ht, path⟩

open TruthCore.Causality.ExerciseContribution.Press
open TruthCore.Causality.ExerciseContribution (Credit)
open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus)
open PressWitness (covered stage)

private theorem noPathToGiverEsse {u : Event} :
    ¬ Relation.TransGen (Step (exercise .application)) u .giverEsse := by
  intro path
  have noLast (e : Event) : ¬ Step (exercise .application) e .giverEsse := by
    rintro ⟨_, _, g, hg, rfl, _⟩
    exact hg.2.elim
  cases path with
  | single h => exact noLast _ h
  | tail _ h => exact noLast _ h

theorem populatedPress : PressWitness.Populated := by
  have certificate := TruthCore.Results.Causality.ExerciseContribution.controls
  obtain ⟨_, existsEsse, universal, strokeMark, driveSignal, _⟩ := certificate.1 .application
  have onlyGiver (a : Role)
      (h : CausesAllInGenus (profile .application).InAct (profile .application).CausesIn .esse a) :
      a = .giver := by
    by_contra ne
    obtain ⟨u, v, _, hv, hr, path⟩ := h .giver (Ne.symm ne) (existsEsse .giver)
    change bearer v = .giver at hv
    cases v <;> first | exact noPathToGiverEsse path | contradiction
  have driveStroke : Step (exercise .application) .drive .stroke :=
    ⟨rfl, rfl, .stroke, ⟨Or.inr (Or.inr (Or.inl rfl)), rfl⟩, rfl, rfl⟩
  refine ⟨?_, ?_, fun _ _ _ path => path, universal, by decide,
    universal .patient (by decide) (existsEsse .patient), ⟨.imprint, rfl, rfl, rfl⟩,
    rfl, Or.inr (Or.inl rfl)⟩
  · intro a v hv
    obtain ⟨rfl, hv⟩ := hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl ⟨.drive, rfl, driveStroke⟩
    · exact Or.inr ⟨.stroke, ⟨rfl, Or.inl rfl⟩, by decide, strokeMark⟩
    · exact Or.inl ⟨.drive, rfl, driveSignal⟩
  · intro a ha x r hxa _ hr
    obtain rfl := onlyGiver a ha
    obtain ⟨v, occurs, rfl, rfl⟩ := hr
    cases v <;> first
      | exact Or.inl rfl
      | exact (hxa rfl).elim
      | exact Or.inr ⟨_, ⟨rfl, by simp⟩, occurs, rfl, rfl⟩

end TruthCore.Results.Causality.AcquiredHistoryTransfer
