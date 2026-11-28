module

public import TruthCore.Causality.StructuralCausalModel
public import TruthCore.Causality.ProductiveDeletion

/-!
Selective deletion in the finite acyclic supply fragment. A variable for
a record's gate is distinct from the variable for any event's supply.
Turning off a gate leaves the intrinsic basis and all other records intact.
-/

@[expose] public section

namespace TruthCore.Causality.StructuralCausalModel.Productive

open TruthCore.Causality.JointGroups (Groups)
open TruthCore.Causality.DerivativeJointPower (Supply)
open TruthCore.Causality.ProductiveDeletion (withoutInputs)

variable {E G : Type}

/-- Only contributors and record gates feed the supply equations. Enablers
in the original interface are subject to separate occurrence constraints. -/
def inputs (h : Groups E G) (p v : G ⊕ E) : Prop :=
  match p, v with
  | _, .inl _ => False
  | .inl g, .inr e => h.admitted g ∧ h.effect g = e
  | .inr a, .inr e => ∃ g, h.admitted g ∧ h.effect g = e ∧ a ∈ h.contributors g

theorem input_wf (h : Groups E G) (wf : WellFounded h.graph.edge) :
    WellFounded (inputs h) := by
  have gate (g : G) : Acc (inputs h) (.inl g) :=
    Acc.intro _ (fun _ hp => by cases hp)
  constructor
  intro v
  cases v with
  | inl g => exact gate g
  | inr e =>
    induction e using wf.induction with
    | h e ih =>
      apply Acc.intro
      intro p hp
      cases p with
      | inl g => exact gate g
      | inr a =>
        obtain ⟨g, hg, he, ha⟩ := hp
        exact ih a ⟨g, hg, he, Or.inl ha⟩

def supplyModel [Finite E] [Finite G] (h : Groups E G) (I : E → Prop) (wf : WellFounded h.graph.edge) :
    Model (G ⊕ E) Unit Prop where
  graph := ⟨inputs h⟩
  acyclic := input_wf h wf
  equation v := match v with
    | .inl _ => fun _ _ => True
    | .inr e => fun _ parents => I e ∨ ∃ (g : G) (hg : h.admitted g) (he : h.effect g = e),
        parents ⟨.inl g, ⟨hg, he⟩⟩ ∧
        ∀ a (ha : a ∈ h.contributors g), parents ⟨.inr a, ⟨g, hg, he, ha⟩⟩

def keeps (h : Groups E G) (D : Set E) (g : G) : Prop :=
  ∀ u ∈ h.contributors g, u ∉ D

/-- Intervene on the gates of all contributor records targeted by the old
productive cut. Event equations (including intrinsic seeds) stay in place. -/
noncomputable def cutSetting (h : Groups E G) (D : Set E) : Setting (G ⊕ E) Prop :=
  open scoped Classical in
  fun v => match v with
    | .inl g => if keeps h D g then none else some False
    | .inr _ => none

private theorem supply_cases (h : Groups E G) (I : E → Prop) (e : E) :
    Supply h I e ↔ I e ∨ ∃ g, h.admitted g ∧ h.effect g = e ∧
      ∀ a ∈ h.contributors g, Supply h I a := by
  constructor
  · intro hs
    cases hs with
    | intrinsic _ hi => exact Or.inl hi
    | joint g hg ha => exact Or.inr ⟨g, hg, rfl, ha⟩
  · rintro (hi | ⟨g, hg, rfl, ha⟩)
    · exact .intrinsic _ hi
    · exact .joint g hg ha

theorem response_matches_deletion [Finite E] [Finite G] (h : Groups E G) (I : E → Prop)
    (wf : WellFounded h.graph.edge) (D : Set E) (e : E) :
    (supplyModel h I wf).response () (cutSetting h D) (.inr e) ↔
      Supply (withoutInputs h D) I e := by
  classical
  let cut := withoutInputs h D
  let candidate : G ⊕ E → Prop := Sum.elim (keeps h D) (Supply cut I)
  have solved : ((supplyModel h I wf).intervene (cutSetting h D)).Solution () candidate := by
    intro v
    cases v with
    | inl g =>
      change keeps h D g = (if keeps h D g then none else some False : Option Prop).getD True
      by_cases hg : keeps h D g <;> simp [hg]
    | inr x =>
      change Supply cut I x = (I x ∨ ∃ (g : G) (_ : h.admitted g) (_ : h.effect g = x),
        keeps h D g ∧ ∀ a ∈ h.contributors g, Supply cut I a)
      apply propext
      rw [supply_cases]
      change (I x ∨ ∃ g, (h.admitted g ∧ keeps h D g) ∧ h.effect g = x ∧
        ∀ a ∈ h.contributors g, Supply cut I a) ↔ _
      constructor
      · rintro (hi | ⟨g, ⟨hg, hk⟩, he, hs⟩)
        · exact .inl hi
        · exact .inr ⟨g, hg, he, hk, hs⟩
      · rintro (hi | ⟨g, hg, he, hk, hs⟩)
        · exact .inl hi
        · exact .inr ⟨g, ⟨hg, hk⟩, he, hs⟩
  have eq := ((supplyModel h I wf).intervene (cutSetting h D)).eq_solve () solved
  exact Iff.of_eq (congrFun eq (.inr e)).symm

end TruthCore.Causality.StructuralCausalModel.Productive
