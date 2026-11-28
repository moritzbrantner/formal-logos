module

public import TruthCore.Causality.ExistentialPriorityOrder
public import TruthCore.Results.Causality.ExistentialSelfActualization.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ExistentialPriorityOrder

open TruthCore.Causality.ExistentialSelfActualization
open TruthCore.Causality.ExistentialPriorityOrder
open TruthCore.Logic.Regress

/-- Characterize mathematical order extension on the same mixed token carrier. -/
theorem exactExtension : ExactExtensionCriterion := by
  intro B E Occurs bearer produces
  constructor
  · rintro ⟨Prior, hBearer, hProduct, hIrrefl, hTrans⟩
    have contains : ∀ x y, RequiredEdge Occurs bearer produces x y → Prior x y := by
      intro x y edge
      cases x with
      | inl b =>
        cases y with
        | inl _ => exact False.elim edge
        | inr a =>
          obtain ⟨occurs, rfl⟩ := edge
          exact hBearer a occurs
      | inr a =>
        cases y with
        | inl b => exact hProduct a b edge.1 edge.2
        | inr _ => exact False.elim edge
    have containsPath : ∀ x y, Relation.TransGen (RequiredEdge Occurs bearer produces) x y →
        Prior x y := by
      intro x y path
      induction path with
      | single edge => exact contains _ _ edge
      | tail _ edge ih => exact hTrans _ _ _ ih (contains _ _ edge)
    exact fun x loop => hIrrefl x (containsPath x x loop)
  · intro acyclic
    exact ⟨Relation.TransGen (RequiredEdge Occurs bearer produces),
      fun a occurs => .single ⟨occurs, rfl⟩,
      fun _ _ occurs producesProduct => .single ⟨occurs, producesProduct⟩,
      acyclic, fun _ _ _ first second => first.trans second⟩

/-- An acyclic required graph supplies the order for the certified exclusion. -/
theorem noSelfOfAcyclic {B E : Type} (Occurs : E → Prop) (bearer : E → B)
    (produces : E → B → Prop) (hAcyclic : RequiredEdgesAcyclic Occurs bearer produces) :
    NoSelfProduction Occurs bearer produces := by
  obtain ⟨Prior, hBearer, hProduct, hIrrefl, hTrans⟩ :=
    (exactExtension B E Occurs bearer produces).mpr hAcyclic
  exact TruthCore.Results.Causality.ExistentialSelfActualization.noSelf
    Occurs bearer produces Prior hBearer hProduct hIrrefl hTrans

/-- Two individually strict interfaces can agree on the data and disagree on the order. -/
theorem splitControl : SplitPriorityControl := by
  let occurs : Unit → Prop := fun _ => True
  let bearer : Unit → Unit := id
  let produces : Unit → Unit → Prop := fun _ _ => True
  let left : Sum Unit Unit → Sum Unit Unit → Prop
    | .inl _, .inr _ => True
    | .inl _, .inl _ | .inr _, _ => False
  let right : Sum Unit Unit → Sum Unit Unit → Prop
    | .inr _, .inl _ => True
    | .inr _, .inr _ | .inl _, _ => False
  have hLeft : IrreflexivePriority left := by intro x; cases x <;> exact id
  have hRight : IrreflexivePriority right := by intro x; cases x <;> exact id
  have hLeftTrans : TransitivePriority left := by
    intro x y z hxy hyz
    cases y with
    | inl _ => cases x <;> exact False.elim hxy
    | inr _ => cases z <;> exact False.elim hyz
  have hRightTrans : TransitivePriority right := by
    intro x y z hxy hyz
    cases y with
    | inl _ => cases z <;> exact False.elim hyz
    | inr _ => cases x <;> exact False.elim hxy
  have hSelf : ¬ NoSelfProduction occurs bearer produces :=
    fun noSelf => noSelf () True.intro True.intro
  have hUnionIrrefl : IrreflexivePriority (RequiredEdge occurs bearer produces) := by
    intro x
    cases x <;> exact id
  have hUnionNotTrans : ¬ TransitivePriority (RequiredEdge occurs bearer produces) :=
    fun trans => hUnionIrrefl (.inl ())
      (trans (.inl ()) (.inr ()) (.inl ()) ⟨True.intro, rfl⟩ ⟨True.intro, True.intro⟩)
  exact ⟨bearer, left, right, fun _ _ => True.intro, fun _ _ _ _ => True.intro,
    hLeft, hLeftTrans, hRight, hRightTrans, hSelf, hUnionIrrefl, hUnionNotTrans,
    fun common => hSelf (noSelfOfAcyclic occurs bearer produces
      ((exactExtension Unit Unit occurs bearer produces).mp common))⟩

/-- No direct self-production still permits a cycle of distinct producers. -/
theorem reciprocalControl : ReciprocalProductionControl := by
  refine ⟨fun a _ producesSelf => producesSelf rfl, ?_⟩
  intro common
  let occurs : Bool → Prop := fun _ => True
  let edge := RequiredEdge occurs id (· ≠ ·)
  have acyclic := (exactExtension Bool Bool occurs id (· ≠ ·)).mp common
  apply acyclic (.inl false)
  have first : Relation.TransGen edge (.inl false) (.inr false) :=
    .single ⟨True.intro, rfl⟩
  have second : Relation.TransGen edge (.inl false) (.inl true) :=
    first.tail ⟨True.intro, Bool.noConfusion⟩
  have third : Relation.TransGen edge (.inl false) (.inr true) :=
    second.tail ⟨True.intro, rfl⟩
  exact third.tail ⟨True.intro, Bool.noConfusion⟩

end TruthCore.Results.Causality.ExistentialPriorityOrder
