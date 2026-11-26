module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
public import TruthCore.Modal.FiniteHitting.Vocabulary
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Finite panels of actual recipients in the Fourth Way's esse dictionary.
Panels index tests of one fixed causal interpretation. -/

@[expose] public section
namespace TruthCore.Causality.FiniteGiverPanels

open TruthCore.Latin.Aquinas.SummaTheologiae

variable {Being : Type} {Respect : Sort v}
variable (InAct : Being → Respect → Prop)
variable (MoreIn : Respect → Being → Being → Prop)
variable (CausesIn : Being → Being → Respect → Prop) (esse : Respect)

/-- The candidate passes a panel if every actual recipient in it is either
the candidate itself or directly receives esse from it. -/
def PanelPresence
    (giver : {g // IsMaximumIn InAct MoreIn esse g})
    (panel : Finset {x // InAct x esse}) : Prop :=
  ∀ x ∈ panel, x.val = giver.val ∨ CausesIn giver.val x.val esse

/-- Each finite panel, including the empty panel, has a passing candidate. -/
def EveryPanelCovered : Prop :=
  ∀ panel, ∃ giver, PanelPresence InAct MoreIn CausesIn esse giver panel

/-- Some panel has finitely many passing actual maximal candidates. The
finite population may be empty unless every panel is covered. -/
def FinitePivot : Prop :=
  ∃ panel, Set.Finite {giver | PanelPresence InAct MoreIn CausesIn esse giver panel}

/-- Infinite omission control with all naturals actual and maximal, and
direct gifts from higher to lower naturals. -/
def NatPanelBoundary : Prop :=
  let actual : ℕ → Unit → Prop := fun _ _ => True
  let more : Unit → ℕ → ℕ → Prop := fun _ _ _ => False
  let gives : ℕ → ℕ → Unit → Prop := fun giver recipient _ => recipient < giver
  EveryPanelCovered actual more gives () ∧
    ¬ FinitePivot actual more gives () ∧
    ¬ MaximeEnsCausesBeingOfAllReading actual more gives ()

/-- A cyclic roster shows that an exhaustive pivot with `k + 1` candidates
can need all `k + 1` additional recipients. Self-coverage is by equality. -/
def CyclicPivotSharpness (k : ℕ) : Prop :=
  let actual : Fin (k + 2) → Unit → Prop := fun _ _ => True
  let more : Unit → Fin (k + 2) → Fin (k + 2) → Prop := fun _ _ _ => False
  let gives : Fin (k + 2) → Fin (k + 2) → Unit → Prop :=
    fun giver recipient _ => recipient ≠ giver ∧ recipient ≠ finRotate (k + 2) giver
  ∃ pivot : Finset {x // actual x ()}, pivot.card = 1 ∧
    (∃ candidates : Finset {g // IsMaximumIn actual more () g},
      candidates.card = k + 1 ∧
      ∀ giver, PanelPresence actual more gives () giver pivot ↔ giver ∈ candidates) ∧
    (∀ extra, extra.card < k + 1 →
      ∃ giver, PanelPresence actual more gives () giver (pivot ∪ extra)) ∧
    (∃ extra, extra.card = k + 1 ∧
      ∀ giver, ¬ PanelPresence actual more gives () giver (pivot ∪ extra))

end TruthCore.Causality.FiniteGiverPanels
