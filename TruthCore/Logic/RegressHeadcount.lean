module

public import Mathlib.SetTheory.Cardinal.Finite
public import TruthCore.Logic.Regress

/-! A quantitative reading of Occam's razor for accounts of the same evidence.
The carrier supplied to the comparison specifies which posits are charged. -/
@[expose] public section

namespace TruthCore.Logic.RegressHeadcount

/-- The first inventory stays smaller after adding any finite number of posits
to it. The extended natural count identifies all infinite sizes. -/
def SurvivesEveryFiniteAddition (A B : Type) : Prop :=
  ∀ extra : ℕ, ENat.card A + (extra : ℕ∞) < ENat.card B

/-- Criteria for an unbounded headcount advantage. An injective assignment on
the visited bearers charges distinct upstream bearers as distinct posits.
The last conjunct compares total inventories with the same infinite background. -/
def RegressHeadcountCriterion : Prop :=
  (∀ A B, SurvivesEveryFiniteAddition A B ↔ Finite A ∧ Infinite B) ∧
  (∀ {Node Posit Alternative : Type} (G : Regress.Graph Node), G.NoCycles →
    ∀ (chain : ℕ → Node), (∀ n, G.edge (chain (n + 1)) (chain n)) →
    ∀ charge : Node → Posit, Set.InjOn charge (Set.range chain) →
    Finite Alternative → SurvivesEveryFiniteAddition Alternative Posit) ∧
  (SurvivesEveryFiniteAddition Unit ℕ ∧
    Cardinal.mk (ℕ ⊕ Unit) = Cardinal.mk (ℕ ⊕ ℕ))

end TruthCore.Logic.RegressHeadcount
