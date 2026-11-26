import TruthCore.Causality.FiniteGiverPanels

namespace TruthCore.Results.Causality.FiniteGiverPanels

open TruthCore.Causality.FiniteGiverPanels
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (AbsenceAmalgamation)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Modal.FiniteHitting (component)

theorem universalGiver {Being : Type} {Respect : Sort v}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (finiteHitting : TruthCore.Modal.FiniteHitting.Package)
    (covered : EveryPanelCovered InAct MoreIn CausesIn esse)
    (pivot : FinitePivot InAct MoreIn CausesIn esse) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  sorry

theorem natPanelBoundary : NatPanelBoundary := by
  sorry

/-- One missed actual recipient per listed candidate defeats them all. The
exhaustiveness hypothesis excludes candidates outside the list at the pivot. -/
theorem boundedRefutation {Being : Type} [DecidableEq Being] {Respect : Sort v}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (pivot : Finset {x // InAct x esse})
    (candidates : Finset {g // IsMaximumIn InAct MoreIn esse g})
    (exhaustive : ∀ giver, PanelPresence InAct MoreIn CausesIn esse giver pivot →
      giver ∈ candidates)
    (noUniversal : ¬ MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) :
    ∃ extra : Finset {x // InAct x esse}, extra.card ≤ candidates.card ∧
      ∀ giver, ¬ PanelPresence InAct MoreIn CausesIn esse giver (pivot ∪ extra) := by
  sorry

theorem cyclicSharpness (k : ℕ) : CyclicPivotSharpness k := by
  sorry

open Classical in
/-- Pairing an independently underived maximal bearer with each actual
recipient tests direct causal coverage by that very bearer. -/
theorem underivedPivotPairs {Being : Type} {Respect : Sort v}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (m : Being) (maximum : IsMaximumIn InAct MoreIn esse m)
    (underived : ∀ g, g ≠ m → ¬ CausesIn g m esse) :
    (∀ x : {b // InAct b esse}, ∃ g,
      PanelPresence InAct MoreIn CausesIn esse g {⟨m, maximum.1⟩, x}) ↔
    CausesAllInGenus InAct CausesIn esse m := by
  sorry

end TruthCore.Results.Causality.FiniteGiverPanels
