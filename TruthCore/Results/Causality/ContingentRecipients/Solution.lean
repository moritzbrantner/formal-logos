module

public import TruthCore.Causality.ContingentRecipients
public import TruthCore.Results.Causality.ActualAncestralSource.Solution

@[expose] public section
namespace TruthCore.Results.Causality.ContingentRecipients
open TruthCore.Causality.ContingentRecipients (CoverageControl)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.PrussPowerPremises.Model (Bg allC)
open TruthCore.Causality.NarDerivation.Model (chainG chainGrounds)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.WillVersusChance.Model (onlyG)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)

/-- On the inherited worlds only c can be absent. The intermediary supplies
it directly at false but cannot also be the ancestor of the underived d. -/
theorem necessaryIntermediary : CoverageControl := by
  let m := groundProfile chainG allC chainGrounds
  have gExists (v : Bool) : m.ontic.ExistsAt v .g := Or.inl rfl
  have dExists (v : Bool) : m.ontic.ExistsAt v .d := Or.inr (Or.inl rfl)
  have cActual : ActualConcrete m false .c := ⟨trivial, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  have dRoot : ActualRoot m false .d := by
    refine ⟨⟨trivial, dExists false⟩, fun x hx => ?_⟩
    rcases hx.2.2 with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he
  have cContingent : ContingentAt m.ontic false .c := by
    refine ⟨cActual.2, true, trivial, ?_⟩
    rintro (hg | hd | ⟨_, hf⟩) <;> contradiction
  refine ⟨dRoot, fun v _ => gExists v, cContingent, cActual,
    ⟨trivial, dExists false, Or.inl ⟨rfl, rfl⟩⟩, ?_, ?_⟩
  · rintro x _ ⟨_, v, _, absent⟩
    cases x with
    | g => exact False.elim (absent (gExists v))
    | d => exact False.elim (absent (dExists v))
    | c => exact ⟨⟨trivial, gExists false, Or.inr ⟨rfl, rfl⟩⟩, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · intro reach
    have eq := ActualAncestralSource.namedRootOfReach m false onlyG reach .g .d rfl dRoot
    cases eq

end TruthCore.Results.Causality.ContingentRecipients
