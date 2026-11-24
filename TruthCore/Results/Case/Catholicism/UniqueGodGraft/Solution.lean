module

public import TruthCore.Case.Catholicism.UniqueGodGraft

/-! The stage-2 attribute premise from the unique classical God: a uniqueness
transfer (#1926 graft), with its nonvacuity and omission controls. Analyst
reconstruction; attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.UniqueGodGraft
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.UniqueGodGraft.Model

/-- Argument G4: every being satisfying `σ.IsGod` has the classical
attributes, from the unique classical God. The witness `g` has them, and by
`IsTheOneGod` every God is `g`. Constructive. -/
theorem godHasClassicalAttributesFromUniqueGod (σ : Signature)
    (h : UniqueClassicalGodExists σ) : GodHasClassicalAttributes σ := by
  obtain ⟨g, _, hOne, hAttr⟩ := h
  intro x hx
  rw [hOne x hx]
  exact hAttr

theorem oneClassicalGod : OneClassicalGod := by
  refine ⟨⟨true, rfl, fun x hx => hx, rfl⟩, fun x hx => hx⟩

theorem twoGodsOneClassical : TwoGodsOneClassical := by
  refine ⟨⟨true, trivial, rfl⟩, fun h => ?_, fun ⟨g, _, hOne, _⟩ => ?_⟩
  · exact Bool.false_ne_true (h false trivial)
  · have h1 := hOne true trivial
    have h2 := hOne false trivial
    exact Bool.false_ne_true (h2.trans h1.symm)

theorem twoClassicalGods_strict : TwoClassicalGods := by
  refine ⟨fun _ _ => trivial, ⟨true, trivial⟩, fun ⟨g, _, hOne, _⟩ => ?_⟩
  have h1 := hOne true trivial
  have h2 := hOne false trivial
  exact Bool.false_ne_true (h2.trans h1.symm)

/-- Argument G5, the certificate of the controls. Premise-free. -/
theorem uniqueGodGraftControls : Controls :=
  ⟨oneClassicalGod, twoGodsOneClassical, twoClassicalGods_strict⟩

end TruthCore.Results.Case.Catholicism.UniqueGodGraft
