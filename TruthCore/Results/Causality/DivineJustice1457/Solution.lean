module

public import TruthCore.Causality.DivineJustice1457

/-! Conditional divine-justice routes (#1457). Source warrant and application
remain open; see `docs/notes/divine-justice-1457.md`. -/
@[expose] public section
namespace TruthCore.Results.Causality.DivineJustice1457
open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1
open TruthCore.Causality.DivineVeracity1410
open TruthCore.Causality.DivineJustice1457

/-- Compose will-only-approved with approval-tracks-order for the same GOD_4 and act. -/
theorem justiceFromWisdom (σ : Signature) (O : Order σ)
    (h0 : GodWillsOnlyApproved σ O)
    (h1 : GodApprovalTracksOrder σ O)
    : GodActsJustly σ O :=
  fun g hg hc a hw => h1 g hg hc a (h0 g hg hc a hw)

/-- A genuine assertion is a willed act, so JUSTICE_1 makes it fitting; the fitting-assertion bridge makes it permitted. -/
theorem permittedFromJustice (σ : Signature) (V : Veracity σ) (O : Order σ) (G : Grounds σ)
    (h0 : GodActsJustly σ O)
    (h1 : GodAssertionIsWilled σ V O)
    (h2 : FittingAssertionPermitted σ O G)
    : GodAssertionsPermitted σ V G :=
  fun g hg hc p ha => h2 g p (h0 g hg hc _ (h1 g hg hc p ha))

/-- Under the voluntarist reading of due order, JUSTICE_1 holds for every will profile. -/
theorem voluntaristTrivializes (σ : Signature) (O : Order σ)
    (h0 : VoluntaristFitting σ O)
    : GodActsJustly σ O :=
  fun g hg hc a hw => (h0 a).2 ⟨g, hg, hc, hw⟩

open TruthCore.Causality.DivineJustice1457.Control in
theorem controls : TruthCore.Causality.DivineJustice1457.Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, trivial, trivial, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ _ _ h => h
    · exact fun _ _ _ _ h => h
    · exact fun _ _ _ _ h => h
    · exact fun _ _ _ _ _ h => h
    · exact fun _ _ _ _ _ => rfl
    · exact fun _ _ _ => trivial
    · exact fun _ _ _ _ _ => trivial
  · refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨order (fun _ => True) (· = true) (· = true) (fun _ => True), ?_, ?_⟩
      · exact fun _ _ _ _ h => h
      · intro h
        exact Bool.false_ne_true (h true rfl trivial false trivial)
    · refine ⟨order (fun _ => True) (fun _ => True) (· = true) (fun _ => True), ?_, ?_⟩
      · exact fun _ _ _ _ h => h
      · intro h
        exact Bool.false_ne_true (h true rfl trivial false trivial)
    · refine ⟨order (fun _ => False) (fun _ => False) (· = false) (fun _ => True),
        grounds (fun _ => False), ?_, ?_, ?_⟩
      · exact fun _ _ _ _ h => h.elim
      · intro _ _ h
        exact Bool.noConfusion h
      · intro h
        exact h true rfl trivial True trivial
    · refine ⟨order (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True),
        grounds (fun _ => False), ?_, ?_, ?_⟩
      · exact fun _ _ _ _ _ => trivial
      · exact fun _ _ _ _ _ => trivial
      · intro h
        exact h true rfl trivial True trivial
  · refine ⟨order (· = true) (· = true) (· = true) (fun _ => True), ?_, ?_, ?_,
      ⟨true, false, trivial⟩, ?_⟩
    · exact fun _ _ _ _ h => h
    · exact fun _ _ _ _ h => h
    · exact fun _ _ _ _ h => h
    · intro h
      exact Bool.false_ne_true (h true rfl trivial true false trivial)
  · refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨fun _ => ⟨true, rfl, trivial, trivial⟩, fun _ => trivial⟩
    · exact fun _ _ _ _ _ => trivial
    · intro h
      exact Bool.false_ne_true (h true rfl trivial false trivial)

end TruthCore.Results.Causality.DivineJustice1457
