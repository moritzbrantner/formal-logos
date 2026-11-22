module

public import TruthCore.Causality.TractarianLogicalSpace

/-! Tautology (NECESSARY_16), combinatorial logical space and the necessary-being
node: strength order, the logical-space law, the checked incompatibility with
elementary existence, and finite models. Analyst formulations; attribution
deferred. -/
@[expose] public section
namespace TruthCore.Results.Causality.TractarianLogicalSpace
open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.LogicalNecessityProfiles
open TruthCore.Causality.LogicalNecessityContrast (DenialContradictory)
open TruthCore.Causality.TractarianLogicalSpace
open TruthCore.Causality.TractarianLogicalSpace.Model
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Case.Catholicism (Signature)

/-- On the truth-functional fragment Kripke truth at a world is truth-functional
truth under that world's atomic profile, whatever the frame. -/
theorem holds_iff_tfHolds {W A : Type} (F : Frame W) (V : Valuation W A) (w : W) :
    ∀ φ : Formula A, BoxFree φ → (Holds F V w φ ↔ TFHolds (V w) φ)
  | .atom _, _ => Iff.rfl
  | .falsum, _ => Iff.rfl
  | .imp φ ψ, h => by
      have hφ := holds_iff_tfHolds F V w φ h.1
      have hψ := holds_iff_tfHolds F V w ψ h.2
      exact ⟨fun k t => hψ.mp (k (hφ.mpr t)), fun k t => hψ.mpr (k (hφ.mp t))⟩
  | .box _, h => h.elim
  | .diamond _, h => h.elim

/-- A tautology holds at every world of every frame under every valuation. -/
theorem tautology_holds {W A : Type} (F : Frame W) (V : Valuation W A) (w : W)
    (φ : Formula A) (h : Tautology φ) : Holds F V w φ :=
  (holds_iff_tfHolds F V w φ h.1).mpr (h.2 (V w))

/-- NECESSARY_16 strengthens NECESSARY_14: a tautology is K-valid. The proof is
the induction `holds_iff_tfHolds`, not an instantiation. -/
theorem tautologyToAllFrameK {A : Type} (φ : Formula A) (h : Tautology φ) :
    AllFrameKValidity φ :=
  fun _ F V w => tautology_holds F V w φ h

/-- In combinatorial logical space only tautologies among truth-functional
formulas are boxed: the world realizing an arbitrary assignment is accessible,
so a boxed formula holds under that assignment. -/
theorem logicalSpaceOnlyLogicalNecessity {W A : Type} (F : Frame W) (V : Valuation W A)
    (w : W) (h : LogicalSpaceAt F V w) : OnlyLogicalNecessityAt F V w := by
  intro φ hφ hBox
  refine ⟨hφ, fun s => ?_⟩
  obtain ⟨v, hv, hEq⟩ := h s
  have hHolds := (holds_iff_tfHolds F V v φ hφ).mp (hBox v hv)
  rw [hEq] at hHolds
  exact hHolds

/-- The box K necessary-being node excludes elementary existence at the same
world: if every combination of the candidates' existence were realized at an
accessible world, the combination in which nothing exists would be, and the
root would be absent there. -/
theorem boxKRootExcludesElementaryExistence {W : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W) (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxK σ m w CN) : NotElementaryExistenceAt m.ontic w := by
  intro hElem
  obtain ⟨n, hBox, _⟩ := h
  obtain ⟨v, hv, hEq⟩ := hElem (fun _ => False)
  have hn : existenceValuation m.ontic v n := hBox v hv
  rw [hEq] at hn
  exact hn

theorem laws : Model.Laws := by
  refine ⟨fun _ _ => holds_iff_tfHolds, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W A F V w φ h v _
    exact tautology_holds F V v φ h
  · intro A φ hφ hK
    exact ⟨hφ, fun s =>
      (holds_iff_tfHolds (⟨fun _ _ => True⟩ : Frame Unit) (fun _ => s) () φ hφ).mp
        (hK Unit ⟨fun _ _ => True⟩ (fun _ => s) ())⟩
  · intro W A F w0 φ hφ hV
    exact ⟨hφ, fun s => (holds_iff_tfHolds F (fun _ => s) w0 φ hφ).mp (hV (fun _ => s) w0)⟩
  · intro W A F w0 φ hφ
    constructor
    · intro hT ⟨V, w, hn⟩
      exact hn (tautology_holds F V w φ hT)
    · intro em hD
      refine ⟨hφ, fun s => ?_⟩
      cases em (TFHolds s φ) with
      | inl h => exact h
      | inr h =>
        exact (hD ⟨fun _ => s, w0, fun k =>
          h ((holds_iff_tfHolds F (fun _ => s) w0 φ hφ).mp k)⟩).elim
  · intro A φ
    constructor
    · intro hT
      exact ⟨hT.1, fun ⟨s, hs⟩ => hs (hT.2 s)⟩
    · intro em hφ hD
      refine ⟨hφ, fun s => ?_⟩
      cases em (TFHolds s φ) with
      | inl h => exact h
      | inr h => exact (hD ⟨s, h⟩).elim
  · intro W A F V w φ hL hφ
    exact ⟨fun hB => logicalSpaceOnlyLogicalNecessity F V w hL φ hφ hB,
      fun hT v _ => tautology_holds F V v φ hT⟩
  · intro W A B o V w φ n hL hφ hD hBox
    apply logicalSpaceOnlyLogicalNecessity o.frame V w hL φ hφ
    intro v hv
    exact (hD v).mpr (hBox v hv)

theorem tractarianModel : Model.TractarianModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w s
    exact ⟨s, trivial, rfl⟩
  · exact ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩
  · intro w
    exact logicalSpaceOnlyLogicalNecessity space factV w (fun s => ⟨s, trivial, rfl⟩)
  · intro w a
    refine ⟨⟨fun _ => True, trivial, trivial⟩, ⟨fun _ => False, trivial, fun h => h⟩, ?_⟩
    intro h
    exact h (fun _ => False) trivial
  · intro w
    refine ⟨fun _ _ => trivial, fun _ _ => trivial, ?_⟩
    intro hElem
    obtain ⟨v, _, hEq⟩ := hElem (fun _ => False)
    have h : existenceValuation objOntic v true := trivial
    rw [hEq] at h
    exact h
  · intro x
    refine ⟨fun v => ⟨fun _ => trivial, fun _ h => h⟩, ?_⟩
    intro hD
    exact (hD (fun _ => False)).mpr trivial
  · intro φ h
    exact h.1
  · refine ⟨fun W F => axiomK_valid F p p, ?_⟩
    intro h
    exact h.1.1
  · intro w
    refine ⟨fun s => ⟨s, trivial, rfl⟩, ?_⟩
    intro x hBox
    exact hBox (fun _ => False) trivial

theorem jointRouteModel : Model.JointRouteModel := by
  intro w
  have hS5 : FrameSatisfies .S5 tractProfile.ontic.frame :=
    ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩
  have hL : LogicalSpaceAt tractProfile.ontic.frame unitFactV w :=
    fun s => ⟨s, trivial, rfl⟩
  refine ⟨hS5, ⟨(), ⟨hS5, fun _ _ => trivial⟩,
    ⟨⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩, trivial, fun _ _ => rfl, trivial⟩⟩,
    hL, logicalSpaceOnlyLogicalNecessity _ _ w hL, ?_⟩
  intro hElem
  obtain ⟨v, _, hEq⟩ := hElem (fun _ => False)
  have h : existenceValuation tractProfile.ontic v () := trivial
  rw [hEq] at h
  exact h

/-- Certified difference (#1598): tautology is exactly K validity plus
membership in the truth-functional fragment. Premise-free, constructive. -/
theorem tautologyOverKValidityExact : TautologyOverKValidityExact := by
  intro A φ
  exact ⟨fun h => ⟨tautologyToAllFrameK φ h, h.1⟩, fun ⟨hK, hφ⟩ => laws.2.2.1 A φ hφ hK⟩

/-- Batch controls (premise-free). -/
theorem controls : Model.Controls := ⟨laws, tractarianModel, jointRouteModel⟩

end TruthCore.Results.Causality.TractarianLogicalSpace
