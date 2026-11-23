module

public import TruthCore.Modal.ActualistDomainsCertificate

@[expose] public section

namespace TruthCore.Results.Modal.ActualistDomains
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.ActualistDomains
open TruthCore.Modal (Euclidean)
variable {W B : Type}
theorem boxAllToAllBox_iff (m : Ontic W B) :
    BoxAllToAllBox m ↔ IncreasingDomains m := by
  constructor
  · intro h w v hAccess x hHere
    exact h (fun u y => m.ExistsAt u y) w (fun _ _ _ hy => hy)
      x hHere v hAccess
  · intro h P w hBox x hHere v hAccess
    exact hBox v hAccess x (h w v hAccess x hHere)

theorem allBoxToBoxAll_iff (m : Ontic W B) :
    AllBoxToBoxAll m ↔ DecreasingDomains m := by
  constructor
  · intro h w v hAccess x hThere
    exact h (fun _ y => m.ExistsAt w y) w (fun _ hy _ _ => hy)
      v hAccess x hThere
  · intro h P w hAll v hAccess x hThere
    exact hAll x (h w v hAccess x hThere) v hAccess

theorem increasing_excludes_contingency (m : Ontic W B)
    (h : IncreasingDomains m) : ∀ w x, ¬ ContingentAt m w x := by
  intro w x hc
  obtain ⟨hx, v, hv, hn⟩ := hc
  exact hn (h w v hv x hx)

theorem checks : ActualistDomainCertificate := by
  refine ⟨fun _ _ m => boxAllToAllBox_iff m,
    fun _ _ m => allBoxToBoxAll_iff m,
    fun _ _ m => increasing_excludes_contingency m, ?_⟩
  let m := TruthCore.Models.PSR.ContingentOnly.model.ontic
  have hPresent : m.ExistsAt false true := Or.inr ⟨rfl, rfl⟩
  have hAbsent : ¬ m.ExistsAt true true := by
    intro h
    rcases h with h | ⟨h, _⟩
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  have hNotIncreasing : ¬ IncreasingDomains m := by
    intro h
    exact hAbsent (h false true True.intro true hPresent)
  have hNotDecreasing : ¬ DecreasingDomains m := by
    intro h
    exact hAbsent (h true false True.intro true hPresent)
  exact ⟨fun _ _ => True.intro, fun _ _ => Or.inl rfl,
    TruthCore.Models.PSR.ContingentOnly.evaluation2,
    hNotIncreasing, hNotDecreasing,
    fun h => hNotIncreasing ((boxAllToAllBox_iff m).mp h),
    fun h => hNotDecreasing ((allBoxToBoxAll_iff m).mp h)⟩

/-! #1864: separate modal compatibility and actual-world naming, reusing the
#1865 maximal-profile interface and the #143 nine-attribute bridge. No proof
below establishes that the full divine profile is metaphysically realizable. -/

/-- Only the E-worlds carrying the COMPLETE selected profile need be admitted
by the M-frame. The existential bearer is unchanged in the transfer. -/
theorem described_greatness_transfer (m : Ontic W B)
    (p : DivinePredicates W B) (E : TruthCore.Modal.Frame W) (w : W)
    (hDescription : DescribedPossibleGreatness E m p w)
    (hAdmit : AdmitGreatnessWorlds E m p w) :
    PossibleGreatness m p w := by
  obtain ⟨v, hEv, x, hProfile⟩ := hDescription
  exact ⟨v, hAdmit v hEv ⟨x, hProfile⟩, x, hProfile⟩

/-- S5 is sufficient, not needed globally for this step. Euclidean access
and reflexivity AT w suffice to return the very same bearer to w and to every
successor of w. No actualist quantifier-shift is used. -/
theorem greatness_at_origin (m : Ontic W B) (p : DivinePredicates W B)
    (w : W) (hRef : m.frame.access w w)
    (hEuclidean : Euclidean m.frame)
    (hPossible : PossibleGreatness m p w) :
    ∃ x, GreatnessAt m p x w := by
  obtain ⟨v, hWv, x, ⟨_, _, hAll⟩⟩ := hPossible
  have hVw : m.frame.access v w := hEuclidean w v w hWv hRef
  have hHere : m.ExistsAt w x ∧ ExcellenceAt p w x := hAll w hVw
  refine ⟨x, hHere.1, hHere.2, ?_⟩
  intro u hWu
  exact hAll u (hEuclidean w v u hWv hWu)

/-- This is a real GOD_4 consumer ONLY IF the actual-world naming bridge is
provided. That bridge is not folded into the possible profile: the name
is applied after the modal transfer; each predicate applies to ONE x.
The existing StageTwo bridge provides the primitive classical-attributes field
from the nine predicates at w, without changing those senses. -/
theorem actual_named_classical_god (σ : TruthCore.Case.Catholicism.Signature)
    (m : Ontic W σ.Being) (p : DivinePredicates W σ.Being)
    (E : TruthCore.Modal.Frame W) (w : W)
    (hRef : m.frame.access w w)
    (hEuclidean : Euclidean m.frame)
    (hDescription : DescribedPossibleGreatness E m p w)
    (hAdmit : AdmitGreatnessWorlds E m p w)
    (hName : ActualDivineNaming σ m p w)
    (hNine : TruthCore.Case.Catholicism.ClassicalAttributesSuffice σ
      (p.simple w) (p.perfect w) (p.good w) (p.one w)
      (p.infinite w) (p.immutable w) (p.eternal w)
      (p.intellect w) (p.will w)) :
    ∃ g, m.ExistsAt w g ∧ σ.IsGod g ∧ σ.HasClassicalAttributes g ∧
      GreatnessAt m p g w := by
  have hm : PossibleGreatness m p w :=
    described_greatness_transfer m p E w hDescription hAdmit
  obtain ⟨g, hg⟩ := greatness_at_origin m p w hRef hEuclidean hm
  have hNineG : TruthCore.Case.Catholicism.NineClassicalAttributes
      (p.simple w) (p.perfect w) (p.good w) (p.one w)
      (p.infinite w) (p.immutable w) (p.eternal w)
      (p.intellect w) (p.will w) g := hg.2.1.1
  have hAttrs : σ.HasClassicalAttributes g :=
    TruthCore.Case.Catholicism.classicalAttributesFromNine σ
      (p.simple w) (p.perfect w) (p.good w) (p.one w)
      (p.infinite w) (p.immutable w) (p.eternal w)
      (p.intellect w) (p.will w) hNine g hNineG
  exact ⟨g, hg.1, hName g hg.1 hg.2.1, hAttrs, hg⟩

/-- The stage-one GOD_4 existential projection, with the explicit naming and
admissibility premises visible in the stronger theorem above. -/
theorem actual_god_exists (σ : TruthCore.Case.Catholicism.Signature)
    (m : Ontic W σ.Being) (p : DivinePredicates W σ.Being)
    (E : TruthCore.Modal.Frame W) (w : W)
    (hRef : m.frame.access w w)
    (hEuclidean : Euclidean m.frame)
    (hDescription : DescribedPossibleGreatness E m p w)
    (hAdmit : AdmitGreatnessWorlds E m p w)
    (hName : ActualDivineNaming σ m p w)
    (hNine : TruthCore.Case.Catholicism.ClassicalAttributesSuffice σ
      (p.simple w) (p.perfect w) (p.good w) (p.one w)
      (p.infinite w) (p.immutable w) (p.eternal w)
      (p.intellect w) (p.will w)) :
    TruthCore.Case.Catholicism.GodExists σ.IsGod := by
  obtain ⟨g, _, hGod, _, _⟩ :=
    actual_named_classical_god σ m p E w hRef hEuclidean
      hDescription hAdmit hName hNine
  exact ⟨g, hGod⟩

/-- A second, non-ontological support direction: a same-bearer actual
excellence witness plus the substantive ESSENTIALITY premise gives genuine
profile possibility under actual reflexivity, without description-to-world
transfer. A cosmological source does NOT automatically meet these hypotheses. -/
theorem actual_essential_bundle_possible (m : Ontic W B)
    (p : DivinePredicates W B) (w : W)
    (hRef : m.frame.access w w)
    (hActual : ∃ x, m.ExistsAt w x ∧ ExcellenceAt p w x)
    (hEssential : EssentialExcellenceAt m p w) :
    PossibleGreatness m p w := by
  obtain ⟨x, hExists, hExcellent⟩ := hActual
  exact ⟨w, hRef, x, hExists, hExcellent, hEssential x hExists hExcellent⟩

/-- Structural separating controls: E-possible full thirteen-predicate bearer
with no M-accessible bearer; nonvacuous weaker profile-specific inclusion;
and individually instantiable attributes with no joint bearer. -/
set_option maxRecDepth 8192 in
theorem divine_controls : DivineControl.Checks := by
  dsimp [DivineControl.Checks, DivineControl.ontic, DivineControl.holdsAt,
    DivineControl.attributes, DivineControl.split, DivineControl.k5Frame,
    DivineControl.k5Ontic, TruthCore.Modal.Euclidean,
    DescribedPossibleGreatness, PossibleGreatness, AdmitGreatnessWorlds,
    GreatnessAt, ExcellenceAt, NineAt,
    TruthCore.Modal.NecessaryIfExistent.MaximalProfile,
    TruthCore.Modal.PossibilityTransfer.epistemic,
    TruthCore.Modal.PossibilityTransfer.metaphysical,
    TruthCore.Modal.PossibilityTransfer.IncludedAt]
  decide

end TruthCore.Results.Modal.ActualistDomains
