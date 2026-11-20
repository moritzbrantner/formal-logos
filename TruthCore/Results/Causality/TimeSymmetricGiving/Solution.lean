module

public import TruthCore.Causality.TimeSymmetricGiving

@[expose] public section

namespace TruthCore.Results.Causality.TimeSymmetricGiving

open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized)
open TruthCore.Modal.TemporalHistory (History)

/-- The momentary PSR and the productive bridge give weak concurrent
actualization `40a97664`. -/
theorem concurrentOfMomentaryPSR {W B T P R : Type} (h : History W B T)
    (G : BeingGiving W B T) (X : PresenceExplanation W B T R) (EsseReceivedIn : B → P → Prop)
    (hPSR : MomentaryPSR h X EsseReceivedIn)
    (hBridge : ExplanationNeedsGiver h G X EsseReceivedIn) :
    ConcurrentlyActualized h G EsseReceivedIn :=
  fun v x t z hz hx =>
    let ⟨r, hr⟩ := hPSR v x t z hz hx
    hBridge v x t z r hz hx hr

/-- Under the momentary PSR the productive bridge is weak concurrent
actualization. -/
theorem psrBridgeCarriesTheCrux : PSRBridgeCarriesTheCrux := by
  intro W B T P R h G X E hPSR
  refine ⟨concurrentOfMomentaryPSR h G X E hPSR, fun hCA => ?_⟩
  intro v x t z _ hz hx _
  exact hCA v x t z hz hx

/-- Coverage, exercise and time symmetry give concurrent actualization for
homogeneous things: the cause of being gives at one moment of presence, and an
automorphism preserving the history carries that moment to any other. -/
theorem homogeneousConcurrentOfSymmetry {W B T P R : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (Facts : W → B → T → Prop) (CausesIn : B → B → R → Prop)
    (esse : R) (EsseReceivedIn : B → P → Prop)
    (hCover : ReceivedEsseHasCauseOfBeing CausesIn esse EsseReceivedIn)
    (hExercise : CausesOfBeingAreExercised h G CausesIn esse)
    (hSymmetry : GivingRespectsTimeSymmetry h G Facts) :
    ConcurrentlyActualizedIfHomogeneous h G Facts EsseReceivedIn := by
  intro v x t z hz hHom hx
  obtain ⟨c, hcx, hc⟩ := hCover x z hz
  obtain ⟨s, hs, hgive⟩ := hExercise v c x hcx hc ⟨t, hx⟩
  obtain ⟨σ, hσ, hst⟩ := hHom s t hs hx
  refine ⟨c, ?_⟩
  rw [← hst]
  exact (hSymmetry v σ hσ c x s).1 hgive

/-- Strength order: weak concurrent actualization entails its restriction to
homogeneous things. -/
theorem homogeneousOfConcurrent {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (Facts : W → B → T → Prop) (EsseReceivedIn : B → P → Prop)
    (hCA : ConcurrentlyActualized h G EsseReceivedIn) :
    ConcurrentlyActualizedIfHomogeneous h G Facts EsseReceivedIn :=
  fun v x t z hz _ hx => hCA v x t z hz hx

open TruthCore.Causality.TimeSymmetricGiving.Control
open TruthCore.Causality.SustainingCausation.Control (trueCausesFalse noCauses)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)

/-- An order automorphism preserving the begun history fixes moment `0`. -/
private theorem begunFixesZero (σ : Int ≃o Int) (hσ : PreservesHistory begun noFacts () σ) :
    σ 0 = 0 := by
  have h1 : 0 ≤ σ 0 := by
    rcases ((hσ false 0).1).1 (Or.inr le_rfl) with h | h
    · cases h
    · exact h
  have h2 : 0 ≤ σ.symm 0 := by
    have hz : begun.IsAt () false (σ (σ.symm 0)) := by
      rw [σ.apply_symm_apply]; exact Or.inr le_rfl
    rcases ((hσ false (σ.symm 0)).1).2 hz with h | h
    · cases h
    · exact h
  have h3 : σ 0 ≤ 0 := by
    have := σ.monotone h2
    rwa [σ.apply_symm_apply] at this
  exact le_antisymm h3 h1

/-- Shifts preserve the eternal history. -/
private theorem eternalPreserved (σ : Int ≃o Int) : PreservesHistory eternal noFacts () σ :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- Omission, rival-reading and nonvacuity controls (`Control.Certificate`). -/
theorem controls : TruthCore.Causality.TimeSymmetricGiving.Control.Certificate := by
  have hom : HomogeneousIn eternal noFacts () false := by
    intro s t _ _
    refine ⟨OrderIso.addRight (t - s), eternalPreserved _, ?_⟩
    simp
  have notHom : ¬ HomogeneousIn begun noFacts () false := by
    intro hH
    obtain ⟨σ, hσ, h1⟩ := hH 0 1 (Or.inr le_rfl) (Or.inr (by omega))
    have := begunFixesZero σ hσ
    omega
  refine ⟨⟨?_, ?_, ?_, ?_, hom, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, notHom⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  -- (1) eternal inertia
  · intro v x t z _ _
    exact ⟨.inr (t - 1), by omega, trivial, fun _ _ _ hd => hd⟩
  · intro v x s t _ _ hnot
    exact absurd trivial hnot
  · intro hB
    obtain ⟨g, hg⟩ := hB () false 0 () (.inr (-1)) rfl trivial ⟨by omega, trivial, fun _ _ _ hd => hd⟩
    exact hg
  · intro hCA
    obtain ⟨g, hg⟩ := hCA () false 0 () rfl trivial
    exact hg
  · intro hC
    obtain ⟨c, _, hc⟩ := hC false () rfl
    exact hc
  · intro v c x _ hc
    exact absurd hc id
  · intro v σ _ g x t
    exact Iff.rfl
  · intro hC
    obtain ⟨g, hg⟩ := hC () false 0 () rfl hom trivial
    exact hg
  -- (2) eternal, giving at moment 0 only
  · intro x z hz
    exact ⟨true, by simp [falseReceived] at hz; simp [hz], rfl, hz⟩
  · intro v c x _ hc _
    exact ⟨0, trivial, hc.1, hc.2, rfl⟩
  · intro hS
    have := ((hS () (OrderIso.addRight (1 : Int)) (eternalPreserved _) true false 0).1
      ⟨rfl, rfl, rfl⟩)
    simp [givesAtZero] at this
  · intro hC
    obtain ⟨g, hg⟩ := hC () false 1 () rfl hom trivial
    simp [givesAtZero] at hg
  -- (3) eternal, cause never exercised
  · intro x z hz
    exact ⟨true, by simp [falseReceived] at hz; simp [hz], rfl, hz⟩
  · intro v σ _ g x t
    exact Iff.rfl
  · intro hE
    obtain ⟨t, _, hg⟩ := hE () true false (by decide) ⟨rfl, rfl⟩ ⟨0, trivial⟩
    exact hg
  · intro hC
    obtain ⟨g, hg⟩ := hC () false 0 () rfl hom trivial
    exact hg
  -- (4) begun inertia
  · intro x z hz
    exact ⟨true, by simp [falseReceived] at hz; simp [hz], rfl, hz⟩
  · intro v c x _ hc _
    exact ⟨0, Or.inr le_rfl, hc.1, hc.2, rfl⟩
  · intro v σ hσ g x t
    have h0 := begunFixesZero σ hσ
    show (g = true ∧ x = false ∧ t = 0) ↔ (g = true ∧ x = false ∧ σ t = 0)
    constructor
    · rintro ⟨hg, hx, rfl⟩
      exact ⟨hg, hx, h0⟩
    · rintro ⟨hg, hx, ht⟩
      exact ⟨hg, hx, σ.injective (ht.trans h0.symm)⟩
  · intro v x t z hz hx
    simp only [falseReceived] at hz
    subst hz
    rcases hx with hx | hx
    · cases hx
    · by_cases h0 : t = 0
      · exact ⟨.inl true, rfl, rfl, h0⟩
      · exact ⟨.inr (t - 1), by omega, Or.inr (by omega), fun _ _ _ hd => hd⟩
  · intro v x s t hst hs hnot
    rcases hs with hs | hs
    · exact absurd (Or.inl hs) hnot
    · exact absurd (Or.inr (by omega)) hnot
  · intro v x z b hz hb
    simp only [falseReceived] at hz
    subst hz
    have hb0 : b = 0 := by
      rcases hb.1 with h | h
      · cases h
      · by_contra hne
        exact hb.2 0 (by omega) (Or.inr le_rfl)
    exact ⟨true, rfl, rfl, hb0⟩
  · intro hCA
    obtain ⟨g, hg⟩ := hCA () false 1 () rfl (Or.inr (by omega))
    simp [givesAtZero] at hg
  · intro v x t z hz hH _
    simp only [falseReceived] at hz
    subst hz
    exact absurd hH notHom
  -- (5) eternal sustaining
  · intro x z hz
    exact ⟨true, by simp [falseReceived] at hz; simp [hz], rfl, hz⟩
  · intro v c x _ hc _
    exact ⟨0, trivial, hc.1, hc.2⟩
  · intro v σ _ g x t
    exact Iff.rfl
  · intro v x t z hz _
    simp only [falseReceived] at hz
    exact ⟨.inl true, rfl, hz⟩
  · intro v x t z r hz _ _
    simp only [falseReceived] at hz
    exact ⟨true, rfl, hz⟩
  · intro v x t z hz _
    simp only [falseReceived] at hz
    exact ⟨true, rfl, hz⟩
  · intro v x t z hz _ _
    simp only [falseReceived] at hz
    exact ⟨true, rfl, hz⟩
  -- (6) no explanations
  · intro v x t z r _ _ hr
    exact absurd hr id
  · intro hP
    obtain ⟨r, hr⟩ := hP () false 0 () rfl trivial
    exact hr
  · intro hCA
    obtain ⟨g, hg⟩ := hCA () false 0 () rfl trivial
    exact hg

end TruthCore.Results.Causality.TimeSymmetricGiving
