module

public import TruthCore.Causality.BegunOrHomogeneousGiving
public import TruthCore.Results.Causality.TimeSymmetricGiving.Solution

@[expose] public section

namespace TruthCore.Results.Causality.BegunOrHomogeneousGiving

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized)
open TruthCore.Causality.SustainingDependence (ConcurrentlyActualizedOnceBegun)
open TruthCore.Causality.TimeSymmetricGiving
  (HomogeneousIn PreservesHistory ConcurrentlyActualizedIfHomogeneous)
open TruthCore.Causality.BegunOrHomogeneousGiving

/-- The begun restriction, the homogeneous restriction and coverage by the two
cases give weak concurrent actualization `40a97664`: a present received-esse
thing either has a first moment of presence, and the begun restriction applies,
or is homogeneous, and the homogeneous restriction applies. -/
theorem concurrentOfBegunOrHomogeneous {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (Facts : W → B → T → Prop) (EsseReceivedIn : B → P → Prop)
    (hBegun : ConcurrentlyActualizedOnceBegun h G EsseReceivedIn)
    (hHom : ConcurrentlyActualizedIfHomogeneous h G Facts EsseReceivedIn)
    (hCover : BegunOrHomogeneous h Facts EsseReceivedIn) :
    ConcurrentlyActualized h G EsseReceivedIn := by
  intro v x t z hz hx
  rcases hCover v x t z hz hx with ⟨b, hb⟩ | hH
  · exact hBegun v x z b hz hb t hx
  · exact hHom v x t z hz hH hx

open TruthCore.Causality.TimeSymmetricGiving.Control (eternal begun noGivingZ givesAtZero
  givesAlways noFacts)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)
open TruthCore.Causality.BegunOrHomogeneousGiving.Control

/-- Nothing has a first moment of presence in the eternal history. -/
private theorem eternalNoBeginning (x : Bool) (b : Int) : ¬ BeginsAt eternal () x b :=
  fun hb => hb.2 (b - 1) (by omega) trivial

/-- An order automorphism preserving the mark at moment `0` fixes `0`. -/
private theorem markedFixesZero (σ : Int ≃o Int)
    (hσ : PreservesHistory eternal markedZero () σ) : σ 0 = 0 :=
  (((hσ false 0).2).1 ⟨rfl, rfl⟩).2

/-- With moment `0` marked, `false` is not homogeneous in the eternal history. -/
private theorem markedNotHomogeneous : ¬ HomogeneousIn eternal markedZero () false := by
  intro hH
  obtain ⟨σ, hσ, h01⟩ := hH 0 1 trivial trivial
  have := markedFixesZero σ hσ
  omega

/-- Shifts preserve the unmarked eternal history, so `false` is homogeneous. -/
private theorem eternalHomogeneous : HomogeneousIn eternal noFacts () false := by
  intro s t _ _
  exact ⟨OrderIso.addRight (t - s), fun _ _ => ⟨Iff.rfl, Iff.rfl⟩, by simp⟩

/-- In the begun history `false` first appears at moment `0`. -/
private theorem begunAtZero : BeginsAt begun () false 0 :=
  ⟨Or.inr le_rfl, fun s hs h => by
    rcases h with h | h
    · cases h
    · omega⟩

/-- Omission and strictness controls (`Control.Certificate`). -/
theorem controls : Certificate := by
  have notCA : ¬ ConcurrentlyActualized eternal noGivingZ falseReceived := by
    intro hCA
    obtain ⟨g, hg⟩ := hCA () false 0 () rfl trivial
    exact hg
  have begunVacuous : ConcurrentlyActualizedOnceBegun eternal noGivingZ falseReceived :=
    fun _ x _ b _ hb => absurd hb (eternalNoBeginning x b)
  have notCover : ¬ BegunOrHomogeneous eternal markedZero falseReceived := by
    intro hC
    rcases hC () false 0 () rfl trivial with ⟨b, hb⟩ | hH
    · exact eternalNoBeginning false b hb
    · exact markedNotHomogeneous hH
  refine ⟨⟨begunVacuous, ?_, notCover, notCA⟩, ⟨begunVacuous, ?_, ?_, notCA⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, notCover⟩⟩
  -- (1) the homogeneous restriction is vacuous: `false` is not homogeneous
  · intro v x t z hz hH _
    simp only [falseReceived] at hz
    subst hz
    exact absurd hH markedNotHomogeneous
  -- (2) coverage by homogeneity; the homogeneous restriction fails
  · intro v x t z hz _
    simp only [falseReceived] at hz
    subst hz
    exact Or.inr eternalHomogeneous
  · intro hH
    obtain ⟨g, hg⟩ := hH () false 0 () rfl eternalHomogeneous trivial
    exact hg
  -- (3) the begun history with giving at moment `0` only
  · exact TruthCore.Results.Causality.TimeSymmetricGiving.controls.2.2.2.1.2.2.2.2.2.2.2.1
  · intro v x t z hz _
    simp only [falseReceived] at hz
    subst hz
    exact Or.inl ⟨0, begunAtZero⟩
  · intro hB
    obtain ⟨g, hg⟩ := hB () false () 0 rfl begunAtZero 1 (Or.inr (by omega))
    simp [givesAtZero] at hg
  · exact TruthCore.Results.Causality.TimeSymmetricGiving.controls.2.2.2.1.2.2.2.2.2.2.1
  -- (4) eternal sustaining with a marked moment
  · intro v x t z hz _
    simp only [falseReceived] at hz
    exact ⟨true, rfl, hz⟩

/-- Populated nonvacuity witness (`Control.Nonvacuity`). -/
theorem nonvacuity : Nonvacuity := by
  have hCA : TruthCore.Causality.ConcurrentActualization.ConcurrentlyActualized
      eternal givesAlways falseReceived := by
    intro v x t z hz _
    simp only [falseReceived] at hz
    exact ⟨true, rfl, hz⟩
  refine ⟨⟨false, 0, rfl, trivial⟩, fun v x z _ hz _ t ht => hCA v x t z hz ht,
    fun v x t z hz _ ht => hCA v x t z hz ht, ?_, hCA⟩
  intro v x t z hz _
  simp only [falseReceived] at hz
  subst hz
  exact Or.inr eternalHomogeneous

end TruthCore.Results.Causality.BegunOrHomogeneousGiving
