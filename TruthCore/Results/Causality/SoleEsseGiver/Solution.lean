module

public import TruthCore.Causality.SoleEsseGiver

@[expose] public section
namespace TruthCore.Results.Causality.SoleEsseGiver

open TruthCore.Causality.SoleEsseGiver
open TruthCore.Causality.Q44EssentialSource
open TruthCore.Causality.CartesianAdequacy (AtLeastAsMuchDegreeInTotalCause)
open TruthCore.Causality.EsseCauseEfficiency (EfficiencyProfile)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.Round2PerfectionPrimacy (OthersThanPrimaryParticipateEsse)
open TruthCore.Causality.TermSenseForks (SomeBeingGreatestInBeing)
open TruthCore.Logic (ExcludedMiddle)

theorem soleGiverOfSelection {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (s : B)
    (hExists : ActualParticipantExists f Participated)
    (hLocal : ParticipatedHasEssentialSource f Participated OwnBeing)
    (hOne : RelevantEssentialSourcesSelected f Participated OwnBeing s) :
    SoleEssentialGiver f Participated OwnBeing s := by
  refine ⟨hExists, ?_⟩
  intro x _ hx
  obtain ⟨c, hne, ha, ho, he⟩ := hLocal x hx
  have hcs := hOne c x hx hne ha ho he
  exact ⟨hcs ▸ ⟨hne, ha, ho, he⟩, fun y => hOne y x hx⟩

theorem boundOfAdequacy {B P R D : Type} [Preorder D] (q : EfficiencyProfile B P R)
    (Participated OwnBeing : B → Prop) (s : B)
    (Total : B → B → R → Prop) (degree : R → B → D)
    (hSource : SoleEssentialGiver q.toProfile Participated OwnBeing s)
    (hWhole : EssentialGivingIsEfficientAndTotal q Participated OwnBeing Total)
    (hAdequate : AtLeastAsMuchDegreeInTotalCause (efficientGrades q) Total degree) :
    BoundsParticipatedEsse q.toProfile Participated degree s := by
  obtain ⟨w, hw, hp⟩ := hSource.1
  refine ⟨(hSource.2 w hw hp).1.2.1, ?_⟩
  intro x ha hx
  obtain ⟨hne, hs, ho, hc⟩ := (hSource.2 x ha hx).1
  obtain ⟨he, ht⟩ := hWhole s x ha hx hne hs ho hc
  exact hAdequate s x q.esse ⟨⟨rfl, he⟩, ht⟩

theorem greatestOfCoverage {B P R D : Type} [Preorder D] (f : Profile B P R)
    (Participated : B → Prop) (s : B) (degree : R → B → D)
    (hBound : BoundsParticipatedEsse f Participated degree s)
    (hCover : OthersThanPrimaryParticipateEsse Participated s)
    (hEM : ExcludedMiddle) :
    SomeBeingGreatestInBeing f.InAct f.esse (degree f.esse) := by
  refine ⟨s, hBound.1, ⟨s, hBound.1, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rcases hEM (x = s) with rfl | hne
  · exact le_rfl
  · exact hBound.2 x hx (hCover x hne)

theorem equalDegree : EqualDegreeControl := by
  let q : EfficiencyProfile Bool Bool Unit := {
    InAct := fun _ _ => True
    CausesIn := fun c x _ => c = true ∧ x = false
    essenceOf := fun _ => false
    esseOf := fun x => !x
    essentialPrinciplesAloneSufficeForEsse := fun _ => False
    esse := ()
    EfficientlyCausesEsse := fun c x => c = true ∧ x = false }
  refine ⟨q, fun _ _ => 1, ⟨⟨false, trivial, rfl⟩, ?_⟩, ?_, ?_, ?_, rfl, rfl, by decide, ?_⟩
  · intro x _ hx
    subst x
    exact ⟨⟨by decide, trivial, rfl, rfl, rfl⟩, fun _ _ _ ho _ => ho⟩
  · intro c x _ _ _ _ _ hc
    exact ⟨hc, hc⟩
  · intro _ _ _ _
    exact le_rfl
  · exact ⟨trivial, fun _ _ _ => le_rfl⟩
  · intro h
    have impossible : 2 ≤ 1 := h true false () ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩
    exact (by decide : ¬ 2 ≤ 1) impossible

end TruthCore.Results.Causality.SoleEsseGiver
