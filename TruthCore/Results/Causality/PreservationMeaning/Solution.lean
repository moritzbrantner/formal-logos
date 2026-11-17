module
public import TruthCore.Causality.PreservationMeaning
@[expose] public section
namespace TruthCore.Results.Causality.PreservationMeaning
open TruthCore.Causality.PreservationMeaning
open TruthCore.Causality.JointGroups

theorem cutConsequences : CutConsequences := by
  intro B E G S m e c cut
  have active : ∀ s, AvailableRecord m s e → ∃ a, m.bearer a = c ∧ m.occurs s a := by
    intro s ⟨g, admitted, target, _, members⟩
    obtain ⟨a, contributor, bearer⟩ := cut g admitted target
    exact ⟨a, bearer, members a (Or.inl contributor)⟩
  have absent : ∀ s, SourceInactive m s c → ¬ AvailableRecord m s e := by
    intro s inactive ⟨g, admitted, target, _, members⟩
    obtain ⟨a, contributor, bearer⟩ := cut g admitted target
    exact inactive g a admitted contributor bearer (members a (Or.inl contributor))
  exact ⟨active, absent, fun coverage s allowed inactive occurrence =>
    absent s inactive (coverage s allowed occurrence)⟩

open Control Control.Event
private theorem populatedLeft (r : Bool) : AvailableRecord model (true, r, true) effect := by
  refine ⟨false, True.intro, rfl, ⟨left, rfl⟩, ?_⟩
  intro a ha
  rcases ha with ha | ha
  · have h : a = left := ha
    subst a
    rfl
  · have h : a = receptive := ha
    subst a
    rfl

private theorem populatedRight (l : Bool) : AvailableRecord model (l, true, true) effect := by
  refine ⟨true, True.intro, rfl, ⟨right, rfl⟩, ?_⟩
  intro a ha
  rcases ha with ha | ha
  · have h : a = right := ha
    subst a
    rfl
  · have h : a = receptive := ha
    subst a
    rfl

private theorem sourceCut : SourceCut model effect false := by
  intro g _ _
  cases g
  · exact ⟨left, rfl, rfl⟩
  · exact ⟨right, rfl, rfl⟩

theorem controls : Controls := by
  have covered : RecordCovered model effect := by
    intro s _ occurrence
    rcases occurrence with ⟨h | h, en⟩
    · rcases s with ⟨l, r, receptive⟩
      change l = true at h
      change receptive = true at en
      subst l; subst receptive
      exact populatedLeft r
    · rcases s with ⟨l, r, receptive⟩
      change r = true at h
      change receptive = true at en
      subst r; subst receptive
      exact populatedRight l
  have cutU : SourceCut uncovered effect false := sourceCut
  have inactive : SourceInactive uncovered (false, false, true) false := by
    intro g a _ contributor _
    cases g <;> change a = _ at contributor <;> subst a <;>
      change ¬ ((false : Bool) = true) <;> intro bad <;> cases bad
  have noReal : ¬ AvailableRecord uncovered (false, false, true) effect :=
    (cutConsequences _ _ _ _ uncovered effect false cutU).2.1 _ inactive
  refine ⟨⟨populatedLeft true, sourceCut⟩, populatedLeft false, populatedRight false, ?_, ?_,
    covered, ?_, ?_, inactive, ?_, ?_⟩
  · intro ⟨g, _, _, _, members⟩
    have bad := members receptive (Or.inr rfl)
    cases bad
  · intro cut
    obtain ⟨a, ha, hb⟩ := cut false True.intro rfl
    change a = left at ha
    subst a
    cases hb
  · dsimp only
    intro cut
    obtain ⟨a, ha, hb⟩ := cut true True.intro rfl
    change a = right at ha
    subst a
    cases hb
  · refine ⟨?_, cutU⟩
    refine ⟨false, True.intro, rfl, ⟨left, rfl⟩, ?_⟩
    intro a ha
    rcases ha with ha | ha
    · have h : a = left := ha
      subst a
      trivial
    · have h : a = receptive := ha
      subst a
      trivial
  · trivial
  · intro coverage
    exact noReal (coverage _ True.intro True.intro)
end TruthCore.Results.Causality.PreservationMeaning
