module

public import TruthCore.Explanation.ContainedSelection

@[expose] public section

namespace TruthCore.Results.Explanation.ContainedSelection

open TruthCore.Explanation.ContainedSelection
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.HistorySelection
open TruthCore.Explanation.BruteContingencyParity

theorem restrictionBoundary : RestrictionBoundary := by
  constructor
  · intro W B F A base a hn p f hp hd hc
    obtain ⟨v, hv, hnv⟩ := hc.2
    have he : SameEvidence A.holds base v a := by
      intro r hr
      exact ⟨fun _ => hn r a hr (Or.inl rfl), fun _ => hn r v hr (Or.inr hv)⟩
    exact hnv (hd.2 v hv ((hp v a he).mpr hd.1))
  · intro W B F A a fixed f hc
    obtain ⟨v, hv, hnv⟩ := hc.2
    exact hnv ((fixed v hv f).mpr hc.1)

theorem target_contingent : Contingent acting.arena 0 .target :=
  ⟨rfl, 1, trivial, Nat.noConfusion⟩

theorem act_contingent : Contingent acting.arena 0 (.member 0) := by
  refine ⟨Or.inl ⟨rfl, rfl⟩, 1, trivial, ?_⟩
  intro h
  cases h with
  | inl h => exact Nat.noConfusion h.2
  | inr h => exact Nat.noConfusion h.1

theorem original_coverage : ContingentPSR acting.arena 0 := by
  intro f h
  cases f with
  | target => exact ⟨.source true, ActingReason.sourceTarget⟩
  | other => exact False.elim (h.1 rfl)
  | source i =>
    obtain ⟨v, _, hv⟩ := h.2
    exact False.elim (hv trivial)
  | member n =>
    cases h.1 with
    | inl hn =>
      cases hn.1
      exact ⟨.source true, ActingReason.sourceAct⟩
    | inr hn => exact False.elim (hn.2 rfl)
  | whole => exact False.elim h.1

theorem cut_unexplained : ¬ Explained unexplainedAct 0 (.member 0) := by
  rintro ⟨r, _, hn⟩
  exact hn rfl

theorem original_existence_coverage :
    NoBruteContingentExistenceAt (existenceView acting.arena) 0 := by
  intro x hx
  cases x with
  | none => exact ⟨.circumstance (some true), ActingReason.sourceTarget⟩
  | some i =>
    obtain ⟨v, _, hv⟩ := hx.2
    exact False.elim (hv trivial)

theorem cut_existence_coverage :
    NoBruteContingentExistenceAt (existenceView unexplainedAct) 0 := by
  intro x hx
  cases x with
  | none =>
    exact ⟨.circumstance (some true), ActingReason.sourceTarget, Fact.noConfusion⟩
  | some i =>
    obtain ⟨v, _, hv⟩ := hx.2
    exact False.elim (hv trivial)

theorem exerciseComparison : ExerciseComparison := by
  refine ⟨rfl, fun _ _ => Iff.rfl, fun _ _ => ⟨rfl, rfl⟩,
    act_contingent, target_contingent, ActingReason.actTarget,
    ⟨ActingReason.actTarget, Fact.noConfusion⟩,
    ⟨ActingReason.sourceTarget, Fact.noConfusion⟩,
    ⟨.source true, ActingReason.sourceAct⟩, cut_unexplained,
    original_coverage, ?_, original_existence_coverage, cut_existence_coverage, ?_, ?_⟩
  · intro h
    exact cut_unexplained (h (.member 0) act_contingent)
  · intro h
    have hact := h 0 (.source true) (.member 0) ActingReason.sourceAct 1 trivial trivial
    cases hact with
    | inl h => exact Nat.noConfusion h.2
    | inr h => exact Nat.noConfusion h.1
  · intro h
    exact Nat.noConfusion
      (h 0 (.source true) .target ⟨ActingReason.sourceTarget, Fact.noConfusion⟩
        1 trivial trivial)

end TruthCore.Results.Explanation.ContainedSelection
