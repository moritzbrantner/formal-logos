module

public import TruthCore.Alternatives.ActualHistoryIdentification
public import TruthCore.Results.Alternatives.PhysicalGround.Solution

@[expose] public section

namespace TruthCore.Results.Alternatives.ActualHistoryIdentification

open TruthCore.Alternatives.ActualHistoryIdentification
open TruthCore.Alternatives.PhysicalGround
open TruthCore.Results.Alternatives.PhysicalGround (ladder maximum_intellect maximum_will)
open TruthCore.Explanation.NoFoundationLawChaos (generated copySchedule)
open TruthCore.Science.Identifiability

private theorem switch_readout (s : Nat → Bool) (t : Nat) :
    (generated s (t + 1) != generated s t) = s t := by
  change ((if s t then !(generated s t) else generated s t) != generated s t) = s t
  cases s t <;> cases generated s t <;> rfl

private def intellectual : Profile :=
  ⟨⟨classicalRoute, copySchedule⟩, ladder.2.2.2.2.1,
    ladder.2.2.2.2.2.1, ladder.2.2.2.2.2.2.1⟩

private def impersonal : Profile :=
  ⟨⟨simpleImpersonal, copySchedule⟩, ladder.2.2.1.1,
    ladder.2.2.1.2.1, ladder.2.2.1.2.2.1⟩

theorem boundary : Boundary := by
  have same : history intellectual.val = history impersonal.val := rfl
  refine ⟨?_, ⟨intellectual, impersonal, same, trivial, trivial, id, id⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro m n eq
    funext t
    change m.val.switches t = n.val.switches t
    change history m.val = history n.val at eq
    rw [← switch_readout m.val.switches, ← switch_readout n.val.switches]
    change (history m.val (t + 1) != history m.val t) =
      (history n.val (t + 1) != history n.val t)
    rw [eq]
  · intro h
    exact Eq.mp (h intellectual impersonal same) (show (attributes intellectual.val).1 from trivial)
  · intro h
    exact Eq.mp (h intellectual impersonal same) (show (attributes intellectual.val).2 from trivial)
  · refine ⟨intellectual.val, intellectual.property, ladder.2.2.2.2.2.2.2.1, ?_⟩
    intro b hb
    cases b
    · trivial
    · exact hb
  · intro ⟨m, ⟨⟨_, structural, maximum⟩, immaterial, will⟩⟩
    apply Prod.ext
    · exact propext ⟨fun _ => trivial, fun _ => maximum_intellect m.route false structural maximum immaterial⟩
    · exact propext ⟨fun _ => trivial, fun _ => maximum_will m.route false structural maximum immaterial will⟩
  · intro I R allowed report
    exact augment_identifies_iff _ _ allowed report

end TruthCore.Results.Alternatives.ActualHistoryIdentification
