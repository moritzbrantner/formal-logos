module

public import TruthCore.Ethics.TrolleyRowe
public import TruthCore.Results.Ethics.Trolley.Solution

/-! Which sense of "wholly good" yields Rowe's permission constraint
(analyst formulation; attribution deferred). -/

@[expose] public section

namespace TruthCore.Results.Ethics.TrolleyRowe
open TruthCore.Ethics.Trolley TruthCore.Ethics.TrolleyRowe TruthCore.English.Rowe
open TruthCore.Results.Ethics.Trolley (switch_notMeans chainMeans loop_means sideEffect_notMeans)

/-- WHOLLY_GOOD_1 with the outcome bridge yields Rowe's simplified permission
constraint: an unblocked preventable suffering would be strictly better prevented,
which an outcome-minimizing wholly good being does not permit. -/
theorem outcomeSenseYieldsPermissionConstraint (s : Sig) (W : PreventionWays s)
    (hO : OutcomeStandard s W) (hB : UnblockedPreventionBetter s W) :
    PermissionConstraintReading s := by
  intro b e _ hG hOcc _ hC
  exact Classical.byContradiction fun hNo => hO b e hG hOcc hC (hB b e hC hNo)

/-- WHOLLY_GOOD_2 with the same bridge yields only the constraint-qualified
permission condition. -/
theorem constraintSenseYieldsQualifiedConstraint (s : Sig) (W : PreventionWays s)
    (hS : ConstraintStandard s W) (hB : UnblockedPreventionBetter s W) :
    ConstraintQualifiedPermission s W := by
  intro b e _ hG hOcc _ hC
  rcases hS b e hG hOcc hC with h | h
  · left
    exact Classical.byContradiction fun hNo => h (hB b e hC hNo)
  · exact Or.inr h

/-- One being, one occurring preventable intense suffering, no costs at all. -/
def costFreeSig : Sig where
  Being := Unit
  Event := Unit
  Outcome := Unit
  Omniscient _ := True
  Omnipotent _ := True
  WhollyGood _ := True
  Occurs _ := True
  IntenseSuffering _ := True
  CanPrevent _ _ := True
  Cost _ _ _ := False
  GreaterGood _ _ := True
  EqualOrWorseEvil _ _ := True
  RecognizesCost _ _ _ := False

theorem costFree_theistic : TheisticBeingExists costFreeSig := ⟨(), trivial, trivial, trivial⟩

theorem costFree_noConstraint : ¬ PermissionConstraintReading costFreeSig := by
  intro h
  obtain ⟨_, hc, _⟩ := h () () trivial trivial trivial trivial trivial
  exact hc

theorem harmless_notMeans : ¬ HarmIsCausalMeans harmlessRescue := by
  intro ⟨_, hAvoid⟩
  exact hAvoid (Relation.ReflTransGen.single ⟨rfl, by decide⟩)

theorem controls : GoodnessSenseControls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨costFreeSig, ⟨fun _ _ w => w = footbridgeCase, fun _ _ => True⟩,
      fun _ _ _ _ => trivial, ?_, costFree_theistic, costFree_noConstraint⟩
    intro _ _ _ _ _
    refine Or.inr ⟨⟨footbridgeCase, rfl⟩, ?_⟩
    intro w hw
    subst hw
    exact Or.inr (Or.inl rfl)
  · intro s W hQ b e hK hG hOcc hI hC hw
    rcases hQ b e hK hG hOcc hI hC with h | h
    · exact h
    · obtain ⟨w, hw, hn⟩ := hw
      exact absurd (h.2 w hw) hn
  · refine ⟨costFreeSig, Unit, fun _ _ => True, fun _ _ => True, fun _ _ _ => True,
      fun _ _ _ => True, (), ⟨?_, ?_⟩, costFree_theistic, costFree_noConstraint⟩
    · intro _ _
      exact ⟨trivial, fun _ _ _ _ => trivial⟩
    · intro _ _ _ _
      exact ⟨(), trivial, trivial⟩
  · exact ⟨costFreeSig, ⟨fun _ _ _ => False, fun _ _ => False⟩,
      fun _ _ _ _ _ h => h, costFree_theistic, costFree_noConstraint⟩
  · refine ⟨?_, ?_, ?_, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl),
      Or.inr (Or.inr (loop_means _ rfl)), by decide⟩
    · rintro (h | h | h)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact switch_notMeans _ rfl h
    · rintro (h | h | h)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact sideEffect_notMeans h
    · rintro (h | h | h)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact harmless_notMeans h
  · intro s Way
    constructor
    · rintro ⟨_, hO, hB⟩ b e hG hOcc hC
      exact Classical.byContradiction fun hNo => hO b e hG hOcc hC (hB b e hC hNo)
    · intro h
      refine ⟨fun b e => ¬ BlockingCost s b e, ?_, fun _ _ _ hNo => hNo⟩
      intro b e hG hOcc hC hNo
      exact hNo (h b e hG hOcc hC)

end TruthCore.Results.Ethics.TrolleyRowe
