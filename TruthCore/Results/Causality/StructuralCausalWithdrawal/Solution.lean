module

public import TruthCore.Causality.StructuralCausalWithdrawal

@[expose] public section

namespace TruthCore.Results.Causality.StructuralCausalWithdrawal

open TruthCore.Causality.StructuralCausalModel
open TruthCore.Causality.StructuralCausalModel.Withdrawal
open TruthCore.Explanation.MechanismInterventionParity (Observation)

/-- Bind the computed cut responses to the corresponding history-level
counterinstances under the two supplied calibrations. -/
theorem calibratedContrast : CalibratedContrast := by
  intro W B T R P Q order F Allowed D X E before cut giver bearer earlier later
  obtain ⟨_, loss, survival⟩ := Mechanism.single_channel_contrast
  constructor
  · intro calibration principle reason received explains
    have present := calibration.readoutCut.mp (congrArg Observation.effect survival)
    refine ⟨present, ?_⟩
    intro bridge
    obtain ⟨candidate, gives⟩ := bridge cut bearer later principle reason received present explains
    by_cases same : candidate = giver
    · subst candidate
      have channelOff := congrArg Observation.b survival
      exact Bool.false_ne_true (channelOff.symm.trans (calibration.channelCut.mpr gives))
    · exact calibration.otherAbsent candidate same gives
  · intro calibration
    have absent : ¬ F.history.IsAt cut bearer later := fun present =>
      Bool.false_ne_true
        ((congrArg Observation.effect loss).symm.trans (calibration.readoutCut.mpr present))
    have began := calibration.earlierCut.mp (congrArg Observation.a loss)
    refine ⟨absent, ?_⟩
    intro law
    obtain ⟨u, lower, upper, inducer⟩ := law cut bearer earlier later calibration.ordered began.1 absent
    exact calibration.noLossCut u lower upper inducer

end TruthCore.Results.Causality.StructuralCausalWithdrawal
