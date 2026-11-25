import TruthCore.Logic.BeliefReasonWitness

namespace TruthCore.Results.Logic.BeliefReasonWitness

open TruthCore.Logic.EpistemicReasons TruthCore.Logic.EpistemicReasonDefinitionFork
open TruthCore.Logic.EpistemicAuthority TruthCore.Logic.BeliefReasonWitness

theorem reasonsFromConcession (f : Frame) (hConcession : ActualForceConcession f)
    (hPresentation : ConsiderationPresentation f) : ThereAreEpistemicReasons f.Reason := by
  sorry

/-- The reverse direction alone at the supplied witness suffices. -/
theorem reasonAtBelief (f : Frame) (a : f.Agent) (r : f.Consideration) (p : f.Content)
    (hAttributed : f.CountsAsReason a r (f.believe p))
    (hLink : (∃ s, f.CountsAsReason a s (f.believe p)) → f.Reason a p) :
    f.Reason a p := by
  sorry

theorem suspensionControl (aim : Preference → Prop) (hActual : aim .accuracy) :
    let f := suspension aim
    OrdinaryDefinition f ∧ ConsiderationPresentation f ∧ GoalRelativeForce f aim ∧
    OrdinaryInstance f () .count (Sum.inr .even) ∧
    f.force () .count (Sum.inr .even) (f.actualPreference ()) ∧
    EpistemicNihilism f.Reason ∧ ¬ ActualForceConcession f := by
  sorry

theorem independentSuspension :
    SomePreferenceIndependentReason (suspension allAim) ∧
    EpistemicNihilism (suspension allAim).Reason := by
  sorry

theorem withoutPresentation :
    ActualForceConcession unlinked ∧ ¬ ConsiderationPresentation unlinked ∧
    EpistemicNihilism unlinked.Reason := by
  sorry

theorem differentContent :
    ActualForceConcession selectedDenial ∧ ConsiderationPresentation selectedDenial ∧
    selectedDenial.Reason () .even ∧
    ExpressesNihilism selectedDenial.Reason selectedDenial.Holds .rain ∧
    (∀ a, ¬ selectedDenial.Reason a .rain) := by
  sorry

end TruthCore.Results.Logic.BeliefReasonWitness
