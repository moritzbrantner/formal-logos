module

public import TruthCore.Logic.BeliefReasonWitness
public import TruthCore.Results.Logic.EpistemicAuthority.Solution

@[expose] public section

namespace TruthCore.Results.Logic.BeliefReasonWitness

open TruthCore.Logic.EpistemicReasons TruthCore.Logic.EpistemicReasonDefinitionFork
open TruthCore.Logic.EpistemicAuthority TruthCore.Logic.BeliefReasonWitness

theorem reasonsFromConcession (f : Frame) (hConcession : ActualForceConcession f)
    (hPresentation : ConsiderationPresentation f) : ThereAreEpistemicReasons f.Reason := by
  obtain ⟨a, r, p, hOrd, _⟩ := hConcession
  exact ⟨a, p, (hPresentation a p).mpr ⟨r, hOrd.1⟩⟩

/-- The reverse direction alone at the supplied witness suffices. -/
theorem reasonAtBelief (f : Frame) (a : f.Agent) (r : f.Consideration) (p : f.Content)
    (hAttributed : f.CountsAsReason a r (f.believe p))
    (hLink : (∃ s, f.CountsAsReason a s (f.believe p)) → f.Reason a p) :
    f.Reason a p := by
  exact hLink ⟨r, hAttributed⟩

theorem suspensionControl (aim : Preference → Prop) (hActual : aim .accuracy) :
    let f := suspension aim
    OrdinaryDefinition f ∧ ConsiderationPresentation f ∧ GoalRelativeForce f aim ∧
    OrdinaryInstance f () .count (Sum.inr .even) ∧
    f.force () .count (Sum.inr .even) (f.actualPreference ()) ∧
    EpistemicNihilism f.Reason ∧ ¬ ActualForceConcession f := by
  dsimp only
  refine ⟨?_, ?_, ?_, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩,
    ⟨⟨rfl, rfl⟩, hActual⟩, fun _ _ h => h, ?_⟩
  · intro _ _ _
    exact ⟨fun h => ⟨trivial, trivial, h⟩, fun h => h.2.2⟩
  · intro _ _
    exact ⟨False.elim, fun ⟨_, _, h⟩ => nomatch h⟩
  · intro _ _ _ _
    exact ⟨fun h => ⟨⟨trivial, trivial, h.1⟩, h.2⟩, fun h => ⟨h.1.2.2, h.2⟩⟩
  · rintro ⟨_, _, _, h, _⟩
    exact nomatch h.1.2

theorem independentSuspension :
    SomePreferenceIndependentReason (suspension allAim) ∧
    EpistemicNihilism (suspension allAim).Reason := by
  exact ⟨⟨(), .count, Sum.inr .even, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩,
    fun _ => ⟨⟨rfl, rfl⟩, trivial⟩⟩, fun _ _ h => h⟩

theorem withoutPresentation :
    ActualForceConcession unlinked ∧ ¬ ConsiderationPresentation unlinked ∧
    EpistemicNihilism unlinked.Reason := by
  have h := TruthCore.Results.Logic.EpistemicAuthority.controls.1
  exact ⟨h.2.2.2.1, fun hp => (hp () .even).mpr ⟨.count, rfl, rfl⟩, fun _ _ hf => hf⟩

theorem differentContent :
    ActualForceConcession selectedDenial ∧ ConsiderationPresentation selectedDenial ∧
    selectedDenial.Reason () .even ∧
    ExpressesNihilism selectedDenial.Reason selectedDenial.Holds .rain ∧
    (∀ a, ¬ selectedDenial.Reason a .rain) := by
  have h := TruthCore.Results.Logic.EpistemicAuthority.controls.1
  refine ⟨h.2.2.2.1, h.2.1, rfl, ?_, ?_⟩
  · constructor
    · intro hn
      cases hn
    · intro hn
      exact (hn () .even rfl).elim
  · intro _ hr
    cases hr

end TruthCore.Results.Logic.BeliefReasonWitness
