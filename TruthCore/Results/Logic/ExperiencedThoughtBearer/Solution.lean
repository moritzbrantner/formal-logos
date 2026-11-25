module

public import TruthCore.Logic.ExperiencedThoughtBearer
public import TruthCore.Logic.CogitoConcrete

@[expose] public section

namespace TruthCore.Results.Logic.ExperiencedThoughtBearer

open TruthCore.Logic.AssertionRetorsion (ExperienceOccurs)
open TruthCore.Logic.ExperiencedThoughtBearer (ExperiencedThoughtsHaveBearers BearerScopeControl)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.German.Kant.CosmologicalInference (Ontic)

/-- The bearer principle is needed only on the phenomenal part of the
occurring thoughts. Retain the episode when introducing its subject. -/
theorem subjectOfExperience {Episode Subject : Type}
    (Occurs Experienced : Episode → Prop) (Bears : Subject → Episode → Prop)
    (hExperience : ExperienceOccurs Occurs Experienced)
    (hBearer : ExperiencedThoughtsHaveBearers Occurs Experienced Bears) :
    SomeThinkingSubject Occurs Bears := by
  obtain ⟨e, hOccurs, hExperienced⟩ := hExperience
  obtain ⟨b, hb⟩ := hBearer e hOccurs hExperienced
  exact ⟨b, e, hOccurs, hb⟩

/-- Two occurring thoughts. Only the first is experienced and borne.
Removing all bearers leaves that very same phenomenal occurrence. -/
theorem bearerScopeControl : BearerScopeControl := by
  refine ⟨⟨false, trivial, rfl⟩, fun e _ he => ⟨(), he⟩, ?_, ?_⟩
  · intro h
    obtain ⟨_, hFalse⟩ := h true trivial
    cases hFalse
  · rintro ⟨_, _, _, hFalse⟩
    exact hFalse

/-- Concreteness and selected-world existence apply to the very same
bearer of the very same occurring thought. -/
theorem populationOfThinkingSubject {W B Episode : Type}
    (m : Ontic W B) (concrete : B → Prop) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hSubject : SomeThinkingSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears concrete)
    (hExists : EveryBearerExistsAt m Occurs Bears w) :
    InhabitedConcreteAt m concrete w := by
  obtain ⟨b, e, he, hb⟩ := hSubject
  exact ⟨b, hConcrete b e he hb, hExists b e he hb⟩

end TruthCore.Results.Logic.ExperiencedThoughtBearer
