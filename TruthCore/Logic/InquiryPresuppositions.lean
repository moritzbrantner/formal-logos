module

public import TruthCore.Logic.AssertionRetorsion
public import TruthCore.Logic.CaseNonContradiction
public import TruthCore.Logic.CogitoSubject
public import TruthCore.Logic.EpistemicReasonBearer
public import TruthCore.Logic.EpistemicReasonDefinitionFork

/-!
# What one occurrence or belief reason witnesses

The actual-inquiry comparisons keep the subject, content and surviving basis
fixed. The two attitude controls use the existing independence profile and a
sum distinguishing belief from suspension with the same subject matter.
-/

@[expose] public section

namespace TruthCore.Logic.InquiryPresuppositions

open TruthCore.Logic.AssertionRetorsion
open TruthCore.Logic.CaseNonContradiction
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.EpistemicReasonBearer
open TruthCore.Logic.EpistemicReasonDefinitionFork
open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.GlobalThesisBoundaries

universe u v

theorem reasonWitnessInhabitsBothDomains {A : Sort u} {C : Sort v} {R : A → C → Prop}
    (h : ThereAreEpistemicReasons R) :
    Nonempty A ∧ Nonempty C ∧
    (∃ a, ¬ ∀ p, ¬ R a p) ∧ (∃ p, ¬ ∀ a, ¬ R a p) := by
  obtain ⟨a, p, hr⟩ := h
  exact ⟨⟨a⟩, ⟨p⟩, ⟨a, fun hn => hn p hr⟩,
    ⟨p, fun hn => hn a hr⟩⟩

theorem expressedNihilismFails {A : Sort u} {C : Sort v} {R : A → C → Prop}
    {Holds : C → Prop} {n : C}
    (h : ThereAreEpistemicReasons R)
    (hexpr : ExpressesNihilism R Holds n) : ¬ Holds n := by
  obtain ⟨a, p, hr⟩ := h
  exact fun ht => (hexpr.mp ht) a p hr

theorem reasonWitnessRespectsNoncontradiction {A : Sort u} {C : Sort v} {R : A → C → Prop}
    (h : ThereAreEpistemicReasons R)
    (nc : CasePredicateNonContradiction.{u,v}) :
    ∃ a p, R a p ∧ ¬ (R a p ∧ ¬ R a p) := by
  obtain ⟨a, p, hr⟩ := h
  exact ⟨a, p, hr, nc A C R a p⟩

theorem observedEpisodeOccurs {W E : Type} (Occurs Seen : W → E → Prop) (w0 : W)
    (actualAccess : ∃ e, Seen w0 e)
    (accessFactive : ∀ w e, Seen w e → Occurs w e) :
    ThoughtOccurs (Occurs w0) ∧
      ¬ ∃ w, (∃ e, Seen w e) ∧ ¬ ThoughtOccurs (Occurs w) := by
  have witness (w : W) : (∃ e, Seen w e) → ThoughtOccurs (Occurs w) := by
    rintro ⟨e, he⟩
    exact ⟨e, accessFactive w e he⟩
  refine ⟨witness w0 actualAccess, ?_⟩
  rintro ⟨w, ha, hn⟩
  exact hn (witness w ha)

theorem survivingOccurrenceBasis (f : ReliabilityFrame) (R : f.Agent → f.Content → Prop)
    (a : f.Agent) (bExternal bOccurrence : f.Basis) (q : f.Content)
    (bad : f.undercuts a bExternal)
    (good : f.supports a bOccurrence q)
    (retained : ¬ f.undercuts a bOccurrence)
    (counts : SurvivingBasisGivesReason f R) :
    bExternal ≠ bOccurrence ∧ UndefeatedSupport f a q ∧
      R a q ∧ ThereAreEpistemicReasons R := by
  have hr := counts a bOccurrence q good retained
  refine ⟨?_, ⟨bOccurrence, good, retained⟩, hr, ⟨a, q, hr⟩⟩
  intro heq
  exact retained (heq ▸ bad)

theorem experiencedPrimaryOrChallenge {W E : Type}
    (Occurs Experienced Primary Challenge : W → E → Prop) (w0 : W)
    (hActual : (∃ e, Primary w0 e) ∨ (∃ e, Challenge w0 e))
    (hPrimary : ∀ w e, Primary w e → Occurs w e ∧ Experienced w e)
    (hChallenge : ∀ w e, Challenge w e → Occurs w e ∧ Experienced w e) :
    ExperienceOccurs (Occurs w0) (Experienced w0) ∧
      ¬ ∃ w, ((∃ e, Primary w e) ∨ (∃ e, Challenge w e)) ∧
        NoExperienceOccurs (Occurs w) (Experienced w) := by
  have witness (w : W)
      (h : (∃ e, Primary w e) ∨ (∃ e, Challenge w e)) :
      ExperienceOccurs (Occurs w) (Experienced w) := by
    rcases h with ⟨e, he⟩ | ⟨e, he⟩
    · exact ⟨e, hPrimary w e he⟩
    · exact ⟨e, hChallenge w e he⟩
  refine ⟨witness w0 hActual, ?_⟩
  rintro ⟨w, he, hn⟩
  exact hn (witness w he)

theorem preferenceIndependentReasonForFalseContent :
    IndependentInstance independent () Consideration.count
      (independent.believe Content.even) ∧
    ¬ independent.Holds (independent.about (independent.believe Content.even)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩
  · intro d
    cases d <;> exact ⟨rfl, rfl⟩
  · intro h
    cases h

theorem everyIndependentAttitudeIsBelief (t : independent.Attitude) :
    ∃ p : independent.Content, independent.believe p = t := by
  exact ⟨t, rfl⟩

theorem beliefAndSuspensionAboutSameContent {C : Type} (p : C) :
    Sum.elim id id (Sum.inl p : Sum C C) = p ∧
    Sum.elim id id (Sum.inr p : Sum C C) = p := ⟨rfl, rfl⟩

theorem suspensionDiffersFromBelief {C : Type} (p q : C) :
    (Sum.inr p : Sum C C) ≠ Sum.inl q := by
  intro h
  cases h

end TruthCore.Logic.InquiryPresuppositions
