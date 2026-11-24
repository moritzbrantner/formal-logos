module

public import TruthCore.Causality.RestatedPremises

/-!
# Restated premises: instances of Aristotelian grounding and equivalences (#1926)

The universal Aristotelian grounding principle entails two of its
single-proposition instances that the Pruss routes use as bare premises, by
instantiation only. The controls prove the three registered equivalences by
`Iff.rfl`, show that the three grounding instances hold on a frame where the
universal principle fails, and that the universal principle is satisfiable on
the same frame. No premise is proved here.
-/

@[expose] public section

namespace TruthCore.Results.Causality.RestatedPremises

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Causality.RestatedPremises
open TruthCore.Causality.ComponentFirstness (ParticipatedHasOtherCause)
open TruthCore.Causality.Round2Grounding (ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.Round3CogitoBase (SelectedBearsOccurringThought)
open TruthCore.Causality.CartesianIdeaOfInfinite (IdeaFrame MeditatorThinks)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.ModalGrounding (ActualAbsenceGrounded SomeContingentConcreteAt
  NoActualContingentConcreteIn NoContingentConcreteIn)
open TruthCore.Modal.PrussPowerPremises (ActualityGroundedAtAbsenceWorlds)

variable {W B T R : Type}

/-- The universal grounding principle gives P1′, its instance at `w` for the
joint absence of the concreta contingent at `w`. Instantiation only. -/
theorem actualAbsenceGroundedOfEverywhere (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hAll : AristotelianGroundingEverywhere F PowerFor) :
    ActualAbsenceGrounded F PowerFor concrete w :=
  hAll w _

/-- The universal grounding principle gives grounding, at each absence world,
of `w`'s obtaining. Instantiation only. -/
theorem actualityGroundedAtAbsenceWorldsOfEverywhere (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hAll : AristotelianGroundingEverywhere F PowerFor) :
    ActualityGroundedAtAbsenceWorlds F PowerFor concrete w :=
  fun v _ _ => hAll v _

/-- The ad 1 and co. readings of q.44 a.1 are the same proposition. -/
theorem participatedCauseReadingsIff {B R : Type} (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) :
    ParticipatedHasOtherCause Participated CausesIn esse ↔
      ParticipatedEsseHasDistinctCause Participated CausesIn esse :=
  Iff.rfl

/-- The meditator's cogito is the selected-bearer premise at the idea frame's
fields. -/
theorem meditatorThinksIff {B R Episode : Type} (I : IdeaFrame B R Episode) :
    MeditatorThinks I ↔ SelectedBearsOccurringThought I.Occurs I.Bears I.me :=
  Iff.rfl

/-- Some contingent concretum on a frame is the same proposition on its ground
profile, whatever the grounding relation. -/
theorem someContingentConcreteIff (F : CausalityFrame W B T R) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W) :
    SomeContingentConcreteAt F concrete w ↔
      SomeActualContingentAt (groundProfile F concrete grounds) w :=
  Iff.rfl

namespace Control

open TruthCore.Causality.RestatedPremises.Control
open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 allC)

theorem a_ne_b : V3.a ≠ V3.b := fun h => by cases h

theorem not_sepEx_b {x : Bg} (hx : x ≠ .g) : ¬ sepEx .b x := fun h => by
  rcases h with h | h
  · exact hx h
  · exact h rfl

theorem g_not_contingent (v : V3) : ¬ ContingentAt sepFrame.history.ontic v .g :=
  fun hc => by
    obtain ⟨_, _, hn⟩ := hc.2
    exact hn (Or.inl rfl)

theorem c_contingent_a : ContingentAt sepFrame.history.ontic .a .c :=
  ⟨Or.inr a_ne_b, .b, trivial, not_sepEx_b (fun h => by cases h)⟩

theorem noActualAtB : NoActualContingentConcreteIn sepFrame allC .a .b := by
  intro x _ hc hx
  cases x with
  | g => exact g_not_contingent .a hc
  | c => exact not_sepEx_b (fun h => by cases h) hx
  | d => exact not_sepEx_b (fun h => by cases h) hx

theorem noContingentAtB : NoContingentConcreteIn sepFrame allC .b := by
  intro x _ hc
  cases x with
  | g => exact g_not_contingent .b hc
  | c => exact not_sepEx_b (fun h => by cases h) hc.1
  | d => exact not_sepEx_b (fun h => by cases h) hc.1

theorem absenceWorldIsB {v : V3}
    (hNo : NoActualContingentConcreteIn sepFrame allC .a v) : v = .b := by
  cases v with
  | a => exact absurd (Or.inr a_ne_b) (hNo .c trivial c_contingent_a)
  | b => rfl
  | z => exact absurd (Or.inr (fun h => by cases h)) (hNo .c trivial c_contingent_a)

theorem groundingInstancesWithoutUniversal : GroundingInstancesWithoutUniversal := by
  refine ⟨⟨.b, trivial, noActualAtB⟩, ⟨.c, trivial, c_contingent_a⟩,
    fun _ _ => ⟨.g, Or.inl rfl, rfl, Or.inl ⟨rfl, noActualAtB⟩⟩, ?_,
    fun _ _ => ⟨.g, Or.inl rfl, rfl, Or.inl ⟨rfl, noContingentAtB⟩⟩, ?_⟩
  · intro v _ hNo
    cases absenceWorldIsB hNo
    exact fun _ _ => ⟨.g, Or.inl rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
  · intro hAll
    obtain ⟨_, _, _, hp⟩ := hAll .a (fun u => u = .z) ⟨.z, trivial, rfl⟩
      (fun h => by cases h)
    rcases hp with ⟨_, hb⟩ | ⟨hab, _⟩
    · cases hb
    · cases hab

theorem universalGroundingSatisfiable : UniversalGroundingSatisfiable :=
  fun _ _ _ _ => ⟨.g, Or.inl rfl, rfl⟩

end Control

/-- The restated-premise controls. -/
theorem restatedPremisesControls : RestatedPremisesControls :=
  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ _ _ => Iff.rfl,
    Control.groundingInstancesWithoutUniversal, Control.universalGroundingSatisfiable⟩

end TruthCore.Results.Causality.RestatedPremises
