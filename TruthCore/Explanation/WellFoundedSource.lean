module

public import Mathlib.Order.WellFounded
public import TruthCore.Explanation.ExistencePSR
public import TruthCore.Models.PSR
public import TruthCore.Logic.RootDescent

/-!
# Existence-PSR, a causal source, and well-foundedness

An explanation of an existence fact need not be an efficient cause of the
individual. This source-free conditional argument reuses the existing PSR
signature and explicitly restricts causation to one world. The sources it
finds are merely without an *existing incoming cause* at that world; neither
their necessity, uniqueness, reality, intrinsic explanatory sufficiency nor
divinity is encoded.
-/

@[expose] public section

namespace TruthCore.Explanation.WellFoundedSource

open TruthCore.Explanation.ExistencePSR
open TruthCore.Logic.RootDescent (acc_exists_unmarked)

variable {World Being : Type}

/-- The selected world has an actually existing individual. Neither the
constant candidate domain nor the presence of a world makes this automatic. -/
def PopulatedAt (m : Model World Being) (w : World) : Prop :=
  ∃ x, m.ontic.ExistsAt w x

/-- One already-existing individual causes the selected individual here.
Neither transitive ancestry nor the existence of an explanation is assumed. -/
def HasExistingCauseAt (m : Model World Being) (w : World) (x : Being) : Prop :=
  ∃ y, m.ontic.ExistsAt w y ∧ m.ontic.Causes w y x

/-- The world's entire modeled causal relation has no infinite descending
chains, in Lean's strong accessibility sense. -/
def WellFoundedCausesAt (m : Model World Being) (w : World) : Prop :=
  WellFounded (m.ontic.Causes w)

/-- One existent has an explanation of its existence fact but no actually
existing efficient cause at this particular world. -/
def ExplainedSourceAt (m : Model World Being) (w : World) : Prop :=
  ∃ x r, m.ontic.ExistsAt w x ∧ m.explains w r (.fact x) ∧
    ¬ HasExistingCauseAt m w x

/-- A populated world with well-founded efficient causation has an existent
with no incoming *existing* efficient cause, even when nonexistent candidates
can be elements of the constant domain. -/
theorem existingSource_of_wellFounded
    (m : Model World Being) (w : World)
    (hExists : PopulatedAt m w)
    (hWF : WellFoundedCausesAt m w) :
    ∃ x, m.ontic.ExistsAt w x ∧ ¬ HasExistingCauseAt m w x := by
  obtain ⟨x, hx⟩ := hExists
  exact acc_exists_unmarked (P := m.ontic.ExistsAt w) (Mark := HasExistingCauseAt m w)
    (fun _ _ => Classical.em _) (fun _ _ ⟨y, hy, hEdge⟩ => ⟨y, hEdge, hy⟩) (hWF.apply x) hx

/-- Genuine conditional syllogism: if some individual exists, existence-PSR
provides a reason for every existent, and existing efficient causes are
well-founded, then *some* existence fact has an explanation but its bearer
has no existing efficient cause. The reason's adequacy is still stipulated. -/
theorem psr_gives_explained_source
    (m : Model World Being) (w : World)
    (hExists : PopulatedAt m w)
    (hPSR : ExistencePSR m)
    (hWF : WellFoundedCausesAt m w) :
    ExplainedSourceAt m w := by
  obtain ⟨x, hx, hNoCause⟩ := existingSource_of_wellFounded m w hExists hWF
  obtain ⟨r, hr⟩ := hPSR w x hx
  exact ⟨x, r, hx, hr, hNoCause⟩

/-- Minimal incompatible profile at a populated world: well-foundedness and
the requirement that *every* existent have a distinct existing external cause.
The premise `ExistencePSR` is not needed for this contradiction. -/
theorem all_external_causes_impossible
    (m : Model World Being) (w : World)
    (hExists : PopulatedAt m w)
    (hWF : WellFoundedCausesAt m w) :
    ¬ EveryExistentExternallyCaused m := by
  obtain ⟨x, hx, hNoCause⟩ := existingSource_of_wellFounded m w hExists hWF
  intro hExternal
  obtain ⟨y, hy, _, hEdge⟩ := hExternal w x hx
  exact hNoCause ⟨y, hy, hEdge⟩

/-- Model control with two distinct mutually efficient causes. Both exist at
the unique world and have stipulated intrinsic existence reasons. There is no
well-foundedness, and no real metaphysical explanation is established. -/
def mutualCauses : Model Unit Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => True
    Causes := fun _ y x => y ≠ x
  }
  explains := fun _ r f => match f with
    | .fact x => r = .intrinsic x

theorem mutualCausesSound : Sound mutualCauses := by
  intro _ _ _ _
  trivial

theorem mutualCausesPSR : ExistencePSR mutualCauses := by
  intro _ x _
  exact ⟨.intrinsic x, rfl⟩

theorem mutualCausesExternal : EveryExistentExternallyCaused mutualCauses := by
  intro _ x _
  cases x with
  | false =>
    refine ⟨true, True.intro, ?_, ?_⟩
    · intro h; cases h
    · change true ≠ false
      intro h; cases h
  | true =>
    refine ⟨false, True.intro, ?_, ?_⟩
    · intro h; cases h
    · change false ≠ true
      intro h; cases h

theorem mutualCausesNotWF : ¬ WellFoundedCausesAt mutualCauses () := by
  intro hWF
  have bad : ∀ x : Bool, Acc (mutualCauses.ontic.Causes ()) x → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      cases x with
      | false =>
        apply ih true
        change true ≠ false
        intro h; cases h
      | true =>
        apply ih false
        change false ≠ true
        intro h; cases h
  exact bad false (hWF.apply false)

theorem mutualCausesPopulated :
    PopulatedAt mutualCauses () := ⟨false, True.intro⟩

theorem mutualCausesNoExplainedSource :
    ¬ ExplainedSourceAt mutualCauses () := by
  rintro ⟨x, _, hx, _, hNoCause⟩
  obtain ⟨y, hy, _, hEdge⟩ := mutualCausesExternal () x hx
  exact hNoCause ⟨y, hy, hEdge⟩

/-- Removing the existence witness makes universal external causation and
well-foundedness coexist vacuously. The candidate domain remains inhabited. -/
def emptyWorld : Model Unit Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => False
    Causes := fun _ _ _ => False
  }
  explains := fun _ _ _ => False

theorem emptyWorldSound : Sound emptyWorld := by
  intro _ _ _ h
  exact h.elim

theorem emptyWorldPSR : ExistencePSR emptyWorld := by
  intro _ _ h
  exact h.elim

theorem emptyWorldExternal : EveryExistentExternallyCaused emptyWorld := by
  intro _ _ h
  exact h.elim

theorem emptyWorldWellFounded : WellFoundedCausesAt emptyWorld () := by
  refine ⟨fun x => Acc.intro x ?_⟩
  intro _ h
  exact h.elim

theorem emptyWorldNotPopulated : ¬ PopulatedAt emptyWorld () := by
  rintro ⟨_, h⟩
  exact h.elim

/-- An existing control, not a new independent model: the original PSR
intrinsic-reason witness has nonempty existence, no causal arrows, and hence a
well-founded cause relation. Its existence reasons remain stipulated. -/
theorem intrinsicPopulated :
    PopulatedAt TruthCore.Models.PSR.Intrinsic.model false := ⟨false, rfl⟩

theorem intrinsicWellFounded :
    WellFoundedCausesAt TruthCore.Models.PSR.Intrinsic.model false := by
  refine ⟨fun x => Acc.intro x ?_⟩
  intro _ h
  exact h.elim

theorem intrinsicExplainedSource :
    ExplainedSourceAt TruthCore.Models.PSR.Intrinsic.model false := by
  refine ⟨false, .intrinsic false, rfl, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨_, _, hCause⟩
  exact hCause.elim

def PSRWithMutualCauses : Prop :=
  ∃ m : Model Unit Bool,
    Sound m ∧ ExistencePSR m ∧ EveryExistentExternallyCaused m ∧
    PopulatedAt m () ∧ ¬ WellFoundedCausesAt m ()

theorem psrWithMutualCauses : PSRWithMutualCauses := by
  exact ⟨mutualCauses, mutualCausesSound, mutualCausesPSR,
    mutualCausesExternal, mutualCausesPopulated, mutualCausesNotWF⟩

end TruthCore.Explanation.WellFoundedSource
