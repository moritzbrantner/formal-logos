module

public import TruthCore.Modal.PrussPowerPremises
public import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.FinitePopulationCover

/-! Hold the reading world's contingent roster fixed when moving between worlds.
The aggregation and roster conditions below are analyst premises. -/

@[expose] public section

namespace TruthCore.Modal.ModalPowerHolder
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (AbsenceAmalgamation)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.ModalGrounding
open TruthCore.Modal.PrussPowerPremises (GivesTo)

variable {W B T R : Type}

/-- The same actual contingent roster is used at every world. -/
abbrev ActualContingentRoster (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W) :=
  {x : B // concrete x ∧ ContingentAt F.history.ontic w x}

/-- Only the populations projected onto the actual contingent roster must
admit a common subpopulation. Other populations may vary freely. -/
def ActualRosterAmalgamates (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W) : Prop :=
  AbsenceAmalgamation F.history.ontic.frame
    (fun (x : ActualContingentRoster F concrete w) v => F.history.ontic.ExistsAt v x.val) w

/-- One finite list includes every member of the actual contingent roster.
Neither the candidate domain nor the population at another world must be finite. -/
def ActualRosterFinite (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W) : Prop :=
  ∃ xs : List (ActualContingentRoster F concrete w), ∀ x, x ∈ xs

/-- At each accessible joint-absence world, every contingent concretum there
exists at the reading world. This only excludes newcomers that are contingent
at those worlds. -/
def ActualRosterCoversAtAbsence (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W) : Prop :=
  ∀ v, F.history.ontic.frame.access w v → NoActualContingentConcreteIn F concrete w v →
    ∀ x, concrete x → ContingentAt F.history.ontic v x → F.history.ontic.ExistsAt w x

/-- Each holder gives at least one member of the actual contingent roster being
at the reading world. The recipient may depend on the holder. -/
def ActualAbsenceHoldersGiveSome (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) →
    ∃ x, concrete x ∧ ContingentAt F.history.ontic w x ∧ GivesTo F w y x

namespace Model
open TruthCore.Modal.ModalGrounding.Model
open TruthCore.Modal (Reflexive Euclidean)

/-- The three populated Boolean profiles, with universal access. Every world
is populated, but each of the two actual beings can be omitted. -/
def populatedProfiles : CausalityFrame {v : Bool × Bool // v ≠ (false, false)} Bool Unit Bool :=
  frameOn (fun _ _ => True) (fun v => comboEx v.val) (fun _ _ _ => False) (fun _ _ => False)

def bothPresent : {v : Bool × Bool // v ≠ (false, false)} :=
  ⟨(true, true), by decide⟩

/-- A positive conjunction of actual-roster existence can fail at an accessible
world even though the whole roster cannot be jointly absent. -/
def AllRosterPresent (F : CausalityFrame W B T R) (concrete : B → Prop) (w v : W) : Prop :=
  ∀ x : ActualContingentRoster F concrete w, F.history.ontic.ExistsAt v x.val

/-- Finite models of both non-entailments on equivalence frames. -/
def Controls : Prop :=
  (Reflexive populatedProfiles.history.ontic.frame ∧ Euclidean populatedProfiles.history.ontic.frame ∧
    ActualRosterFinite populatedProfiles allConcrete bothPresent ∧
    AllRosterPresent populatedProfiles allConcrete bothPresent bothPresent ∧
    (∃ v, populatedProfiles.history.ontic.frame.access bothPresent v ∧
      ¬ AllRosterPresent populatedProfiles allConcrete bothPresent v) ∧
    ¬ ActualRosterAmalgamates populatedProfiles allConcrete bothPresent ∧
    ¬ PossiblyNoActualContingentConcrete populatedProfiles allConcrete bothPresent) ∧
  (Reflexive swappedFrame.history.ontic.frame ∧ Euclidean swappedFrame.history.ontic.frame ∧
    PossiblyNoActualContingentConcrete swappedFrame allConcrete true ∧
    ¬ ActualRosterCoversAtAbsence swappedFrame allConcrete true ∧
    ¬ PossiblyNoContingentConcrete swappedFrame allConcrete true)

end Model
end TruthCore.Modal.ModalPowerHolder
