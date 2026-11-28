module

public import TruthCore.Causality.ContingentBeingNode
public import TruthCore.Causality.Frame
public import TruthCore.Logic.CogitoEsse
public import TruthCore.Results.Case.Catholicism.CauseOfBeingHasBeing.Solution
public import TruthCore.Results.Causality.ActualFusionNecessaryBeing.Solution
public import TruthCore.Results.Mereology.FusionNoNecessaryParts.Solution

@[expose] public section

namespace TruthCore.Results.Causality.CompositionRoutes

open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt NecessaryBeing)
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)
open TruthCore.Mereology.FusionNoNecessaryParts (NoNecessaryPartsAt)

/-- Calibrate the already actual witness on the same Profile, world and frame. -/
theorem necessaryConcreteOfCalibratedExistence {W B : Type}
    (m : Profile W B) (w : W)
    (hNecessary : NecessaryBeing m.ontic w)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w) :
    NecessaryConcreteAt m w := by
  obtain ⟨x, hx, hAll⟩ := hNecessary
  exact ⟨x, hConcrete x hx, hx, hAll⟩

/-- Reflexive parthood excludes necessity of the selected object itself.
Its separate actual-concrete premise then supplies the actual contingent bearer. -/
theorem actualContingentOfNoNecessaryParts {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (x : B)
    (hActual : ActualConcrete m w x)
    (hParts : NoNecessaryPartsAt m.ontic w x) :
    SomeActualContingentAt m w := by
  have hNotNecessary := hParts x (le_refl x)
  simp only [NecessaryAt, Classical.not_forall] at hNotNecessary
  obtain ⟨v, hAccess, hAbsent⟩ := hNotNecessary
  exact ⟨x, hActual.1, hActual.2, v, hAccess, hAbsent⟩

open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Mereology.FusionNoNecessaryParts
  (FamilyNoNecessaryPartsAt NecessityDownwardAlongParthoodAt)
open TruthCore.Mereology.UniversalFusionBoundary (Fusion)

-- Worked compositions bind the shared arguments to the same inputs end to end.

/-- Use the five-input actual-fusion proof and the existing two-input esse
calibration, with the same selected world and full ontology throughout. -/
theorem necessaryConcreteOfActualFusion {W B T R : Type} [PartialOrder B]
    (F : CausalityFrame W B T R) (InAct : B → R → Prop)
    (m : Profile W B) (w : W) (sum : B)
    (hFusion : ActualFusionAt m.ontic w sum)
    (hParts : ActualPartsExistAt m.ontic w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m.ontic w)
    (hActual : CausesHaveActualEndpointsAt m.ontic w)
    (hNonoverlap : CauseEffectNonoverlapAt m.ontic w)
    (hExisting : ExistingInActAt m.ontic InAct F.esse w)
    (hConcrete : EsseInReIsConcrete m InAct F.esse) :
    NecessaryConcreteAt m w :=
  necessaryConcreteOfCalibratedExistence m w
    (ActualFusionNecessaryBeing.necessaryBeing m.ontic w sum hFusion hParts hCausal
      hActual hNonoverlap)
    (TruthCore.Results.Case.Catholicism.CauseOfBeingHasBeing.everyExistentConcreteOfCalibration
      m w InAct F.esse hExisting hConcrete)

/-- The L3 result supplies the necessary-part exclusion for the same fusion
whose actual concreteness is given separately. -/
theorem actualContingentOfFusion {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (family : Set B) (sum : B)
    (hActual : ActualConcrete m w sum)
    (hFusion : Fusion family sum)
    (hFamily : FamilyNoNecessaryPartsAt m.ontic w family)
    (hDownward : NecessityDownwardAlongParthoodAt m.ontic w) :
    SomeActualContingentAt m w :=
  actualContingentOfNoNecessaryParts m w sum hActual
    (TruthCore.Results.Mereology.FusionNoNecessaryParts.noNecessaryParts
      m.ontic w family sum hFusion hFamily hDownward)

namespace Control

/-- The two candidates exist at world false; only true exists at world true. -/
def profile (concrete : Bool → Prop) : Profile Bool Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => x = true ∨ w = false
    Causes := fun _ _ _ => False }
  concrete := concrete
  grounds := fun _ _ _ => False

/-- Both bridges have a joint instance with different necessary and contingent
witnesses. Candidate false has no parts other than itself in the Bool order. -/
theorem joint :
    let m := profile (fun _ => True)
    NecessaryBeing m.ontic false ∧ EveryExistentConcreteAt m.ontic m.concrete false ∧
      ActualConcrete m false false ∧ NoNecessaryPartsAt m.ontic false false := by
  refine ⟨⟨true, Or.inl rfl, fun _ _ => Or.inl rfl⟩, fun _ _ => trivial,
    ⟨trivial, Or.inr rfl⟩, ?_⟩
  intro p hp hn
  have hp' : p = false := le_antisymm hp (by cases p <;> decide)
  subst p
  simpa [profile] using hn true trivial

/-- Bare actual necessity can coexist with actual concrete population even
when the only necessary individual is nonconcrete in the stipulated profile. -/
theorem bareNecessityWithoutNecessaryConcrete :
    let m := profile (· = false)
    NecessaryBeing m.ontic false ∧ ActualConcrete m false false ∧
      ¬ NecessaryConcreteAt m false := by
  refine ⟨⟨true, Or.inl rfl, fun _ _ => Or.inl rfl⟩,
    ⟨rfl, Or.inr rfl⟩, ?_⟩
  rintro ⟨x, hx, _, hn⟩
  change x = false at hx
  subst x
  simpa [profile] using hn true trivial

end Control
end TruthCore.Results.Causality.CompositionRoutes
