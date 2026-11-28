module

public import TruthCore.Causality.ActualFusionNecessaryBeing
public import TruthCore.Causality.BruteFoundationBoundary
public import TruthCore.Logic.CogitoEsse
public import TruthCore.Logic.StrengthComparison

@[expose] public section

namespace TruthCore.Causality.LocalActualFusion
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)

/-- A part of the selected sum or of any actual cause of that same sum. -/
def SelectedFusionPart {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (sum p : B) : Prop :=
  p ≤ sum ∨ ∃ c, m.ExistsAt w c ∧ m.Causes w c sum ∧ p ≤ c

/-- At the selected world, the parts considered by the proof exist if the sum
does. Other wholes and their parts are outside the scope of this premise. -/
def SelectedFusionPartsExistAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (sum : B) : Prop :=
  m.ExistsAt w sum → ∀ p, SelectedFusionPart m w sum p → m.ExistsAt w p

/-- Only actual parts in the selected fusion scope must be concrete. -/
def SelectedActualFusionPartsConcreteAt {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B) : Prop :=
  ∀ p, m.ontic.ExistsAt w p →
    SelectedFusionPart m.ontic w sum p → m.concrete p

/-- Global calibration on the same profile used by the local premise. -/
def ProfileExistentConcreteAt {W B : Type} (m : Profile W B) (w : W) : Prop :=
  EveryExistentConcreteAt m.ontic m.concrete w

/-- The complement of the local fusion calibration at this world. -/
def OutsideFusionActualConcreteAt {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B) : Prop :=
  ∀ p, m.ontic.ExistsAt w p →
    ¬ SelectedFusionPart m.ontic w sum p → m.concrete p

/-- Compare both scopes on the same profile, world, sum, and order. -/
def calibrationComparison {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B) : TruthCore.Logic.StrengthComparison.ComparisonSpec where
  stronger := ProfileExistentConcreteAt m w
  weaker := SelectedActualFusionPartsConcreteAt m w sum
  delta := OutsideFusionActualConcreteAt m w sum

/-- Global calibration is exactly the local and outside-scope calibrations. -/
def CalibrationExactDifference : Prop :=
  ∀ {W B : Type} [PartialOrder B] (m : Profile W B) (w : W) (sum : B),
    TruthCore.Logic.StrengthComparison.Equivalence (calibrationComparison m w sum)

namespace Control

/-- At the actual world both individuals exist. The only accessible world
omits true. The selected sum false is concrete and has no proper parts, and
the causal relation is empty. -/
def strictProfile : Profile Bool Bool where
  ontic := {
    frame := ⟨fun _ v => v = true⟩
    ExistsAt := fun w x => w = false ∨ x = false
    Causes := fun _ _ _ => False }
  concrete := (· = false)
  grounds := fun _ _ _ => False

def CalibrationStrictness : Prop :=
  SelectedActualFusionPartsConcreteAt strictProfile false false ∧
    ¬ EveryExistentConcreteAt strictProfile.ontic strictProfile.concrete false

end Control
end TruthCore.Causality.LocalActualFusion
