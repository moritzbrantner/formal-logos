module

public import TruthCore.Causality.NecessaryConcreteUnderived
public import TruthCore.Causality.NecessarilyUnderived
public import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers

/-! Analyst adapters between actualist profile exemplification and existential
support. The profile is rigid; numerical uniqueness ranges over candidates,
not merely the actual inhabitants of each world. No possibility or positivity
axiom is supplied. These are conditional connections, not God identification. -/
@[expose] public section
namespace TruthCore.Causality.ExistenceAccountIntegration
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (DeDicto)

variable {W B : Type}

/-- A concrete actual exemplar, with no modal or causal conclusion. -/
def ActualConcreteProfile (m : Profile W B) (p : RealityProfile B) (w : W) : Prop :=
  ∃ n, m.concrete n ∧ m.ontic.ExistsAt w n ∧ MostReal p n

/-- Actualist necessary exemplification, explicitly using the existing de dicto
quantifier. This is not conceivability, nor Scott's possibilist NE. -/
def NecessaryProfilePopulation (m : Profile W B) (p : RealityProfile B) (w : W) : Prop :=
  DeDicto m.ontic.frame (fun n v => m.ontic.ExistsAt v n ∧ MostReal p n) w

/-- The actual concrete profile bearer itself is necessary and has no existing
supporter at any world. No intrinsic reason, efficient causation or GOD_4. -/
def UnderivedConcreteProfile (m : Profile W B) (p : RealityProfile B)
    (support : W → B → B → Prop) (w : W) : Prop :=
  ∃ n, m.concrete n ∧ m.ontic.ExistsAt w n ∧ MostReal p n ∧
    NecessaryAt m.ontic w n ∧ ∀ v, NoExistingSupportAt m.ontic support v n

/-- Explicit finite assignments, not metaphysical possibility claims. -/
def fixture (present : Bool → Bool → Prop) : Profile Bool Bool :=
  ⟨⟨TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.alternatingFrame,
    present, fun _ _ _ => False⟩, fun _ => True, fun _ _ _ => False⟩ -- category-constant: intended (all-concrete finite quantifier control)

def reality (all : Bool) : RealityProfile Bool :=
  ⟨Unit, fun x _ => all = true ∨ x = false⟩

/-- Joint nonvacuity and omission of numerical uniqueness or necessary
population while retaining the other two premises of the first adapter. -/
def PopulationControls : Prop :=
  (ActualConcreteProfile (fixture (fun _ x => x = false)) (reality false) false ∧
    NecessaryProfilePopulation (fixture (fun _ x => x = false)) (reality false) false ∧
    MostRealUnique (reality false) ∧
    NecessaryConcreteAt (fixture (fun _ x => x = false)) false) ∧
  (ActualConcreteProfile (fixture (fun w x => x = w)) (reality true) false ∧
    NecessaryProfilePopulation (fixture (fun w x => x = w)) (reality true) false ∧
    ¬ MostRealUnique (reality true) ∧
    ¬ NecessaryConcreteAt (fixture (fun w x => x = w)) false) ∧
  (ActualConcreteProfile (fixture (fun w x => x = w)) (reality false) false ∧
    ¬ NecessaryProfilePopulation (fixture (fun w x => x = w)) (reality false) false ∧
    MostRealUnique (reality false) ∧
    ¬ NecessaryConcreteAt (fixture (fun w x => x = w)) false)

/-- A distinct actual necessary source supports the unique profile exemplar.
This tests preservation of the exemplar, not whether some underived source exists. -/
def otherSupport (_ : Bool) (a b : Bool) : Prop := a = true ∧ b = false

/-- Full-package nonvacuity, and omission of necessity-to-profile identification
with another underived necessary source surviving in the very same model. -/
def SupportControls : Prop :=
  (let m := fixture (fun _ x => x = false)
   let p := reality false
   let support : Bool → Bool → Bool → Prop := fun _ _ _ => False
   ActualConcreteProfile m p false ∧ NecessaryProfilePopulation m p false ∧
     MostRealUnique p ∧ NecessaryIsMostReal m.ontic p false ∧
     WellFoundedPresentEsseSupport m.ontic support false ∧
     NecessaryPredecessorLifting m.ontic support false ∧
     UnderivedConcreteProfile m p support false) ∧
  (let m := fixture (fun _ _ => True)
   let p := reality false
   ActualConcreteProfile m p false ∧ NecessaryProfilePopulation m p false ∧
     MostRealUnique p ∧ ¬ NecessaryIsMostReal m.ontic p false ∧
     WellFoundedPresentEsseSupport m.ontic otherSupport false ∧
     NecessaryPredecessorLifting m.ontic otherSupport false ∧
     ¬ UnderivedConcreteProfile m p otherSupport false ∧
     NecessarilyUnderived m.ontic otherSupport false)

/-! ## Controls for the sibling from the two weaker bridges

The same-witness conclusion also follows from `NoContingentGroundOfNecessary`
and `NoNovelNecessarySupport` instead of `NecessaryPredecessorLifting`, without
actual reflexivity. These finite assignments keep every other input of that
sibling and omit one bridge at a time; they are interpretations only. -/

/-- One individual that exists at both worlds of a universal two-world frame
and is concrete and most real. -/
def soleProfile : Profile Bool Unit :=
  ⟨⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩,
    fun _ => True, fun _ _ _ => False⟩ -- category-constant: intended (single concrete individual control)

/-- Every individual has the single profile feature. -/
def soleReality : RealityProfile Unit := ⟨Unit, fun _ _ => True⟩

/-- The individual supports itself at world `true` only. -/
def selfSupportElsewhere (w : Bool) (_ _ : Unit) : Prop := w = true

/-- Individual `false` exists at both worlds of a universal frame; individual
`true` exists only at world `true`. Both are concrete. -/
def contingentHelperProfile : Profile Bool Bool :=
  ⟨⟨⟨fun _ _ => True⟩, fun w x => x = false ∨ w = true, fun _ _ _ => False⟩,
    fun _ => True, fun _ _ _ => False⟩ -- category-constant: intended (all-concrete finite control)

/-- Only individual `false` is most real. -/
def falseReality : RealityProfile Bool := ⟨Unit, fun x _ => x = false⟩

/-- Individual `true` supports individual `false` at world `true` only. -/
def contingentHelperSupport (w s t : Bool) : Prop := w = true ∧ s = true ∧ t = false

/-- Omission controls for the weak sibling, actual world `false`:
1. no novel necessary support omitted: all other inputs hold (no contingent
   ground holds, no support edge at the actual world), and the unique exemplar
   supports itself at the other world, so it is not underived;
2. no contingent ground omitted: all other inputs hold (no novel necessary
   support holds vacuously), and a contingent individual supports the exemplar
   at the other world, so it is not underived. -/
def WeakSiblingOmissions : Prop :=
  (ActualConcreteProfile soleProfile soleReality false ∧
    NecessaryProfilePopulation soleProfile soleReality false ∧
    MostRealUnique soleReality ∧ NecessaryIsMostReal soleProfile.ontic soleReality false ∧
    WellFoundedPresentEsseSupport soleProfile.ontic selfSupportElsewhere false ∧
    NoContingentGroundOfNecessary soleProfile.ontic selfSupportElsewhere false ∧
    ¬ NoNovelNecessarySupport soleProfile.ontic selfSupportElsewhere false ∧
    ¬ UnderivedConcreteProfile soleProfile soleReality selfSupportElsewhere false) ∧
  (ActualConcreteProfile contingentHelperProfile falseReality false ∧
    NecessaryProfilePopulation contingentHelperProfile falseReality false ∧
    MostRealUnique falseReality ∧
    NecessaryIsMostReal contingentHelperProfile.ontic falseReality false ∧
    WellFoundedPresentEsseSupport contingentHelperProfile.ontic contingentHelperSupport false ∧
    NoNovelNecessarySupport contingentHelperProfile.ontic contingentHelperSupport false ∧
    ¬ NoContingentGroundOfNecessary contingentHelperProfile.ontic contingentHelperSupport false ∧
    ¬ UnderivedConcreteProfile contingentHelperProfile falseReality contingentHelperSupport false)

end TruthCore.Causality.ExistenceAccountIntegration
