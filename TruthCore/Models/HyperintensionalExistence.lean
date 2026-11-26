module

public import TruthCore.Logic.ContentInterpretation
public import TruthCore.Explanation.EssenceReasonSeparation
public import TruthCore.Modal.Cube
public import TruthCore.Modal.RigidDesignation
public import TruthCore.Results.Causality.SelectedPlgTheory.Solution

/-! A finite test at the dependence-to-PLG bridge (issue #2058).
The earlier directed nature profile supplies the contents and modal frame.
Its nature assignment and the PLG presentation are independent inputs.
Their alignment here is a checked property of those inputs. -/

@[expose] public section

namespace TruthCore.Models.HyperintensionalExistence

open TruthCore.Explanation.ExistencePSR (ExistenceFact)
open TruthCore.Explanation.EssenceReasonSeparation (directedNature natureWithoutReason)
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)
open TruthCore.Logic.ContentInterpretation (Interpretation extensionCriterion)
open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion)
open TruthCore.Modal.RigidDesignation (Name RigidAt CoRef)
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Causality.SelectedPlgTheory.Control (weakOnly strictForward)
open TruthCore.Causality.DependenceStrictGroundMap (DependenceMapsToStrictExistenceGround)
open TruthCore.Results.Modern.Fine.StrictGroundAcyclic (strictIrrefl)
open Sequent

/-- A fact of existence carries its bearer. The same ontic profile determines
its truth at each world independently of the PLG presentation. -/
def extension : Interpretation Bool (ExistenceFact Bool)
  | .fact x => fun w => directedNature.explanation.ontic.ExistsAt w x

/-- Labelling reverses the Boolean names so the selected PLG control prints
the supplier as false and the dependent as true. -/
def label : ExistenceFact Bool → Bool
  | .fact x => !x

/-- The stipulated supplier and recipient existence facts in the fixed model. -/
def supplier : ExistenceFact Bool := .fact true
def recipient : ExistenceFact Bool := .fact false

/-- Names for the bearers, which are rigid and have distinct denotations. -/
def name (x : Bool) : Name Bool Bool := fun _ y => y = x

theorem modalProfile :
    TruthCore.Modal.FrameSatisfies .S5 directedNature.explanation.ontic.frame ∧
    (∀ w, Box directedNature.explanation.ontic.frame
      (fun v => extension supplier v ↔ extension recipient v) w) ∧
    (∀ w x, RigidAt directedNature.explanation.ontic (name x) w x) ∧
    (∀ w, ¬ CoRef (name true) (name false) w) ∧
    (Dia directedNature.explanation.ontic.frame (fun w => w = true) false ∧
      ¬ Box directedNature.explanation.ontic.frame (fun w => w = true) false) := by
  refine ⟨⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩, fun _ _ _ => Iff.rfl,
    fun _ _ _ _ _ => ⟨fun h => ⟨h, trivial⟩, And.left⟩, ?_, ?_⟩
  · rintro _ ⟨x, htrue, hfalse⟩
    exact Bool.noConfusion (htrue.symm.trans hfalse)
  · exact ⟨⟨true, trivial, rfl⟩, fun h => Bool.noConfusion (h false trivial)⟩

theorem sameExtension : extension supplier = extension recipient := rfl

theorem distinctContents : supplier ≠ recipient := by
  intro h
  exact Bool.noConfusion (congrArg label h)

/-- Coextensive facts can retain a strict edge and its weak consequence.
A weak return would contradict consistency. With the strictly oriented
assumption replaced by its weak counterpart even the forward strict edge
is underivable. -/
theorem groundProfile :
    Consistent strictForward ∧ StrictlyGrounds strictForward (label supplier) (label recipient) ∧
    Derivable strictForward (weakPartial (label supplier) (label recipient)) ∧
    ¬ Derivable strictForward (weakPartial (label recipient) (label supplier)) ∧
    Consistent weakOnly ∧ Derivable weakOnly (weakPartial (label supplier) (label recipient)) ∧
    ¬ StrictlyGrounds weakOnly (label supplier) (label recipient) := by
  have controls := TruthCore.Results.Causality.SelectedPlgTheory.presentationControls
  have consistent : Consistent strictForward := controls.2.2.1
  have forward : StrictlyGrounds strictForward (label supplier) (label recipient) :=
    controls.2.2.2.1 true false (by decide) ⟨rfl, rfl⟩
  refine ⟨consistent, forward, Derivable.subsumptionStrictPartial forward,
    fun back => strictIrrefl consistent _ (Derivable.transStrictWeak forward back),
    controls.1, ?_, ?_⟩
  · exact Derivable.subsumptionWeakFullPartial
      (Derivable.assumption (show weakFull {false} true ∈ weakOnly from rfl)) rfl
  · intro h
    apply controls.2.1
    rintro _ _ _ ⟨rfl, rfl⟩
    exact h

/-- The assignment discriminates the same facts shown coextensive above.
The existing alternative profile omits the membership at the supplier fact
while preserving its ontic profile. -/
theorem essenceProfile :
    directedNature.InEssence false supplier ∧ ¬ directedNature.InEssence false recipient ∧
    natureWithoutReason.explanation.ontic = directedNature.explanation.ontic ∧
    ¬ natureWithoutReason.InEssence false supplier := by
  refine ⟨⟨rfl, rfl⟩, fun h => distinctContents h.2.symm, rfl, ?_⟩
  exact fun h => distinctContents h.2

/-- The strict PLG presentation realizes the map for the stipulated
nature relation. Here the endpoint labelling sends a bearer to the label
of its existence fact. -/
theorem selectedNatureMap :
    DependenceMapsToStrictExistenceGround
      (fun x y => directedNature.InEssence x (.fact y))
      (fun x => label (.fact x)) strictForward := by
  rintro x y _ ⟨hx, hy⟩
  cases hx
  have hy' : y = true := ExistenceFact.fact.inj hy
  cases hy'
  exact groundProfile.2.1

private theorem noCriterion (J : ExistenceFact Bool → Prop)
    (holds : J supplier) (fails : ¬ J recipient) : ¬ AdmitsCriterion extension J := by
  intro h
  exact fails (((extensionCriterion extension J).mp h supplier recipient sameExtension).mp holds)

/-- Neither the selected ground in the displayed antecedent slot (strict)
or consequent slot (weak), nor essence membership at this bearer, can be
classified using just the extension of the varying fact. -/
theorem extensionCollapse :
    ¬ Function.Injective extension ∧
    (¬ AdmitsCriterion extension (fun c => StrictlyGrounds strictForward (label c) (label recipient))) ∧
    (¬ AdmitsCriterion extension
      (fun c => Derivable strictForward (weakPartial (label recipient) (label c)))) ∧
    (¬ AdmitsCriterion extension (directedNature.InEssence false)) := by
  refine ⟨fun h => distinctContents (h sameExtension), ?_, ?_, ?_⟩
  · exact noCriterion _ groundProfile.2.1 (strictIrrefl groundProfile.1 _)
  · intro h
    have invariant := (extensionCriterion extension _).mp h
    exact groundProfile.2.2.2.1 ((invariant supplier recipient sameExtension).mpr
      (Derivable.subsumptionWeakFullPartial (Derivable.identity (label recipient)) rfl))
  · exact noCriterion _ essenceProfile.1 essenceProfile.2.1

/-- Any alternative labelling which identifies these two facts loses the
forward strict edge in every consistent PLG presentation on its labels. -/
theorem collapsedLabelsLoseStrictGround {Atom : Type} (tag : ExistenceFact Bool → Atom)
    (S : Set (Sequent Atom)) (consistent : Consistent S)
    (same : tag supplier = tag recipient) : ¬ StrictlyGrounds S (tag supplier) (tag recipient) := by
  rw [same]
  exact strictIrrefl consistent _

end TruthCore.Models.HyperintensionalExistence
