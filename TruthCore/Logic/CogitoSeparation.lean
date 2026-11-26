module

public import TruthCore.Causality.BruteFoundationBoundary
public import TruthCore.Logic.CogitoConcrete
public import TruthCore.Logic.ReflectiveCoherence
public import TruthCore.Ontology.ConcreteAbstract
public import TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.Solution

/-!
# Episode-only models and concrete population (#543)

`Base` carries all of the original interpretation, including any old assertion
and content relations. An old model property reads only that component. The
extension adds the existing ontological profile on the specified carriers.
-/

@[expose] public section

namespace TruthCore.Logic.CogitoSeparation

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Logic.CogitoSubject (ThoughtOccurs)
open TruthCore.Logic.ReflectiveCoherence (Semantics)
open TruthCore.Ontology.ConcreteAbstract (Classification)

/-- The fresh concrete predicate is empty. Accessibility and the existence
assignment are parameters, so the same construction permits inhabited existence. -/
def withEmptyConcrete {W B : Type} (frame : TruthCore.Modal.Frame W)
    (existsAt : W → B → Prop) : Profile W B where
  ontic := { frame, ExistsAt := existsAt, Causes := fun _ _ _ => False }
  concrete := fun _ => False
  grounds := fun _ _ _ => False

theorem populationFails {W B : Type} (frame : TruthCore.Modal.Frame W)
    (existsAt : W → B → Prop) (w : W) :
    let p := withEmptyConcrete frame existsAt
    ¬ InhabitedConcreteAt p.ontic p.concrete w :=
  fun ⟨_, hc, _⟩ => hc

/-- The same original structure and the same particular occurrence survive.
Every property of the reduct includes, as instances, satisfaction of individual
old sentences or an entire old theory under its supplied semantics. -/
def ConservativeSeparation : Prop :=
  ∀ (Base Episode W B : Type) (base : Base) (frame : TruthCore.Modal.Frame W)
    (occurs : Base → Episode → Prop) (e : Episode), occurs base e →
    ∃ x : Base × Profile W B,
      x.1 = base ∧ x.2.ontic.frame = frame ∧
      (∀ old : Base → Prop, old x.1 ↔ old base) ∧ occurs x.1 e ∧
      (∀ b, ¬ x.2.concrete b) ∧ (∀ w b, ¬ x.2.ontic.ExistsAt w b) ∧
      ∀ w, ¬ (ThoughtOccurs (occurs x.1) → InhabitedConcreteAt x.2.ontic x.2.concrete w)

theorem emptyExpansion : ConservativeSeparation := by
  intro Base Episode W B base frame occurs e he
  let p : Profile W B := withEmptyConcrete frame (fun _ _ => False)
  exact ⟨(base, p), rfl, rfl, fun _ => Iff.rfl, he, fun _ h => h,
    fun _ _ h => h, fun w h => populationFails frame _ w (h ⟨e, he⟩)⟩

/-- One performed token denies concrete existence of its own representative.
Another denies its own occurrence. The interpretations give the first content
truth and the second falsity on the very same empty concrete extension. -/
def DenialContentControl : Prop :=
  ∃ (p : Profile Unit Bool) (occurs : Bool → Prop) (represent : Bool → Bool)
    (content : Bool → Prop),
    represent false = false ∧ represent true = true ∧
    occurs false ∧ occurs true ∧
    (content false ↔ ¬ (p.concrete (represent false) ∧ p.ontic.ExistsAt () (represent false))) ∧
    (content true ↔ ¬ occurs true) ∧ content false ∧ ¬ content true ∧
    ¬ InhabitedConcreteAt p.ontic p.concrete ()

theorem denialContentControl : DenialContentControl := by
  let frame : TruthCore.Modal.Frame Unit := ⟨fun _ _ => True⟩
  let p : Profile Unit Bool := withEmptyConcrete frame (fun _ _ => False)
  let occurs : Bool → Prop := fun _ => True
  let content : Bool → Prop
    | false => ¬ (p.concrete false ∧ p.ontic.ExistsAt () false)
    | true => ¬ occurs true
  exact ⟨p, occurs, id, content, rfl, rfl, trivial, trivial, Iff.rfl, Iff.rfl,
    (fun h => h.1), (fun h => h trivial), populationFails frame _ ()⟩

/-- The old contents are propositions. At the selected world their truth is
given by their usual meanings, including a true and a false content. All are
classified as abstract in this assignment. No entity has concrete existence. -/
def AbstractTruthControl : Prop :=
  ∃ (p : Profile Unit Prop) (c : Classification Prop) (S : Semantics Unit Prop),
    p.concrete = c.concrete ∧ (∀ q, c.abstract q) ∧ (∀ q, S.trueAt () q ↔ q) ∧
    (∃ q, c.abstract q ∧ S.trueAt () q) ∧ (∃ q, c.abstract q ∧ ¬ S.trueAt () q) ∧
    (∀ q, ¬ p.ontic.ExistsAt () q) ∧ ¬ InhabitedConcreteAt p.ontic c.concrete ()

theorem abstractTruthControl : AbstractTruthControl := by
  let frame : TruthCore.Modal.Frame Unit := ⟨fun _ _ => True⟩
  let p : Profile Unit Prop := withEmptyConcrete frame (fun _ _ => False)
  let c : Classification Prop :=
    { concrete := p.concrete, «abstract» := fun _ => True, disjoint := fun _ _ h => h }
  let S : Semantics Unit Prop :=
    { trueAt := fun _ q => q, neg := Not, neg_true_iff := fun _ _ => Iff.rfl }
  obtain ⟨q, hq⟩ :=
    TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.somePropositionHolds
  exact ⟨p, c, S, rfl, fun _ => trivial, fun _ => Iff.rfl, ⟨q, trivial, hq⟩,
    ⟨False, trivial, fun h => h⟩, fun _ h => h, populationFails frame _ ()⟩

end TruthCore.Logic.CogitoSeparation
