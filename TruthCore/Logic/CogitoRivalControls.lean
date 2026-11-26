module

public import TruthCore.Logic.CogitoEsse

/-!
# Two bounded cogito rival fixtures

The first profile retains an actual bearer and independent state labels
with empty proper grounding. The second represents a single event and
leaves distinct bearing and substance empty. These are interpretation
controls with stipulated modal frames.
-/

@[expose] public section

namespace TruthCore.Logic.CogitoRivalControls

open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

def split : Profile Bool Bool where
  ontic := ⟨⟨fun _ _ => True⟩, Eq, fun _ _ _ => False⟩
  concrete := fun _ => True
  grounds := fun _ _ _ => False

def occurs (_ : Unit) : Prop := True
def understands (_ : Unit) : Prop := True
def bears (b : Bool) (_ : Unit) : Prop := b = false
def act (b : Bool) (_ : Bool) : Prop := b = false

inductive Stage where
  | question | grasp
  deriving DecidableEq

def earlier (t u : Bool) : Prop := t = false ∧ u = true

def state (w b t : Bool) : Option Stage :=
  if w = false ∧ b = false then some (if t then .grasp else .question) else none

/-- The actual bearer is false at world false, and the other candidate alone
exists at world true. The stage comparison does not supply an edge. -/
theorem splitPopulation :
    (∀ w v, split.ontic.frame.access w v) ∧
    (∀ w, InhabitedConcreteAt split.ontic split.concrete w) ∧
    ¬ NecessaryConcreteAt split false ∧
    (∃ b e, occurs e ∧ understands e ∧ bears b e ∧
      split.ontic.ExistsAt false b ∧ act b false ∧ act b true) ∧
    earlier false true ∧ state false false false = some .question ∧
    state false false true = some .grasp ∧
    state false false false ≠ state false false true ∧
    ∀ w a b, ¬ split.grounds w a b := by
  refine ⟨fun _ _ => trivial, fun w => ⟨w, trivial, rfl⟩, ?_,
    ⟨false, (), trivial, trivial, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ?_,
    fun _ _ _ h => h⟩
  · rintro ⟨b, _, (h : false = b), necessary⟩
    have diff : true = b := necessary true trivial
    cases h
    contradiction
  · decide

def eventOnly : Profile Unit Unit where
  ontic := ⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩
  concrete := fun _ => True
  grounds := fun _ _ _ => False

def distinctBearer (_ _ : Unit) : Prop := False
def substance (_ : Unit) : Prop := False

theorem singleEvent :
    occurs () ∧ InhabitedConcreteAt eventOnly.ontic eventOnly.concrete () ∧
    (∀ e, (∃ w, eventOnly.ontic.frame.access () w ∧ eventOnly.ontic.ExistsAt w e) ↔
      eventOnly.ontic.ExistsAt () e) ∧
    (∀ b e, ¬ distinctBearer b e) ∧ (∀ e, ¬ substance e) ∧
    ∀ w a b, ¬ eventOnly.grounds w a b := by
  exact ⟨trivial, ⟨(), trivial, trivial⟩,
    fun _ => ⟨fun _ => trivial, fun _ => ⟨(), trivial, trivial⟩⟩,
    fun _ _ h => h, fun _ h => h, fun _ _ _ h => h⟩

end TruthCore.Logic.CogitoRivalControls
