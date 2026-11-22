module

public import TruthCore.Ontology.EncodingAndRealPredicates

/-! Existence as a predicate, part 2: an encoding/exemplification control, a
real-predicate control for Kant's thesis, and the Meditation V argument.
Analyst formulations; attribution deferred. Vocabulary:
`TruthCore.Ontology.EncodingAndRealPredicates`.

* `encodingControl`: comprehension gives the characterized god encoded but not
  exemplified existence; the encoded reading of God is unusable with the
  exemplified reading of being; a model with the encoded reading of both.
* `realPredicateControl`: with existence a real predicate every most-real
  candidate exists; a model of Kant's thesis with the identification and
  uniqueness premises and a most-real candidate in which nothing most real
  exists. Zero axioms.
* `meditationFive`: a supremely perfect God candidate and existence as a real
  predicate give some existing God. Zero axioms. -/

@[expose] public section

namespace TruthCore.Results.Ontology.EncodingAndRealPredicates

open TruthCore.Ontology.EncodingAndRealPredicates
open TruthCore.Case.Catholicism (GodExists GodNamesTheUniqueMaximeEns)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)
open TruthCore.German.Kant.CosmologicalInference

/-- Meditation V, analyst formulation: if some candidate is supremely perfect and
God, and existence at `w` is a real predicate (a perfection of the profile), then
some being existing at `w` is God. -/
theorem meditationFive {W E : Type} (m : Ontic W E) (p : RealityProfile E) (w : W)
    (IsGod : E → Prop) (d1 : SupremelyPerfectGodCandidate p IsGod)
    (d2 : ExistenceIsRealPredicate m p w) :
    GodExists (fun b : {x : E // m.ExistsAt w x} => IsGod b.1) := by
  obtain ⟨x, hx, hg⟩ := d1
  obtain ⟨f, hf⟩ := d2
  exact ⟨⟨x, (hf x).1 (hx f)⟩, hg⟩

/-- Kant model: one candidate, universal access, nothing exists. -/
def kantOntic : Ontic Unit Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => False
  Causes := fun _ _ _ => False

/-- Kant model: one positive reality, had by every candidate. -/
def kantProfile : RealityProfile Unit where
  Feature := Unit
  Has := fun _ _ => True

/-- The real-predicate control. -/
theorem realPredicateControl : RealPredicateControl := by
  refine ⟨?_, ?_⟩
  · rintro W E m p w ⟨f, hf⟩ x hx
    exact (hf x).1 (hx f)
  · refine ⟨kantOntic, kantProfile, ?_, ?_, ?_, ⟨(), fun _ => trivial⟩, ?_, ?_⟩
    · rintro ⟨f, hf⟩
      exact (hf ()).1 trivial
    · intro _ _ _
      trivial
    · intro x y _ _
      cases x
      cases y
      rfl
    · rintro ⟨_, _, h⟩
      exact h
    · rintro ⟨_, h, _⟩
      exact h

namespace Model

/-- Three properties: E!, god, benevolent. -/
inductive ZP where
  | concrete
  | god
  | benevolent

/-- One ordinary object and one abstract object per set of properties. -/
inductive ZObj where
  | ordinary
  | abstract (S : Set ZP)

/-- The ordinary object exemplifies exactly E! and encodes nothing; the abstract
object for `S` exemplifies nothing and encodes exactly `S`. -/
def frame : ZaltaFrame where
  Object := ZObj
  Property := ZP
  Exemplifies := fun x p => match x with
    | .ordinary => p = ZP.concrete
    | .abstract _ => False
  Encodes := fun x p => match x with
    | .ordinary => False
    | .abstract S => p ∈ S
  concrete := ZP.concrete

theorem comprehension : ObjectComprehension frame := by
  intro S
  refine ⟨.abstract S, fun h => h, fun _ => Iff.rfl, ?_⟩
  intro y hy hS
  cases y with
  | ordinary => exact absurd rfl hy
  | abstract T => exact congrArg ZObj.abstract (Set.ext hS)

theorem ordinaryEncodeNothing : OrdinaryEncodeNothing frame := by
  intro x hx p
  cases x with
  | ordinary => exact fun h => h
  | abstract _ => exact absurd hx (fun h => h)

/-- The characterized god: encodes god, benevolent and E!. -/
def godObj : ZObj := .abstract {ZP.god, ZP.benevolent, ZP.concrete}

theorem godObj_god : frame.Encodes godObj ZP.god := Set.mem_insert _ _

theorem godObj_benevolent : frame.Encodes godObj ZP.benevolent :=
  Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem godObj_concrete : frame.Encodes godObj ZP.concrete :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-- `godObj` is more in being than every other object. -/
def MoreIn : Unit → ZObj → ZObj → Prop := fun _ y m => y = godObj ∧ m ≠ godObj

theorem maximum_is_godObj (m : ZObj)
    (h : IsMaximumIn (fun x (_ : Unit) => EncodesExistence frame x) MoreIn () m) :
    m = godObj :=
  Classical.byContradiction fun hne => h.2 godObj ⟨rfl, hne⟩

theorem no_exemplified_god :
    ¬ ∃ x, ExemplifiesExistence frame x ∧ frame.Exemplifies x ZP.god := by
  rintro ⟨x, _, hg⟩
  cases x with
  | ordinary => cases hg
  | abstract _ => exact hg

end Model

/-- General part (a). -/
theorem encodedExistenceWitness (F : ZaltaFrame) (h : ObjectComprehension F)
    (g o : F.Property) :
    ∃ x, F.Encodes x g ∧ F.Encodes x o ∧ EncodesExistence F x ∧
      ¬ ExemplifiesExistence F x := by
  obtain ⟨x, hab, henc, _⟩ := h {g, o, F.concrete}
  exact ⟨x, (henc g).2 (Set.mem_insert _ _),
    (henc o).2 (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
    (henc F.concrete).2 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)), hab⟩

open Model in
/-- The encoding control. -/
theorem encodingControl : EncodingControl := by
  refine ⟨encodedExistenceWitness, ?_, frame, comprehension, ordinaryEncodeNothing,
    ⟨.ordinary, rfl⟩, ZP.god, ZP.benevolent,
    ⟨godObj, godObj_god, godObj_benevolent, godObj_concrete⟩, no_exemplified_god, ?_,
    MoreIn, fun _ _ _ => True, ?_, ⟨godObj, ⟨godObj_concrete, ?_⟩, fun _ _ _ => trivial,
      maximum_is_godObj⟩, ⟨godObj, godObj_god⟩⟩
  · rintro F hOrd g MoreIn' CausesIn hNames ⟨m, hmax, hc, hu⟩
    exact hOrd m hmax.1 g (hNames m hmax hc hu)
  · rintro ⟨⟨x, hx⟩, hg⟩
    exact no_exemplified_god ⟨x, hx, hg⟩
  · intro m hm _ _
    rw [maximum_is_godObj m hm]
    exact godObj_god
  · rintro y ⟨_, hne⟩
    exact hne rfl

end TruthCore.Results.Ontology.EncodingAndRealPredicates
