module

public import TruthCore.Ontology.ExistencePredicate

/-! Existence as a predicate: the owner's definitional argument, its retorsion,
and a nuclear-characterization (Parsons-style) control. Analyst formulations;
attribution deferred. Vocabulary: `TruthCore.Ontology.ExistencePredicate`.

* `definitionalArgument`: P1 (the existing omnibenevolent God is defined) and
  the weak P2 (whatever is defined is true) give `GodExists` over the frame's
  beings. Valid, and a transcription by instantiation: its whole content is P2
  applied to P1's description, then dropping two conjuncts.
* `unrestrictedGivesDefinitionsTrue`: the unrestricted P2 implies the weak P2.
* `definitionalTruthRetorsion`: the unrestricted P2 is logically false in every
  frame; the weak P2 fails once the contrary sole-God description is also
  defined; each description is satisfiable on its own; P1 and the weak P2 are
  jointly consistent. Zero axioms.
* `analyticReadingCountermodel`: under the analytic reading of P2 the argument
  is invalid. Zero axioms.
* `nuclearCharacterizationControl`: nuclear characterization delivers a
  nuclear-existent (EXISTENCE_5) god object, and a model of it has no
  extranuclear-existent (EXISTENCE_4) god while satisfying the weak P2 on
  nuclear descriptions and, with a nuclear reading of being in act at esse, the
  naming premise. -/

@[expose] public section

namespace TruthCore.Results.Ontology.ExistencePredicate

open TruthCore.Ontology.ExistencePredicate
open TruthCore.Case.Catholicism (GodExists GodNamesTheUniqueMaximeEns)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)

/-- The owner's definitional argument: from P1 and the weak P2, some being (an
object that exists) is God. -/
theorem definitionalArgument (F : DefinitionalFrame) (IsGod OB : F.Object → Prop)
    (p1 : DefinesExistingOmnibenevolentGod F IsGod OB) (p2 : DefinitionsAreTrue F) :
    GodExists (fun b : Beings F => IsGod b.1) := by
  obtain ⟨x, hx, hg, _⟩ := p2 _ p1
  exact ⟨⟨x, hx⟩, hg⟩

/-- Strength order: the unrestricted characterization principle implies that
whatever is defined is true. -/
theorem unrestrictedGivesDefinitionsTrue (F : DefinitionalFrame)
    (h : UnrestrictedCharacterization F) : DefinitionsAreTrue F := by
  intro D _
  exact h D

/-- Retorsion: unrestricted characterization refutes itself, and definitional
truth fails under two contrary sole-God definitions. -/
theorem definitionalTruthRetorsion : DefinitionalTruthRetorsion := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F h
    obtain ⟨_, hx⟩ := h (fun _ => False)
    exact hx
  · intro F IsGod OB h1 h2 hT
    obtain ⟨x1, _, _, hu1, hob⟩ := hT _ h1
    obtain ⟨x2, _, hg2, _, hnob⟩ := hT _ h2
    have h21 : x2 = x1 := hu1 x2 hg2
    rw [h21] at hnob
    exact hnob hob
  · exact ⟨{ Object := Unit, Existent := fun _ => True, Defined := fun _ => True },
      fun _ => True, fun _ => True, (), trivial, trivial, fun _ _ => rfl, trivial⟩
  · exact ⟨{ Object := Unit, Existent := fun _ => True, Defined := fun _ => True },
      fun _ => True, fun _ => False, (), trivial, trivial, fun _ _ => rfl, fun h => h⟩
  · let F : DefinitionalFrame :=
      { Object := Unit, Existent := fun _ => True
        Defined := fun D => D = fun _ => True ∧ True ∧ True }
    refine ⟨F, fun _ => True, fun _ => True, rfl, ?_⟩
    intro D hD
    subst hD
    exact ⟨(), trivial, trivial, trivial⟩

/-- Under the analytic reading of P2 the definitional argument is invalid: a
frame with no beings in which P1's description is defined. -/
theorem analyticReadingCountermodel : AnalyticReadingCountermodel :=
  ⟨{ Object := Unit, Existent := fun _ => False, Defined := fun _ => True },
    fun _ => True, fun _ => True, trivial, fun _ _ _ h => h,
    fun ⟨⟨_, h⟩, _⟩ => h⟩

namespace Model

/-- Three nuclear properties: god, benevolent, and the watered-down existent. -/
inductive Nuc where
  | god
  | benevolent
  | existent

/-- Objects are the sets of nuclear properties (one object per set). The
extranuclear-existent objects are the nuclear-existent non-gods. -/
def frame : ParsonsFrame where
  Object := Set Nuc
  Nuclear := Nuc
  HasNuclear := fun x p => p ∈ x
  ExistsExtranuclear := fun x => Nuc.existent ∈ x ∧ Nuc.god ∉ x
  existentNuclear := Nuc.existent

/-- The characterized "existing omnibenevolent god": nuclear properties god,
benevolent and existent. -/
def godObj : Set Nuc := {Nuc.god, Nuc.benevolent, Nuc.existent}

theorem characterization : NuclearCharacterization frame :=
  fun S => ⟨S, rfl, fun _ hy => hy⟩

theorem godObj_god : Nuc.god ∈ godObj := Set.mem_insert _ _

theorem godObj_benevolent : Nuc.benevolent ∈ godObj :=
  Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem godObj_existent : Nuc.existent ∈ godObj :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-- The nuclear-existent maximum: everything else is less in being. -/
def MoreIn : Unit → Set Nuc → Set Nuc → Prop := fun _ y m => y = godObj ∧ m ≠ godObj

theorem maximum_is_godObj (m : Set Nuc)
    (h : IsMaximumIn (fun x (_ : Unit) => NuclearExistent frame x) MoreIn () m) : m = godObj :=
  Classical.byContradiction fun hne => h.2 godObj ⟨rfl, hne⟩

theorem no_existing_god : ¬ ∃ x, frame.ExistsExtranuclear x ∧ frame.HasNuclear x Nuc.god :=
  fun ⟨_, ⟨_, hng⟩, hg⟩ => hng hg

end Model

/-- General part (a): nuclear characterization yields a nuclear-existent object
with any two given nuclear properties. -/
theorem nuclearExistentWitness (F : ParsonsFrame) (h : NuclearCharacterization F)
    (g o : F.Nuclear) :
    ∃ x, F.HasNuclear x g ∧ F.HasNuclear x o ∧ NuclearExistent F x := by
  obtain ⟨x, hx, _⟩ := h {g, o, F.existentNuclear}
  have hg : g ∈ nuclearSet F x := by rw [hx]; exact Set.mem_insert _ _
  have ho : o ∈ nuclearSet F x := by
    rw [hx]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have he : F.existentNuclear ∈ nuclearSet F x := by
    rw [hx]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  exact ⟨x, hg, ho, he⟩

open Model in
/-- The nuclear-characterization control. -/
theorem nuclearCharacterizationControl : NuclearCharacterizationControl := by
  refine ⟨nuclearExistentWitness, frame, characterization,
    ⟨({Nuc.existent} : Set Nuc), rfl, fun h => Nuc.noConfusion h⟩, Nuc.god, Nuc.benevolent,
    ⟨godObj, godObj_god, godObj_benevolent, godObj_existent⟩, no_existing_god,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro D ⟨S, rfl⟩
    exact ⟨S, fun _ hp => hp⟩
  · rintro ⟨S, hS⟩
    have hu : nuclearDescription frame S Set.univ := fun _ _ => trivial
    rw [← hS] at hu
    exact hu.1.2 hu.2.1
  · intro Stip hAdm hStip
    obtain ⟨S, hS⟩ := hAdm _ hStip
    have hu : nuclearDescription frame S Set.univ := fun _ _ => trivial
    rw [← hS] at hu
    exact hu.1.2 hu.2.1
  · rintro ⟨⟨x, _, hng⟩, hg⟩
    exact hng hg
  · refine ⟨MoreIn, fun _ _ _ => True, ?_, ⟨godObj, ⟨godObj_existent, ?_⟩, fun _ _ _ => trivial,
      maximum_is_godObj⟩, ⟨godObj, godObj_god⟩, no_existing_god⟩
    · intro m hm _ _
      rw [maximum_is_godObj m hm]
      exact godObj_god
    · rintro y ⟨_, hne⟩
      exact hne rfl

end TruthCore.Results.Ontology.ExistencePredicate
