module

public import TruthCore.Case.Catholicism.ClassicalAttributesJointWitness
public import TruthCore.Case.Catholicism.StagesOneTwo

/-! Tests identification of a joint attribute-bearer when the name has an inhabitant and when its extension is empty. -/

@[expose] public section

namespace TruthCore.Case.Catholicism.ClassicalAttributesNaming

open TruthCore.Case.Catholicism

theorem identify (σ : Signature) (g : σ.Being)
    (one : IsTheOneGod σ.IsGod g) (attrs : σ.HasClassicalAttributes g) :
    UniqueClassicalGodExists σ ↔ ∃ h, σ.IsGod h := by
  constructor
  · rintro ⟨h, god, _⟩
    exact ⟨h, god⟩
  · rintro ⟨h, god⟩
    exact ⟨g, one h god ▸ god, one, attrs⟩

open ClassicalAttributesJointWitness

def unnamed : Signature := { σ with IsGod := fun _ => False }

abbrev Nine (g : Being) :=
  NineClassicalAttributes (IsSimple Composite) (IsPerfect InAct)
    (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod unnamed.IsGod)
    Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill g

theorem missingName : Nine false ∧
    (∀ g : Being, Nine g → unnamed.HasClassicalAttributes g) ∧
    ¬ UniqueClassicalGodExists unnamed := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl⟩
    · intro h
      exact Bool.noConfusion h
    · intro _ r _
      exact Or.inl rfl
    · refine ⟨Or.inl rfl, ?_⟩
      intro x r hx _
      cases x
      · exact False.elim (hx rfl)
      · exact ⟨rfl, rfl⟩
    · intro h hh
      exact False.elim hh
    · intro r hr
      exact Bool.noConfusion hr.1
  · intro g h
    exact h.2.2.2.2.1
  · rintro ⟨_, h, _⟩
    exact h

end TruthCore.Case.Catholicism.ClassicalAttributesNaming
