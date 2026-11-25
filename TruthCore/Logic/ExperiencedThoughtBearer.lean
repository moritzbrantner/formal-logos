module

public import TruthCore.Logic.AssertionRetorsion

/-! A scoped bearer principle for the Cogito. The occurrence predicate ranges
over thoughts and the phenomenal predicate selects those experienced. Whether
that selection licenses a bearer is an independent interpretation question. -/

@[expose] public section

namespace TruthCore.Logic.ExperiencedThoughtBearer

/-- Only experienced, occurring thoughts require a bearer. Nothing here
identifies the bearer with a speaker or classifies it as a substance. -/
def ExperiencedThoughtsHaveBearers {Episode Subject : Type}
    (Occurs Experienced : Episode → Prop) (Bears : Subject → Episode → Prop) : Prop :=
  ∀ e, Occurs e → Experienced e → ∃ b, Bears b e

/-- Two occurring thoughts. Only the first is experienced and borne.
Removing all bearers leaves that very same phenomenal occurrence. -/
def BearerScopeControl : Prop :=
    let occurs : Bool → Prop := fun _ => True
    let experienced : Bool → Prop := fun e => e = false
    let bears : Unit → Bool → Prop := fun _ e => e = false
    let noBearer : Unit → Bool → Prop := fun _ _ => False
    AssertionRetorsion.ExperienceOccurs occurs experienced ∧
    ExperiencedThoughtsHaveBearers occurs experienced bears ∧
    ¬ CogitoSubject.EveryThoughtHasSubject occurs bears ∧
    ¬ CogitoSubject.SomeThinkingSubject occurs noBearer

end TruthCore.Logic.ExperiencedThoughtBearer
