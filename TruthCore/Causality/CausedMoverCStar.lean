module

public import TruthCore.Causality.MotionMapsBatch1

/-!
# C\* for caused movers: the operation route and the reciprocity exclusion

Analyst formulations, attribution deferred, for the commitment C\* on the
absolute First Way (`docs/notes/caused-mover-cstar.md`, sections 2 and 4). The
vocabulary of the prima via and of `MotionMapsBatch1` is reused unchanged
(`MovedIn`, `MovesIn`, `RelevantTo`, `MovesAsMoved`, `OperationOf`,
`InPotency`, `ActualizedQuaPotential`, `CausesIn`, `esse`); the senses are
MOTION_1 for being moved and moving and CAUSE_2 for causing being.

A *caused mover* is one whose being something other than itself causes
(`∃ c, c ≠ y ∧ CausesIn c y esse`). The guard is written out in each
definition; it is the only CAUSE_2 use, and the premise `631e014f` is the
explicit passage from it to MOTION_1 moving.

Applicability of every premise below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.CausedMoverCStar

universe u v

/-- A mover whose being another causes is, whenever it moves something, in
potency to an operation respect of its own (`631e014f`). -/
def CausedMoverInPotencyToItsOperation {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (OperationOf : Being → Being → Respect → Respect → Prop)
    (InPotency : Being → Respect → Prop) : Prop :=
  ∀ y x r, (∃ c, c ≠ y ∧ CausesIn c y esse) → MovesIn y x r →
    ∃ o, OperationOf y x r o ∧ InPotency y o

/-- The operation respect of a moving is relevant to that moving (`7bf380c6`). -/
def OperationRespectIsRelevant {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (OperationOf : Being → Being → Respect → Respect → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop) : Prop :=
  ∀ y x r o, MovesIn y x r → OperationOf y x r o → RelevantTo y x r o

/-- C\* for caused movers (`e3afc8a3`): a caused mover of another that is being
moved in some respect is being moved in some respect relevant to that moving. -/
def CausedMoverMovedInRelevantRespect {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (RelevantTo : Being → Being → Respect → Respect → Prop) : Prop :=
  ∀ y x r, (∃ c, c ≠ y ∧ CausesIn c y esse) → y ≠ x → MovesIn y x r →
    (∃ r', MovedIn y r') → ∃ r', MovedIn y r' ∧ RelevantTo y x r r'

/-- A mover of another that is being moved in some respect has its being caused
by something other than itself. Classically this is the contrapositive of "a
mover of another whose being nothing else causes is moved in no respect"; the
positive form is constructively stronger. -/
def MovedMoverIsCaused {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ y x r r', y ≠ x → MovesIn y x r → MovedIn y r' → ∃ c, c ≠ y ∧ CausesIn c y esse

/-- Reciprocal moved movers (`4f6ac439`): two distinct beings each move the
other while each is being moved in the respect in which the other moves it. -/
def SomeTwoMoveEachOtherWhileMoved {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∃ a b r s, a ≠ b ∧ MovesIn a b r ∧ MovesIn b a s ∧ MovedIn a s ∧ MovedIn b r

/-- No two distinct beings each move the other while each is being moved in the
respect in which the other moves it. -/
def NoTwoMoveEachOtherWhileMoved {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ¬ SomeTwoMoveEachOtherWhileMoved MovedIn MovesIn

end TruthCore.Causality.CausedMoverCStar
