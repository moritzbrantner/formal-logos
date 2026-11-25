module

public import TruthCore.Logic.EpistemicAuthority

@[expose] public section

namespace TruthCore.Logic.BeliefReasonWitness

open EpistemicReasons EpistemicReasonDefinitionFork EpistemicAuthority

/-- In the ambiguous-count profile the only attributed consideration favors
withholding on parity. Both attitudes have the same subject matter. The aim
parameter varies the force rule without changing this bearing. -/
def suspension (aim : Preference → Prop) : Frame where
  Agent := Unit
  Content := Content
  Consideration := Consideration
  Preference := Preference
  Attitude := Sum Content Content
  believe := Sum.inl
  about := Sum.elim id id
  beliefAbout := fun _ => rfl
  Reason := fun _ _ => False
  CountsAsReason := fun _ r t => r = .count ∧ t = Sum.inr .even
  assessable := fun _ => True
  applies := fun _ _ _ => True
  favors := fun _ r t => r = .count ∧ t = Sum.inr .even
  Holds := fun p => p = .even
  produces := fun _ _ _ => False
  rewards := fun _ _ _ => False
  force := fun _ r t d => (r = .count ∧ t = Sum.inr .even) ∧ aim d
  actualPreference := fun _ => .accuracy

/-- Drop only the presentation, retaining the count and its actual force. -/
def unlinked : Frame := { goalRelative with Reason := fun _ _ => False }

/-- Interpret the second content as the denial: its truth slot is false while
the first content has a reason to believe it. No adoption semantics is supplied. -/
def selectedDenial : Frame := { goalRelative with Holds := fun p => p = .even }

end TruthCore.Logic.BeliefReasonWitness
