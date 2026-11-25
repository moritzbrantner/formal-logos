import TruthCore.Case.Catholicism.DivineLoveBridge
import TruthCore.Causality.AppetitePowerExercise
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

namespace SelfKnowledgeLove.OwnGood

open TruthCore.Case.Catholicism.DivineLoveBridge
open TruthCore.Causality.AppetitePowerExercise
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

/-- The self-case alone needs neither a creature nor causal responsibility for one. -/
theorem thinSelfLove {B R : Type} {IsGod HasWill : B → Prop} {GoodIn : B → R → Prop}
    {WillsGoodFor : B → B → R → Prop} {Loves : B → B → Prop} {esse : R} {g : B}
    (hOwn : DivineOwnGoodWilling IsGod HasWill GoodIn WillsGoodFor esse)
    (hMeaning : WillingGoodEntailsLove GoodIn WillsGoodFor Loves)
    (hg : IsGod g) (hw : HasWill g) (hGood : GoodIn g esse) : Loves g g :=
  hMeaning g g esse hGood (hOwn g hg hw hGood)

/-- Classify the selected exercise. Other exercises can communicate goods,
including this good on this same occasion. -/
def unsharedMode {m : Interpretation} {s : m.Subject} {o : m.Object}
    {t : m.Occasion} : Exercise m s o t → Prop
  | .seeking .. | .loving .. | .delighting .. => True
  | .communicating .. => False

/-- A test of actual appetite at its principal end. The end is identified at
the level of the apprehended object. The open dilemma concerns failure of the
principal exercise, not failure to perform each possible act of will. -/
theorem restInOwnGood (m : Interpretation) {R : Type} {g : m.Subject}
    {t : m.Occasion} {own : m.Object} {principal : m.Object → Prop}
    {potent : m.Subject → R → Prop} {r : R}
    (hPure : PureAct potent g)
    (hDue : (∃ o, principal o ∧ ∃ act : Exercise m g o t, unsharedMode act) ∨ potent g r)
    (hObject : ∀ o, principal o → o = own)
    (hPossessed : m.possessed g own t) :
    m.loves g own t ∨ m.delights g own t := by
  obtain ⟨o, hEnd, act, mode⟩ := hDue.resolve_right (hPure r)
  have same := hObject o hEnd
  subst o
  cases act with
  | seeking _ absent _ => exact False.elim (absent hPossessed)
  | loving _ _ affirms => exact Or.inl affirms
  | delighting _ _ delights => exact Or.inr delights
  | communicating _ _ _ _ _ => exact False.elim mode

example : possessedLove.loves () () () ∨ possessedLove.delights () () () :=
  restInOwnGood possessedLove (potent := fun _ (_ : Unit) => False) (r := ())
    (principal := fun o => o = ()) (fun _ => id)
    (.inl ⟨(), rfl, .loving True.intro True.intro True.intro, True.intro⟩)
    (fun _ h => h) True.intro

/-- The exercise in this populated interpretation affirms the possessed good,
without delight, a recipient of communication, or a second subject. -/
theorem oneLover : possessedLove.loves () () () ∧ ¬ possessedLove.delights () () () ∧
    (∀ recipient, ¬ possessedLove.communicates () recipient () ()) ∧
    (∀ s : possessedLove.Subject, s = ()) :=
  ⟨True.intro, id, fun _ => id, fun | () => rfl⟩

end SelfKnowledgeLove.OwnGood
