module

public import TruthCore.Modal.Cube
public import TruthCore.Logic.DistributedKnowledge
public import TruthCore.Logic.BeliefReasonWitness
public import TruthCore.Logic.AssertionRetorsion

/-! Idealized relational belief. The frame of each agent and the actual world
are independently supplied. The laws concern this representation of belief. -/

@[expose] public section
namespace TruthCore.Logic.Doxastic

open TruthCore.Modal

structure Context (Agent W : Type) where
  belief : Agent → Frame W
  actual : W

variable {Agent W : Type}

/-- Belief is universal truth over the agent's selected alternatives. -/
def Believes (c : Context Agent W) (a : Agent) (p : W → Prop) (w : W) : Prop :=
  Holds (c.belief a) (fun v (_ : Unit) => p v) w (.box (.atom ()))

def Withholds (c : Context Agent W) (a : Agent) (p : W → Prop) (w : W) : Prop :=
  ¬ Believes c a p w ∧ ¬ Believes c a (fun v => ¬ p v) w

theorem consistent (c : Context Agent W) (a : Agent) (h : Serial (c.belief a))
    (p : W → Prop) (w : W) :
    Believes c a p w → ¬ Believes c a (fun v => ¬ p v) w := by
  intro hp hn
  obtain ⟨v, ha, hv⟩ :=
    axiomD_valid (c.belief a) h (.atom ()) (fun v _ => p v) w hp
  exact hn v ha hv

theorem positiveIntrospection (c : Context Agent W) (a : Agent)
    (h : Transitive (c.belief a)) (p : W → Prop) (w : W) :
    Believes c a p w → Believes c a (Believes c a p) w :=
  axiom4_valid (c.belief a) h (.atom ()) (fun v _ => p v) w

theorem negativeIntrospection (c : Context Agent W) (a : Agent)
    (h : Euclidean (c.belief a)) (p : W → Prop) (w : W) :
    ¬ Believes c a p w → Believes c a (fun v => ¬ Believes c a p v) w := by
  classical
  intro hn
  have possible : Holds (c.belief a) (fun (v : W) (_ : Unit) => ¬ p v) w
      (.diamond (.atom ())) := by
    apply Classical.byContradiction
    intro hNone
    apply hn
    intro v hv
    apply Classical.byContradiction
    intro hFalse
    exact hNone ⟨v, hv, hFalse⟩
  intro v hv hp
  obtain ⟨u, hu, hFalse⟩ :=
    axiom5_valid (c.belief a) h (.atom ()) (fun v _ => ¬ p v) w possible v hv
  exact hFalse (hp u hu)

theorem distribution (c : Context Agent W) (a : Agent) (p q : W → Prop) (w : W) :
    Believes c a (fun v => p v → q v) w →
    Believes c a p w → Believes c a q w :=
  axiomK_valid (c.belief a) (.atom false) (.atom true)
    (fun v b => if b then q v else p v) w

theorem conjunction (c : Context Agent W) (a : Agent) (p q : W → Prop) (w : W) :
    Believes c a (fun v => p v ∧ q v) w ↔ Believes c a p w ∧ Believes c a q w :=
  ⟨fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩,
   fun ⟨hp, hq⟩ v hv => ⟨hp v hv, hq v hv⟩⟩

theorem closedUnderConsequence (c : Context Agent W) (a : Agent)
    {p q : W → Prop} (imp : ∀ v, p v → q v) (w : W)
    (hp : Believes c a p w) : Believes c a q w :=
  distribution c a p q w (fun v _ => imp v) hp

theorem knownImpliesBelieved (c : Context Agent W) (a : Agent)
    (epistemic : Frame W)
    (included : ∀ v, (c.belief a).access c.actual v → epistemic.access c.actual v)
    (p : W → Prop) :
    JustificationIntrospection.Knows epistemic p c.actual → Believes c a p c.actual :=
  fun hk v hv => hk v (included v hv)

/-- Transfer preserves the agent and time of the distributed knowledge witness. -/
theorem distributedKnownImpliesBelieved {Time : Type}
    (c : Context Agent W) (epistemic : Agent → Time → Frame W) (modal : Frame W)
    (included : ∀ a t v, (c.belief a).access c.actual v →
      (epistemic a t).access c.actual v)
    (p : W → Prop)
    (known : (DistributedKnowledge.context
      (fun a t => JustificationIntrospection.Knows (epistemic a t))
      modal c.actual).knows p c.actual) :
    ∃ a : Agent, Believes c a p c.actual := by
  obtain ⟨a, t, hk⟩ := known
  exact ⟨a, knownImpliesBelieved c a (epistemic a t) (included a t) p hk⟩

/-- A fixed core selects the same alternatives at every world. -/
def fixed (core : W → Prop) : Frame W := ⟨fun _ v => core v⟩

theorem fixedKD45 (core : W → Prop) (inhabited : ∃ v, core v) :
    FrameSatisfies .KD45 (fixed core) :=
  ⟨fun _ => inhabited, fun _ _ _ _ hv => hv, fun _ _ _ _ hv => hv⟩

/-- Both worlds consider only true possible. The designated world is false. -/
def biased (Agent : Type) : Context Agent Bool :=
  ⟨fun _ => fixed (· = true), false⟩

theorem biasedKD45 (a : Agent) :
    FrameSatisfies .KD45 ((biased Agent).belief a) :=
  fixedKD45 _ ⟨true, rfl⟩

theorem biasedFalseBelief (a : Agent) :
    Believes (biased Agent) a (· = true) (biased Agent).actual ∧
      ¬ ((biased Agent).actual = true) :=
  ⟨fun _ hv => hv, Bool.noConfusion⟩

/-- A reflexive knowledge frame can sit inside the belief frame while Kp holds
and the belief agent withholds on p. The omitted direction of inclusion matters. -/
theorem reverseInclusionControl :
    let c : Context Unit Bool := ⟨fun _ => fixed (fun _ => True), false⟩
    let epistemic : Frame Bool := ⟨Eq⟩
    Reflexive epistemic ∧ FrameSatisfies .KD45 (c.belief ()) ∧
      (∀ v, epistemic.access c.actual v → (c.belief ()).access c.actual v) ∧
      JustificationIntrospection.Knows epistemic (· = false) c.actual ∧
      Withholds c () (· = false) c.actual := by
  exact ⟨fun _ => rfl, fixedKD45 _ ⟨false, trivial⟩, fun _ _ => trivial,
    fun _ hv => hv.symm, fun hp => Bool.noConfusion (hp true trivial),
    fun hn => hn false trivial rfl⟩

def MooreOmissive (c : Context Agent W) (a : Agent) (p : W → Prop) (w : W) : Prop :=
  p w ∧ ¬ Believes c a p w

def MooreCommissive (c : Context Agent W) (a : Agent) (p : W → Prop) (w : W) : Prop :=
  p w ∧ Believes c a (fun v => ¬ p v) w

/-- Each Moore content is true at the actual world of the biased frame.
The reverse-inclusion control supplies the omissive content with withholding. -/
theorem mooreTruth :
    MooreOmissive (biased Unit) () (· = false) false ∧
      MooreCommissive (biased Unit) () (· = false) false :=
  ⟨⟨rfl, fun hp => Bool.noConfusion (hp true rfl)⟩,
   ⟨rfl, fun _ hv hn => Bool.noConfusion (hv.symm.trans hn)⟩⟩

/-- For a fixed speech context, local sincerity gives belief in the exact
asserted content at that context's actual world. -/
theorem noSincereOmissiveAssertion (c : Context Agent W) (p : W → Prop)
    (ascribes : Agent → (W → Prop) → Prop) (a : Agent)
    (serial : Serial (c.belief a)) (transitive : Transitive (c.belief a))
    (sincere : AssertionRetorsion.AssertedContentIsBelieved ascribes
      (fun b q => Believes c b q c.actual) (MooreOmissive c a p)) :
    ¬ ascribes a (MooreOmissive c a p) := by
  intro asserted
  have h := sincere a asserted
  have hp : Believes c a p c.actual := fun v hv => (h v hv).1
  obtain ⟨v, hv⟩ := serial c.actual
  exact (h v hv).2 (positiveIntrospection c a transitive p c.actual hp v hv)

theorem noSincereCommissiveAssertion (c : Context Agent W) (p : W → Prop)
    (ascribes : Agent → (W → Prop) → Prop) (a : Agent)
    (serial : Serial (c.belief a)) (transitive : Transitive (c.belief a))
    (sincere : AssertionRetorsion.AssertedContentIsBelieved ascribes
      (fun b q => Believes c b q c.actual) (MooreCommissive c a p)) :
    ¬ ascribes a (MooreCommissive c a p) := by
  intro asserted
  have h := sincere a asserted
  have hp : Believes c a p c.actual := fun v hv => (h v hv).1
  obtain ⟨v, hv⟩ := serial c.actual
  exact consistent c a serial p v (positiveIntrospection c a transitive p c.actual hp v hv)
    (h v hv).2

/-- Use the existing suspension profile, with parity true at actuality and
false at the other alternative. A reason targeting suspension does not adopt
an attitude for the agent or furnish a reason for the belief target. -/
theorem suspensionControl :
    let f := BeliefReasonWitness.suspension (fun _ => True)
    EpistemicReasonDefinitionFork.OrdinaryInstance f () .count (.inr .even) ∧
      ¬ (∃ r, EpistemicReasonDefinitionFork.OrdinaryInstance f () r (f.believe .even)) ∧
      Withholds (⟨fun _ => fixed (fun _ => True), false⟩ : Context Unit Bool)
        () (· = false) false := by
  refine ⟨⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩, ?_, reverseInclusionControl.2.2.2.2⟩
  rintro ⟨_, h⟩
  cases h.1.2

/-- A supplied justification predicate can be believed while false at the
actual world. This is a structural control, with warrant interpreted separately. -/
theorem beliefInJustificationControl :
    ∃ justified : Bool → Prop,
      Believes (biased Unit) () justified false ∧ ¬ justified false :=
  ⟨(· = true), biasedFalseBelief ()⟩

end TruthCore.Logic.Doxastic
