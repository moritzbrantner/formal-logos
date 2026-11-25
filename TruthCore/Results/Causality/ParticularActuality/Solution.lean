module

public import TruthCore.Causality.ParticularActuality
public import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ParticularActuality

open TruthCore.Causality.ParticularActuality
open TruthCore.Causality.JointGroups (Groups)
open TruthCore.Causality.DerivativeJointPower (Supply)
open TruthCore.Causality.Round2PerfectionPrimacy (PerfectionsAreModesOfBeing)
open TruthCore.Case.Catholicism

private theorem lastStep {E G : Type} {h : Groups E G} {I : E → Prop} {e : E}
    (supplied : Supply h I e) :
    I e ∨ ∃ g, h.admitted g ∧ h.effect g = e ∧ ∀ d ∈ h.contributors g, Supply h I d := by
  cases supplied with
  | intrinsic _ hi => exact Or.inl hi
  | joint g hg hInputs => exact Or.inr ⟨g, hg, rfl, hInputs⟩

theorem inheritance {B R E G : Type} (h : Groups E G) (I : E → Prop)
    (event : B → R → E) (esse : R) (selected InAct mode : B → R → Prop)
    (hModes : PerfectionsAreModesOfBeing InAct mode)
    (hBearer : ModeUsesBearer h I event esse selected mode) :
    InheritsEsseCuts h I event esse selected InAct := by
  intro x r hs ha
  obtain ⟨supplied, derived, required⟩ := hBearer x r hs (hModes x r ha)
  refine ⟨supplied, ?_⟩
  intro keep cut realization
  rcases lastStep realization with hi | ⟨g, hg, he, inputs⟩
  · exact derived hi
  · exact cut (inputs _ (required g hg.1 he))

theorem mediatedInheritance {B R E G : Type} (h : Groups E G) (I : E → Prop)
    (event : B → R → E) (esse : R) (selected InAct mode : B → R → Prop)
    (hModes : PerfectionsAreModesOfBeing InAct mode)
    (hMediated : ModeThroughBearer h I event esse selected mode) :
    InheritsEsseCuts h I event esse selected InAct := by
  intro x r hs ha
  obtain ⟨original, region, inside, root, step⟩ := hMediated x r hs (hModes x r ha)
  refine ⟨original, ?_⟩
  intro keep cut realization
  apply cut
  have trace {e} (derivation : Supply (restrict h keep) I e) :
      e ∈ region → Supply (restrict h keep) I (event x esse) := by
    induction derivation with
    | intrinsic e hi =>
      intro he
      exact root e he hi ▸ Supply.intrinsic e hi
    | joint g hg inputs ih =>
      intro he
      rcases step g hg.1 he with hb | ⟨d, hd, member⟩
      · exact hb ▸ Supply.joint g hg inputs
      · exact ih d hd member
  exact trace realization inside

theorem singleDeletion : SingleDeletionTest := by
  intro B R E G h I event esse selected InAct nonIntrinsic
  constructor
  · intro cuts x r hs ha
    obtain ⟨original, inheritCuts⟩ := cuts x r hs ha
    refine ⟨original, inheritCuts _ ?_⟩
    intro hb
    rcases lastStep hb with hi | ⟨g, hg, he, _⟩
    · exact nonIntrinsic x r hs ha hi
    · exact hg.2 he
  · intro noBypass x r hs ha
    obtain ⟨original, blocked⟩ := noBypass x r hs ha
    refine ⟨original, ?_⟩
    intro keep missing supplied
    apply blocked
    have transport {e} (derivation : Supply (restrict h keep) I e) :
        Supply (restrict h (fun g => h.effect g ≠ event x esse)) I e := by
      induction derivation with
      | intrinsic e hi => exact .intrinsic e hi
      | joint g hg inputs ih =>
        have different : h.effect g ≠ event x esse := by
          intro he
          exact missing (he ▸ Supply.joint g hg inputs)
        exact .joint g ⟨hg.1, different⟩ ih
    exact transport supplied

open Control

private theorem seed {h : Groups Event Event} :
    Supply h intrinsic (.source, false) := .intrinsic _ rfl

private theorem esseSupply (j : Bool) (h : Groups Event Event)
    (hc : h.contributors = (records j).contributors) (he : h.effect = id)
    (x : TransferRole) (ha : x ≠ .source → h.admitted (x, false)) :
    Supply h intrinsic (x, false) := by
  by_cases root : x = .source
  · subst x
    exact seed
  · have derivation := Supply.joint (h := h) (intrinsic := intrinsic) (x, false) (ha root)
      (fun d hd => by
        rw [hc] at hd
        change d = (.source, false) at hd
        exact hd ▸ seed)
    simpa only [he, id_eq] using derivation

private theorem allSupply (j : Bool) (x : TransferRole) (r : Bool) :
    Supply (records j) intrinsic (event x r) := by
  have esse (y : TransferRole) : Supply (records j) intrinsic (y, false) :=
    esseSupply j _ rfl rfl y (by intro h e; exact h (congrArg Prod.fst e))
  cases r with
  | false => exact esse x
  | true =>
    apply Supply.joint (h := records j) (x, true) (by
      intro eq
      exact Bool.noConfusion (congrArg Prod.snd eq))
    intro d hd
    change d = (.producer, false) ∨ j = true ∧ d = (x, false) at hd
    rcases hd with h | ⟨_, h⟩
    · exact h ▸ esse .producer
    · exact h ▸ esse x

private theorem bearerBasis :
    ModeUsesBearer (records true) intrinsic event false selected transferAct := by
  intro x r hr _
  change r = true at hr
  subst r
  refine ⟨allSupply true x true, ?_, ?_⟩
  · intro eq
    exact Bool.noConfusion (congrArg Prod.snd eq)
  · intro g _ he
    change g = (x, true) at he
    subst g
    exact Or.inr ⟨rfl, rfl⟩

private theorem cutTarget (j r : Bool) :
    ¬ Supply (restrict (records j) (elsewhere r)) intrinsic (event .recipient r) := by
  intro h
  rcases lastStep h with hi | ⟨g, hg, he, _⟩
  · exact TransferRole.noConfusion (congrArg Prod.fst hi)
  · exact hg.2 he

theorem controls : Control.Certificate := by
  have modes : PerfectionsAreModesOfBeing transferAct transferAct := fun _ _ h => h
  have cuts := inheritance _ _ _ _ _ _ _ modes bearerBasis
  refine ⟨TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.rival,
    modes, bearerBasis, cuts, allSupply false, cutTarget true false,
    (cuts .recipient true rfl trivial).2 _ (cutTarget true false),
    cutTarget false false, ?_, ?_, cutTarget true true⟩
  · have producer : Supply (restrict (records false) (elsewhere false)) intrinsic
        (.producer, false) := esseSupply false (restrict (records false) (elsewhere false)) rfl rfl .producer (by
          intro _
          exact ⟨by unfold records; decide, by unfold elsewhere; decide⟩)
    apply Supply.joint (h := restrict (records false) (elsewhere false)) (.recipient, true)
      (by exact ⟨by unfold records; decide, by unfold elsewhere; decide⟩)
    intro d hd
    change d = (.producer, false) ∨ false = true ∧ d = (.recipient, false) at hd
    rcases hd with h | ⟨h, _⟩
    · exact h ▸ producer
    · contradiction
  · exact esseSupply true (restrict (records true) (elsewhere true)) rfl rfl .recipient (by
      intro _
      exact ⟨by unfold records; decide, by unfold elsewhere; decide⟩)

end TruthCore.Results.Causality.ParticularActuality
