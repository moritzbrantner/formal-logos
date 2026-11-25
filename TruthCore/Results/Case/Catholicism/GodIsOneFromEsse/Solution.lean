module

public import TruthCore.Case.Catholicism.GodIsOneFromEsse
public import TruthCore.Models.FiniteSupport
public import TruthCore.Results.Causality.ClassicalGodAssembly.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.GodIsOneFromEsse
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.GodIsOneFromEsse
open TruthCore.Causality.GodMaximalCausal
open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.Round2Grounding
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic

/-- The maximal witness has esse, so even the converse restricted to actual
recipients suffices. This scope check uses the existing CausesAllInGenus. -/
theorem oneFromActualRecipients {Being Respect : Type} (IsGod : Being → Prop)
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hWitness : SomeBeingMaximalInBeing InAct MoreIn esse)
    (hExclude : MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn esse)
    (hCause : ∀ g, IsGod g → CausesAllInGenus InAct CausesIn esse g)
    (hEM : ExcludedMiddle) : GodIsOne IsGod := by
  obtain ⟨m, hm⟩ := hWitness
  have pin (g : Being) (hg : IsGod g) : g = m := by
    rcases hEM (g = m) with heq | hne
    · exact heq
    · exact (hExclude m hm g hne (hCause g hg m (Ne.symm hne) hm.1)).elim
  intro g hg k hk
  exact (pin k hk).trans (pin g hg).symm

theorem oneFromWitness {Being Respect : Type} (IsGod : Being → Prop)
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hWitness : SomeBeingMaximalInBeing InAct MoreIn esse)
    (hExclude : MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn esse)
    (hCause : GodCausesBeingOfAllOthers IsGod CausesIn esse)
    (hEM : ExcludedMiddle) : GodIsOne IsGod := by
  exact oneFromActualRecipients IsGod InAct MoreIn CausesIn esse hWitness hExclude
    (fun g hg y hne _ => hCause g y hg hne) hEM

theorem oneFromGodMaximal {Being Respect : Type} (IsGod : Being → Prop)
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMax : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hExclude : MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn esse)
    (hCause : GodCausesBeingOfAllOthers IsGod CausesIn esse)
    (hEM : ExcludedMiddle) : GodIsOne IsGod := by
  intro g hg k hk
  rcases hEM (k = g) with heq | hne
  · exact heq
  · exact (hExclude g (hMax g hg) k hne (hCause k g hk (Ne.symm hne))).elim

theorem oneFromNonmutualDependence {Being Respect : Type} (IsGod : Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (DependsForBeing : Being → Being → Prop)
    (hCause : GodCausesBeingOfAllOthers IsGod CausesIn esse)
    (hDepend : EsseEffectDependsOnItsCause CausesIn esse DependsForBeing)
    (hNonmutual : DistinctBeingsNotMutuallyDependent DependsForBeing)
    (hEM : ExcludedMiddle) : GodIsOne IsGod := by
  intro g hg k hk
  rcases hEM (k = g) with heq | hne
  · exact heq
  · have hkg := hDepend g k (Ne.symm hne) (hCause g k hg hne)
    have hgk := hDepend k g hne (hCause k g hk (Ne.symm hne))
    exact (hNonmutual k g hne hkg hgk).elim

/-- Apply the existing assembly to the very same signature. Existence and
the classical field are still separate premises of that assembly. -/
theorem assembleFromWitness (σ : Signature) {Respect : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (hWitness : SomeBeingMaximalInBeing InAct MoreIn esse)
    (hExclude : MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn esse)
    (hCause : GodCausesBeingOfAllOthers σ.IsGod CausesIn esse)
    (hEM : ExcludedMiddle) (hExists : GodExists σ.IsGod)
    (hAttributes : GodHasClassicalAttributes σ) : UniqueClassicalGodExists σ := by
  exact TruthCore.Results.Causality.ClassicalGodAssembly.assemble σ hExists
    (oneFromWitness σ.IsGod InAct MoreIn CausesIn esse hWitness hExclude hCause hEM) hAttributes

/-- Enumerate the two coordinates constructively using the existing Bool
instances. This keeps the finite controls on the zero-axiom boundary. -/
local instance pairForall {p : Bool × Bool → Prop} [DecidablePred p] :
    Decidable (∀ x, p x) :=
  decidable_of_iff (∀ a b, p (a, b))
    ⟨fun h ⟨a, b⟩ => h a b, fun h a b => h (a, b)⟩

local instance pairExists {p : Bool × Bool → Prop} [DecidablePred p] :
    Decidable (∃ x, p x) :=
  decidable_of_iff (∃ a b, p (a, b))
    ⟨fun ⟨a, b, h⟩ => ⟨(a, b), h⟩, fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩⟩

theorem controls : Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [Joint, MaximalControls, DependenceControls, Partition, RecipientBoundary, SomeBeingMaximalInBeing,
      GodIsMaximalInBeing, MaximumHasNoDistinctEsseCause, GodCausesBeingOfAllOthers,
      EsseEffectDependsOnItsCause, DistinctBeingsNotMutuallyDependent, GodIsOne, IsTheOneGod,
      MaximumInGenusCausesAllInGenusReading, CausesAllInGenus, IsMaximalIn, IsMaximumIn,
      one, both, neither, receives, gives, above, actual, flat, cyclic, reciprocal, independent,
      opposite, sourceAbove, domainReceives, domainGift, source]
  all_goals and_intros <;> decide

end TruthCore.Results.Case.Catholicism.GodIsOneFromEsse
