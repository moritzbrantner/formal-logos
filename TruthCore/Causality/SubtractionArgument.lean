module

public import TruthCore.Causality.TractarianLogicalSpace
public import TruthCore.Causality.ModalSenseSupport
public import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers
public import TruthCore.Logic.ExcludedMiddle

/-!
# The subtraction argument, free recombination and the necessary-being node

Analyst formulation, attribution deferred (logic first). The subtraction
argument for metaphysical nihilism (Baldwin 1996; Rodriguez-Pereyra 1997,
2002; Efird and Stoneham 2005) and the recombination principles behind its
premises (Hume's "distinct existences", Lewis 1986 and Armstrong 1989 on
recombination) are navigation only. No source claim is made; the formulations
below are the analyst's, stated on the route's own profile `m : Profile W B`
(worlds `m.ontic.frame`, rigid candidates `B`, world-relative existence
`m.ontic.ExistsAt`, a world-independent concreteness predicate `m.concrete`).
The causal fields of the shared `CausalityFrame` are not used: nothing here is
causal, and the necessary-being nodes are stated on `Profile`.

* `ConcretePresence m x v`: `x` is concrete and exists at `v`.
* A1 `PossiblyFinitelyManyConcrete`: some world accessible from `w` has only
  finitely many concrete objects, read as "all of them lie in one finite list".
  The family is zero-axiom and does not import Mathlib; covering by a list is
  the standard characterization of `Set.Finite` and is used for that reason.
* A2 `EachConcreteCouldFailAt m v`: every concrete object present at `v` is
  absent at some world accessible from `v`. `…Throughout` asks this at every
  world accessible from `w`.
* A3 `SubtractableAt m v` (subtraction, conditional form): if a concrete object
  present at `v` could fail to exist, it could fail to exist with no newcomer,
  that is at some accessible world where it is absent and every concrete object
  present there is present at `v`. The literal wording "the non-existence of
  `x` does not necessitate the existence of any other concrete object" is
  `NonNecessitationAt`; it contains the A2 instance (`Laws`, 3), so the
  conditional form is the A2-free remainder.
* Conclusion `PossiblyNoConcrete m w`: the existing `JointAbsence` of the
  stage-one quantifier family for the concrete-presence predicate (some world
  accessible from `w` has no concrete object). Reused, not restated.

Recombination (absence half of Hume's dictum), on concrete candidates:

* `UnrestrictedRecombinationAt`: for distinct concrete `x`, `y`, if `x` could
  exist then `x` could exist without `y`.
* `ContingentRecombinationAt`: the same for those `y` that could be absent.
* Their exact difference is `CompanionedConcretaPossiblyAbsentAt`: every
  concrete candidate with a distinct possible concrete companion could be
  absent.

All principles are inputs of checked consequences. None is asserted, and the
worlds are elements of `W`, not a claim about metaphysical possibility.
-/

@[expose] public section

namespace TruthCore.Causality.SubtractionArgument

open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (Dia Box)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.ModalSenseSupport (OnticFrameTransitive)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (JointAbsence)
open TruthCore.Case.Catholicism (Signature)
open TruthCore.Logic.StrengthComparison (ComparisonSpec)

variable {W B : Type}

/-! ## The subtraction argument -/

/-- `x` is concrete and exists at `v`. Concreteness alone confers no existence. -/
def ConcretePresence (m : Profile W B) : B → W → Prop :=
  fun x v => m.concrete x ∧ m.ontic.ExistsAt v x

/-- A1: some world accessible from `w` has finitely many concrete objects:
one finite list contains every concrete object present there. Weaker than the
existing `FinitePopulationCover`, which bounds every accessible world at once. -/
def PossiblyFinitelyManyConcrete (m : Profile W B) (w : W) : Prop :=
  Dia m.ontic.frame (fun v => ∃ xs : List B, ∀ x, ConcretePresence m x v → x ∈ xs) w

/-- A2 at `v`: each concrete object present at `v` could fail to exist, that
is, is absent at some world accessible from `v`. -/
def EachConcreteCouldFailAt (m : Profile W B) (v : W) : Prop :=
  ∀ x, ConcretePresence m x v → Dia m.ontic.frame (fun u => ¬ m.ontic.ExistsAt u x) v

/-- A2 throughout the worlds accessible from `w`. -/
def EachConcreteCouldFailThroughout (m : Profile W B) (w : W) : Prop :=
  ∀ v, m.ontic.frame.access w v → EachConcreteCouldFailAt m v

/-- No newcomer at `u` relative to `v`: every concrete object present at `u` is
present at `v`. -/
def NoNewcomer (m : Profile W B) (v u : W) : Prop :=
  ∀ y, ConcretePresence m y u → ConcretePresence m y v

/-- A3 at `v`, conditional subtraction: a concrete object present at `v` that
could fail to exist could fail to exist with no newcomer. -/
def SubtractableAt (m : Profile W B) (v : W) : Prop :=
  ∀ x, ConcretePresence m x v →
    Dia m.ontic.frame (fun u => ¬ m.ontic.ExistsAt u x) v →
    Dia m.ontic.frame (fun u => ¬ m.ontic.ExistsAt u x ∧ NoNewcomer m v u) v

/-- A3 throughout the worlds accessible from `w`. -/
def SubtractableThroughout (m : Profile W B) (w : W) : Prop :=
  ∀ v, m.ontic.frame.access w v → SubtractableAt m v

/-- The literal A3 at `v`: the non-existence of a concrete object present at
`v` does not necessitate the existence of any concrete object absent at `v`
(one accessible world realizes the absence with no newcomer). -/
def NonNecessitationAt (m : Profile W B) (v : W) : Prop :=
  ∀ x, ConcretePresence m x v →
    Dia m.ontic.frame (fun u => ¬ m.ontic.ExistsAt u x ∧ NoNewcomer m v u) v

/-- Conclusion: possibly no concrete object exists. The existing stage-one
`JointAbsence` for the concrete-presence predicate. -/
def PossiblyNoConcrete (m : Profile W B) (w : W) : Prop :=
  JointAbsence m.ontic.frame (ConcretePresence m) w

/-- Necessarily some concrete object exists (de dicto): the negation of
`PossiblyNoConcrete`. It attaches necessity to no individual. -/
def NotPossiblyNoConcrete (m : Profile W B) (w : W) : Prop :=
  ¬ PossiblyNoConcrete m w

/-- A2 fails at `w`: not every concrete object present at `w` could fail to
exist. It names no particular object. -/
def NotEachConcreteCouldFailAt (m : Profile W B) (w : W) : Prop :=
  ¬ EachConcreteCouldFailAt m w

/-- A2 at the actual world is exactly the denial of the stage-one node
`NecessaryConcreteAt` at that world. -/
def ContingencyPremiseIsNoNecessaryConcretum (m : Profile W B) (w : W) : Prop :=
  EachConcreteCouldFailAt m w ↔ ¬ NecessaryConcreteAt m w

/-! ## Recombination -/

/-- Unrestricted free absence among distinct concrete candidates (absence half
of Hume's dictum): if `x` could exist, `x` could exist without `y`. -/
def UnrestrictedRecombinationAt (m : Profile W B) (w : W) : Prop :=
  ∀ x y, m.concrete x → m.concrete y → x ≠ y →
    Dia m.ontic.frame (fun v => m.ontic.ExistsAt v x) w →
    Dia m.ontic.frame (fun v => m.ontic.ExistsAt v x ∧ ¬ m.ontic.ExistsAt v y) w

/-- Free absence restricted to candidates that could be absent: if `x` could
exist and `y` could be absent, `x` could exist without `y`. -/
def ContingentRecombinationAt (m : Profile W B) (w : W) : Prop :=
  ∀ x y, m.concrete x → m.concrete y → x ≠ y →
    Dia m.ontic.frame (fun v => m.ontic.ExistsAt v x) w →
    Dia m.ontic.frame (fun v => ¬ m.ontic.ExistsAt v y) w →
    Dia m.ontic.frame (fun v => m.ontic.ExistsAt v x ∧ ¬ m.ontic.ExistsAt v y) w

/-- Difference: every concrete candidate that has a distinct concrete
candidate which could exist could itself be absent. -/
def CompanionedConcretaPossiblyAbsentAt (m : Profile W B) (w : W) : Prop :=
  ∀ y, m.concrete y →
    (∃ x, x ≠ y ∧ m.concrete x ∧ Dia m.ontic.frame (fun v => m.ontic.ExistsAt v x) w) →
    Dia m.ontic.frame (fun v => ¬ m.ontic.ExistsAt v y) w

/-- Every concrete candidate has a distinct concrete candidate that could
exist: no concrete candidate is the only possible concrete thing. -/
def ConcreteCompanionsAt (m : Profile W B) (w : W) : Prop :=
  ∀ y, m.concrete y →
    ∃ x, x ≠ y ∧ m.concrete x ∧ Dia m.ontic.frame (fun v => m.ontic.ExistsAt v x) w

/-- Unrestricted over contingent recombination; difference: companioned
concreta could be absent. -/
def unrestrictedOverContingent (m : Profile W B) (w : W) : ComparisonSpec where
  stronger := UnrestrictedRecombinationAt m w
  weaker := ContingentRecombinationAt m w
  delta := CompanionedConcretaPossiblyAbsentAt m w

/-- Exact factorization, for every profile and world. -/
def RecombinationFactorsExact : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W),
    UnrestrictedRecombinationAt m w ↔
      ContingentRecombinationAt m w ∧ CompanionedConcretaPossiblyAbsentAt m w

/-! ## Lowe's reply (analyst formulation) -/

/-- Some non-concrete candidate exists at every world accessible from `w`
(a necessary abstractum, de re). -/
def NecessaryAbstractumAt (m : Profile W B) (w : W) : Prop :=
  ∃ a, ¬ m.concrete a ∧ Box m.ontic.frame (fun v => m.ontic.ExistsAt v a) w

/-- At every world accessible from `w`, an existing non-concrete candidate
requires some existing concrete object (abstracta depend on concreta). -/
def AbstractaNeedConcretaThroughout (m : Profile W B) (w : W) : Prop :=
  ∀ v, m.ontic.frame.access w v → ∀ a, ¬ m.concrete a → m.ontic.ExistsAt v a →
    ∃ x, ConcretePresence m x v

/-! ## Laws and models -/

namespace Model

/-- General laws:
1. the stage-one node excludes the subtraction conclusion at its world, with
   no frame condition;
2. so does the box K necessary-being node;
3. the literal A3 is A2 together with the conditional A3, at every world;
4. elementary existence of all candidates (Tractarian logical space, the full
   recombination of `TractarianLogicalSpace`) gives the subtraction conclusion;
5. unrestricted recombination at every accessible world, with companions
   there, gives A2 throughout;
6. Lowe's reply: a necessary abstractum whose existence requires concreta at
   every accessible world excludes the subtraction conclusion;
7. given A1, A2 throughout, transitivity and excluded middle, Lowe's reply
   excludes A3 throughout: it denies subtraction, not contingency;
8. given excluded middle, A2 at a world is exactly the denial of the
   stage-one node there. -/
def Laws : Prop :=
  (∀ (W B : Type) (m : Profile W B) (w : W),
    NecessaryConcreteAt m w → NotPossiblyNoConcrete m w) ∧
  (∀ (W : Type) (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop),
    NecessaryRootBoxK σ m w CN → NotPossiblyNoConcrete m w) ∧
  (∀ (W B : Type) (m : Profile W B) (v : W),
    NonNecessitationAt m v ↔ EachConcreteCouldFailAt m v ∧ SubtractableAt m v) ∧
  (∀ (W B : Type) (m : Profile W B) (w : W),
    TractarianLogicalSpace.ElementaryExistenceAt m.ontic w → PossiblyNoConcrete m w) ∧
  (∀ (W B : Type) (m : Profile W B) (w : W),
    (∀ v, m.ontic.frame.access w v →
      UnrestrictedRecombinationAt m v ∧ ConcreteCompanionsAt m v) →
    EachConcreteCouldFailThroughout m w) ∧
  (∀ (W B : Type) (m : Profile W B) (w : W),
    NecessaryAbstractumAt m w → AbstractaNeedConcretaThroughout m w →
      NotPossiblyNoConcrete m w) ∧
  (∀ (W B : Type) (m : Profile W B) (w : W),
    TruthCore.Logic.ExcludedMiddle → OnticFrameTransitive m →
    PossiblyFinitelyManyConcrete m w → EachConcreteCouldFailThroughout m w →
    NecessaryAbstractumAt m w → AbstractaNeedConcretaThroughout m w →
      ¬ SubtractableThroughout m w) ∧
  (∀ (W B : Type) (m : Profile W B) (w : W),
    TruthCore.Logic.ExcludedMiddle → ContingencyPremiseIsNoNecessaryConcretum m w)

/-- Universal access on any world type. -/
def universal (W : Type) : Frame W := ⟨fun _ _ => True⟩

/-- Nonvacuity: one concrete object, present at world `true`, absent at
world `false`. -/
def unitProfile : Profile Bool Unit where
  ontic := { frame := universal Bool, ExistsAt := fun v _ => v = true, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (one-candidate nonvacuity model: the test concerns subtraction, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- A1 omitted: world `n` has exactly the concrete objects `k ≥ n`; every
world is infinite and none is empty. -/
def tailProfile : Profile Nat Nat where
  ontic := { frame := universal Nat, ExistsAt := fun n k => n ≤ k, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (A1 omission model: the test concerns finiteness, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- The candidates of the pairwise and Lowe model: two concrete objects and
one abstract object. -/
inductive PairCandidate where
  | a
  | b
  | s


/-- A3 omitted (pairwise recombination, Lowe): world `true` has `a`, world
`false` has `b`; the abstract `s` exists at both. -/
def pairProfile : Profile Bool PairCandidate where
  ontic := { frame := universal Bool
             ExistsAt := fun v x => x = .s ∨ (x = .a ∧ v = true) ∨ (x = .b ∧ v = false)
             Causes := fun _ _ _ => False }
  concrete := fun x => x ≠ .s
  grounds := fun _ _ _ => False

/-- Three worlds for the transitivity omission. -/
inductive Stage where
  | zero
  | one
  | two

/-- `zero → one → two` only: not transitive. -/
def chain : Frame Stage :=
  ⟨fun u v => (u = .zero ∧ v = .one) ∨ (u = .one ∧ v = .two)⟩

/-- Transitivity omitted: the one concrete object is present at `zero` and
`one` and absent at `two`. -/
def chainProfile : Profile Stage Unit where
  ontic := { frame := chain, ExistsAt := fun v _ => v ≠ .two, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (transitivity omission model: the test concerns accessibility, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- A two-being signature: `true` is God and has the classical attributes;
`false` is a creature. Historical and creedal fields are unused placeholders. -/
def pairSignature : Signature where
  Being := Bool
  IsGod := fun x => x = true
  HasClassicalAttributes := fun x => x = true
  RevealsRecognizably := fun _ => False
  jesus := true
  ClaimedDivineAuthority := fun _ => False
  RoseFromTheDead := fun _ => False
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => False
  VisibleWithAuthority := fun _ => False
  FoundedAsTeachingAuthority := fun _ _ => False
  DefinitivelyProposesAsRevealed := fun _ _ => False
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

/-- The theist model: God (`true`) exists at both worlds; the creature
(`false`) exists at world `true` only. Universal access (S5). -/
def theistProfile : Profile Bool pairSignature.Being where
  ontic := { frame := universal Bool
             ExistsAt := fun v x => x = true ∨ v = true
             Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (God and one creature are both concrete in this model; the test concerns modal status, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- Models:
1. nonvacuity: all subtraction premises and the conclusion hold together;
2. A1 omitted: A2, A3, transitivity hold, the conclusion fails;
3. A3 omitted, pairwise recombination and Lowe's reply: A1, A2, transitivity,
   unrestricted recombination and companions hold, A3 and the conclusion
   fail; Lowe's two premises hold while no concrete object is necessary;
4. transitivity omitted: A1, A2 and A3 hold throughout, the conclusion fails;
5. the theist model (A2 omitted): on an S5 frame the box K and S5
   necessary-being nodes, the stage-one node, A1, A3 throughout, contingent
   recombination and companions hold; A2 at the actual world, A2 throughout,
   unrestricted recombination and the conclusion fail. -/
def Models : Prop :=
  (PossiblyFinitelyManyConcrete unitProfile true ∧
    EachConcreteCouldFailThroughout unitProfile true ∧
    SubtractableThroughout unitProfile true ∧ OnticFrameTransitive unitProfile ∧
    PossiblyNoConcrete unitProfile true) ∧
  (¬ PossiblyFinitelyManyConcrete tailProfile 0 ∧
    EachConcreteCouldFailThroughout tailProfile 0 ∧
    SubtractableThroughout tailProfile 0 ∧ OnticFrameTransitive tailProfile ∧
    ¬ PossiblyNoConcrete tailProfile 0) ∧
  (PossiblyFinitelyManyConcrete pairProfile true ∧
    EachConcreteCouldFailThroughout pairProfile true ∧
    OnticFrameTransitive pairProfile ∧
    UnrestrictedRecombinationAt pairProfile true ∧ ConcreteCompanionsAt pairProfile true ∧
    ¬ SubtractableThroughout pairProfile true ∧ ¬ PossiblyNoConcrete pairProfile true ∧
    NecessaryAbstractumAt pairProfile true ∧ AbstractaNeedConcretaThroughout pairProfile true ∧
    ¬ NecessaryConcreteAt pairProfile true) ∧
  (PossiblyFinitelyManyConcrete chainProfile .zero ∧
    EachConcreteCouldFailThroughout chainProfile .zero ∧
    SubtractableThroughout chainProfile .zero ∧ ¬ OnticFrameTransitive chainProfile ∧
    ¬ PossiblyNoConcrete chainProfile .zero) ∧
  (OnticFrameS5 theistProfile ∧
    NecessaryRootBoxK pairSignature theistProfile true (fun _ _ => False) ∧
    NecessaryRootBoxS5 pairSignature theistProfile true (fun _ _ => False) ∧
    NecessaryConcreteAt theistProfile true ∧
    PossiblyFinitelyManyConcrete theistProfile true ∧
    SubtractableThroughout theistProfile true ∧
    ContingentRecombinationAt theistProfile true ∧ ConcreteCompanionsAt theistProfile true ∧
    ¬ EachConcreteCouldFailAt theistProfile true ∧
    ¬ EachConcreteCouldFailThroughout theistProfile true ∧
    ¬ UnrestrictedRecombinationAt theistProfile true ∧
    ¬ PossiblyNoConcrete theistProfile true)

/-- The batch controls. -/
def Controls : Prop := Laws ∧ Models

end Model

end TruthCore.Causality.SubtractionArgument
