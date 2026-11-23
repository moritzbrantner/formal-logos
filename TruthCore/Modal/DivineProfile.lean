module

public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Modal.NecessaryIfExistent
public import TruthCore.Modal.PossibilityTransfer
public import TruthCore.Causality.ActualEuclidean
public import TruthCore.Causality.GodNamingSenses
public import TruthCore.Causality.RootPositiveIntellectWill
public import TruthCore.Causality.DeiFiliusAttributeField
public import TruthCore.Logic.ReflectiveCoherence
public import TruthCore.Results.Causality.NamingVeracityBatch1.Solution
public import TruthCore.Causality.ActPriorityAtFirst
public import TruthCore.Causality.ActPriorityThetaEight
public import TruthCore.Modal.NecessaryVariableEffects

/-! # A thirteen-slot profile schema, targeted admissibility and actual naming (#1864)

Analyst formulation; attribution deferred. Complementary to #1865's generic
`MaximalProfile` (`TruthCore.Modal.NecessaryIfExistent`), whose interface it reuses.

**No sense is fixed.** `ProfileSlots` is a *13-slot predicate schema*: thirteen
world-indexed predicate parameters whose labels (simple, perfect, good, one,
infinite, immutable, eternal, intellect, will, omnipotent, omniscient,
morallyPerfect, free) are mnemonic only. Every theorem below quantifies over an
arbitrary schema `p`, and every one of them holds with every slot `True`
(`Control.allTrue`). The slots are NOT the typed StageTwo senses (`IsSimple
Composite`, `IsPerfect InAct`, `IsSupremelyGood …`, `IsTheOneGod σ.IsGod`,
`IsImmutable InPotency`) and NOT `NamingVeracityBatch1.Power`'s `CanDo`.

Why the existing typed vocabulary is not reused directly: the StageTwo senses and
`Power` are world-invariant predicates over `σ.Being`, whereas the modal profile
needs world-indexed slots; and `IsTheOneGod σ.IsGod` and `GodIsOmnipotent` are
defined through `σ.IsGod`, which must stay out of every possible-world premise
(asserting the world-invariant root predicate inside an accessible world would beg
the actuality question). The connection to the typed senses is therefore an
explicit *actual-world* sense bridge, `ProfileToStageTwoSenses`, never a
definitional identification. A corresponding bridge for omnipotence would map
`p.omnipotent w x` to `∀ t, P.Consistent t → P.CanDo x t` for a fixed
`P : NamingVeracityBatch1.Power σ`; it is not built here.

**Interpretation of the carrier (OPEN).** Where `σ : Signature` appears,
`σ.Being` is read as the constant (possibilist) roster of an `Ontic` model with
world-relative existence, and the selected world `w` is read as actuality. Both
identifications go beyond the σ-sense disambiguation fe91cc1f (intended
interpretation of the case vocabulary) and are open interpretive premises.
-/

@[expose] public section

namespace TruthCore.Modal.DivineProfile
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Case.Catholicism
open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)

variable {W B : Type}

/-- A 13-slot predicate schema at each world and bearer; **no sense is fixed**.
The slot names are labels, not meanings: nothing relates `good` to
`morallyPerfect`, `intellect` to `omniscient` or `will` to `free`
(`Control.separations`), and no slot is world-invariant by stipulation. -/
structure ProfileSlots (World Entity : Type) where
  simple : World → Entity → Prop
  perfect : World → Entity → Prop
  good : World → Entity → Prop
  one : World → Entity → Prop
  infinite : World → Entity → Prop
  immutable : World → Entity → Prop
  eternal : World → Entity → Prop
  intellect : World → Entity → Prop
  will : World → Entity → Prop
  omnipotent : World → Entity → Prop
  omniscient : World → Entity → Prop
  morallyPerfect : World → Entity → Prop
  free : World → Entity → Prop

/-- The first nine *opaque* slots at one world and one bearer, packed in the order
of StageTwo's connective `NineClassicalAttributes`. Only the connective is reused:
the slots are not StageTwo's typed senses (see `ProfileToStageTwoSenses`). -/
def NineAt (p : ProfileSlots W B) (w : W) (x : B) : Prop :=
  NineClassicalAttributes
    (p.simple w) (p.perfect w) (p.good w) (p.one w)
    (p.infinite w) (p.immutable w) (p.eternal w)
    (p.intellect w) (p.will w) x

/-- All thirteen slots hold of THE SAME x at THE SAME world. Not a claim that any
reading of the slots describes a possible essence. -/
def ExcellenceAt (p : ProfileSlots W B) (w : W) (x : B) : Prop :=
  NineAt p w x ∧ p.omnipotent w x ∧ p.omniscient w x ∧
    p.morallyPerfect w x ∧ p.free w x

/-- Maximal greatness relative to the ontology's frame M (`m.frame`): x exists and
is excellent at w and at every M-successor of w. Reuses #1865's `MaximalProfile`. -/
def GreatnessAt (m : Ontic W B) (p : ProfileSlots W B) (x : B) (w : W) : Prop :=
  TruthCore.Modal.NecessaryIfExistent.MaximalProfile
    m.frame m.ExistsAt (ExcellenceAt p) x w

/-- M-possible greatness: some M-successor of w hosts a maximally great bearer.
Reading M as genuine metaphysical accessibility remains OPEN. -/
def PossibleGreatness (m : Ontic W B) (p : ProfileSlots W B) (w : W) : Prop :=
  ∃ v, m.frame.access w v ∧ ∃ x, GreatnessAt m p x v

/-- Candidate-description possibility, **outer-E / inner-M**: some E-successor v
of w at which x exists, is excellent, and stays existent and excellent at every
**M**-successor of v (because `GreatnessAt` is defined with `m.frame`). This is
load-bearing for `greatness_at_origin`: the E-premise is therefore not purely
descriptive, since it already asserts M-necessity at the E-world. The inner-E
sibling is `DescribedPossibleGreatnessInnerE`; passing from it to this reading
needs the extra bridge `InnerSuccessorsCovered` (`describedInnerE_to_outerE`). -/
def DescribedPossibleGreatness (E : TruthCore.Modal.Frame W)
    (m : Ontic W B) (p : ProfileSlots W B) (w : W) : Prop :=
  ∃ v, E.access w v ∧ ∃ x, GreatnessAt m p x v

/-- Purely descriptive possibility, **inner-E**: some E-successor v of w at which
x exists, is excellent, and stays so at every **E**-successor of v. -/
def DescribedPossibleGreatnessInnerE (E : TruthCore.Modal.Frame W)
    (m : Ontic W B) (p : ProfileSlots W B) (w : W) : Prop :=
  ∃ v, E.access w v ∧ ∃ x,
    TruthCore.Modal.NecessaryIfExistent.MaximalProfile E m.ExistsAt (ExcellenceAt p) x v

/-- Extra bridge from inner-E to outer-E: every M-successor of each E-successor of
w is also its E-successor (`IncludedAt M E v`). OPEN; not assumed anywhere else. -/
def InnerSuccessorsCovered (E : TruthCore.Modal.Frame W) (m : Ontic W B) (w : W) : Prop :=
  ∀ v, E.access w v → TruthCore.Modal.PossibilityTransfer.IncludedAt m.frame E v

/-- A *profile-specific*, witness-preserving admissibility condition: E-successors
of w bearing the complete greatness profile are M-successors of w. Strictly
weaker than the universal `IncludedAt E M w` (`Control.targetedNotGlobal`); still
a substantive OPEN metaphysical premise. -/
def AdmitGreatnessWorlds (E : TruthCore.Modal.Frame W)
    (m : Ontic W B) (p : ProfileSlots W B) (w : W) : Prop :=
  ∀ v, E.access w v → (∃ x, GreatnessAt m p x v) → m.frame.access w v

/-- Actual-world naming: an existing bearer at w with all thirteen slots satisfies
the root predicate `σ.IsGod`. Applied only after the modal step, never inside a
possible world. OPEN; not derived from the other premises
(`Control.namingOmission`). -/
def ActualDivineNaming (σ : Signature)
    (m : Ontic W σ.Being) (p : ProfileSlots W σ.Being) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → ExcellenceAt p w x → σ.IsGod x

/-- Analyst bridge, **distinct from STMT-CLASSICAL-ATTRIBUTES-SUFFICE**: the nine
opaque slots at the actual world w suffice for the primitive field
`σ.HasClassicalAttributes`. Its own head constant keeps it from binding to the
canonical statement, whose Lean instance uses the typed StageTwo senses. It
follows from the canonical bridge plus the explicit sense bridges
(`profileNineSuffice_of_senseBridges`). OPEN. -/
def ProfileNineSuffice (σ : Signature) (p : ProfileSlots W σ.Being) (w : W) : Prop :=
  ∀ g, NineAt p w g → σ.HasClassicalAttributes g

/-- The sense bridges `ProfileNineSuffice` would need to reach the canonical
StageTwo instance, at the ACTUAL world w only: each slot implies its typed
StageTwo sense. The `one` slot is meant to be GOD-free, so that its bridge to
`IsTheOneGod σ.IsGod` is the only place `σ.IsGod` enters, and only at w. This
is an instantiation rule, not something the type enforces: `p` is arbitrary, and
a slot built from `σ.IsGod` would put GOD_4 into the possibility premise and
trivialize `ActualDivineNaming`. Any registration must check that no slot
mentions `σ.IsGod`. Every conjunct is OPEN. -/
def ProfileToStageTwoSenses (σ : Signature) {Respect : Type}
    (p : ProfileSlots W σ.Being) (w : W)
    (Composite : σ.Being → Prop) (InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (Infinite Eternal HasIntellect HasWill : σ.Being → Prop) : Prop :=
  ∀ g,
    (p.simple w g → IsSimple Composite g) ∧
    (p.perfect w g → IsPerfect InAct g) ∧
    (p.good w g → IsSupremelyGood InAct GoodIn CausesIn esse g) ∧
    (p.one w g → IsTheOneGod σ.IsGod g) ∧
    (p.infinite w g → Infinite g) ∧
    (p.immutable w g → IsImmutable InPotency g) ∧
    (p.eternal w g → Eternal g) ∧
    (p.intellect w g → HasIntellect g) ∧
    (p.will w g → HasWill g)

/-- Necessary existence plus necessary excellence of every actual excellent
bearer over M-successors of w. This is NOT essentiality (no claim about what x
is, only about where it exists and which slots it satisfies). Freedom, read as
a slot here, would have to be a necessarily held capacity, not a fixed contingent
choice. OPEN; not derived. -/
def NecessaryExcellenceAt (m : Ontic W B)
    (p : ProfileSlots W B) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → ExcellenceAt p w x →
    ∀ v, m.frame.access w v → m.ExistsAt v x ∧ ExcellenceAt p v x

/-! ## Conditional theorems -/

/-- Inner-E to outer-E, with the extra bridge made explicit. -/
theorem describedInnerE_to_outerE (E : TruthCore.Modal.Frame W) (m : Ontic W B)
    (p : ProfileSlots W B) (w : W)
    (hInner : DescribedPossibleGreatnessInnerE E m p w)
    (hCover : InnerSuccessorsCovered E m w) :
    DescribedPossibleGreatness E m p w := by
  obtain ⟨v, hEv, x, hEx, hExc, hAll⟩ := hInner
  exact ⟨v, hEv, x, hEx, hExc, fun u hMu => hAll u (hCover v hEv u hMu)⟩

/-- **Near-transcription.** A definitional unpacking: the conclusion is one
application of `hAdmit` to the given witness. It is the singleton-predicate case
of #438's `PossibilityTransfer.TransferLaws`, restricted to the greatness
profile; it delivers no transfer principle beyond its premise. -/
theorem described_greatness_transfer (m : Ontic W B)
    (p : ProfileSlots W B) (E : TruthCore.Modal.Frame W) (w : W)
    (hDescription : DescribedPossibleGreatness E m p w)
    (hAdmit : AdmitGreatnessWorlds E m p w) :
    PossibleGreatness m p w := by
  obtain ⟨v, hEv, x, hProfile⟩ := hDescription
  exact ⟨v, hAdmit v hEv ⟨x, hProfile⟩, x, hProfile⟩

/-- Witness-relative return: if the profile world v sees w and every M-successor
of w, the same bearer is maximally great at w. No reflexivity at w is needed. -/
theorem greatness_at_origin_of_witness (m : Ontic W B) (p : ProfileSlots W B)
    (w v : W) (x : B)
    (hBack : m.frame.access v w)
    (hForward : ∀ u, m.frame.access w u → m.frame.access v u)
    (hGreat : GreatnessAt m p x v) :
    GreatnessAt m p x w := by
  obtain ⟨_, _, hAll⟩ := hGreat
  have hHere : m.ExistsAt w x ∧ ExcellenceAt p w x := hAll w hBack
  exact ⟨hHere.1, hHere.2, fun u hWu => hAll u (hForward u hWu)⟩

/-- Euclidean access AT w (`EuclideanAt`) and reflexivity AT w (`ActualReflexive`)
return the very same bearer, with its full profile, to w and its successors.
Same algorithm as `ActualEuclidean.necessaryAtOrigin` (prior art); the new content
is the excellence conjunct carried along. No actualist quantifier shift is used.
Reflexivity is sufficient here, not shown necessary: see
`greatness_at_origin_of_witness` and `Control.nonreflexiveReturn`. -/
theorem greatness_at_origin (m : Ontic W B) (p : ProfileSlots W B) (w : W)
    (hEuclidean : EuclideanAt m.frame w)
    (hRef : ActualReflexive m w)
    (hPossible : PossibleGreatness m p w) :
    ∃ x, GreatnessAt m p x w := by
  obtain ⟨v, hWv, x, hGreat⟩ := hPossible
  exact ⟨x, greatness_at_origin_of_witness m p w v x (hEuclidean v w hWv hRef)
    (fun u hWu => hEuclidean v u hWv hWu) hGreat⟩

/-- The analyst bridge `ProfileNineSuffice` follows from the canonical StageTwo
instance of `ClassicalAttributesSuffice` together with the explicit actual-world
sense bridges. This makes visible what binding to the canonical statement would
require; neither input is established. -/
theorem profileNineSuffice_of_senseBridges (σ : Signature) {Respect : Type}
    (p : ProfileSlots W σ.Being) (w : W)
    (Composite : σ.Being → Prop) (InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hSenses : ProfileToStageTwoSenses σ p w Composite InPotency InAct GoodIn CausesIn esse
      Infinite Eternal HasIntellect HasWill)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill) :
    ProfileNineSuffice σ p w := by
  intro g ⟨hs, hp, hg, ho, hi, hm, he, hx, hw⟩
  obtain ⟨bs, bp, bg, bo, bi, bm, be, bx, bw⟩ := hSenses g
  exact hSuffice g (bs hs) (bp hp) (bg hg) (bo ho) (bi hi) (bm hm) (be he) (bx hx) (bw hw)

/-- Conditional GOD_4 consumer. The naming bridge is applied only after the modal
return to the actual world; every slot applies to ONE bearer; `σ.IsGod` occurs in
no possible-world premise of this statement, provided the slots of `p` are
instantiated without `σ.IsGod` (an instantiation rule the type does not enforce;
a registration must check it). -/
theorem actual_named_classical_god (σ : Signature)
    (m : Ontic W σ.Being) (p : ProfileSlots W σ.Being)
    (E : TruthCore.Modal.Frame W) (w : W)
    (hEuclidean : EuclideanAt m.frame w)
    (hRef : ActualReflexive m w)
    (hDescription : DescribedPossibleGreatness E m p w)
    (hAdmit : AdmitGreatnessWorlds E m p w)
    (hName : ActualDivineNaming σ m p w)
    (hNine : ProfileNineSuffice σ p w) :
    ∃ g, m.ExistsAt w g ∧ σ.IsGod g ∧ σ.HasClassicalAttributes g ∧
      GreatnessAt m p g w := by
  obtain ⟨g, hg⟩ := greatness_at_origin m p w hEuclidean hRef
    (described_greatness_transfer m p E w hDescription hAdmit)
  exact ⟨g, hg.1, hName g hg.1 hg.2.1, hNine g hg.2.1.1, hg⟩

/-- The existential projection of `actual_named_classical_god`. -/
theorem actual_god_exists (σ : Signature)
    (m : Ontic W σ.Being) (p : ProfileSlots W σ.Being)
    (E : TruthCore.Modal.Frame W) (w : W)
    (hEuclidean : EuclideanAt m.frame w)
    (hRef : ActualReflexive m w)
    (hDescription : DescribedPossibleGreatness E m p w)
    (hAdmit : AdmitGreatnessWorlds E m p w)
    (hName : ActualDivineNaming σ m p w)
    (hNine : ProfileNineSuffice σ p w) :
    GodExists σ.IsGod := by
  obtain ⟨g, _, hGod, _, _⟩ :=
    actual_named_classical_god σ m p E w hEuclidean hRef hDescription hAdmit hName hNine
  exact ⟨g, hGod⟩

/-- An actual excellent bearer plus `NecessaryExcellenceAt` already gives the
ACTUAL maximal profile, with no frame condition at all (neither Euclidean nor
reflexive). So the possibility route adds no independent support once these two
premises are granted. -/
theorem actual_necessary_bundle_greatness (m : Ontic W B)
    (p : ProfileSlots W B) (w : W)
    (hActual : ∃ x, m.ExistsAt w x ∧ ExcellenceAt p w x)
    (hNecessary : NecessaryExcellenceAt m p w) :
    ∃ x, GreatnessAt m p x w := by
  obtain ⟨x, hExists, hExcellent⟩ := hActual
  exact ⟨x, hExists, hExcellent, hNecessary x hExists hExcellent⟩

/-- With reflexivity at w the actual profile is also M-possible. This is
M-possibility only; reading M as metaphysical accessibility is OPEN. -/
theorem actual_necessary_bundle_possible (m : Ontic W B)
    (p : ProfileSlots W B) (w : W)
    (hRef : ActualReflexive m w)
    (hActual : ∃ x, m.ExistsAt w x ∧ ExcellenceAt p w x)
    (hNecessary : NecessaryExcellenceAt m p w) :
    PossibleGreatness m p w := by
  obtain ⟨x, hx⟩ := actual_necessary_bundle_greatness m p w hActual hNecessary
  exact ⟨w, hRef, x, hx⟩

/-! ## Interpreted profile and attribute intersections

Selected analyst reading of the EXISTING thirteen-slot schema, without any
occurrence of σ.IsGod inside its predicates. The original modal theorems are
unchanged. The typed source, StageTwo and task-power vocabularies are reused.
Content-knowledge and action-selection are world-indexed new primitives with
explicit intended meanings below. The moral and free-exercise senses are
deliberately WEAKER than unrestricted perfect goodness and libertarian freedom.
Nine slots of `fixedProfile` (simple, perfect, good, infinite, immutable,
eternal, intellect, will, omnipotent) ignore the world argument, and their
dictionaries are world-free, so they are rigid BY CONSTRUCTION of this
interpretation (`fixedProfile_rigid`): they hold at every world once they hold
at one, even at worlds where the bearer does not exist. This is an encoded
interpretive commitment, not a derived essentiality, and it adds no evidence
for M-necessary excellence; any later use of `fixedProfile` in `GreatnessAt` or
`NecessaryExcellenceAt` inherits the stipulated rigidity. The genuinely open
cross-world gap for this profile is the four world-varying slots one,
omniscient, morallyPerfect and free.
-/
namespace Interpreted
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPositiveIntellectWill (NecessaryPositiveRootIntellectWillAt)
open TruthCore.Causality.DeiFiliusAttributeField (IsAlmighty)
open TruthCore.Causality.ActPriorityAtFirst (ActAndPotencyMakeComposite)
open TruthCore.Causality.ActPriorityThetaEight (ActInBeingAndPotencyMakeComposite)
open TruthCore.Latin.Aquinas.SummaTheologiae (ImmutableIsEternalReading)
open TruthCore.Causality.NamingVeracityBatch1 (Power)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Logic.ReflectiveCoherence (Semantics)

/-- `Knows` holds of exactly the contents true at `v`: of each true individuated
content in the selected `C`, and of no false one. `Knows` is a primitive
world-indexed relation, INTENDED as cognitive uptake rather than mere assent,
but the type does not enforce that: nothing separates it from a truth oracle
(`CreationControl.knows` satisfies this definition with one). Its DEF record,
the reality of uptake and coverage beyond `C` are OPEN. -/
def KnowsAllContentsAt {C : Type} (S : Semantics W C)
    (Knows : W → B → C → Prop) (v : W) (x : B) : Prop :=
  ∀ c, Knows v x c ↔ S.trueAt v c

/-- Moral impeccability of selection only: forbidden acts are never chosen.
Permitted is a primitive normative evaluation; no relation to ontological
goodness or best-possible creation is implied. -/
def PermissibleChoicesAt {A : Type} (Chooses : W → B → A → Prop)
    (Permitted : W → A → Prop) (v : W) (x : B) : Prop :=
  ∀ a, Chooses v x a → Permitted v a

/-- Weak free exercise: some actual selection is within capacity and is not
externally imposed. Does NOT imply a different available choice with the same
complete inputs or that contingent effects follow from that selection. -/
def NoncoercedChoiceAt {A : Type} (Chooses Capable Imposed : W → B → A → Prop)
    (v : W) (x : B) : Prop :=
  ∃ a, Chooses v x a ∧ Capable v x a ∧ ¬ Imposed v x a

/-- Fixed, GOD-free instance of all thirteen slots. The one slot means unique
root of this selected actual-concrete grounding relation at each world; it is
NOT IsTheOneGod. Omnipotence uses the existing IsAlmighty, coherent-task
capacity rather than compulsory task performance. New primitives for knowledge
and action have distinct meanings from the preexisting StageTwo fields.
A closed logical model of this constructor is not a real metaphysical world. -/
def fixedProfile {P R C A : Type} (σ : Signature)
    (m : Profile W σ.Being)
    (q : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile σ.Being P R)
    (Composite Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (GoodIn InPotency : σ.Being → R → Prop)
    (power : Power σ) (S : Semantics W C)
    (Knows : W → σ.Being → C → Prop)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (Capable Imposed : W → σ.Being → A → Prop) :
    ProfileSlots W σ.Being where
  simple := fun _ x => IsSimple Composite x
  perfect := fun _ x => IsPerfect q.InAct x
  good := fun _ x => IsSupremelyGood q.InAct GoodIn q.CausesIn q.esse x
  one := fun v x => ActualRoot m v x ∧ ∀ y, ActualRoot m v y → y = x
  infinite := fun _ x => Infinite x
  immutable := fun _ x => IsImmutable InPotency x
  eternal := fun _ x => Eternal x
  intellect := fun _ x => HasIntellect x
  will := fun _ x => HasWill x
  omnipotent := fun _ x => IsAlmighty σ power x
  omniscient := KnowsAllContentsAt S Knows
  morallyPerfect := PermissibleChoicesAt Chooses Permitted
  free := NoncoercedChoiceAt Chooses Capable Imposed

/-- Rigidity BY CONSTRUCTION, not derived essentiality: the nine world-free
slots of `fixedProfile` (simple, perfect, good, infinite, immutable, eternal,
intellect, will, omnipotent) hold at every world `v` once they hold at one
world `w`, for every bearer, whether or not it exists at `v`. The proof is
definitional unfolding; it records an interpretive commitment of the encoding
and adds no evidence for M-necessary excellence. Only one, omniscient,
morallyPerfect and free can vary by world. -/
theorem fixedProfile_rigid {P R C A : Type} (σ : Signature)
    (m : Profile W σ.Being)
    (q : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile σ.Being P R)
    (Composite Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (GoodIn InPotency : σ.Being → R → Prop)
    (power : Power σ) (S : Semantics W C)
    (Knows : W → σ.Being → C → Prop)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (Capable Imposed : W → σ.Being → A → Prop) (w v : W) (x : σ.Being) :
    let p := fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
      GoodIn InPotency power S Knows Chooses Permitted Capable Imposed
    (p.simple w x → p.simple v x) ∧ (p.perfect w x → p.perfect v x) ∧
      (p.good w x → p.good v x) ∧ (p.infinite w x → p.infinite v x) ∧
      (p.immutable w x → p.immutable v x) ∧ (p.eternal w x → p.eternal v x) ∧
      (p.intellect w x → p.intellect v x) ∧ (p.will w x → p.will v x) ∧
      (p.omnipotent w x → p.omnipotent v x) :=
  ⟨fun h => h, fun h => h, fun h => h, fun h => h, fun h => h, fun h => h,
    fun h => h, fun h => h, fun h => h⟩

/-- A connective for six selected attributes of ONE necessary actual bearer.
The other seven are not inferred. -/
def PositiveCoreAt (m : Ontic W B) (p : ProfileSlots W B) (v : W) (x : B) : Prop :=
  m.ExistsAt v x ∧ NecessaryAt m v x ∧
    p.simple v x ∧ p.perfect v x ∧ p.good v x ∧ p.one v x ∧
    p.intellect v x ∧ p.will v x

/-- Same-bearer support from the existing RootPositiveIntellectWill result:
six fixed attribute slots and necessity of this selected actual root.
All the source argument's open premises are retained. -/
theorem positiveCore_from_same_root {P R C A : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (q : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile σ.Being P R)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (GoodIn InPotency : σ.Being → R → Prop)
    (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (power : Power σ) (S : Semantics W C)
    (Knows : W → σ.Being → C → Prop)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (Capable Imposed : W → σ.Being → A → Prop)
    (hRoot : NecessaryPositiveRootIntellectWillAt m w q GoodIn MoreIn
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill) :
    ∃ n, PositiveCoreAt m.ontic
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed) w n := by
  obtain ⟨n, hPerfectRoot, hGood, _, hSimple, _, _, _, hInt, hWill⟩ := hRoot
  obtain ⟨hActualRoot, hNec, hOnly, _, hPerfect⟩ := hPerfectRoot
  refine ⟨n, ?_⟩
  change m.ontic.ExistsAt w n ∧ NecessaryAt m.ontic w n ∧
    IsSimple Composite n ∧ IsPerfect q.InAct n ∧
    IsSupremelyGood q.InAct GoodIn q.CausesIn q.esse n ∧
    (ActualRoot m w n ∧ ∀ y, ActualRoot m w y → y = n) ∧
    HasIntellect n ∧ HasWill n
  exact ⟨hActualRoot.1.2, hNec, hSimple, hPerfect, hGood,
    ⟨hActualRoot, hOnly⟩, hInt, hWill⟩

/-- Positive same-bearer extension through two ALREADY EXISTING arguments:
q.7 esse=essence -> infinite and q.25 unlimited act + power follows act ->
capacity for all contradiction-free tasks. The three power bridges and the
subsistent-being infinity reading are explicit inputs. Neither new piece
mentions GOD_4 or asserts actual exercise, self-knowledge, or full moral
freedom. This extends six to EIGHT interpreted attribute slots, on one n. -/
theorem positiveCore_with_infinite_power_from_same_root {P R C A : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (q : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile σ.Being P R)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (GoodIn InPotency : σ.Being → R → Prop)
    (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (power : Power σ) (S : Semantics W C)
    (Knows : W → σ.Being → C → Prop)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (Capable Imposed : W → σ.Being → A → Prop)
    (hRoot : NecessaryPositiveRootIntellectWillAt m w q GoodIn MoreIn
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hInfinity : TruthCore.Latin.Aquinas.SummaTheologiae.SubsistentBeingIsInfiniteReading
      q.essenceOf q.esseOf Infinite)
    (hUnlimited : TruthCore.Causality.NamingVeracityBatch1.InfiniteIsUnlimitedAct
      σ Infinite power)
    (hActive : TruthCore.Causality.NamingVeracityBatch1.ActivePowerFollowsAct σ power)
    (hPossible : TruthCore.Causality.NamingVeracityBatch1.ConsistentTaskRequiresOnlyPossiblePerfections
      σ power) :
    ∃ n, PositiveCoreAt m.ontic
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed) w n ∧
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed).infinite w n ∧
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed).omnipotent w n := by
  obtain ⟨n, hPerfectRoot, hGood, hEsse, hSimple, _, _, _, hInt, hWill⟩ := hRoot
  obtain ⟨hActualRoot, hNec, hOnly, _, hPerfect⟩ := hPerfectRoot
  have hInfinite : Infinite n := hInfinity n hEsse
  have hInfinitePower :=
    TruthCore.Results.Causality.NamingVeracityBatch1.infinitePowerFromAct
      σ Infinite power hUnlimited hActive hPossible
  have hOmnipotent : IsAlmighty σ power n := hInfinitePower n hInfinite
  refine ⟨n, ?_, hInfinite, hOmnipotent⟩
  change m.ontic.ExistsAt w n ∧ NecessaryAt m.ontic w n ∧
    IsSimple Composite n ∧ IsPerfect q.InAct n ∧
    IsSupremelyGood q.InAct GoodIn q.CausesIn q.esse n ∧
    (ActualRoot m w n ∧ ∀ y, ActualRoot m w y → y = n) ∧
    HasIntellect n ∧ HasWill n
  exact ⟨hActualRoot.1.2, hNec, hSimple, hPerfect, hGood,
    ⟨hActualRoot, hOnly⟩, hInt, hWill⟩

/-- A simple source in act in the esse respect has no passive potency WHEN
being in act in being and in potency in some respect counts as a composition.
This is the registered weaker premise
ActPriorityThetaEight.ActInBeingAndPotencyMakeComposite (statement d8024a38,
the esse instance of ActPriorityAtFirst.ActAndPotencyMakeComposite, strength
relation 4b6d0b59); it is not proved by the word simple. The eternity step
reuses q.10's explicit reading. Neither premise mentions GOD_4 or contingent
decisions: possible-world differences in effects need not be intrinsic
potencies of the source. -/
theorem immutable_eternal_of_simple_act {R : Type}
    (InAct InPotency : B → R → Prop) (Composite : B → Prop)
    (Eternal : B → Prop) (x : B) (esse : R)
    (hEsse : InAct x esse)
    (hSimple : IsSimple Composite x)
    (hMixedComposite : ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal) :
    IsImmutable InPotency x ∧ Eternal x := by
  have hNoPot : IsImmutable InPotency x := by
    intro r hPot
    exact hSimple (hMixedComposite x r hEsse hPot)
  exact ⟨hNoPot, hEternity x hNoPot⟩

/-- Same-bearer positive extension: the earlier eight slots plus immutability
and eternity, from actual esse and simplicity of THAT root. Two added open
philosophical premises are named individually: being in act in esse and in
potency in some respect is composition (the registered weaker d8024a38, not
the unrestricted 3d99779b), and unchangeable pure act is eternal. Prior art:
registered argument 379399d1 (NecessaryClassicalGodRootByComposition) already
derives the root's pure actuality and eternity on this positive-root route from
simplicity, d8024a38 and the q.10 reading; this theorem adds the GOD-free
packaging and omnipotence. The older eight-slot route does not need these
premises and remains available on its own. This proves NO
omniscient cognition, moral perfection, free creative exercise or metaphysical
possibility of the thirteen-slot essence. -/
theorem positiveCore_with_ten_from_same_root {P R C A : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (q : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile σ.Being P R)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (GoodIn InPotency : σ.Being → R → Prop)
    (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (power : Power σ) (S : Semantics W C)
    (Knows : W → σ.Being → C → Prop)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (Capable Imposed : W → σ.Being → A → Prop)
    (hRoot : NecessaryPositiveRootIntellectWillAt m w q GoodIn MoreIn
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hInfinity : TruthCore.Latin.Aquinas.SummaTheologiae.SubsistentBeingIsInfiniteReading
      q.essenceOf q.esseOf Infinite)
    (hUnlimited : TruthCore.Causality.NamingVeracityBatch1.InfiniteIsUnlimitedAct
      σ Infinite power)
    (hActive : TruthCore.Causality.NamingVeracityBatch1.ActivePowerFollowsAct σ power)
    (hPossible : TruthCore.Causality.NamingVeracityBatch1.ConsistentTaskRequiresOnlyPossiblePerfections
      σ power)
    (hMixedComposite : ActInBeingAndPotencyMakeComposite q.InAct InPotency q.esse Composite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal) :
    ∃ n, PositiveCoreAt m.ontic
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed) w n ∧
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed).infinite w n ∧
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed).omnipotent w n ∧
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed).immutable w n ∧
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed).eternal w n := by
  obtain ⟨g, hCore, hInfinite, hOmnipotent⟩ :=
    positiveCore_with_infinite_power_from_same_root σ m w q
      Composite MatterForm Infinite Eternal HasIntellect HasWill
      GoodIn InPotency MoreIn PriorSimply ComponentOf
      power S Knows Chooses Permitted Capable Imposed
      hRoot hInfinity hUnlimited hActive hPossible
  obtain ⟨n, hPerfectRoot, _, _, hSimple, _, _, _, _, _⟩ := hRoot
  have hOne :
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed).one w g :=
    hCore.2.2.2.2.2.1
  change ActualRoot m w g ∧ (∀ y, ActualRoot m w y → y = g) at hOne
  have hEq : g = n := hPerfectRoot.2.2.1 g hOne.1
  have hEsse : q.InAct n q.esse := hPerfectRoot.2.2.2.1.1
  have hImmutableEternal := immutable_eternal_of_simple_act
    q.InAct InPotency Composite Eternal n q.esse hEsse hSimple
    hMixedComposite hEternity
  rw [hEq] at hCore hInfinite hOmnipotent
  exact ⟨n, hCore, hInfinite, hOmnipotent, hImmutableEternal.1, hImmutableEternal.2⟩

/-- Eight StageTwo sense bridges are definitional on this fixed profile.
The ninth, from uniqueness of the selected root to uniqueness of GOD_4,
is a separate OPEN actual-world naming assumption. -/
theorem fixed_to_stageTwo_senses {P R C A : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (q : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile σ.Being P R)
    (Composite Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (GoodIn InPotency : σ.Being → R → Prop)
    (power : Power σ) (S : Semantics W C)
    (Knows : W → σ.Being → C → Prop)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (Capable Imposed : W → σ.Being → A → Prop)
    (hRootNamesOne : ∀ x, ActualRoot m w x →
      (∀ y, ActualRoot m w y → y = x) → IsTheOneGod σ.IsGod x) :
    ProfileToStageTwoSenses σ
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed)
      w Composite InPotency q.InAct GoodIn q.CausesIn q.esse
      Infinite Eternal HasIntellect HasWill := by
  intro x
  change
    (IsSimple Composite x → IsSimple Composite x) ∧
    (IsPerfect q.InAct x → IsPerfect q.InAct x) ∧
    (IsSupremelyGood q.InAct GoodIn q.CausesIn q.esse x →
      IsSupremelyGood q.InAct GoodIn q.CausesIn q.esse x) ∧
    ((ActualRoot m w x ∧ ∀ y, ActualRoot m w y → y = x) →
      IsTheOneGod σ.IsGod x) ∧
    (Infinite x → Infinite x) ∧
    (IsImmutable InPotency x → IsImmutable InPotency x) ∧
    (Eternal x → Eternal x) ∧
    (HasIntellect x → HasIntellect x) ∧
    (HasWill x → HasWill x)
  exact ⟨(fun h => h), (fun h => h), (fun h => h),
    (fun h => hRootNamesOne x h.1 h.2),
    (fun h => h), (fun h => h), (fun h => h),
    (fun h => h), (fun h => h)⟩

/-- A chain of three biconditionals that makes explicit that strict invariance
of known contents is incompatible with complete factive knowledge of a content
whose truth varies: complete and factive knowledge at both worlds plus an
invariant known-content set give invariant truth of every covered content.
Simplicity alone does NOT imply this strong content-invariance premise. -/
theorem invariant_knowledge_forces_truth_agreement {C : Type}
    (S : Semantics W C) (Knows : W → B → C → Prop)
    (w v : W) (x : B)
    (hw : KnowsAllContentsAt S Knows w x)
    (hv : KnowsAllContentsAt S Knows v x)
    (hInvariant : ∀ c, Knows w x c ↔ Knows v x c) :
    ∀ c, S.trueAt w c ↔ S.trueAt v c := by
  intro c
  exact (hw c).symm.trans ((hInvariant c).trans (hv c))

/-- A genuinely changing truth-content rules out that strong content-invariance
bridge if the same bearer is omniscient about it in both worlds. A simple,
unchanging intellectual act can instead have extrinsically varying relations
to contingent truths; this theorem does not exclude that interpretation. -/
theorem varying_truth_excludes_invariant_knowledge {C : Type}
    (S : Semantics W C) (Knows : W → B → C → Prop)
    (w v : W) (x : B) (c : C)
    (hw : KnowsAllContentsAt S Knows w x)
    (hv : KnowsAllContentsAt S Knows v x)
    (hHere : S.trueAt w c) (hThere : ¬ S.trueAt v c) :
    ¬ (∀ d, Knows w x d ↔ Knows v x d) := by
  intro hInvariant
  exact hThere ((invariant_knowledge_forces_truth_agreement S Knows w v x
    hw hv hInvariant c).mp hHere)

/-- Power to do a coherent task and actual impeccable selection differ.
Whether a morally forbidden act corresponds to a coherent Power.Task is
EXPLICITLY stipulated by hCons; perfection may dispute that classification. -/
theorem can_do_without_choosing_forbidden {A : Type} (σ : Signature)
    (power : Power σ)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (taskOf : A → power.Task) (w : W) (x : σ.Being) (a : A)
    (hOmni : IsAlmighty σ power x)
    (hMoral : PermissibleChoicesAt Chooses Permitted w x)
    (hCons : power.Consistent (taskOf a)) (hForbidden : ¬ Permitted w a) :
    power.CanDo x (taskOf a) ∧ ¬ Chooses w x a := by
  refine ⟨hOmni (taskOf a) hCons, ?_⟩
  intro hSelected
  exact hForbidden (hMoral a hSelected)
/-- A stronger, disputed reading of moral impeccability: the source is
INCAPABLE of any morally forbidden action, even when the corresponding task
is not logically contradictory. This is distinct from PermissibleChoicesAt,
which forbids actual selection only. The taskOf map is a substantive bridge
between moral actions and Power.Task; it is not assumed surjective. -/
def IncapableOfForbiddenTasks {A : Type} (σ : Signature)
    (power : Power σ) (Permitted : W → A → Prop)
    (taskOf : A → power.Task) (w : W) (x : σ.Being) : Prop :=
  ∀ a, ¬ Permitted w a → ¬ power.CanDo x (taskOf a)

/-- With all coherent tasks in the scope of omnipotence, *incapacity* for
morally forbidden actions forces every such mapped task to count as
logically inconsistent. This is the exact price of that stronger goodness
reading, not a proof that evil really is metaphysically contradictory.
The same conclusion does NOT follow from forbidding actual choice.
`Permitted` varies by world but `taskOf`, `Consistent` and `CanDo` do not, so
this theorem turns a world-relative prohibition into a world-free
inconsistency; the "exact price" is relative to that indexing. -/
theorem moral_incapacity_forces_task_inconsistency {A : Type} (σ : Signature)
    (power : Power σ) (Permitted : W → A → Prop)
    (taskOf : A → power.Task) (w : W) (x : σ.Being)
    (hOmni : IsAlmighty σ power x)
    (hIncapable : IncapableOfForbiddenTasks σ power Permitted taskOf w x) :
    ∀ a, ¬ Permitted w a → ¬ power.Consistent (taskOf a) := by
  intro a hForbidden hConsistent
  exact hIncapable a hForbidden (hOmni (taskOf a) hConsistent)

/-- Exact incompatible bundle: coherent forbidden task, omnipotent ability and
goodness-as-inability. The selected, weaker goodness-of-choice interpretation
remains compatible because it does not imply incapacity. The theorem needs the
forbidden action to correspond to some task via `taskOf`; the classical reply
that sin is a defect, not an exercise of power, rejects that mapping. -/
theorem coherent_forbidden_task_rules_out_moral_incapacity {A : Type} (σ : Signature)
    (power : Power σ) (Permitted : W → A → Prop)
    (taskOf : A → power.Task) (w : W) (x : σ.Being) (a : A)
    (hConsistent : power.Consistent (taskOf a))
    (hForbidden : ¬ Permitted w a) :
    ¬ (IsAlmighty σ power x ∧
      IncapableOfForbiddenTasks σ power Permitted taskOf w x) := by
  intro hJoint
  exact (moral_incapacity_forces_task_inconsistency σ power Permitted
    taskOf w x hJoint.1 hJoint.2 a hForbidden) hConsistent

/-! ## C5 from an actual same-source bearer: the four nonrigid slots

This refines the already verified ten-attribute route rather than inserting an
E-to-M admissibility assumption. A fixedProfile instance makes nine attributes
world-invariant by definition, not by argument. The remaining positive
conditions are three actual-world attributes and persistence at M-successors
of four world-sensitive slots (selected-root uniqueness, complete cognition,
moral selection and free selection). These conditions are NOT derived from
pure actuality or from absence of contradictions. M-as-metaphysical, essential
interpretation, and the intentional/moral/agency content remain OPEN.
-/

/-- A full candidate profile from ten SAME-source actual attributes and the
explicit four-slot completion. The equality to fixedProfile is important:
without it the nine rigid fields cannot be transported. The actual-world
knowledge, impeccable selection and free exercise are separately required;
the four world-sensitive predicates must hold at every M-successor. This
is a conditional assembly, not an independent warrant for those predicates.
`hComplete` asks `free` (a noncoerced choice actually made) at EVERY
M-successor: the "necessarily exercised" reading of freedom, not merely an
essentially available capacity. The conclusion names the bearer: the same `n`
with `PositiveCoreAt` (hence the selected unique root at `w`) is maximally
great at `w`. -/
theorem candidate_greatness_from_ten_and_four {P R C A : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (q : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile σ.Being P R)
    (Composite Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (GoodIn InPotency : σ.Being → R → Prop)
    (power : Power σ) (S : Semantics W C)
    (Knows : W → σ.Being → C → Prop)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (Capable Imposed : W → σ.Being → A → Prop)
    (p : ProfileSlots W σ.Being)
    (hFixed : p = fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
      GoodIn InPotency power S Knows Chooses Permitted Capable Imposed)
    (hTen : ∃ n, PositiveCoreAt m.ontic p w n ∧ p.infinite w n ∧
      p.omnipotent w n ∧ p.immutable w n ∧ p.eternal w n)
    (hComplete : ∀ n, PositiveCoreAt m.ontic p w n →
      p.omniscient w n ∧ p.morallyPerfect w n ∧ p.free w n ∧
        (∀ v, m.ontic.frame.access w v →
          p.one v n ∧ p.omniscient v n ∧ p.morallyPerfect v n ∧ p.free v n)) :
    ∃ n, PositiveCoreAt m.ontic p w n ∧ GreatnessAt m.ontic p n w := by
  subst p
  let p := fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
    GoodIn InPotency power S Knows Chooses Permitted Capable Imposed
  obtain ⟨n, hCore, hInf, hOmni, hImm, hEter⟩ := hTen
  obtain ⟨hKnow, hMoral, hFree, hAcross⟩ := hComplete n hCore
  refine ⟨n, hCore, ?_⟩
  obtain ⟨hExists, hNecessary, hSimple, hPerfect, hGood, hOne, hInt, hWill⟩ := hCore
  have hNine : NineAt p w n :=
    ⟨hSimple, hPerfect, hGood, hOne, hInf, hImm, hEter, hInt, hWill⟩
  refine ⟨hExists, ⟨hNine, hOmni, hKnow, hMoral, hFree⟩, ?_⟩
  intro v hV
  obtain ⟨hS, hP, hG, hI, hM, hE, hX, hW, hPow⟩ :=
    fixedProfile_rigid σ m q Composite Infinite Eternal HasIntellect HasWill
      GoodIn InPotency power S Knows Chooses Permitted Capable Imposed w v n
  obtain ⟨hOneV, hKnowV, hMoralV, hFreeV⟩ := hAcross v hV
  have hNineV : NineAt p v n :=
    ⟨hS hSimple, hP hPerfect, hG hGood, hOneV,
      hI hInf, hM hImm, hE hEter, hX hInt, hW hWill⟩
  exact ⟨hNecessary v hV, ⟨hNineV, hPow hOmni, hKnowV, hMoralV, hFreeV⟩⟩

/-- Explicit composition with the EXISTING same-root ten-slot theorem. Unlike
a pure E-to-M transfer, the starting bearer is actual and necessary already;
the remaining three attributes and cross-world four-slot completion remain
open inputs. Actual reflexivity then gives M-possible greatness, but does not
establish that the chosen M frame captures genuine metaphysical possibility.
The second conjunct pins the bearer: the actual selected root `n` itself (it
has `PositiveCoreAt`, which includes the `one` slot at `w`) is maximally great
at `w`; `PossibleGreatness` alone would quantify the bearer away.
The output is NOT a GOD_4 name. -/
theorem candidate_possible_from_same_root {P R C A : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (q : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile σ.Being P R)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (GoodIn InPotency : σ.Being → R → Prop)
    (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (power : Power σ) (S : Semantics W C)
    (Knows : W → σ.Being → C → Prop)
    (Chooses : W → σ.Being → A → Prop) (Permitted : W → A → Prop)
    (Capable Imposed : W → σ.Being → A → Prop)
    (hRoot : NecessaryPositiveRootIntellectWillAt m w q GoodIn MoreIn
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hInfinity : TruthCore.Latin.Aquinas.SummaTheologiae.SubsistentBeingIsInfiniteReading
      q.essenceOf q.esseOf Infinite)
    (hUnlimited : TruthCore.Causality.NamingVeracityBatch1.InfiniteIsUnlimitedAct
      σ Infinite power)
    (hActive : TruthCore.Causality.NamingVeracityBatch1.ActivePowerFollowsAct σ power)
    (hPossible : TruthCore.Causality.NamingVeracityBatch1.ConsistentTaskRequiresOnlyPossiblePerfections
      σ power)
    (hMixedComposite : ActInBeingAndPotencyMakeComposite q.InAct InPotency q.esse Composite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hComplete : ∀ n, PositiveCoreAt m.ontic
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed) w n →
      let p := fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed
      p.omniscient w n ∧ p.morallyPerfect w n ∧ p.free w n ∧
        (∀ v, m.ontic.frame.access w v →
          p.one v n ∧ p.omniscient v n ∧ p.morallyPerfect v n ∧ p.free v n))
    (hRef : ActualReflexive m.ontic w) :
    PossibleGreatness m.ontic
      (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
        GoodIn InPotency power S Knows Chooses Permitted Capable Imposed) w ∧
    ∃ n, PositiveCoreAt m.ontic
        (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
          GoodIn InPotency power S Knows Chooses Permitted Capable Imposed) w n ∧
      GreatnessAt m.ontic
        (fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
          GoodIn InPotency power S Knows Chooses Permitted Capable Imposed) n w := by
  let p := fixedProfile σ m q Composite Infinite Eternal HasIntellect HasWill
    GoodIn InPotency power S Knows Chooses Permitted Capable Imposed
  have hTen := positiveCore_with_ten_from_same_root σ m w q
    Composite MatterForm Infinite Eternal HasIntellect HasWill
    GoodIn InPotency MoreIn PriorSimply ComponentOf
    power S Knows Chooses Permitted Capable Imposed
    hRoot hInfinity hUnlimited hActive hPossible hMixedComposite hEternity
  obtain ⟨n, hCore, hGreat⟩ :=
    candidate_greatness_from_ten_and_four σ m w q Composite Infinite Eternal
      HasIntellect HasWill GoodIn InPotency power S Knows Chooses Permitted
      Capable Imposed p rfl hTen hComplete
  exact ⟨⟨w, hRef, n, hGreat⟩, n, hCore, hGreat⟩

/-- Decree-as-respect collapses contingency under the constant family. Read
`SimplicityCollapse.RespectSuffices m InAct' w g d x` with the constant family
`InAct' := fun _ => InAct` (the C5 encoding's world-free `q.InAct`); its body is
then exactly `hSuffices`. If the decree `d` is a respect of `g`, it holds at
every world, so the effect exists at every accessible world and is not
contingent at `w`. No ModalCapacity, IX.6 reading, immutability,
ExclusiveDecree or decree-at-each-world is used. The world-free `InAct` is
rigid by construction, an encoding artifact like `fixedProfile_rigid`, and is
evidence for neither C5 nor its negation; under it a contingent effect requires
that the decree not be an `InAct`-respect of the source or that respect
sufficiency fail. Unregistered helper. -/
theorem constant_respect_collapses_contingency {R : Type} (m : Ontic W B)
    (InAct : B → R → Prop) (w : W) (g x : B) (d : R)
    (hDecree : InAct g d)
    (hSuffices : ∀ v, m.frame.access w v → InAct g d → m.ExistsAt v x) :
    ¬ TruthCore.German.Kant.CosmologicalInference.ContingentAt m w x := by
  rintro ⟨_, v, hV, hAbsent⟩
  exact hAbsent (hSuffices v hV hDecree)

/-! ## Restoring the omitted source and intentional-output constraints

Uses exactly the previous NecessaryVariableEffects.alternatingEffects model,
not a new frame or a claimed metaphysical possibility. Unlike a vacuous
all-True attributes model, a distinct actual effect has real passive potency
and composition, and the source exists and is actual while lacking both.
Knowledge tracks nonconstant contents; permissible choices differ across the
two alternatives. The single forbidden option `none` is never chosen, but it
is also outside `Capable` and has no causal output, so the control instantiates
nonselection by incapacity, not "able but never chooses"; a permissible
abstention is not modelled.
The choice-output correspondence is extensional only: no intrinsic
intentional self-knowledge or reason-grounded creation is represented. -/
namespace CreationControl
open TruthCore.Modal.NecessaryVariableEffects
  (EffectBeing source firstEffect secondEffect alternatingEffects
   SameNecessaryEffect noFixedEffect)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-- The actual-world esse dictionary, matched to false's existing roster.
A global q.InAct dictionary applying also at the alternative would need an
explicit cross-world translation, which this control does not assert. -/
def inAct (_x : EffectBeing) (_r : Unit) : Prop :=
  _x = source ∨ _x = firstEffect

/-- The selected source is noncomposite and potency-free, while the actual
first effect is both composite and passively potent. -/
def composite (x : EffectBeing) : Prop := x ≠ source
def inPotency (x : EffectBeing) (_ : Unit) : Prop := x ≠ source
def eternal (x : EffectBeing) : Prop := x = source

/-- Two nonempty, mutually opposed contingent truth contents. This is an
extensional surrogate, not a mechanism of true self-understanding. -/
def truth : Semantics Bool Bool where
  trueAt w c := w = c
  neg c := !c
  neg_true_iff := by intro w c; cases w <;> cases c <;> decide

def knows (w : Bool) (x : EffectBeing) (c : Bool) : Prop :=
  x = source ∧ w = c

/-- Both different selected effects (`some false`, `some true`) are equally
permitted; the single forbidden action is `none`, which lies outside `capable`
(the forbidden option is never within capacity, so its nonselection is by
incapacity) and has no causal output. All positive choices are within the
source's uncoerced capacity. A permissible abstention is not modelled.
`chooses` is world-dependent; `permitted`, `capable` and `imposed` are not. -/
def chooses (w : Bool) (x : EffectBeing) (a : Option Bool) : Prop :=
  x = source ∧ a = some w
def permitted (_ : Bool) (a : Option Bool) : Prop := a ≠ none
def capable (_ : Bool) (x : EffectBeing) (a : Option Bool) : Prop :=
  x = source ∧ a ≠ none
def imposed (_ : Bool) (_ : EffectBeing) (_ : Option Bool) : Prop := False

/-- NONMETAPHYSICAL structural non-collapse with one actual/source bearer:
actual existing composite/potent effects coexist with a simple, purely
actual, eternal source, complete factive SELECTED-content knowledge, and
permissible genuinely different choices at both worlds. The source's
necessity and contingent distinct effect are existing verified #462
results. A strict same-decree efficiency or real intentional choice bridge
is NOT supplied, so #555 is not contradicted. -/
def Compatibility : Prop :=
  (∀ x, inAct x () ↔ alternatingEffects.ExistsAt false x) ∧
  inAct source () ∧ inAct firstEffect () ∧ inPotency firstEffect () ∧
  composite firstEffect ∧ IsSimple composite source ∧
  ActAndPotencyMakeComposite inAct inPotency composite ∧
  ImmutableIsEternalReading inPotency eternal ∧
  IsImmutable inPotency source ∧ eternal source ∧
  (∀ w, alternatingEffects.ExistsAt w source ∧
    KnowsAllContentsAt truth knows w source ∧
    PermissibleChoicesAt chooses permitted w source ∧
    NoncoercedChoiceAt chooses capable imposed w source) ∧
  chooses false source (some false) ∧ chooses true source (some true) ∧
  permitted false (some false) ∧ permitted true (some true) ∧
  ¬ permitted false none ∧ ¬ capable false source none ∧
  knows false source false ∧ ¬ knows true source false ∧
  (∀ w b, chooses w source (some b) ↔
    alternatingEffects.Causes w source (some b)) ∧
  NecessaryAt alternatingEffects false source ∧
  ContingentAt alternatingEffects false firstEffect ∧
  ¬ SameNecessaryEffect alternatingEffects false source

theorem compatibility : Compatibility := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x
    rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    exact h rfl
  · intro x r s _ hPot
    exact hPot
  · intro x hPure
    cases x with
    | none => rfl
    | some b =>
      exact False.elim (hPure () (by intro h; cases h))
  · intro r h
    exact h rfl
  · rfl
  · intro w
    refine ⟨Or.inl rfl, ?_, ?_, ?_⟩
    · intro c
      change (source = source ∧ w = c) ↔ w = c
      exact ⟨And.right, fun h => ⟨rfl, h⟩⟩
    · intro a hChoose
      obtain ⟨_, ha⟩ := hChoose
      rw [ha]
      intro h
      cases h
    · refine ⟨some w, ⟨rfl, rfl⟩, ⟨rfl, ?_⟩, ?_⟩
      · intro h
        cases h
      · intro h
        exact h
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    exact h rfl
  · intro h
    exact h.2 rfl
  · exact ⟨rfl, rfl⟩
  · intro h
    cases h.2
  · intro w b
    rfl
  · exact TruthCore.Modal.NecessaryVariableEffects.sourceNecessaryAt
  · exact TruthCore.Modal.NecessaryVariableEffects.firstEffectContingent
  · exact noFixedEffect
end CreationControl

end Interpreted

/-! ## Finite structural controls

They concern only the stated Bool models; none says anything about a real divine
essence. -/
namespace Control

/-- Only the selected world's single bearer `true` exists, and all thirteen slots
hold together exactly where that bearer exists. -/
def holdsAt (selected : Bool) (v x : Bool) : Prop :=
  v = selected ∧ x = true

/-- M = identity (#438's `metaphysical`). -/
def ontic (selected : Bool) : Ontic Bool Bool where
  frame := TruthCore.Modal.PossibilityTransfer.metaphysical
  ExistsAt := holdsAt selected
  Causes := fun _ _ _ => False

/-- Every slot is `holdsAt selected`. -/
def slots (selected : Bool) : ProfileSlots Bool Bool where
  simple := holdsAt selected
  perfect := holdsAt selected
  good := holdsAt selected
  one := holdsAt selected
  infinite := holdsAt selected
  immutable := holdsAt selected
  eternal := holdsAt selected
  intellect := holdsAt selected
  will := holdsAt selected
  omnipotent := holdsAt selected
  omniscient := holdsAt selected
  morallyPerfect := holdsAt selected
  free := holdsAt selected

/-- Every slot `True`: the schema imposes no content. -/
def allTrue : ProfileSlots Bool Bool where
  simple := fun _ _ => True
  perfect := fun _ _ => True
  good := fun _ _ => True
  one := fun _ _ => True
  infinite := fun _ _ => True
  immutable := fun _ _ => True
  eternal := fun _ _ => True
  intellect := fun _ _ => True
  will := fun _ _ => True
  omnipotent := fun _ _ => True
  omniscient := fun _ _ => True
  morallyPerfect := fun _ _ => True
  free := fun _ _ => True

/-- The nine StageTwo-order slots hold everywhere; omniscience, moral perfection
and freedom hold nowhere; omnipotence holds everywhere. -/
def unlinked : ProfileSlots Bool Bool where
  simple := fun _ _ => True
  perfect := fun _ _ => True
  good := fun _ _ => True
  one := fun _ _ => True
  infinite := fun _ _ => True
  immutable := fun _ _ => True
  eternal := fun _ _ => True
  intellect := fun _ _ => True
  will := fun _ _ => True
  omnipotent := fun _ _ => True
  omniscient := fun _ _ => False
  morallyPerfect := fun _ _ => False
  free := fun _ _ => False

/-- Power and knowledge attributed to DIFFERENT bearers. -/
def split : ProfileSlots Bool Bool where
  simple := fun _ _ => True
  perfect := fun _ _ => True
  good := fun _ _ => True
  one := fun _ _ => True
  infinite := fun _ _ => True
  immutable := fun _ _ => True
  eternal := fun _ _ => True
  intellect := fun _ _ => True
  will := fun _ _ => True
  omnipotent := fun _ x => x = true
  omniscient := fun _ x => x = false
  morallyPerfect := fun _ _ => True
  free := fun _ _ => True

/-- K5 without reflexivity at `false`: every world sees only `true`. -/
def k5Frame : TruthCore.Modal.Frame Bool := ⟨fun _ v => v = true⟩

def k5Ontic : Ontic Bool Bool where
  frame := k5Frame
  ExistsAt := holdsAt true
  Causes := fun _ _ _ => False

/-- `false` sees only `true`; `true` sees both worlds. Not reflexive at `false`. -/
def returnFrame : TruthCore.Modal.Frame Bool := ⟨fun a b => a = true ∨ b = true⟩

/-- The bearer `true` exists at both worlds. -/
def returnOntic : Ontic Bool Bool where
  frame := returnFrame
  ExistsAt := fun _ x => x = true
  Causes := fun _ _ _ => False

/-- M universal (#438's `epistemic`), bearer only at `true`. -/
def innerOntic : Ontic Bool Bool where
  frame := TruthCore.Modal.PossibilityTransfer.epistemic
  ExistsAt := holdsAt true
  Causes := fun _ _ _ => False

/-- A signature whose root predicate is empty and whose classical-attributes field
is total; otherwise `GodNamingSenses.Control.boolSignature`. -/
def godless : Signature :=
  { TruthCore.Causality.GodNamingSenses.Control.boolSignature with
    IsGod := fun _ => False
    HasClassicalAttributes := fun _ => True }

def godlessOntic : Ontic Bool godless.Being := ontic false
def godlessSlots : ProfileSlots Bool godless.Being := slots false

/-- E-possible complete bearer (at `true`) not admitted by M = identity at `false`. -/
def eNotM : Prop :=
  DescribedPossibleGreatness TruthCore.Modal.PossibilityTransfer.epistemic
      (ontic true) (slots true) false ∧
    ¬ PossibleGreatness (ontic true) (slots true) false

/-- Targeted admissibility holds and yields an M-witness although the universal
inclusion `IncludedAt E M false` fails. -/
def targetedNotGlobal : Prop :=
  DescribedPossibleGreatness TruthCore.Modal.PossibilityTransfer.epistemic
      (ontic false) (slots false) false ∧
    AdmitGreatnessWorlds TruthCore.Modal.PossibilityTransfer.epistemic
      (ontic false) (slots false) false ∧
    ¬ TruthCore.Modal.PossibilityTransfer.IncludedAt
        TruthCore.Modal.PossibilityTransfer.epistemic (ontic false).frame false ∧
    PossibleGreatness (ontic false) (slots false) false

/-- Separately instantiated power and knowledge without a joint bearer. -/
def noJointBearer : Prop :=
  (∃ x, split.omnipotent false x) ∧ (∃ x, split.omniscient false x) ∧
    ¬ ∃ x, ExcellenceAt split false x

/-- Euclidean (K5) alone does not give actual existence. -/
def k5NoActual : Prop :=
  TruthCore.Modal.Euclidean k5Frame ∧ ¬ ActualReflexive k5Ontic false ∧
    PossibleGreatness k5Ontic (slots true) false ∧ ¬ ∃ x, k5Ontic.ExistsAt false x

/-- Reflexivity at w is not necessary: Euclidean-at-w, no reflexivity at w, and
the witness-relative condition gives the actual maximal profile. -/
def nonreflexiveReturn : Prop :=
  EuclideanAt returnFrame false ∧ ¬ ActualReflexive returnOntic false ∧
    PossibleGreatness returnOntic allTrue false ∧ ∃ x, GreatnessAt returnOntic allTrue x false

/-- Inner-E (E = identity) holds at `true` while outer-E (M universal) fails,
and the covering bridge fails. -/
def innerNotOuter : Prop :=
  DescribedPossibleGreatnessInnerE TruthCore.Modal.PossibilityTransfer.metaphysical
      innerOntic (slots true) true ∧
    ¬ DescribedPossibleGreatness TruthCore.Modal.PossibilityTransfer.metaphysical
      innerOntic (slots true) true ∧
    ¬ InnerSuccessorsCovered TruthCore.Modal.PossibilityTransfer.metaphysical innerOntic true

/-- Slot separations: good without morallyPerfect, intellect without omniscient,
will without free; the nine StageTwo-order slots without the full excellence. -/
def separations : Prop :=
  (∃ x, unlinked.good false x ∧ ¬ unlinked.morallyPerfect false x) ∧
    (∃ x, unlinked.intellect false x ∧ ¬ unlinked.omniscient false x) ∧
    (∃ x, unlinked.will false x ∧ ¬ unlinked.free false x) ∧
    NineAt unlinked false true ∧ ¬ ExcellenceAt unlinked false true

/-- The schema is satisfied with every slot `True`. -/
def noSenseFixed : Prop := ∀ w x, ExcellenceAt allTrue w x

/-- Naming omission: every premise of `actual_god_exists` except `hName` holds,
and `GodExists` fails. So the naming bridge is not derivable from the others. -/
def namingOmission : Prop :=
  EuclideanAt godlessOntic.frame false ∧ ActualReflexive godlessOntic false ∧
    DescribedPossibleGreatness TruthCore.Modal.PossibilityTransfer.epistemic
      godlessOntic godlessSlots false ∧
    AdmitGreatnessWorlds TruthCore.Modal.PossibilityTransfer.epistemic
      godlessOntic godlessSlots false ∧
    ProfileNineSuffice godless godlessSlots false ∧
    ¬ ActualDivineNaming godless godlessOntic godlessSlots false ∧
    ¬ GodExists godless.IsGod

/-- S5, a rigid necessary bearer, and ALL thirteen opaque slots ACTUALLY
satisfied need not give a possible maximal profile: the opaque `one` slot (here
`v = false`; not `fixedProfile`'s ActualRoot uniqueness) can fail at an
accessible world even when the bearer continues to exist. All other slots
remain true. Slot names on the generic `ProfileSlots` are mnemonic only.
Whether the `fixedProfile` root premises entail `one` at M-successors is
untested. "Essential" in `actualButNotEssential` means de re modal possession
of the slots at every M-successor, not a Finean essence (cf.
`NecessaryExcellenceAt`). This is a structural omission control, not a
metaphysical counterexample to the divine essence. -/
def persistingOntic : Ontic Bool Bool where
  frame := TruthCore.Modal.PossibilityTransfer.epistemic
  ExistsAt := fun _ x => x = true
  Causes := fun _ _ _ => False

def uniquenessOnlyHere : ProfileSlots Bool Bool :=
  { allTrue with one := fun v _ => v = false }

def actualButNotEssential : Prop :=
  TruthCore.Modal.FrameSatisfies .S5 persistingOntic.frame ∧
    persistingOntic.ExistsAt false true ∧
    TruthCore.German.Kant.CosmologicalInference.NecessaryAt persistingOntic false true ∧
    ExcellenceAt uniquenessOnlyHere false true ∧
    ¬ GreatnessAt persistingOntic uniquenessOnlyHere true false ∧
    ¬ PossibleGreatness persistingOntic uniquenessOnlyHere false

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 100000 in
theorem actualButNotEssential_holds : actualButNotEssential := by
  dsimp [actualButNotEssential, persistingOntic, uniquenessOnlyHere, allTrue,
    TruthCore.German.Kant.CosmologicalInference.NecessaryAt, ExcellenceAt, NineAt, NineClassicalAttributes, GreatnessAt,
    PossibleGreatness, TruthCore.Modal.NecessaryIfExistent.MaximalProfile,
    TruthCore.Modal.PossibilityTransfer.epistemic,
    TruthCore.Modal.FrameSatisfies, TruthCore.Modal.Reflexive,
    TruthCore.Modal.Euclidean]
  decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 100000 in
theorem eNotM_holds : eNotM := by
  dsimp [eNotM, ontic, slots, holdsAt, DescribedPossibleGreatness, PossibleGreatness,
    GreatnessAt, ExcellenceAt, NineAt, NineClassicalAttributes,
    TruthCore.Modal.NecessaryIfExistent.MaximalProfile,
    TruthCore.Modal.PossibilityTransfer.epistemic,
    TruthCore.Modal.PossibilityTransfer.metaphysical]
  decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 100000 in
theorem targetedNotGlobal_holds : targetedNotGlobal := by
  dsimp [targetedNotGlobal, ontic, slots, holdsAt, DescribedPossibleGreatness,
    PossibleGreatness, AdmitGreatnessWorlds, GreatnessAt, ExcellenceAt, NineAt,
    NineClassicalAttributes, TruthCore.Modal.NecessaryIfExistent.MaximalProfile,
    TruthCore.Modal.PossibilityTransfer.epistemic,
    TruthCore.Modal.PossibilityTransfer.metaphysical,
    TruthCore.Modal.PossibilityTransfer.IncludedAt]
  decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 100000 in
theorem noJointBearer_holds : noJointBearer := by
  dsimp [noJointBearer, split, ExcellenceAt, NineAt, NineClassicalAttributes]
  decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 100000 in
theorem k5NoActual_holds : k5NoActual := by
  dsimp [k5NoActual, k5Frame, k5Ontic, slots, holdsAt, TruthCore.Modal.Euclidean,
    ActualReflexive, PossibleGreatness, GreatnessAt, ExcellenceAt, NineAt,
    NineClassicalAttributes, TruthCore.Modal.NecessaryIfExistent.MaximalProfile]
  decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 100000 in
theorem nonreflexiveReturn_holds : nonreflexiveReturn := by
  dsimp [nonreflexiveReturn, returnFrame, returnOntic, allTrue, EuclideanAt,
    ActualReflexive, PossibleGreatness, GreatnessAt, ExcellenceAt, NineAt,
    NineClassicalAttributes, TruthCore.Modal.NecessaryIfExistent.MaximalProfile]
  decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 100000 in
theorem innerNotOuter_holds : innerNotOuter := by
  dsimp [innerNotOuter, innerOntic, slots, holdsAt, DescribedPossibleGreatnessInnerE,
    DescribedPossibleGreatness, InnerSuccessorsCovered, GreatnessAt, ExcellenceAt,
    NineAt, NineClassicalAttributes, TruthCore.Modal.NecessaryIfExistent.MaximalProfile,
    TruthCore.Modal.PossibilityTransfer.epistemic,
    TruthCore.Modal.PossibilityTransfer.metaphysical,
    TruthCore.Modal.PossibilityTransfer.IncludedAt]
  decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 100000 in
theorem separations_hold : separations := by
  dsimp [separations, unlinked, ExcellenceAt, NineAt, NineClassicalAttributes]
  decide

theorem noSenseFixed_holds : noSenseFixed := by
  intro _ _
  exact ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩,
    trivial, trivial, trivial, trivial⟩

theorem namingOmission_holds : namingOmission := by
  refine ⟨?_, ?_, ?_, ?_, fun _ _ => trivial, ?_, fun ⟨_, h⟩ => h⟩
  · dsimp [godlessOntic, ontic, EuclideanAt, TruthCore.Modal.PossibilityTransfer.metaphysical]
    decide
  · exact (rfl : false = false)
  · exact targetedNotGlobal_holds.1
  · exact targetedNotGlobal_holds.2.1
  · intro hName
    have hEx : ExcellenceAt godlessSlots false true := by
      dsimp [godlessSlots, slots, holdsAt, ExcellenceAt, NineAt, NineClassicalAttributes]
      decide
    exact hName true ⟨rfl, rfl⟩ hEx

end Control

end TruthCore.Modal.DivineProfile
