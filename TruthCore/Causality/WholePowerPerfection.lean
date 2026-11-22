module

public import TruthCore.Causality.RootPurity
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity

/-! Unrestricted perfection from whole power of being; uniqueness from perfect
beings (SCG I.28, ST I q.4 a.2, SCG I.42; #320)

Typed homes for three source statements that entered the corpus through
definition records and had no argument consumer:
* `STMT-AQUINAS-SCG-I28-OWN-BEING-WHOLE-POWER-PERFECTION`: what is its own being
  lacks no excellence belonging to being (`OwnBeingLacksNoPerfectionOfBeing`).
  Only "lacks no excellence" is encoded; "has no defect" is not used.
* `STMT-ALL-PERFECTIONS-PERTAIN-TO-PERFECTION-OF-BEING`: every pure perfection is
  a perfection of being (`PurePerfectionsPertainToBeing`). Read for pure
  perfections only, which is weaker than "every perfection of a thing".
* `STMT-AQUINAS-SCG-I42-PERFECT-BEINGS-DIFFERENTIATION`: beings each lacking no
  perfection and having no admixture of imperfection are not several
  (`PerfectBeingsNotSeveral`).

`OwnBeing x` ("x is its own being", subsistent esse) is a primitive predicate.
The SCG I.28 claim warns that this is not a consequence of a represented
essence/esse equality, so the step from having no represented limiting principle
to being one's own being is the explicit OPEN analyst bridge
`UnlimitedIsOwnBeing`, attributed to no source. -/

@[expose] public section

namespace TruthCore.Causality.WholePowerPerfection
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)

variable {B D P : Type}

/-- SCG I.28 [2–3], encoded part: whatever is its own being has every
determination that is a perfection of being. -/
def OwnBeingLacksNoPerfectionOfBeing
    (OwnBeing : B → Prop) (Has : B → D → Prop) (OfBeing : D → Prop) : Prop :=
  ∀ x, OwnBeing x → ∀ d, OfBeing d → Has x d

/-- ST I q.4 a.2, restricted to pure perfections: each pure perfection pertains
to the perfection of being. -/
def PurePerfectionsPertainToBeing (Pure OfBeing : D → Prop) : Prop :=
  ∀ d, Pure d → OfBeing d

/-- OPEN analyst bridge: a being with none of the three represented limiting
principles is its own being. -/
def UnlimitedIsOwnBeing (Composite : B → Prop) (Prior : B → B → Prop)
    (essence esse : B → P) (OwnBeing : B → Prop) : Prop :=
  ∀ x, ¬ HasLimitingPrinciple Composite Prior essence esse x → OwnBeing x

/-- SCG I.42 [3]: two beings, each having every pure perfection and only pure
perfections among its real determinations, are one. Ranges over all beings. -/
def PerfectBeingsNotSeveral (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ x y, (∀ d, Pure d → Has x d) → (∀ d, Has x d → Pure d) →
    (∀ d, Pure d → Has y d) → (∀ d, Has y d → Pure d) → x = y

/-- OPEN analyst bridge, near-definitional under DEF-INFINITE ("infinity of
perfection"): whatever is infinite has every pure perfection. `Infinite` stays the
primitive predicate of `SubsistentBeingIsInfiniteReading` and `GodIsInfinite`. -/
def InfiniteHasEveryPurePerfection (Infinite : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) : Prop :=
  ∀ x, Infinite x → ∀ d, Pure d → Has x d


/-! ## Subsistent wisdom and intrinsically directed self-understanding

The whole-perfection principle yields possession of any stipulated pure wisdom
determination at an OwnBeing bearer. It does NOT identify this generic Has
relation with intellect, self-representation, or actual understanding.

The following OPEN bridges separate:
1. wisdom's positive self-directed cognitive capacity (not merely a power to
   produce a cognitive effect);
2. actual apprehension versus an unexercised *immanent* capacity at the designated
   self-understanding respect;
3. properly based apprehension versus a correct but non-cognitive signal.

"About" fixes the SAME being as object; "Correct" is an extensional truth
condition, not the explanation of its epistemic authority. "CognitivelyGrounded"
denotes content-sensitive cognitive grounding, not simple causal correlation.
No premise makes generic productive powers into intellectual powers. -/
namespace WisdomSelfUnderstanding

/-- Source-borne, true and cognitively grounded actual apprehension about that very source.
This is a selected, stronger knowledge-like specification, not the existing
unary HAS_INTELLECT_1, omniscience, or an externally produced signal. -/
def IntrinsicSelfKnowledge {B C : Type}
    (About Correct : C → B → Prop)
    (Apprehends CognitivelyGrounded : B → C → Prop) (g : B) : Prop :=
  ∃ content, About content g ∧ Correct content g ∧
    Apprehends g content ∧ CognitivelyGrounded g content

/-- OPEN recognition/interpretation premise: at a subsistent source, possessing
wisdom as a pure perfection supplies a *capacity* for true self-directed
content. The truth/capacity conjunction is not an exercise, and generic
productive virtual possession does not imply it. -/
def WisdomSelfCapacity {B D C : Type}
    (OwnBeing : B → Prop) (Has : B → D → Prop) (wisdom : D)
    (About Correct : C → B → Prop) (CanApprehend : B → C → Prop) : Prop :=
  ∀ g, OwnBeing g → Has g wisdom →
    ∃ content, About content g ∧ Correct content g ∧ CanApprehend g content

/-- OPEN bridge scoped to the actual source and its *self-directed* capacity:
either it apprehends that content or the specified understanding respect
remains in potency. This is stronger than an idle productive power, and
cannot be obtained merely by defining InAct to include virtual possession. -/
def SelfCapacityExercisedOrPotent {B C R : Type}
    (OwnBeing : B → Prop) (About : C → B → Prop)
    (CanApprehend Apprehends : B → C → Prop)
    (InPotency : B → R → Prop) (understanding : R) : Prop :=
  ∀ g content, OwnBeing g → About content g → CanApprehend g content →
    Apprehends g content ∨ InPotency g understanding

/-- OPEN intellectual-norm bridge: true apprehension by the specified subsistent
source to content *about itself* is intrinsically grounded in the intelligible
object rather than just a successful register reading or a lawlike output.
This need not be discursive reasoning or a temporal acquisition. This needs
semantic warrant, not a primitive rename of Apprehends. -/
def TrueSelfApprehensionGrounded {B C : Type}
    (OwnBeing : B → Prop) (About Correct : C → B → Prop)
    (Apprehends CognitivelyGrounded : B → C → Prop) : Prop :=
  ∀ g content, OwnBeing g → About content g → Correct content g →
    Apprehends g content → CognitivelyGrounded g content

namespace Control

/-- One fixed source and one cognitive effect, one wisdom determination and
two distinct possible contents. Only the cognitive/epistemic bridge fields
vary across omissions. No metaphysical possibility claim is made. -/
def own (g : Bool) : Prop := g = true
def has (g : Bool) (_ : Unit) : Prop := g = true
def pure (_ : Unit) : Prop := True
def ofBeing (_ : Unit) : Prop := True
def about (content g : Bool) : Prop := content = g
def correct (content g : Bool) : Prop := content = g
def canApprehend (g content : Bool) : Prop := g = true ∧ content = true
def apprehends (g content : Bool) : Prop := g = true ∧ content = true
def cognitivelyGrounded (g content : Bool) : Prop := g = true ∧ content = true
def none (_ _ : Bool) : Prop := False
def noPotency (_ : Bool) (_ : Unit) : Prop := False
def causesIn (c x : Bool) (_ : Unit) : Prop := c = true ∧ x = false
def hasIntellect (g : Bool) : Prop := g = false

/-- The same existing whole-power premises have an actual first source,
a real cognitive effect and a nonempty source-to-effect causal edge. Assigning
HasIntellect only to the effect does NOT determine the source's wisdom sense. -/
def Background : Prop :=
  OwnBeingLacksNoPerfectionOfBeing own has ofBeing ∧
  PurePerfectionsPertainToBeing pure ofBeing ∧ pure () ∧ own true ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PureAct noPotency true ∧
  causesIn true false () ∧ hasIntellect false ∧
  ¬ (∀ g, own g → hasIntellect g)

/-- Populated omission witnesses for three independent bridges:
(1) no source cognitive capacity, (2) unexercised source capacity despite
no passive potency, (3) actual correct apprehends without the specified
cognitive grounding. The fourth conjunct instantiates all three and yields
actual self-knowledge. Even that does not set the separate old HasIntellect
predicate unless an explicit recognition bridge is supplied. -/
def Controls : Prop :=
  Background ∧
  (¬ WisdomSelfCapacity own has () about correct none ∧
    SelfCapacityExercisedOrPotent own about none none noPotency () ∧
    TrueSelfApprehensionGrounded own about correct none none ∧
    ¬ IntrinsicSelfKnowledge about correct none none true) ∧
  (WisdomSelfCapacity own has () about correct canApprehend ∧
    ¬ SelfCapacityExercisedOrPotent own about canApprehend none noPotency () ∧
    TrueSelfApprehensionGrounded own about correct none none ∧
    ¬ IntrinsicSelfKnowledge about correct none none true) ∧
  (WisdomSelfCapacity own has () about correct canApprehend ∧
    SelfCapacityExercisedOrPotent own about canApprehend apprehends noPotency () ∧
    ¬ TrueSelfApprehensionGrounded own about correct apprehends none ∧
    ¬ IntrinsicSelfKnowledge about correct apprehends none true) ∧
  (WisdomSelfCapacity own has () about correct canApprehend ∧
    SelfCapacityExercisedOrPotent own about canApprehend apprehends noPotency () ∧
    TrueSelfApprehensionGrounded own about correct apprehends cognitivelyGrounded ∧
    IntrinsicSelfKnowledge about correct apprehends cognitivelyGrounded true)

end Control
end WisdomSelfUnderstanding

namespace Control
open TruthCore.Causality.PureActThisness
open TruthCore.Causality.PureIndiscernibility (PurelyDeterminedIndiscerniblesIdentical)
open TruthCore.Causality.RootPurity.Control (fmMoved fmMoves none1 none2 flat)

/-- Two inert beings with no determinations; one pure determination exists. -/
def inertHas (_ : Bool) (_ : Unit) : Prop := False

/-- Finite interpretations; satisfiability of encoded bundles only.
* SCG I.42 is strictly weaker than the narrower bridge: two determination-free
  beings are purely determined and indiscernible yet distinct, while I.42 holds
  vacuously because neither has the one pure perfection.
* SCG I.42 omitted: on the unchanged part-free model, unrestricted perfection and
  strict pure actuality hold, I.42 fails, at-most-one fails.
* Whole-power bridge omitted: a simple first mover that is first in being, with
  SCG I.28 and q.4 a.2, lacks the one pure perfection when it is not its own
  being; unrestricted perfection fails.
* SCG I.28 omitted: the first mover owns its being but lacks the perfection.
* q.4 a.2 omitted: the pure perfection is not a perfection of being.
* Positive witness: all inputs of the unrestricted-perfection derivation hold
  with an actual first mover.
* Infinity bridge omitted: the simple first mover is infinite under the q.7
  reading but lacks the pure perfection; with the bridge it has it. -/
def Certificate : Prop :=
  (PerfectBeingsNotSeveral inertHas (fun _ => True) ∧
    ¬ PurelyDeterminedIndiscerniblesIdentical inertHas (fun _ => True)) ∧
  (FirstMoverHasEveryPureDetermination TruthCore.Causality.PartFreePlurality.moved
      TruthCore.Causality.PartFreePlurality.moves Control.actHas Control.allPure ∧
    FirstMoverDeterminationsArePure TruthCore.Causality.PartFreePlurality.moved
      TruthCore.Causality.PartFreePlurality.moves Control.actHas Control.allPure ∧
    ¬ PerfectBeingsNotSeveral Control.actHas Control.allPure ∧
    ¬ TruthCore.Case.Catholicism.AtMostOneFirstUnmovedMover
      TruthCore.Causality.PartFreePlurality.moved TruthCore.Causality.PartFreePlurality.moves) ∧
  (TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverIsSimpleReading
      fmMoved fmMoves none1 none1 none1 flat.essenceOf flat.esseOf ∧
    TruthCore.Case.Catholicism.FirstUnmovedMoverIsFirstBeing fmMoved fmMoves none2 ∧
    ¬ UnlimitedIsOwnBeing none1 none2 flat.essenceOf flat.esseOf (fun _ => False) ∧
    OwnBeingLacksNoPerfectionOfBeing (fun _ => False) inertHas (fun _ => True) ∧
    PurePerfectionsPertainToBeing (fun (_ : Unit) => True) (fun _ => True) ∧
    ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas (fun _ => True)) ∧
  (UnlimitedIsOwnBeing none1 none2 flat.essenceOf flat.esseOf (fun _ => True) ∧
    ¬ OwnBeingLacksNoPerfectionOfBeing (fun _ => True) inertHas (fun _ => True) ∧
    PurePerfectionsPertainToBeing (fun (_ : Unit) => True) (fun _ => True) ∧
    ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas (fun _ => True)) ∧
  (UnlimitedIsOwnBeing none1 none2 flat.essenceOf flat.esseOf (fun _ => True) ∧
    OwnBeingLacksNoPerfectionOfBeing (fun _ => True) inertHas (fun _ => False) ∧
    ¬ PurePerfectionsPertainToBeing (fun (_ : Unit) => True) (fun _ => False) ∧
    ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas (fun _ => True)) ∧
  (UnlimitedIsOwnBeing none1 none2 flat.essenceOf flat.esseOf (fun _ => True) ∧
    OwnBeingLacksNoPerfectionOfBeing (fun _ => True) (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => True) ∧
    PurePerfectionsPertainToBeing (fun (_ : Unit) => True) (fun _ => True) ∧
    FirstMoverHasEveryPureDetermination fmMoved fmMoves (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => True) ∧
    TruthCore.Case.Catholicism.IsFirstUnmovedMover fmMoved fmMoves true) ∧
  (TruthCore.Latin.Aquinas.SummaTheologiae.SubsistentBeingIsInfiniteReading
      flat.essenceOf flat.esseOf (fun _ => True) ∧
    ¬ InfiniteHasEveryPurePerfection (fun _ => True) inertHas (fun _ => True) ∧
    ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas (fun _ => True) ∧
    InfiniteHasEveryPurePerfection (fun _ => True) (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => True))

end Control
end TruthCore.Causality.WholePowerPerfection
