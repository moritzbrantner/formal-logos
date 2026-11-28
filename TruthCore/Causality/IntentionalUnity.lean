module

public import TruthCore.Causality.ImitabilityPlurality

/-! # Constituents, operations, and their objects

Analyst formulations, attribution deferred. The question is whether plurality
of specifications supplies plurality of proper actualizers of the SAME
intrinsic actuality. The specifications can concern intentional presence or
noncognitive formal modes. Nothing in these criteria privileges either reading.

`RealConstituent` retains the existing meaning, including a simple being's
whole nature. A selected specification has a real realization and a fact
expressing the actuality relevant to the proposed constitutive explanation.
It is not identified with an external object's existence fact. The OPEN
constituency-to-priority bridge concerns only a realizer distinct from the
designated whole. It therefore does not demand strict self-grounding of the
whole nature. The converse sufficient diagnostic (a real intrinsic proper
co-principle actually constituting the whole) is a philosophical motivation,
not a theorem identifying all real constituents with strict prior facts.

The first law composes the existing `PriorityOmission` no-cycle theorem with
that guarded item-to-fact bridge. Specifications posterior to an actuality
cannot supply distinct real realizers under the bridge. Concluding simplicity
also needs exhaustive coverage of real constituents by those specifications.
Neither the priority bridge nor coverage follows from object-directedness.
The result is local to one world, one explanandum and one interpreted relation.
No bridge from efficient giving to explanation is assumed.

The second law applies the existing `ImitabilityPlurality` collapse theorem
to operations selected at one bearer and exercise. The OPEN identity premise
says that bearer, exercise and the supplied COMPLETE IMMEDIATE actuality
jointly individuate the token. A remote cause, faculty or common source is
not automatically that complete actuality. An exercise index need not be a
time; its adequacy for an eternal operation remains OPEN. The earlier
`ConstitutiveNatureUniqueness.ConstitutiveContentComplete` concerns equality
of represented nature-content profiles, not this identity of operation tokens.
No extensionality of an operation's object profile is asserted here.

The controls use arbitrary object carriers and countably many specifications
and operations. They are interpretations of the displayed structure, not
metaphysical possibility proofs. They expose omitted priority, coverage,
realization and individuation commitments. In the simple positive row the
proper-realizer guard is empty because every realizer is the whole; the
omission rows restore a distinct real constituent. Ordinary multi-object
operations are not thereby shown simple, and repeated operations can have
identical object profiles. Existing priority-structure omission controls in
`ImitabilityGrounding` are reused rather than reproduced.
-/

@[expose] public section

namespace TruthCore.Causality.IntentionalUnity

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Explanation.PSRStrength (Arena Coherent Factive)
open TruthCore.Causality.ImitabilityGrounding
  (FactPriorityAsymmetricAt FactPriorityTransitiveAt)
open TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence
  (ConstitutivelySimple)

variable {W B T R C A F O E : Type}

/-- Each eligible specification's selected actuality fact is downstream of
`target` through a nonempty finite chain in the SAME `Arena.explains` relation
at `w`. For intentional contents the fact may be their intentional presence;
it is not the existence of their external objects. For formal modes it may
be the mode's derivative specification. This is an OPEN direction-of-
explanation premise, not a consequence of being an object or predicate.
Mathlib's `Relation.TransGen` admits chains of any finite length. -/
def PosteriorSpecificationsAt (I : Arena W B F) (w : W)
    (eligible : Set C) (specification : C → F) (target : F) : Prop :=
  ∀ c ∈ eligible, Relation.TransGen (I.explains w) target (specification c)

/-- OPEN necessary bridge for the selected constitutive interpretation:
if an eligible specification's realizer is a real constituent of `b` distinct
from `whole`, its associated actuality fact strictly contributes to the SAME
target. A proper actualizing form in a composite is a motivating case; a
remote causal condition, an object of understanding, or the whole nature
realizing itself is not automatically such a case. No sufficiency or
exhaustiveness is hidden here. The strict-priority laws remain separate.
Its applicability to intentional and nonintentional specifications is equal.
-/
def DistinctRealizersContributeAt (I : Arena W B F) (w : W)
    (RealConstituent : B → A → Prop) (b : B) (whole : A)
    (eligible : Set C) (realize : C → A) (specification : C → F)
    (target : F) : Prop :=
  ∀ c ∈ eligible, RealConstituent b (realize c) → realize c ≠ whole →
    I.explains w (specification c) target

/-- OPEN coverage: every real constituent of this bearer is realized by at
least one eligible specification. This is needed to extend a conclusion
about selected realizers to the bearer's full constitution. A description
omitting an actual power or constituent fails it. It is not completeness of
an object list, a sufficient explanation, or injectivity of realization. -/
def RealizersCoverConstituents (RealConstituent : B → A → Prop) (b : B)
    (eligible : Set C) (realize : C → A) : Prop :=
  ∀ a, RealConstituent b a → ∃ c ∈ eligible, realize c = a

/-- Guarded application of strict priority to actual constitution. First,
each eligible realizer counted as real equals the designated whole. Only
with coverage does constitutive simplicity follow. This is at-most-one
constituency; actual existence and nonempty realization are not conclusions.
The positive control supplies both rather than hiding their absence. -/
def PosteriorConstitutionLaws : Prop :=
  ∀ (W B C A F : Type) (I : Arena W B F) (w : W)
    (RealConstituent : B → A → Prop) (b : B) (whole : A)
    (eligible : Set C) (realize : C → A) (specification : C → F) (target : F),
    FactPriorityAsymmetricAt I w → FactPriorityTransitiveAt I w →
    PosteriorSpecificationsAt I w eligible specification target →
    DistinctRealizersContributeAt I w RealConstituent b whole eligible
      realize specification target →
    (∀ c ∈ eligible, RealConstituent b (realize c) → realize c = whole) ∧
      (RealizersCoverConstituents RealConstituent b eligible realize →
        ConstitutivelySimple RealConstituent b)

/-- A selected operation occurs at `w`, belongs to the existing bearer `b`,
and has exercise index `e`. `occurs`, `bearer`, and `exercise` are explicit
primitive assignments. An exercise index names the occurrence relevant to
individuation; no claim identifies it with the frame's effect-side moment.
The existence predicate is reused from the shared causality frame. -/
def OperationAt (K : CausalityFrame W B T R) (w : W)
    (occurs : W → O → Prop) (bearer : O → B) (exercise : O → E)
    (b : B) (e : E) (o : O) : Prop :=
  K.history.ontic.ExistsAt w b ∧ occurs w o ∧ bearer o = b ∧ exercise o = e

/-- OPEN operation-to-constitution bridge: each selected operation's
complete immediate realizer is a real constituent of its bearer. Merely
having an object, effect or remote ground does not establish this. Realizers
may coincide; distinct operations do not force distinct constituents without
the separate identity premise and matching exercise. -/
def IntrinsicOperationRealizersAt (K : CausalityFrame W B T R) (w : W)
    (occurs : W → O → Prop) (bearer : O → B) (exercise : O → E)
    (RealConstituent : B → A → Prop) (realize : O → A) (b : B) (e : E) : Prop :=
  ∀ o, OperationAt K w occurs bearer exercise b e o → RealConstituent b (realize o)

/-- OPEN extensionality of the supplied intrinsic operation profile. Its
last component must be the complete immediate actuality of the operation,
not merely its bearer, a faculty or a common real cause. Its first two
components retain bearer and exercise identity. The tuple does not prove
that these data are metaphysically complete: injectivity asserts exactly
that disputed adequacy. Object equality is absent. -/
def OperationProfileComplete (bearer : O → B) (exercise : O → E)
    (realize : O → A) : Prop :=
  Function.Injective (fun o => (bearer o, exercise o, realize o))

/-- A wrapper for the primitive relation that an operation concerns an
object. For a comparison, both compared terms are objects of the operation;
the subject's faculty or the comparison's own real occurrence need not be.
An object need not be an actual external being. This records incidence only:
it implies neither apprehension, truth, existence, intrinsic constituency nor
a priority edge. Those stronger interpretations need their own bridges. -/
def ObjectOf (Concerns : O → C → Prop) (o : O) (c : C) : Prop := Concerns o c

/-- The local subtype of operations is a subsingleton when simplicity,
intrinsic realization and complete intrinsic-profile individuation hold.
This applies the earlier realizer-collapse law to a restricted carrier.
It does not assert an operation exists, identify different exercises, or
collapse a carrier of objects. The controls populate the selected subtype. -/
def LocalOperationUnityLaws : Prop :=
  ∀ (W B T R O E A : Type) (K : CausalityFrame W B T R) (w : W)
    (occurs : W → O → Prop) (bearer : O → B) (exercise : O → E)
    (RealConstituent : B → A → Prop) (realize : O → A) (b : B) (e : E),
    ConstitutivelySimple RealConstituent b →
    IntrinsicOperationRealizersAt K w occurs bearer exercise RealConstituent realize b e →
    OperationProfileComplete bearer exercise realize →
    Subsingleton {o // OperationAt K w occurs bearer exercise b e o}

namespace ExistingAccounts

open TruthCore.Causality.ImitabilityPlurality.PositiveControl (arena values Fact)
open TruthCore.Causality.ImitabilityPlurality.Control (realizer)
open TruthCore.Causality.PossibiliaContent.Control (realBlob)
open TruthCore.Causality.AxiarchicFoundation.Control (Item)

/-- Application to BOTH existing restored source-based accounts, at both
worlds. Their positive nature-to-mode paths supply posteriority. All selected
realizers are the whole nature, so the proper-realizer bridge is vacuous;
coverage and simplicity are already true in the earlier interpretation.
This demonstrates the criterion's identical application, not new warrant
for either account's metaphysical coherence or complete mind-independence.
-/
def Application : Prop :=
  ∀ personal v,
    PosteriorSpecificationsAt (arena personal values) v Set.univ Fact.mode Fact.nature ∧
    DistinctRealizersContributeAt (arena personal values) v realBlob true Item.blob
      Set.univ realizer Fact.mode Fact.nature ∧
    RealizersCoverConstituents realBlob true Set.univ realizer ∧
    ConstitutivelySimple realBlob true

end ExistingAccounts

namespace Control

/-- Reuse the populated shared frame from the earlier priority controls:
both beings exist and the source gives the effect being. No giving-to-
priority bridge is needed or asserted in this investigation. -/
abbrev frame := TruthCore.Causality.ImitabilityGrounding.CycleControl.frame

/-- Countably many true fact tokens, with the selected explanation relation.
All represented facts and both bearers are actual. Modal variation and an
exhaustive theory of explanation are outside this interpretation. -/
def arena (rel : Nat → Nat → Prop) : Arena Unit Bool Nat where
  ontic := frame.history.ontic
  holds := fun _ _ => True
  exist := fun b => if b then 0 else 1
  explains := fun _ => rel
  conjunct := Eq

/-- The source has exactly its whole nature `0` as a real constituent. -/
def simpleReal (b : Bool) (a : Nat) : Prop := b = true ∧ a = 0

/-- A second actual constituent is present; the whole remains `0`. -/
def twoReal (b : Bool) (a : Nat) : Prop := b = true ∧ (a = 0 ∨ a = 1)

/-- Countably many real constituents of the source, used only to test the
omission of subject simplicity. -/
def manyReal (b : Bool) (_ : Nat) : Prop := b = true

/-- Every specification shares one real realization; their own carrier is
still Nat. This is not equality of different specifications. -/
def commonRealizer (_ : Nat) : Nat := 0

/-- Both represented constituents are covered: specification 0 realizes the
whole, and every positive specification realizes the second constituent. -/
def splitRealizer (n : Nat) : Nat := if n = 0 then 0 else 1

/-- Specification actuality facts start at 2, distinct from BOTH existence
facts 0 and 1. This keeps intentional presence or a mode specification from
silently becoming the external effect's existence fact. -/
def specification (n : Nat) : Nat := n + 2

/-- Positive nonempty simple row: infinitely many distinct specification
facts depend on target 0, and their realizers are the actual whole. The
proper-realizer contribution guard has no instances in this row. -/
def PosteriorWhole : Prop :=
  simpleReal true 0 ∧
  (∀ n, specification n ≠ specification (n + 1)) ∧
  (∀ n, specification n ≠ (arena Nat.lt).exist true ∧
    specification n ≠ (arena Nat.lt).exist false) ∧
  (∀ n, simpleReal true (commonRealizer n)) ∧
  PosteriorSpecificationsAt (arena Nat.lt) () Set.univ specification 0 ∧
  DistinctRealizersContributeAt (arena Nat.lt) () simpleReal true 0
    Set.univ commonRealizer specification 0 ∧
  RealizersCoverConstituents simpleReal true Set.univ commonRealizer ∧
  ConstitutivelySimple simpleReal true

/-- Omitting coverage leaves a second real constituent unrepresented by
the posterior specifications. Strict priority and the guarded bridge hold;
constitutive simplicity fails. -/
def OmitCoverage : Prop :=
  twoReal true 0 ∧ twoReal true 1 ∧
  PosteriorSpecificationsAt (arena Nat.lt) () Set.univ specification 0 ∧
  DistinctRealizersContributeAt (arena Nat.lt) () twoReal true 0
    Set.univ commonRealizer specification 0 ∧
  ¬ RealizersCoverConstituents twoReal true Set.univ commonRealizer ∧
  ¬ ConstitutivelySimple twoReal true

/-- Omitting the item-to-fact contribution bridge allows both actual
constituents to be covered while all specifications are posterior. This is
a counterinterpretation to inferring simplicity from direction alone. -/
def OmitContribution : Prop :=
  twoReal true 0 ∧ twoReal true 1 ∧
  PosteriorSpecificationsAt (arena Nat.lt) () Set.univ specification 0 ∧
  RealizersCoverConstituents twoReal true Set.univ splitRealizer ∧
  ¬ DistinctRealizersContributeAt (arena Nat.lt) () twoReal true 0
    Set.univ splitRealizer specification 0 ∧
  ¬ ConstitutivelySimple twoReal true

/-- With the priority order reversed, the distinct constituent's fact
really contributes to target 0. Coverage and the guarded bridge hold;
posteriority and simplicity fail. The contribution bridge is nonvacuous. -/
def OmitPosteriority : Prop :=
  twoReal true 0 ∧ twoReal true 1 ∧
  DistinctRealizersContributeAt (arena (fun p q => q < p)) () twoReal true 0
    Set.univ splitRealizer specification 0 ∧
  RealizersCoverConstituents twoReal true Set.univ splitRealizer ∧
  ¬ PosteriorSpecificationsAt (arena (fun p q => q < p)) () Set.univ specification 0 ∧
  ¬ ConstitutivelySimple twoReal true

/-- The SAME-explanandum restriction is material: target 0 explains each
specification n+2, which can then explain the DIFFERENT operation-actuality
fact n+3, all within strict priority. No reverse contribution to 0 occurs.
These are distinct facts, not an identity of subject and operation. -/
def DifferentExplanandum : Prop :=
  ∀ n, (arena Nat.lt).explains () 0 (specification n) ∧
    (arena Nat.lt).explains () (specification n) (n + 3) ∧
    (arena Nat.lt).explains () 0 (n + 3) ∧
    ¬ (arena Nat.lt).explains () (specification n) 0

/-- Joint priority controls over countably many specifications. Existence,
factivity and populated giving do not themselves establish any explanation
edge. Both displayed orders have positive edges and are strict/transitive.
The three omission rows isolate semantic inputs, not metaphysical failures.
-/
def PriorityControls : Prop :=
  (∀ rel, Coherent (arena rel) ∧ Factive (arena rel)) ∧
  frame.GivesAt () true false () ∧
  FactPriorityAsymmetricAt (arena Nat.lt) () ∧
  FactPriorityTransitiveAt (arena Nat.lt) () ∧
  FactPriorityAsymmetricAt (arena (fun p q => q < p)) () ∧
  FactPriorityTransitiveAt (arena (fun p q => q < p)) () ∧
  PosteriorWhole ∧ OmitCoverage ∧ OmitContribution ∧ OmitPosteriority ∧
  DifferentExplanandum ∧ ExistingAccounts.Application

def occurs {O : Type} (_ : Unit) (_ : O) : Prop := True
def bearer {O : Type} (_ : O) : Bool := true
def exercise {O : Type} (_ : O) : Unit := ()
def whole {O : Type} (_ : O) : Nat := 0

/-- Object incidence for one operation and ANY selected set on ANY carrier.
Membership specifies which objects the operation concerns. It does not say
that those objects, their existence, or their represented contents are
intrinsic constituents. Cognitive correctness is not encoded. -/
def objects {C : Type} (selected : Set C) (_ : Unit) (c : C) : Prop := c ∈ selected

/-- Repeated operations all concern the same two objects. Their exercise
indices, rather than their object profiles, distinguish their tokens. -/
def repeatedObjects (_ : Nat) (c : Nat) : Prop := c = 0 ∨ c = 1

/-- One actual operation can concern an arbitrary specified object set while
its subject is simple in the selected sense. The same operation and object
relation also meet intrinsic realization with the composite `manyReal`
subject; operation unity does not imply subject simplicity. -/
def ArbitraryObjects : Prop :=
  ∀ (C : Type) (selected : Set C),
    OperationAt frame () occurs bearer exercise true () () ∧
    OperationProfileComplete (bearer : Unit → Bool) exercise whole ∧
    IntrinsicOperationRealizersAt frame () occurs (bearer : Unit → Bool) exercise
      simpleReal whole true () ∧
    IntrinsicOperationRealizersAt frame () occurs (bearer : Unit → Bool) exercise
      manyReal whole true () ∧
    (∀ c, ObjectOf (objects selected) () c ↔ c ∈ selected)

/-- Countably many actual operations with the same object profile and one
realizer have distinct exercise indices. Profile completeness holds, and
each fixed exercise has one operation, while the full token carrier is not
a subsingleton. This supplies no application to an eternal exercise. -/
def RepeatedOperations : Prop :=
  OperationProfileComplete (bearer : Nat → Bool) id whole ∧
  (∀ n, OperationAt frame () occurs bearer id true n n) ∧
  (∀ n, IntrinsicOperationRealizersAt frame () occurs (bearer : Nat → Bool) id
    simpleReal whole true n) ∧
  (∀ n, Subsingleton {o // OperationAt frame () occurs (bearer : Nat → Bool) id true n o}) ∧
  (∀ a b c, ObjectOf repeatedObjects a c ↔ ObjectOf repeatedObjects b c) ∧
  ObjectOf repeatedObjects 0 0 ∧ ObjectOf repeatedObjects 0 1 ∧
  ¬ Subsingleton Nat

/-- Same bearer, exercise and realizer but many operation tokens: denying
profile completeness blocks the inference. No model establishes that these
descriptors really were a metaphysically complete actuality. -/
def OmitOperationIndividuation : Prop :=
  IntrinsicOperationRealizersAt frame () occurs (bearer : Nat → Bool) exercise
    simpleReal whole true () ∧
  ¬ OperationProfileComplete (bearer : Nat → Bool) exercise whole ∧
  ¬ Subsingleton {o // OperationAt frame () occurs (bearer : Nat → Bool) exercise true () o}

/-- Complete token profile with many distinct realizers outside the simple
subject's one constituent: omission of intrinsic membership blocks unity.
-/
def OmitIntrinsicRealization : Prop :=
  OperationProfileComplete (bearer : Nat → Bool) exercise id ∧
  ¬ IntrinsicOperationRealizersAt frame () occurs (bearer : Nat → Bool) exercise
    simpleReal id true () ∧
  ¬ Subsingleton {o // OperationAt frame () occurs (bearer : Nat → Bool) exercise true () o}

/-- Multiple intrinsic realizers and complete token identity are compatible
with many operations once subject simplicity is omitted. -/
def OmitSubjectSimplicity : Prop :=
  ¬ ConstitutivelySimple manyReal true ∧
  IntrinsicOperationRealizersAt frame () occurs (bearer : Nat → Bool) exercise
    manyReal id true () ∧
  OperationProfileComplete (bearer : Nat → Bool) exercise id ∧
  ¬ Subsingleton {o // OperationAt frame () occurs (bearer : Nat → Bool) exercise true () o}

/-- Arbitrary object sets, repeated operations and populated omission tests
use the SAME operation criterion. No apprehension flag or worldview label
changes the criteria. In particular Nat objects can all belong to one act,
but that fact alone is also compatible with a composite subject. -/
def OperationControls : Prop :=
  ConstitutivelySimple simpleReal true ∧ simpleReal true 0 ∧
  ¬ ConstitutivelySimple manyReal true ∧
  ArbitraryObjects ∧
  (∀ n, ObjectOf (objects (Set.univ : Set Nat)) () n ∧ n ≠ n + 1) ∧
  RepeatedOperations ∧ OmitOperationIndividuation ∧
  OmitIntrinsicRealization ∧ OmitSubjectSimplicity

end Control

end TruthCore.Causality.IntentionalUnity
