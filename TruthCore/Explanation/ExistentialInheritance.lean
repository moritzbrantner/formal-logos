module

public import TruthCore.Explanation.EssenceReasonSeparation
public import TruthCore.Explanation.ExplanatoryAdequacy
public import TruthCore.Explanation.ExplanatoryClosure

/-!
# Existential inheritance without recombination

Analyst formulations, attribution deferred. The modal part reuses the source-
indexed nature and modal requirement of `EssenceReasonSeparation`. The resource
part reuses `Arena`, `Groups`, `FullSupply` and `Trap`: it interprets a group as
a record of factual prerequisites, not as a productive cause. No predicate
named adequate and no unrestricted PSR is assumed.

One possible absence of a common required bearer suffices to remove its actual
dependents together. Actual causation, a sufficient law, and an essential
requirement are different conditions. In the contained model every derivative
has a proximate reason, although deriving it from the recorded resources still
requires the initial existence fact. Admitting that fact as a primitive resource
restores derivability; the theorem does not prohibit that stopping policy.

The models certify only their stated interpretations. Whether their reason
assignments are adequate, their worlds metaphysically possible, their rules
exhaustive, or their primitive resources acceptable remains OPEN. The root
connection to the existence PSR `608a262d-08fe-4dfd-9413-67e2ecf35b84` also remains
OPEN. See `docs/notes/explanatory-adequacy-750.md`.
-/

@[expose] public section

namespace TruthCore.Explanation.ExistentialInheritance

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Explanation.EssenceReasonSeparation
open TruthCore.Explanation.PSRStrength
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Explanation.ExplanatoryClosure

variable {W B F G : Type}

/-- OPEN essence-to-modality bridge: an existence fact in x's nature holds
wherever that same x exists at a world accessible from w. The modal consequent
is the existing co-presence condition, not a definition of essence, causation,
explanation or sufficiency. No relation is inferred from the word essential. -/
def EssenceAbsenceBridge (p : Profile W B) (w : W) : Prop :=
  ∀ x b, EssenceRequiresExistence p x b → ModalRequiresExistence p w x b

/-- Same-bearer absence transfer, transitive composition of modal requirements,
and joint absence through one common required bearer. The last conjunct uses
one witness world for the whole selected class; it does not infer joint absence
from merely individual contingency. Actual existence is explicit. -/
def AbsenceInheritance : Prop :=
  (∀ (W B : Type) (p : Profile W B) (w : W) (x b : B),
    p.explanation.ontic.ExistsAt w x → ModalRequiresExistence p w x b →
    ContingentAt p.explanation.ontic w b → ContingentAt p.explanation.ontic w x) ∧
  (∀ (W B : Type) (p : Profile W B) (w : W) (x y b : B),
    ModalRequiresExistence p w x y → ModalRequiresExistence p w y b →
    ModalRequiresExistence p w x b) ∧
  (∀ (W B : Type) (p : Profile W B) (w : W) (x b : B),
    EssenceAbsenceBridge p w → EssenceRequiresExistence p x b →
    p.explanation.ontic.ExistsAt w x → ContingentAt p.explanation.ontic w b →
    ContingentAt p.explanation.ontic w x) ∧
  (∀ (W B : Type) (p : Profile W B) (w : W) (b : B) (D : B → Prop),
    (∀ x, D x → p.explanation.ontic.ExistsAt w x ∧ ModalRequiresExistence p w x b) →
    ContingentAt p.explanation.ontic w b →
    (∀ x, D x → ContingentAt p.explanation.ontic w x) ∧
    ∃ v, p.explanation.ontic.frame.access w v ∧
      ∀ x, D x → ¬ p.explanation.ontic.ExistsAt v x)

/-- A record's effect and every listed prerequisite are actual truths.
This states actual availability, not that the record explains or produces its
effect. `Groups` supplies only the existing membership/effect structure. -/
def ActualResources (A : Arena W B F) (w : W) (h : Groups F G) : Prop :=
  ∀ g, h.admitted g → A.holds w (h.effect g) ∧
    ∀ f, f ∈ h.members g → A.holds w f

/-- Each admitted record preserves truth at each accessible world when ALL its
listed prerequisites hold there. These are the selected deterministic rules;
the condition is not imposed on every possible kind of explanation. -/
def RulesPreserveTruth (A : Arena W B F) (w : W) (h : Groups F G) : Prop :=
  ∀ g, h.admitted g → ∀ v, Access A w v →
    (∀ f, f ∈ h.members g → A.holds v f) → A.holds v (h.effect g)

namespace Contained

/-- Fixed candidate identities: a persistent background, a foundation, and
arbitrarily many derivative bearers. A numeral is a dependence layer, not time. -/
inductive Being
  | background
  | base
  | derivative (n : Nat)
  deriving DecidableEq

/-- Existence facts stay distinct from their bearers and from the law fact. -/
inductive Fact
  | law
  | exists (b : Being)
  deriving DecidableEq

def parent : Nat → Being
  | 0 => .base
  | n + 1 => .derivative n

/-- Structural immediate-source relation. Causal and explanatory assignments
below both use it by stipulation; no general identification is asserted. -/
def Step (source target : Being) : Prop :=
  ∃ n, source = parent n ∧ target = .derivative n

/-- With k=false the base is contingent; k=true makes it necessary. The actual
world is false in both overlays. The candidate domain and rules never change. -/
def enabled (k w : Bool) : Prop := w = false ∨ k = true

def present (k w : Bool) : Being → Prop
  | .background => True
  | .base => enabled k w
  | .derivative _ => enabled k w

def holds (k w : Bool) : Fact → Prop
  | .law => True
  | .exists b => present k w b

def ontic (k : Bool) : Ontic Bool Being where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := present k
  Causes := fun w c x => enabled k w ∧ Step c x

/-- The sole existence reasons are the immediate actual predecessors of
derivatives. The foundation has none. The necessary law is a separate record
prerequisite, and its truth is never treated as a producing being. -/
def arena (k : Bool) : Arena Bool Being Fact where
  ontic := ontic k
  holds := holds k
  exist := Fact.exists
  explains := fun w r f => enabled k w ∧
    ∃ n, r = .exists (parent n) ∧ f = .exists (.derivative n)
  conjunct := fun g f => g = f

/-- The same ontology with #312 existence-reason tokens and source-indexed
essential requirements. Only derivatives have the base in this nature field.
The essence-to-modality bridge is checked separately for this interpretation. -/
def profile (k : Bool) : Profile Bool Being where
  explanation := {
    ontic := ontic k
    explains := fun w r f => enabled k w ∧
      ∃ n, r = .circumstance (parent n) ∧ f = .fact (.derivative n) }
  InEssence := fun x f => (∃ n, x = .derivative n) ∧ f = .fact .base

/-- The record for derivative n uses the existence of its immediate predecessor
AND the fixed law. A group is a rule record, not another concrete bearer.
`FullSupply` reads ALL contributors and enablers through `allMembers`. -/
def records : Groups Fact Nat where
  contributors := fun n => {f | f = .exists (parent n)}
  enablers := fun _ => {f | f = .law}
  effect := fun n => .exists (.derivative n)
  admitted := fun _ => True

/-- One expressly permitted resource policy: the law and the background fact.
Their acceptance is not a claim that either explains its own obtaining. -/
def fixedResources (f : Fact) : Prop := f = .law ∨ f = .exists .background

/-- The rival may also admit the actual base existence as a primitive resource.
This restores derivability without supplying a reason for that existence. -/
def withBase (f : Fact) : Prop := fixedResources f ∨ f = .exists .base

/-- All existence facts whose bearers require the base in this model. This is
not the set of facts lacking proximate reasons: every derivative has one. -/
def baseDependent : Set Fact :=
  {f | f = .exists .base ∨ ∃ n, f = .exists (.derivative n)}

end Contained

/-- Unbounded but finitely layered contained control, in two modal overlays.
For each overlay: the law and background hold everywhere; the same base
existence fixes every bearer's existence profile; every derivative has an
actual reason and an existing distinct cause wherever it exists; all records
are actually available and truth preserving. The base has no reason. No
derivative is derivable from fixedResources, while each is derivable once the
base is admitted. The last implication extracts the actual base and law from
ANY derivation that admits no derivative as a primitive leaf. It therefore
exposes the resource used, not an undefined adequacy premise. -/
def ResourceInheritance : Prop :=
  (∀ k, (∀ w, (Contained.arena k).holds w .law ∧
      (Contained.arena k).ontic.ExistsAt w .background) ∧
    Coherent (Contained.arena k) ∧ Factive (Contained.arena k) ∧
    (∀ w v, ((Contained.arena k).ontic.ExistsAt w .base ↔
      (Contained.arena k).ontic.ExistsAt v .base) → ∀ b,
      (Contained.arena k).ontic.ExistsAt w b ↔ (Contained.arena k).ontic.ExistsAt v b) ∧
    ActualResources (Contained.arena k) false Contained.records ∧
    RulesPreserveTruth (Contained.arena k) false Contained.records ∧
    ¬ Explained (Contained.arena k) false (.exists .base) ∧
    (∀ n, Explained (Contained.arena k) false (.exists (.derivative n))) ∧
    (∀ w n, (Contained.arena k).ontic.ExistsAt w (.derivative n) →
      ∃ c, (Contained.arena k).ontic.ExistsAt w c ∧ c ≠ .derivative n ∧
        (Contained.arena k).ontic.Causes w c (.derivative n))) ∧
  Trap (allMembers Contained.records) Contained.fixedResources Contained.baseDependent ∧
  (∀ n, ¬ FullSupply Contained.records Contained.fixedResources (.exists (.derivative n))) ∧
  (∀ n, FullSupply Contained.records Contained.withBase (.exists (.derivative n))) ∧
  (∀ (S : Contained.Fact → Prop), (∀ n, ¬ S (.exists (.derivative n))) →
    ∀ n, FullSupply Contained.records S (.exists (.derivative n)) →
      S (.exists .base) ∧ S .law) ∧
  EssenceAbsenceBridge (Contained.profile false) false ∧
  ContingentAt (Contained.ontic false) false .base ∧
  (∀ n, ContingentAt (Contained.ontic false) false (.derivative n)) ∧
  (∀ n, ¬ (Contained.ontic false).ExistsAt true (.derivative n)) ∧
  NecessaryAt (Contained.ontic true) false .base ∧
  (∀ n, NecessaryAt (Contained.ontic true) false (.derivative n))

namespace Replacement

inductive Being | background | base | alternative | target deriving DecidableEq

/-- The target and background exist in both worlds; its contingent immediate
source is base at false and alternative at true. This is replacement across
whole worlds, not spontaneous entry into the actual world. -/
def present (w : Bool) : Being → Prop
  | .background | .target => True
  | .base => w = false
  | .alternative => w = true

def source : Bool → Being | false => .base | true => .alternative

def profile : Profile Bool Being where
  explanation := {
    ontic := {
      frame := ⟨fun _ _ => True⟩
      ExistsAt := present
      Causes := fun w c x => c = source w ∧ x = .target }
    explains := fun w r f => r = .circumstance (source w) ∧ f = .fact .target }
  InEssence := fun _ _ => False

end Replacement

/-- Populated omission control. A contingent base really is the selected
actual cause and existence-reason source for the same target, which exists
necessarily and has an existing cause at every world. The target does not
modally require that base. Necessary co-presence in the earlier directedNature
control is reused and remains different from source-indexed essence. -/
def ReplacementBoundary : Prop :=
  ContingentAt Replacement.profile.explanation.ontic false .base ∧
  Replacement.profile.explanation.ontic.Causes false .base .target ∧
  Replacement.profile.explanation.explains false (.circumstance .base) (.fact .target) ∧
  NecessaryAt Replacement.profile.explanation.ontic false .target ∧
  (∀ w, Replacement.profile.explanation.ontic.ExistsAt w .background ∧
    ∃ c, Replacement.profile.explanation.ontic.ExistsAt w c ∧ c ≠ .target ∧
      Replacement.profile.explanation.ontic.Causes w c .target) ∧
  ¬ ModalRequiresExistence Replacement.profile false .target .base ∧
  ModalRequiresExistence directedNature false false true ∧
  ModalRequiresExistence directedNature false true false ∧
  EssenceRequiresExistence directedNature false true ∧
  ¬ EssenceRequiresExistence directedNature true false

end TruthCore.Explanation.ExistentialInheritance
