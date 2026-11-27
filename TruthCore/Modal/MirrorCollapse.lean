module

public import TruthCore.Modal.SimplicityCollapse
public import TruthCore.Modal.ModalGrounding
public import TruthCore.Causality.ContingentBeingNode
public import TruthCore.Causality.RootPurity
public import TruthCore.Causality.RootPerfectionIntellect
public import TruthCore.Explanation.BruteContingencyParity

/-!
# The relation-of-reason account and the mirror-world rule (#2145, lane M; #555)

Analyst formulations, attribution deferred. Nothing here is attributed to
Aquinas, Leibniz, Clarke, Kant or Spinoza; their names in the note are
navigation only. Every model is a finite structural surrogate: it witnesses a
stated formal interpretation, never a metaphysical possibility.

**A. The relation-of-reason (extrinsic-decree) account.** #2174 (premise lane E)
and lane P found that the personal case's own premises commit the classical root
to this account of its contingent willing: its free selection adds no real
intrinsic determination. Here it is stated on #462's `OutputProfile` together
with a world-indexed intrinsic profile `Has : W → B → D → Prop` (the lane-E
reading: `Has v g d` says that `g` really has the determination `d` at `v`):

* the bearer's intrinsic profile is the same at every accessible world
  (`IntrinsicProfileInvariant`);
* one real determination of the bearer carries the act (`ActCarriedBy`): wherever
  the bearer has it, the act is performed;
* the act's actual terminus is the effect (`p.output w a x`); a terminus exists
  wherever it is a terminus;
* the effect is contingent.

"Explained by the act without being an intrinsic variable" is then a pair of
checkable notions. A world-predicate `e` is `IntrinsicTo` the bearer when worlds
at which the bearer has the same determinations agree on `e`. It
`Discriminates` an explanandum `E` at `w` when it holds at `w` and fails at every
accessible world where `E` fails (contrast relevance).

**B. The mirror-world rule.** A world map `σ` (the global mirror) and a world
feature `H` (global handedness). ESSENCE_5 (`ModalGrounding.EssentialTruth`,
Fine's `□ₓ φ` over world-propositions) is the grain at which a nature constrains
worlds. Four premises: essence-grounded possibility at the world level (every
world violating no essential truth is accessible), factivity at the actual
world, preservation of the actual world's essential truths by the mirror, and
reversal of handedness by the mirror. A necessitarian who keeps all four
contradicts actual modal collapse (`RouteCollapsedAt`); denying each premise is
one of the brief's options (non-qualitative nature; no distinct mirror image;
brute impossibility). With a fifth premise, a chiral individual at the mirror
image (`ChiralAtMirrorImageAt`), the same four give a contingent actual concrete
being (`SomeActualContingentAt`), so they also press concrete necessitarianism.
The registered argument takes the mirror in sense MIRROR_2 (CPT conjugation,
`CPTConjugation`); MIRROR_1 (spatial reflection P, `SpatialReflection`) is a
distinct type.
-/

@[expose] public section

namespace TruthCore.Modal.MirrorCollapse

open TruthCore.German.Kant.CosmologicalInference (Ontic ContingentAt)
open TruthCore.Modal.SelectedEffectBridge (OutputProfile SameActEverywhere)
open TruthCore.Modal.ModalGrounding (EssentialTruth)

variable {W B A D : Type}

/-! ## A. Intrinsic invariance, contrast relevance and the relation-of-reason account -/

/-- The bearer `g` has the same real intrinsic determinations at every world
accessible from `w` as at `w`. Stronger than lane E's N (`906f9077`), which
gives only the direction from an accessible world to `w`: N keeps the root's
absences fixed and lets it lack at `v` what it has at `w`. -/
def IntrinsicProfileInvariant (o : Ontic W B) (Has : W → B → D → Prop) (w : W) (g : B) :
    Prop :=
  ∀ v, o.frame.access w v → ∀ d, Has v g d ↔ Has w g d

/-- The world-predicate `e` is intrinsic to `g` from `w`: at each accessible world
at which `g` has exactly its determinations at `w`, `e` agrees with its value at
`w`. An intrinsic fact about `g` varies only with `g`'s determinations. -/
def IntrinsicTo (o : Ontic W B) (Has : W → B → D → Prop) (w : W) (g : B) (e : W → Prop) :
    Prop :=
  ∀ v, o.frame.access w v → (∀ d, Has v g d ↔ Has w g d) → (e v ↔ e w)

/-- `e` discriminates the explanandum `E` at `w` (contrast relevance): `e` holds at
`w` and fails at every accessible world at which `E` fails. A reason that
discriminates explains why `E` rather than its absence in the contrastive sense
of #750's `ContrastRelevant`, stated here for one world-predicate. -/
def Discriminates (o : Ontic W B) (w : W) (E e : W → Prop) : Prop :=
  e w ∧ ∀ v, o.frame.access w v → ¬ E v → ¬ e v

/-- The act `a` is carried by the bearer's real determination `d`: the source has
`d` at `w`, and at every accessible world where it has `d` it performs `a`. The
determination-level counterpart of #555's `BeingCarriesAct`. -/
def ActCarriedBy (p : OutputProfile W B A) (Has : W → B → D → Prop) (w : W) (a : A) (d : D) :
    Prop :=
  Has w p.source d ∧ ∀ v, p.ontic.frame.access w v → Has v p.source d → p.performs v a

/-- Every terminus of `a` at an accessible world exists there: the act's output
is real where it is an output. -/
def TerminusSound (p : OutputProfile W B A) (w : W) (a : A) (x : B) : Prop :=
  ∀ v, p.ontic.frame.access w v → p.output v a x → p.ontic.ExistsAt v x

/-- The relation-of-reason (extrinsic-decree) account of the effect `x` of the
source through the act `a` at `w`: the source's intrinsic profile is invariant,
one of its real determinations carries the act, the act's actual terminus is
`x`, every terminus exists, and `x` is contingent. Whether the terminus relation
`p.output` is real in the source is exactly what the account denies; nothing in
the definition makes it a determination of the source. Nothing mentions
intellect: an impersonal permissive propensity whose chance outcome is its
terminus satisfies the same clauses. -/
def RelationOfReasonAt (p : OutputProfile W B A) (Has : W → B → D → Prop) (w : W) (a : A)
    (x : B) : Prop :=
  IntrinsicProfileInvariant p.ontic Has w p.source ∧ (∃ d, ActCarriedBy p Has w a d) ∧
    p.output w a x ∧ TerminusSound p w a x ∧ ContingentAt p.ontic w x

/-- The bearer-level form of lane E's N (`906f9077`, #2174): no world accessible
from `w` gives `g` a real determination it lacks at `w`. Lane E's
`RootAbsencesNecessary` states this for every actual root; this declaration is
its instance at one bearer. -/
def AbsencesNecessaryFor (o : Ontic W B) (Has : W → B → D → Prop) (w : W) (g : B) : Prop :=
  ∀ v, o.frame.access w v → ∀ d, Has v g d → Has w g d

/-- A real decree family: `dec c` is the real intrinsic determination "has decreed
`c`". At most one decree is had by `g` at `w`. -/
def DecreesExclusiveAt {X : Type} (Has : W → B → D → Prop) (w : W) (g : B) (dec : X → D) :
    Prop :=
  ∀ c c', Has w g (dec c) → Has w g (dec c') → c = c'

/-- Wherever accessible `g` has the decree `dec c`, the effect `x` exists. -/
def DecreeSuffices {X : Type} (o : Ontic W B) (Has : W → B → D → Prop) (w : W) (g : B)
    (dec : X → D) (c : X) (x : B) : Prop :=
  ∀ v, o.frame.access w v → Has v g (dec c) → o.ExistsAt v x

/-! ## B. The mirror-world rule -/

/-- OPEN premise (world-level essence-grounded possibility, ESSENCE_5): every world
at which every essential truth of every being holds is accessible from `w`.
Whatever no nature excludes is possible. The world-level counterpart of
`ModalGrounding.EssentialExclusionAccount` (absence of one being). Lane E's EM
(`f6f956a1`, #2174) is a different-grain counterpart over ESSENCE_6 profile
conditions; no ESSENCE_5/ESSENCE_6 bridge is asserted. Powers-based accounts deny
it (a world no nature excludes can lack a power for it). Humean recombination does
not deny it; modal primitivism denies only that possibility is grounded in
essences. -/
def EssenceGroundedWorldPossibility (o : Ontic W B) (w : W)
    (Essential : B → (W → Prop) → Prop) : Prop :=
  ∀ v, (∀ x φ, EssentialTruth Essential x φ → φ v) → o.frame.access w v

/-- OPEN premise (factivity at the actual world): every essential truth of every
being holds at `w`. What lies in a nature is true. It follows from "essence
grounds necessity" on a frame reflexive at `w`. -/
def EssentialTruthsHoldAt (Essential : B → (W → Prop) → Prop) (w : W) : Prop :=
  ∀ x φ, EssentialTruth Essential x φ → φ w

/-- Essence grounds necessity, at the world level and at `w`: every ESSENCE_5 truth
of every being holds at every world accessible from `w`. The `Ontic` counterpart of
`ModalGrounding.EssenceGroundsNecessity` (stated there over a `CausalityFrame`).
With it and reflexivity at `w` factivity follows; with it, essence-grounded
possibility and factivity, preservation by the mirror is equivalent to the mirror
image's accessibility (`pres_iff_mirrorPossible`). -/
def EssenceGroundsNecessityAt (o : Ontic W B) (w : W) (Essential : B → (W → Prop) → Prop) :
    Prop :=
  ∀ x φ, EssentialTruth Essential x φ → ∀ v, o.frame.access w v → φ v

/-- OPEN premise (orientation-free natures, at `w`): every essential truth of every
being that holds at `w` holds at the mirror image `σ w`. No nature contains a
condition that the actual arrangement meets and its mirror image violates. Under
essence grounding necessity, essence-grounded possibility and factivity it is
equivalent to the mirror image's possibility (`pres_iff_mirrorPossible`). For the
plain spatial reflection P it is doubtful on dispositional essentialism: the weak
interaction is not reflection-invariant, so the P-image of the actual world
violates the law-grounding natures of creaturely kinds (option 1 at a creature).
With `σ` read as CPT conjugation, under which local Lorentz-invariant quantum field
theory is invariant, creaturely law-natures give no such violation. -/
def EssentialTruthsPreservedByMirrorAt (Essential : B → (W → Prop) → Prop) (σ : W → W)
    (w : W) : Prop :=
  ∀ x φ, EssentialTruth Essential x φ → φ w → φ (σ w)

/-- OPEN premise (the mirror image is a different arrangement): the feature `H`
(global spatial handedness) holds at the mirror image of `w` exactly when it fails
at `w`. Reflection and CPT conjugation are both intended to reverse spatial
handedness; this premise says that the given map does at `w`.
A relationalist about global orientation, who rejects a global handedness
feature, denies it. Identifying `w` with its mirror image (`σ w = w`) also denies
it; for the CPT map that identity needs more than orientation relationalism:
charge conjugation and time reversal must be identified away as well. -/
def HandednessReversedAt (σ : W → W) (H : W → Prop) (w : W) : Prop :=
  H (σ w) ↔ ¬ H w

/-- OPEN premise (a chiral individual, local to the mirror image): some actual
concrete being exists at the mirror image `σ w` only if `σ w` has the actual
handedness. With reversed handedness it is equivalent to the being's absence from
`σ w`, and the absence implies it. It says nothing about any other world.
Example: an actual molecule, if being of its chemical kind is essential to it and
its only candidate at the mirror image is its mirror counterpart, of another
kind; then it is absent from `σ w`. Under the CPT map the counterpart is made of
antimatter, so charge conjugation alone changes the kind and the absence holds
for achiral material beings too; under the plain reflection only an enantiomer's
reversed handedness changes the kind. A haecceitist who holds that the same
molecule exists at the mirror image (for CPT, as antimatter) denies it. The earlier global form (the being exists only at worlds sharing
the actual handedness) is not supported by this example and is not used. -/
def ChiralAtMirrorImageAt (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B)
    (σ : W → W) (w : W) (H : W → Prop) : Prop :=
  ∃ x, m.concrete x ∧ m.ontic.ExistsAt w x ∧
    (m.ontic.ExistsAt (σ w) x → (H (σ w) ↔ H w))

/-! ### The two mirror senses (DISAMB `MIRROR`)

The generic premises above take any world map `σ`. The registered argument fixes
the sense of the mirror: MIRROR_2, CPT conjugation. MIRROR_1, spatial reflection
P, is recorded as a distinct type so that a statement in one sense cannot be
used for the other. -/

/-- MIRROR_1 (PRIMITIVE): spatial reflection P as a map on worlds. `image v` is `v`
with every spatial arrangement reflected and nothing else changed. Lean fixes only
the type; which features the map preserves is not assumed. Under it, preservation
of essential truths is doubtful on dispositional essentialism, since the weak
interaction is not invariant under P. -/
structure SpatialReflection (W : Type) where
  /-- The P-image of each world. -/
  image : W → W

/-- MIRROR_2 (PRIMITIVE): CPT conjugation as a map on worlds. `image v` is the CPT
conjugate of `v`: spatial reflection, charge conjugation and time reversal
together. Lean fixes only the type; which features the map preserves is not
assumed. Local Lorentz-invariant quantum field theory is invariant under it
(physics background, navigation only). -/
structure CPTConjugation (W : Type) where
  /-- The CPT image of each world. -/
  image : W → W

/-- OPEN premise, MIRROR_2: the CPT image of `w` satisfies every essential truth
`w` satisfies. `EssentialTruthsPreservedByMirrorAt` at the CPT map. -/
def EssentialTruthsPreservedByCPTAt (Essential : B → (W → Prop) → Prop)
    (τ : CPTConjugation W) (w : W) : Prop :=
  EssentialTruthsPreservedByMirrorAt Essential τ.image w

/-- OPEN premise, MIRROR_2: the CPT image of `w` has the opposite handedness.
`HandednessReversedAt` at the CPT map. -/
def HandednessReversedByCPTAt (τ : CPTConjugation W) (H : W → Prop) (w : W) : Prop :=
  HandednessReversedAt τ.image H w

/-- OPEN premise, MIRROR_2: some actual concrete being exists at the CPT image of
`w` only if that image has the actual handedness. `ChiralAtMirrorImageAt` at the
CPT map. -/
def ChiralAtCPTImageAt (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B)
    (τ : CPTConjugation W) (w : W) (H : W → Prop) : Prop :=
  ChiralAtMirrorImageAt m τ.image w H

/-- A rule `ρ` singles out `w` among the worlds that violate no essential truth:
`ρ` holds at `w` and at no other such world. A necessitating selection rule in
the owner's sense. -/
def SelectsAmongUnexcluded (Essential : B → (W → Prop) → Prop) (ρ : W → Prop) (w : W) : Prop :=
  ρ w ∧ ∀ v, (∀ x φ, EssentialTruth Essential x φ → φ v) → ρ v → v = w

/-! ### The orientation token at a root (lane P's mechanism, handedness instance) -/

/-- No admissible profile contains both orientation tokens. -/
def OrientationTokensExclusive (Admissible : Set D → Prop) (left right : D) : Prop :=
  ∀ q, Admissible q → left ∈ q → right ∈ q → False

/-- OPEN sense bridge (ESSENCE_5 to real determinations, carriage of orientation):
if an ESSENCE_5 truth of `r` holds at `w` and fails at the mirror image `σ w` (an
orientation in `r`'s nature), then `r` really has one of the two orientation tokens.
Orientation in a nature is carried by a real determination of its bearer. It is
the orientation instance of the carriage pattern of lane E's LE (#2174), stated
between ESSENCE_5 and `Has`; lane E records no bridge between ESSENCE_5 and its
ESSENCE_6, and none is asserted here beyond this premise. -/
def OrientationInNatureCarried (Essential : B → (W → Prop) → Prop) (Has : B → D → Prop)
    (σ : W → W) (w : W) (left right : D) : Prop :=
  ∀ r φ, EssentialTruth Essential r φ → φ w → ¬ φ (σ w) → Has r left ∨ Has r right

/-- The two orientation tokens are on a par in purity: one is a pure perfection
exactly when the other is. A mirror that preserves every qualitative feature
gives this when purity is qualitative. -/
def OrientationPurityParity (Pure : D → Prop) (left right : D) : Prop :=
  Pure left ↔ Pure right

/-! ## Finite controls

Assignments of the stated relations only. They say nothing about what essence,
orientation, willing, propensity or purity metaphysically are. -/
namespace Control

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.SourceIntellectControls.ProfileControls (Determination pure effect)
open TruthCore.Explanation.ExistencePSR (Reason ExistenceFact)

/-! ### A. The relation-of-reason carrier

Worlds and beings `Bool`; the actual world is `true`. The root `true` exists at
both worlds and has the four pure #1970 determinations at both; the effect
`false` exists only at `true`, is grounded by the root there, and has `esse` and
`noesis` there. Access is universal. The act is `Unit`, performed at both worlds;
its terminus is the effect at `true` only. -/

/-- Universal access; the root at both worlds, the effect at `true` only. -/
def rrOntic : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun v x => x = true ∨ v = true
  Causes := fun v g x => v = true ∧ g = true ∧ x = false

/-- The route profile: both beings concrete, the root grounds the effect at `true`. -/
def rrProfile : Profile Bool Bool where
  ontic := rrOntic
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests the modal and profile structure of the relation-of-reason account, not the concrete/abstract line)
  grounds := fun v g x => v = true ∧ g = true ∧ x = false

/-- The root's one act, performed at both worlds, terminating in the effect at
`true` only. -/
def rrOutput : OutputProfile Bool Bool Unit where
  ontic := rrOntic
  source := true
  performs := fun _ _ => True
  output := fun v _ x => v = true ∧ x = false

/-- Intrinsic profiles: the root has the pure determinations at both worlds; the
effect has `esse` and `noesis` where it exists. -/
def rrHas : Bool → Bool → Determination → Prop
  | _, true, d => d ∈ pure
  | v, false, d => v = true ∧ d ∈ effect

/-- Purity on the carrier: the four pure #1970 determinations. -/
def rrPure (d : Determination) : Prop := d ∈ pure

/-- Ability on the carrier: what each being has, and for the effect also the
impure `limiter`, which it can have and does not (restored creature potency). -/
def rrCanBe (v x : Bool) (d : Determination) : Prop :=
  rrHas v x d ∨ (x = false ∧ d = Determination.limiter)

/-- Potency exactly as the IX.6 reading gives it from `rrCanBe` and `rrHas`: the
effect is in potency to `limiter`; the root is in potency to nothing. -/
def rrPotency (v x : Bool) (d : Determination) : Prop := rrCanBe v x d ∧ ¬ rrHas v x d

/-- The effect is composite (a represented limiting principle); the root is not. -/
def rrComposite (x : Bool) : Prop := x = false

/-- No simple priority. -/
def rrPrior (_ _ : Bool) : Prop := False

/-- One represented essence and esse for both beings. -/
def rrRep (_ : Bool) : Unit := ()

/-- The impure `limiter` requires the lack of `noesis`; nothing else requires a lack. -/
def rrRequiresLack (d : Determination) (S : Set Determination) : Prop :=
  d = Determination.limiter ∧ Determination.noesis ∈ S

/-- Admissible exactly when exclusion-free (member grounding, both directions). -/
def rrAdmissible (q : Set Determination) : Prop :=
  TruthCore.Causality.RootPerfectionIntellect.ExclusionFree rrRequiresLack q

/-- At `true` the root is admitted as a (non-necessitating) reason for the
effect's existence. -/
def rrExplains (v : Bool) (r : Reason Bool) (f : ExistenceFact Bool) : Prop :=
  v = true ∧ r = Reason.circumstance true ∧ f = ExistenceFact.fact false

/-- The #312 explanation model on the carrier. -/
def rrModel : TruthCore.Explanation.ExistencePSR.Model Bool Bool := ⟨rrOntic, rrExplains⟩

/-! ### B. The mirror carrier

Worlds `Bool`, actual world `true`, one concrete being, the mirror `not` (or `id`)
as a `CPTConjugation` value (`cptNot`, `cptId`), and
handedness `H v := v = true`. The three-world carriers add `none`, a world that
no essential truth excludes; the mirror there is `Option.map not`. -/

/-- Universal access. -/
def univAccess (_ _ : Bool) : Prop := True

/-- Only the actual world is accessible. -/
def onlyActual (_ v : Bool) : Prop := v = true

/-- No essential truths. -/
def noEss (_ : Unit) (_ : Bool → Prop) : Prop := False

/-- The one nature contains the orientation "the arrangement is the actual-handed one". -/
def orientedEss (_ : Unit) (φ : Bool → Prop) : Prop := φ = fun v => v = true

/-- The one nature contains an unsatisfiable condition. -/
def absurdEss (_ : Unit) (φ : Bool → Prop) : Prop := φ = fun _ => False

/-- Global handedness: the actual-handed arrangement. -/
def handed (v : Bool) : Prop := v = true

/-- One concrete being present only at the actual world, under the supplied access. -/
def cProfile (acc : Bool → Bool → Prop) : Profile Bool Unit where
  ontic := ⟨⟨acc⟩, fun v _ => v = true, fun _ _ _ => False⟩
  concrete := fun _ => True  -- category-constant: intended (one stipulated concrete being; the model tests modal structure, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- One concrete being present at both worlds, universal access. -/
def fixedProfile : Profile Bool Unit where
  ontic := ⟨⟨univAccess⟩, fun _ _ => True, fun _ _ _ => False⟩
  concrete := fun _ => True  -- category-constant: intended (one stipulated concrete being; the model tests modal structure, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- Three worlds, only the two arrangements accessible, one concrete being
present where `ex` holds. -/
def threeProfile (ex : Option Bool → Prop) : Profile (Option Bool) Unit where
  ontic := ⟨⟨fun _ v => v ≠ none⟩, fun v _ => ex v, fun _ _ _ => False⟩
  concrete := fun _ => True  -- category-constant: intended (one stipulated concrete being; the model tests modal structure, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- Three worlds, universal access, one concrete being present where `ex` holds. -/
def threeUnivProfile (ex : Option Bool → Prop) : Profile (Option Bool) Unit where
  ontic := ⟨⟨fun _ _ => True⟩, fun v _ => ex v, fun _ _ _ => False⟩
  concrete := fun _ => True  -- category-constant: intended (one stipulated concrete being; the model tests modal structure, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- The mirror `not` on the two-world carrier, as a CPT map. -/
def cptNot : CPTConjugation Bool := ⟨not⟩

/-- The identity as a CPT map (option 2: the mirror image is the world itself). -/
def cptId : CPTConjugation Bool := ⟨id⟩

/-- The mirror on the three-world carrier, as a CPT map. -/
def cpt3 : CPTConjugation (Option Bool) := ⟨Option.map not⟩

/-- No essential truths on the three-world carrier. -/
def noEss3 (_ : Unit) (_ : Option Bool → Prop) : Prop := False

/-- Handedness on the three-world carrier. -/
def handed3 (v : Option Bool) : Prop := v = some true

end Control

/-! ## Certificates -/

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ContingentBeingNode (RouteCollapsedAt RouteNotCollapsedAt
  SomeActualContingentAt)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple
  UnlimitedDeterminationsArePure)
open TruthCore.Causality.RootPerfectionIntellect (ExclusionFreeAdmissible
  AdmissibleIsExclusionFree PureRequiresNoPureLack)
open TruthCore.Modal.SimplicityCollapse (StrictEfficacy)
open TruthCore.Explanation.BruteContingencyParity (NoBruteContingentExistenceAt)
open Control

/-- The relation-of-reason account: its exact cost, and its consistency with the
personal case's intrinsic-profile premises.

1. **Cost.** On the account the act is performed at every accessible world and
   does not strictly suffice for the effect (#555's nonnecessitating necessary
   act); no fact intrinsic to the source discriminates the effect's presence from
   its absence; the act's terminus does discriminate it, and is not intrinsic to
   the source. So no intrinsic fact carries the contrast; the terminus does.
2. **Real decree under N.** A real decree family that is exclusive at `w`: for any
   bearer meeting lane E's necessity condition N at `w` (for instance an actual
   root), every decree of the family that the bearer has at an accessible world is
   its actual one. If moreover the actual decree suffices for the effect, the
   effect is contingent only if some accessible world lacking it has no decree of
   the family. With a decree of the family at every accessible world the effect is
   not contingent.
3. **Joint model.** On `rr…`, the account holds together with RootPurity
   (`c78c77da`), `a30c5963`, N at the root (`AbsencesNecessaryFor`), the
   requirement-form premises (`0c8631bd`, the
   sufficiency direction and the necessity direction of member grounding), the
   existential PSR for contingents (`608a262d`), some actual contingent concrete
   being (`c94b5446`), the failure of actual collapse (`185ce448`), and #555's
   root-route readings at the actual world (the Metaphysics IX.6 potency
   reading, `IsImmutable` and `ModalCapacity`, with ability read as act). -/
def RelationOfReasonCertificate : Prop :=
  (∀ (W B A D : Type) (p : OutputProfile W B A) (Has : W → B → D → Prop) (w : W) (a : A)
      (x : B), RelationOfReasonAt p Has w a x →
    SameActEverywhere p w a ∧ ¬ StrictEfficacy p w a x ∧
    (∀ e, IntrinsicTo p.ontic Has w p.source e →
      ¬ Discriminates p.ontic w (fun v => p.ontic.ExistsAt v x) e) ∧
    Discriminates p.ontic w (fun v => p.ontic.ExistsAt v x) (fun v => p.output v a x) ∧
    ¬ IntrinsicTo p.ontic Has w p.source (fun v => p.output v a x)) ∧
  (∀ (W B D X : Type) (o : Ontic W B) (Has : W → B → D → Prop) (w : W) (g : B)
      (dec : X → D) (c : X),
    AbsencesNecessaryFor o Has w g → DecreesExclusiveAt Has w g dec → Has w g (dec c) →
    ∀ v, o.frame.access w v → ∀ c', Has v g (dec c') → c' = c) ∧
  (∀ (W B D X : Type) (o : Ontic W B) (Has : W → B → D → Prop) (w : W) (g x : B)
      (dec : X → D) (c : X),
    AbsencesNecessaryFor o Has w g → DecreesExclusiveAt Has w g dec → Has w g (dec c) →
    DecreeSuffices o Has w g dec c x → ContingentAt o w x →
    ∃ v, o.frame.access w v ∧ ¬ o.ExistsAt v x ∧ ∀ c', ¬ Has v g (dec c')) ∧
  (RelationOfReasonAt rrOutput rrHas true () false ∧
    UnlimitedDeterminationsArePure rrComposite rrPrior rrRep rrRep (rrHas true) rrPure ∧
    ActualRootsWithoutLimitingPrinciple rrProfile true rrComposite rrPrior rrRep rrRep ∧
    PureRequiresNoPureLack rrRequiresLack rrPure ∧
    ExclusionFreeAdmissible rrAdmissible rrRequiresLack ∧
    AdmissibleIsExclusionFree rrAdmissible rrRequiresLack ∧
    NoBruteContingentExistenceAt rrModel true ∧
    SomeActualContingentAt rrProfile true ∧ RouteNotCollapsedAt rrOntic true ∧
    TruthCore.Modal.SimplicityCollapse.ReadingsAt rrOntic rrHas rrPotency rrCanBe true true ∧
    (∃ d, rrPotency true false d) ∧
    AbsencesNecessaryFor rrOntic rrHas true true ∧
    (∀ r, ActualRoot rrProfile true r ↔ r = true))

/-- The mirror fork for a necessitarian, and what the mirror case says of every
account.

1. **Collapse with essence-grounded possibility, restated.** Under actual
   collapse and world-level essence-grounded possibility, every world violating
   no essential truth is the actual world. This is one term from the two
   premises; a necessitarian who holds both already asserts it, so it records no
   further cost.
2. **Option 1 is exact.** Under collapse, essence-grounded possibility,
   factivity and reversed handedness, some essential truth holds at the actual
   world and fails at its mirror image.
3. **Option 3 is exact.** Under collapse, factivity, preservation and reversed
   handedness, the mirror image violates no essential truth and is not accessible.
4. **Option 2 is exact.** Under collapse, essence-grounded possibility,
   factivity and preservation, the mirror image is the actual world, so no
   feature is reversed by the mirror. The identity is derived from these four
   premises, not from relationalism about orientation; for the CPT map it needs
   charge conjugation and time reversal identified away too.
5. **Rules.** A rule that singles out the actual world among the worlds violating
   no essential truth, applied where the mirror image violates none, holds at the
   actual world and fails at its mirror image when handedness is reversed: a
   necessitating rule is itself not mirror-invariant.
6. **Contrast gap for every invariant source.** If a source's intrinsic profile is
   invariant and the mirror image is accessible, no fact intrinsic to the source
   discriminates any explanandum true at the actual world and false at its
   mirror image (handedness either way).
7. **An orientation token at a root.** Under `a30c5963`, RootPurity, the
   sufficiency direction, `0c8631bd`, exclusivity of the two orientation tokens
   and their parity in purity, no actual root has either token. This concerns
   real determinations (`Has`), not ESSENCE_5 truths.
8. **Concrete necessitarianism.** If every actual concrete being is necessary,
   and some actual concrete being is chiral at the mirror image, then with factivity, preservation and
   reversed handedness, world-level essence-grounded possibility fails: the
   concrete necessitarian, not only the full-collapse necessitarian, must take
   one of the fork's options (or deny the chiral individual).
9. **Preservation is the mirror's possibility.** Under essence grounding
   necessity at `w`, essence-grounded possibility and factivity, preservation by
   the mirror holds exactly when the mirror image is accessible.
10. **Option 1 at a root, through the carriage bridge.** With clause 7's
    premises and the open bridge `OrientationInNatureCarried`, no ESSENCE_5 truth
    of an actual root holds at `w` and fails at its mirror image. Without the
    bridge, clause 7 says nothing about orientation in a root's nature. -/
def MirrorForkCertificate : Prop :=
  (∀ (W B : Type) (o : Ontic W B) (w : W) (E : B → (W → Prop) → Prop),
    RouteCollapsedAt o w → EssenceGroundedWorldPossibility o w E →
    ∀ v, (∀ x φ, EssentialTruth E x φ → φ v) → v = w) ∧
  (∀ (W B : Type) (o : Ontic W B) (w : W) (E : B → (W → Prop) → Prop) (σ : W → W)
      (H : W → Prop),
    RouteCollapsedAt o w → EssenceGroundedWorldPossibility o w E → EssentialTruthsHoldAt E w →
    HandednessReversedAt σ H w → ∃ x φ, EssentialTruth E x φ ∧ φ w ∧ ¬ φ (σ w)) ∧
  (∀ (W B : Type) (o : Ontic W B) (w : W) (E : B → (W → Prop) → Prop) (σ : W → W)
      (H : W → Prop),
    RouteCollapsedAt o w → EssentialTruthsHoldAt E w → EssentialTruthsPreservedByMirrorAt E σ w →
    HandednessReversedAt σ H w →
    ¬ o.frame.access w (σ w) ∧ ∀ x φ, EssentialTruth E x φ → φ (σ w)) ∧
  (∀ (W B : Type) (o : Ontic W B) (w : W) (E : B → (W → Prop) → Prop) (σ : W → W),
    RouteCollapsedAt o w → EssenceGroundedWorldPossibility o w E → EssentialTruthsHoldAt E w →
    EssentialTruthsPreservedByMirrorAt E σ w →
    σ w = w ∧ ∀ H : W → Prop, ¬ HandednessReversedAt σ H w) ∧
  (∀ (W B : Type) (w : W) (E : B → (W → Prop) → Prop) (σ : W → W) (H ρ : W → Prop),
    SelectsAmongUnexcluded E ρ w → (∀ x φ, EssentialTruth E x φ → φ (σ w)) →
    HandednessReversedAt σ H w → ρ w ∧ ¬ ρ (σ w)) ∧
  (∀ (W B D : Type) (o : Ontic W B) (Has : W → B → D → Prop) (w : W) (g : B) (σ : W → W),
    IntrinsicProfileInvariant o Has w g → o.frame.access w (σ w) →
    ∀ Ex e, Ex w → ¬ Ex (σ w) → IntrinsicTo o Has w g e → ¬ Discriminates o w Ex e) ∧
  (∀ (W B D P : Type) (m : Profile W B) (w : W) (Admissible : Set D → Prop)
      (RequiresLack : D → Set D → Prop) (Has : B → D → Prop) (Pure : D → Prop)
      (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P) (left right : D),
    ActualRootsWithoutLimitingPrinciple m w Composite Prior essence esse →
    UnlimitedDeterminationsArePure Composite Prior essence esse Has Pure →
    ExclusionFreeAdmissible Admissible RequiresLack → PureRequiresNoPureLack RequiresLack Pure →
    OrientationTokensExclusive Admissible left right → OrientationPurityParity Pure left right →
    ∀ r, ActualRoot m w r → ¬ Has r left ∧ ¬ Has r right) ∧
  (∀ (W B : Type) (m : Profile W B) (w : W) (E : B → (W → Prop) → Prop) (σ : W → W)
      (H : W → Prop),
    TruthCore.Causality.ContingentBeingNode.EveryActualConcreteNecessaryAt m w →
    EssentialTruthsHoldAt E w → EssentialTruthsPreservedByMirrorAt E σ w →
    HandednessReversedAt σ H w → ChiralAtMirrorImageAt m σ w H →
    ¬ EssenceGroundedWorldPossibility m.ontic w E) ∧
  (∀ (W B : Type) (o : Ontic W B) (w : W) (E : B → (W → Prop) → Prop) (σ : W → W),
    EssenceGroundsNecessityAt o w E → EssenceGroundedWorldPossibility o w E →
    EssentialTruthsHoldAt E w →
    (EssentialTruthsPreservedByMirrorAt E σ w ↔ o.frame.access w (σ w))) ∧
  (∀ (W B D P : Type) (m : Profile W B) (w : W) (Admissible : Set D → Prop)
      (RequiresLack : D → Set D → Prop) (Has : B → D → Prop) (Pure : D → Prop)
      (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P) (left right : D)
      (E : B → (W → Prop) → Prop) (σ : W → W),
    ActualRootsWithoutLimitingPrinciple m w Composite Prior essence esse →
    UnlimitedDeterminationsArePure Composite Prior essence esse Has Pure →
    ExclusionFreeAdmissible Admissible RequiresLack → PureRequiresNoPureLack RequiresLack Pure →
    OrientationTokensExclusive Admissible left right → OrientationPurityParity Pure left right →
    OrientationInNatureCarried E Has σ w left right →
    ∀ r, ActualRoot m w r → ∀ φ, EssentialTruth E r φ → φ w → φ (σ w))

/-- Controls for the chiral mirror argument (the companion of
`contingentFromChiralMirror`). `P1`…`P5` are essence-grounded possibility,
factivity, preservation, reversal and a chiral individual at the mirror image,
all at the actual world and, for the mirror, in sense MIRROR_2 (the CPT map
`cptNot`, `cptId` or `cpt3`; the identity map in rows 3 and 8); `C` is that some
actual concrete being is contingent.

* Row 0: all five premises and `C` (universal access, no essential truths, the
  one being present only at the actual world).
* Rows 1–5, one premise deleted, the other four kept, `C` fails (the being is
  necessary):
  1. a nature containing the orientation (option 1): preservation fails;
  2. no essential truths, only the actual world accessible (option 3, brute):
     essence-grounded possibility fails;
  3. the mirror is the identity (option 2): reversal fails;
  4. an unsatisfiable essential truth: factivity fails;
  5. the being present at both worlds: no chiral individual.
* Rows 6–10: one premise deleted, the other four kept, and `C` still holds:
  6. the oriented nature with universal access (preservation fails);
  7. three worlds, an unexcluded inaccessible world (possibility fails);
  8. the identity mirror with universal access (reversal fails);
  9. the unsatisfiable essential truth with universal access (factivity fails);
  10. three worlds, the being present at the actual world and at its mirror
      image, absent at the unexcluded world `none` (no chiral individual at the
      mirror image).
  Rows 6 and 9 violate essence grounding necessity (`EssenceGroundsNecessityAt`),
  which is the source of factivity. Under that principle, essence-grounded
  possibility and factivity, preservation is equivalent to the accessibility of
  the mirror image (`pres_iff_mirrorPossible`, fork clause 9), so the argument's
  load is the possibility of the mirror world; these rows do not show otherwise. -/
def MirrorControls : Prop :=
  -- row 0
  (EssenceGroundedWorldPossibility (cProfile univAccess).ontic true noEss ∧
    EssentialTruthsHoldAt noEss true ∧ EssentialTruthsPreservedByCPTAt noEss cptNot true ∧
    HandednessReversedByCPTAt cptNot handed true ∧ ChiralAtCPTImageAt (cProfile univAccess) cptNot true handed ∧
    SomeActualContingentAt (cProfile univAccess) true) ∧
  -- row 1
  (EssenceGroundedWorldPossibility (cProfile onlyActual).ontic true orientedEss ∧
    EssentialTruthsHoldAt orientedEss true ∧
    ¬ EssentialTruthsPreservedByCPTAt orientedEss cptNot true ∧
    HandednessReversedByCPTAt cptNot handed true ∧ ChiralAtCPTImageAt (cProfile onlyActual) cptNot true handed ∧
    ¬ SomeActualContingentAt (cProfile onlyActual) true) ∧
  -- row 2
  (¬ EssenceGroundedWorldPossibility (cProfile onlyActual).ontic true noEss ∧
    EssentialTruthsHoldAt noEss true ∧ EssentialTruthsPreservedByCPTAt noEss cptNot true ∧
    HandednessReversedByCPTAt cptNot handed true ∧ ChiralAtCPTImageAt (cProfile onlyActual) cptNot true handed ∧
    ¬ SomeActualContingentAt (cProfile onlyActual) true) ∧
  -- row 3
  (EssenceGroundedWorldPossibility (cProfile onlyActual).ontic true orientedEss ∧
    EssentialTruthsHoldAt orientedEss true ∧
    EssentialTruthsPreservedByCPTAt orientedEss cptId true ∧
    ¬ HandednessReversedByCPTAt cptId handed true ∧ ChiralAtCPTImageAt (cProfile onlyActual) cptId true handed ∧
    ¬ SomeActualContingentAt (cProfile onlyActual) true) ∧
  -- row 4
  (EssenceGroundedWorldPossibility (cProfile onlyActual).ontic true absurdEss ∧
    ¬ EssentialTruthsHoldAt absurdEss true ∧
    EssentialTruthsPreservedByCPTAt absurdEss cptNot true ∧
    HandednessReversedByCPTAt cptNot handed true ∧ ChiralAtCPTImageAt (cProfile onlyActual) cptNot true handed ∧
    ¬ SomeActualContingentAt (cProfile onlyActual) true) ∧
  -- row 5
  (EssenceGroundedWorldPossibility fixedProfile.ontic true noEss ∧
    EssentialTruthsHoldAt noEss true ∧ EssentialTruthsPreservedByCPTAt noEss cptNot true ∧
    HandednessReversedByCPTAt cptNot handed true ∧ ¬ ChiralAtCPTImageAt fixedProfile cptNot true handed ∧
    ¬ SomeActualContingentAt fixedProfile true) ∧
  -- row 6
  (EssenceGroundedWorldPossibility (cProfile univAccess).ontic true orientedEss ∧
    EssentialTruthsHoldAt orientedEss true ∧
    ¬ EssentialTruthsPreservedByCPTAt orientedEss cptNot true ∧
    HandednessReversedByCPTAt cptNot handed true ∧ ChiralAtCPTImageAt (cProfile univAccess) cptNot true handed ∧
    SomeActualContingentAt (cProfile univAccess) true) ∧
  -- row 7
  (¬ EssenceGroundedWorldPossibility (threeProfile fun v => v = some true).ontic (some true)
      noEss3 ∧
    EssentialTruthsHoldAt noEss3 (some true) ∧
    EssentialTruthsPreservedByCPTAt noEss3 cpt3 (some true) ∧
    HandednessReversedByCPTAt cpt3 handed3 (some true) ∧
    ChiralAtCPTImageAt (threeProfile fun v => v = some true) cpt3 (some true) handed3 ∧
    SomeActualContingentAt (threeProfile fun v => v = some true) (some true)) ∧
  -- row 8
  (EssenceGroundedWorldPossibility (cProfile univAccess).ontic true noEss ∧
    EssentialTruthsHoldAt noEss true ∧ EssentialTruthsPreservedByCPTAt noEss cptId true ∧
    ¬ HandednessReversedByCPTAt cptId handed true ∧ ChiralAtCPTImageAt (cProfile univAccess) cptId true handed ∧
    SomeActualContingentAt (cProfile univAccess) true) ∧
  -- row 9
  (EssenceGroundedWorldPossibility (cProfile univAccess).ontic true absurdEss ∧
    ¬ EssentialTruthsHoldAt absurdEss true ∧
    EssentialTruthsPreservedByCPTAt absurdEss cptNot true ∧
    HandednessReversedByCPTAt cptNot handed true ∧ ChiralAtCPTImageAt (cProfile univAccess) cptNot true handed ∧
    SomeActualContingentAt (cProfile univAccess) true) ∧
  -- row 10
  (EssenceGroundedWorldPossibility (threeUnivProfile fun v => v ≠ none).ontic (some true)
      noEss3 ∧
    EssentialTruthsHoldAt noEss3 (some true) ∧
    EssentialTruthsPreservedByCPTAt noEss3 cpt3 (some true) ∧
    HandednessReversedByCPTAt cpt3 handed3 (some true) ∧
    ¬ ChiralAtCPTImageAt (threeUnivProfile fun v => v ≠ none) cpt3 (some true) handed3 ∧
    SomeActualContingentAt (threeUnivProfile fun v => v ≠ none) (some true))

end TruthCore.Modal.MirrorCollapse
