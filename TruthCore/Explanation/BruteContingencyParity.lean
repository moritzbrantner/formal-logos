module

public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Causality.GradedSupportFoundation
public import TruthCore.Explanation.NoBruteExistence
public import TruthCore.Explanation.StoppingPoints

/-!
# Brute contingency and the parity of brute-existence demands (B2)

Analyst formulations, attribution deferred. The target is the open bridge B2 of
`TruthCore.Causality.FirstMoverNecessity` (`ContingentHasDistinctEsseCause`):
every being contingent at `w` has a distinct cause of its esse (CAUSE_2). Its
strongest standing rival is brute contingency: a contingent being whose
existence has neither a cause of its esse nor any reason.

Three parts, all over existing vocabulary.

* **Two further support options for B2 on the shared frame.** (i) The #312
  reason tokens (`ExistencePSR.Model`, `Reason.intrinsic`/`circumstance`) on
  the frame's own existence: a local existence PSR for contingents, the bridge
  that no reason for a contingent being's existence is about that being itself,
  and the bridge that the distinct source of such a reason causes its esse
  together give B2. (ii) The selected-grounding closure, the existing bridge
  from actual grounding to a distinct esse-cause, and the interface that
  contingents are concrete give B2.
* **The rival at matching scope.** `BruteContingentBeingAt`: on the same frame
  and world, some contingent being has no distinct esse-cause and no reason.
* **The parity argument (owner direction 2026-11-23, refined the same day).** A
  #756 stance extended by an ONTIC demand (`requiresWhy`: a reason why the fact
  obtains, as against `Stance.demands`, a reason to accept it;
  DISAMB-REASON-EPISTEMIC-ONTIC). If the stance requires a reason why `t`
  obtains, requires reasons uniformly in a feature `k`, and `t` and `o` agree on
  `k`, it cannot meet its demand while accepting `o` as a brute contingent truth
  (`ExcludesBruteRival`). The stronger sibling (`ExcludesUnreasonedAcceptance`)
  drops contingency: under the same premises the stance cannot accept `o` with
  no reason at all. Only the sibling is symmetric: it binds a naturalist who
  rejects an unreasoned God (God's existence as a mere brute fact, in the
  owner's wording; DISAMB-BRUTE-TERMINAL-UNREASONED calls a necessary fact with
  no reason unreasoned, not brute) and a theist who rejects unreasoned
  contingents alike. With unreasoned existence rejected on both sides, the
  question becomes comparative. The scene lists, as scene-relative tallies,
  which existents each picture leaves unexplained (many diverse contingents, one
  contingent state, one necessary base, God); the tallies rank nothing by
  themselves (the #746 count control: a bare count favours copying reasons). A
  general law shows that factive, well-founded reasons always leave some truth
  unexplained, so a picture with none needs reasons that are not well-founded:
  a self-reason, a circle or an infinite chain. In the scene it is a
  self-reason at the terminus ("existence by its own nature"), for God or for a
  necessary physical base alike; circles and endless regresses of contingents
  are not in the scene (named gap).
* **Evidence is not explanation.** An inquiry can support the existence of the
  contingent foundation (an epistemic reason to accept it) while the foundation
  has no reason why it exists (`Inquiry.supports` versus `Arena.explains`). An
  evidential stance therefore gains no ontic explanation from its evidence and
  is not an exit from the comparison; whether there is evidence for God is a
  separate question that this argument does not answer.

A new structure `WhyStance` is needed because #756's `Stance.demands` is
epistemic, and reusing it for the ontic demand would equivocate. The #756
standings `Uniform`, `Selective` and `Restricted` are reused unchanged through
`whyView`, which presents the ontic demand in the demand slot: those standings
use no property of the demanded relation.

Models are finite analyst-built interpretations: logical boundaries, not
metaphysical possibility, and no stance is attributed to any person.
See `docs/notes/psr-self-application-756.md`, "Brute contingency and parity".
-/

@[expose] public section

namespace TruthCore.Explanation.BruteContingencyParity

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FirstMoverNecessity (ContingentHasDistinctEsseCause
  ContingentHasDistinctEsse groundProfile)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.Causality.GradedSupportFoundation (ActualGroundIsDistinctEsseCause)
open TruthCore.Explanation.ExistencePSR (Model Reason ExistenceFact)
open TruthCore.Explanation.PSRStrength (Arena Access Contingent Explained
  IrreflexiveContingent basic everywhere)
open TruthCore.Explanation.PSRSelfApplication (Stance BruteAt)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-! ## Part 1: reasons for existence on the shared frame -/

section Frame

variable {W B T R : Type}

/-- The #312 explanation model on the frame's own world-relative existence:
`explains w r (.fact x)` says that at `w` the reason token `r` is admitted as a
reason why `x` exists. Only the reason relation is added; the frame's
existence, accessibility and causes are unchanged. -/
def reasonModel (F : CausalityFrame W B T R)
    (explains : W → Reason B → ExistenceFact B → Prop) : Model W B :=
  ⟨F.history.ontic, explains⟩

/-- The being a reason token is about: the bearer of an intrinsic token (its
own nature) or the being of a circumstantial token. -/
def source : Reason B → B
  | .intrinsic z => z
  | .circumstance y => y

/-- OPEN, the local existence PSR for contingents: every being contingent at
`w` has some reason for its existence at `w`. It is the contingent-only,
single-world weakening of `NoBruteExistenceAt` (which covers necessary
existents too), and says nothing about what kind of reason. -/
def NoBruteContingentExistenceAt (m : Model W B) (w : W) : Prop :=
  ∀ x, ContingentAt m.ontic w x → ∃ r, m.explains w r (.fact x)

/-- OPEN bridge (BX1): no reason at `w` for the existence of a being contingent
at `w` is about that being itself, whether by its own nature (an intrinsic
token, NECESSARY_EXISTENCE_BY_OWN_NATURE_4) or by itself as a circumstance.
The being-level form of contingent irreflexivity. -/
def ContingentExistenceNotSelfExplained (m : Model W B) (w : W) : Prop :=
  ∀ x r, ContingentAt m.ontic w x → m.explains w r (.fact x) → source r ≠ x

/-- OPEN bridge (BX2): if a reason at `w` for the existence of a being
contingent at `w` is about another being, that other being causes its esse
(the frame's `CausesIn … esse`, CAUSE_2). The causal reading of existential
reasons by another. It does not say that every cause is a reason. -/
def ExistenceReasonSourceCausesEsse (F : CausalityFrame W B T R) (m : Model W B)
    (w : W) : Prop :=
  ∀ x r, ContingentAt m.ontic w x → m.explains w r (.fact x) → source r ≠ x →
    F.CausesIn (source r) x F.esse

/-- OPEN interface: every being contingent at `w` is concrete in the
selected-grounding profile. It excludes contingent abstracta (for example a set
of contingent individuals on criteria that count it abstract); the grounding
route below therefore covers B2 only through this interface. -/
def ContingentsConcrete (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W) :
    Prop :=
  ∀ x, ContingentAt F.history.ontic w x → concrete x

/-- The brute-contingency rival at the scope of B2: on the same frame and at
the same world, some being contingent at `w` has no distinct cause of its esse
(CAUSE_2) and no reason at all for its existence. -/
def BruteContingentBeingAt (F : CausalityFrame W B T R) (m : Model W B) (w : W) :
    Prop :=
  ∃ x, ContingentAt F.history.ontic w x ∧ (¬ ∃ c, c ≠ x ∧ F.CausesIn c x F.esse) ∧
    ¬ ∃ r, m.explains w r (.fact x)

/-- Existence explained by own nature in the essence–esse sense: the only
reasons are intrinsic tokens, and `x`'s own token explains its existence exactly
when its represented esse is not distinct from its represented essence. Used to
test the theist's "explained by its own nature" against B6. -/
def natureModel {P : Type} (F : CausalityFrame W B T R) (essenceOf esseOf : B → P) :
    Model W B :=
  ⟨F.history.ontic, fun _ r f => match r, f with
    | .intrinsic z, .fact x => z = x ∧ ¬ esseOf x ≠ essenceOf x
    | .circumstance _, .fact _ => False⟩

end Frame

/-! ## Part 2: the ontic demand of a stance -/

section Stances

variable {W B F : Type}

/-- A #756 stance with an ONTIC demand added: `requiresWhy f` says the stance
accepts `f` only if `f` has a reason why it obtains (the #755 `explains`). It
is not `demands` (a reason to accept `f`): smoke is a reason to accept a fire
and no reason why there is one. -/
structure WhyStance (F : Type) extends Stance F where
  requiresWhy : F → Prop

/-- The ontic demand presented in the demand slot of a #756 stance, so that the
#756 standings `Uniform`, `Selective` and `Restricted`, which use no property of
the demanded relation, apply unchanged. -/
def whyView (S : WhyStance F) : Stance F := ⟨S.accepts, S.core, S.requiresWhy⟩

/-- The stance meets its ontic demand in the picture `A` at `w`: whatever it both
requires a reason why for and accepts has a reason there. -/
def WhyHonors (S : WhyStance F) (A : Arena W B F) (w : W) : Prop :=
  ∀ f, S.requiresWhy f → S.accepts f → Explained A w f

/-- The same demand met by a necessitating reason: one whose truth at each
accessible world brings the target's. -/
def WhyHonorsNecessitating (S : WhyStance F) (A : Arena W B F) (w : W) : Prop :=
  ∀ f, S.requiresWhy f → S.accepts f →
    ∃ r, A.explains w r f ∧ ∀ v, Access A w v → A.holds v r → A.holds v f

/-- P1 of the parity argument: the stance requires a reason why `t` obtains, so
that, meeting its demand, it rejects `t` posited as brute. -/
def RequiresWhyFor (S : WhyStance F) (t : F) : Prop := S.requiresWhy t

/-- P2 of the parity argument: `t` and `o` agree on the feature `k`. -/
def ShareFeature (k : F → Prop) (t o : F) : Prop := (k t ↔ k o)

/-- P3 of the parity argument, the consistency norm: the stance's ontic demand
is uniform in `k`; facts agreeing on `k` are alike required or not. -/
def FeatureUniform (S : WhyStance F) (k : F → Prop) : Prop :=
  ∀ f g, (k f ↔ k g) → S.requiresWhy f → S.requiresWhy g

/-- The rival as a stance holds it: the stance meets its ontic demand in its
picture `A` at `w`, accepts `o`, and `o` is a brute contingent truth there. -/
def HoldsBruteRival (S : WhyStance F) (A : Arena W B F) (w : W) (o : F) : Prop :=
  WhyHonors S A w ∧ S.accepts o ∧ BruteAt A w o

/-- The parity conclusion: the stance does not hold `o` as a brute rival. -/
def ExcludesBruteRival (S : WhyStance F) (A : Arena W B F) (w : W) (o : F) : Prop :=
  ¬ HoldsBruteRival S A w o

/-- The stronger parity conclusion: the stance does not at once meet its ontic
demand in `A` at `w`, accept `o`, and have `o` without a reason there, whether
`o` is contingent or not. For a necessary `o` (God's existence, a necessary
base) `ExcludesBruteRival` holds vacuously, because `BruteAt` requires
contingency; this form does not. -/
def ExcludesUnreasonedAcceptance (S : WhyStance F) (A : Arena W B F) (w : W) (o : F) :
    Prop :=
  ¬ (WhyHonors S A w ∧ S.accepts o ∧ ¬ Explained A w o)

end Stances

/-! ## The parity scene -/

/-- Facts of the parity scene: `god`, that God exists; `base`, that a necessary
physical ground exists; `found`, that a contingent initial state (the contingent
foundation) exists; `atom` and `star`, that two diverse ordinary contingent
existents exist. -/
inductive PFact | god | base | found | atom | star

/-- A table over the facts. Written without a wildcard. -/
def ptbl {α : Type} (god base found atom star : α) : PFact → α
  | .god => god
  | .base => base
  | .found => found
  | .atom => atom
  | .star => star

/-- A row of a reason table with nothing. -/
def pnone : PFact → Prop := ptbl False False False False False

/-- A picture over the scene: universal access, the given truth and reason
tables, and conjuncts only of themselves. The reading world is `false`. -/
def picture (holds : Bool → PFact → Prop) (explains : Bool → PFact → PFact → Prop) :
    Arena Bool Empty PFact :=
  basic everywhere holds explains (fun g f => g = f)

/-- Ordinary existents and the initial state obtain at `false` only. -/
def contingentRow (w : Bool) : Prop := w = false

/-- Many diverse brute contingents: the atom and the star obtain at `false`
with no reason; nothing else obtains. -/
def manyBrute : Arena Bool Empty PFact :=
  picture (fun w => ptbl False False False (contingentRow w) (contingentRow w))
    (fun _ _ => pnone)

/-- One brute contingent initial state (the naturalist picture): the initial
state obtains at `false` with no reason and is a reason for the atom and the
star. -/
def naturalist : Arena Bool Empty PFact :=
  picture (fun w => ptbl False False (contingentRow w) (contingentRow w) (contingentRow w))
    (fun w => ptbl pnone pnone (ptbl False False False (contingentRow w) (contingentRow w))
      pnone pnone)

/-- A necessary physical base with no reason: it obtains at every world and is a
reason for the contingent initial state, which is a reason for the atom and the
star. -/
def bruteBase : Arena Bool Empty PFact :=
  picture (fun w => ptbl False True (contingentRow w) (contingentRow w) (contingentRow w))
    (fun w => ptbl pnone (ptbl False False (contingentRow w) False False)
      (ptbl False False False (contingentRow w) (contingentRow w)) pnone pnone)

/-- As `bruteBase`, but the base's existence has a reason by its own nature,
represented as a self-reason of a fact true at every world. -/
def natureBase : Arena Bool Empty PFact :=
  picture (fun w => ptbl False True (contingentRow w) (contingentRow w) (contingentRow w))
    (fun w => ptbl pnone (ptbl False True (contingentRow w) False False)
      (ptbl False False False (contingentRow w) (contingentRow w)) pnone pnone)

/-- The hypothesis the parity argument's atheist rejects: God obtains at every
world with no reason, and is a reason for the contingent initial state (its
free, non-necessitating choice), which is a reason for the atom and the star. -/
def bruteGod : Arena Bool Empty PFact :=
  picture (fun w => ptbl True False (contingentRow w) (contingentRow w) (contingentRow w))
    (fun w => ptbl (ptbl False False (contingentRow w) False False) pnone
      (ptbl False False False (contingentRow w) (contingentRow w)) pnone pnone)

/-- The theist picture: as `bruteGod`, but God's existence has a reason by its
own nature, represented as a self-reason of a fact true at every world. The
#755 `ground true` arena with an initial state and two effects added; the
contingent initial state plays `ground true`'s free choice. -/
def theist : Arena Bool Empty PFact :=
  picture (fun w => ptbl True False (contingentRow w) (contingentRow w) (contingentRow w))
    (fun w => ptbl (ptbl True False (contingentRow w) False False) pnone
      (ptbl False False False (contingentRow w) (contingentRow w)) pnone pnone)

/-- As `theist`, but God obtains only at `false`: a contingent God whose
existence has only a self-reason. -/
def contingentGod : Arena Bool Empty PFact :=
  picture (fun w => ptbl (contingentRow w) False (contingentRow w) (contingentRow w)
      (contingentRow w))
    (fun w => ptbl (ptbl (contingentRow w) False (contingentRow w) False False) pnone
      (ptbl False False False (contingentRow w) (contingentRow w)) pnone pnone)

/-- The truths at `w` with no reason at `w`, listed exactly by `l`: the number
and identity of the existents a picture leaves unexplained. -/
def UnexplainedAre (A : Arena Bool Empty PFact) (w : Bool) (l : List PFact) : Prop :=
  ∀ f, (A.holds w f ∧ ¬ Explained A w f) ↔ f ∈ l

/-- The truths at `w` with no necessitating reason at `w`, listed exactly by `l`:
what is unexplained when only a reason whose truth brings the fact's at every
accessible world counts. -/
def UnnecessitatedAre (A : Arena Bool Empty PFact) (w : Bool) (l : List PFact) : Prop :=
  ∀ f, (A.holds w f ∧ ¬ ∃ r, A.explains w r f ∧ ∀ v, Access A w v → A.holds v r → A.holds v f)
    ↔ f ∈ l

/-- Observation: at `false`, the atom supports that the initial state exists
(inference from effect to cause), and nothing else is supported. An epistemic
relation only: it gives no reason why anything obtains. -/
def observation : TruthCore.Explanation.PSRSelfApplication.Inquiry Bool PFact :=
  ⟨fun w e p => w = false ∧ e = .atom ∧ p = .found⟩

/-- The reason-status feature of the parity argument, read in the picture where
each fact is posited: the fact obtains at the reading world `false` of its
picture and has no reason there. -/
def PositedWithoutReason (pic : PFact → Arena Bool Empty PFact) (f : PFact) : Prop :=
  (pic f).holds false f ∧ ¬ Explained (pic f) false f

/-- God posited as brute, everything else as in the naturalist picture. -/
def atheistReading : PFact → Arena Bool Empty PFact :=
  ptbl bruteGod naturalist naturalist naturalist naturalist

/-- God posited as in the theist picture, everything else as in the naturalist
picture. -/
def theistReading : PFact → Arena Bool Empty PFact :=
  ptbl theist naturalist naturalist naturalist naturalist

/-- The idleness feature, a description: God is posited as an explainer whose
posit lowers no count of unexplained existents below the naturalist picture's
one. A stipulated table, not computed; the scene's map lists the unexplained
existents of each picture. It is the stance's own measure, and the #746 count
control applies to it. -/
def idle : PFact → Prop := ptbl True False False False False

/-- Being an existence fact of a posited or observed being: every scene fact. -/
def existence : PFact → Prop := ptbl True True True True True

/-- A stance in the scene from four membership tables. -/
def wstance (acc cor dem why : PFact → Prop) : WhyStance PFact :=
  ⟨⟨acc, cor, dem⟩, why⟩

/-- Accepts the initial state, the atom and the star; the state is core. -/
def natAccepts : PFact → Prop := ptbl False False True True True

/-- Core: the initial state. -/
def natCore : PFact → Prop := ptbl False False True False False

/-- Requires a reason why God exists and nothing else. Whether it is
`FeatureUniform` depends on the feature: in `idle` yes, in the reason-status
feature no. -/
def godOnly : WhyStance PFact :=
  wstance natAccepts natCore pnone (ptbl True False False False False)

/-- Requires a reason why for God and for the initial state. -/
def uniformRejector : WhyStance PFact :=
  wstance natAccepts natCore pnone (ptbl True False True False False)

/-- The evidential atheist: demands a reason to accept God's existence and the
initial state's (the epistemic slot) and requires no reason why for anything. -/
def evidential : WhyStance PFact :=
  wstance natAccepts natCore (ptbl True False True False False) pnone

/-- The symmetric stance: accepts a stopping point with no reason, and requires
no reason why for God or the initial state. -/
def symmetric : WhyStance PFact :=
  wstance natAccepts natCore pnone pnone

/-- The naturalist who rejects brute existence across the board: accepts the
base, the state and the two existents and requires a reason why for each. -/
def baseNaturalist : WhyStance PFact :=
  wstance (ptbl False True True True True) (ptbl False True False False False) pnone
    (ptbl False True True True True)

/-- The theist: accepts God, the state and the two existents and requires a
reason why for each. -/
def theistStance : WhyStance PFact :=
  wstance (ptbl True False True True True) (ptbl True False False False False) pnone
    (ptbl True False True True True)

/-- The reason-status theist: accepts God, the state and the two existents, and
requires a reason why for God and for the initial state, uniformly in the
reason-status feature (the facts posited with no reason). -/
def reasonStatusTheist : WhyStance PFact :=
  wstance (ptbl True False True True True) (ptbl True False False False False) pnone
    (ptbl True False True False False)

/-- The modally restricted theist: as `theistStance`, but requires a reason why
only for the contingent facts. -/
def contingentOnlyTheist : WhyStance PFact :=
  wstance (ptbl True False True True True) (ptbl True False False False False) pnone
    (ptbl False False True True True)

/-! ## Certificates -/

open TruthCore.Explanation.PSRSelfApplication (Uniform Selective Restricted)
open TruthCore.Explanation.PSRStrength (ofModel)
open TruthCore.Causality.FirstMoverNecessity.Model (bruteFirst conserved allConcrete
  noneConcrete noGround xGroundsF unitOf)

/-- No reasons at all. -/
def noReasons (_ : Bool) (_ : Reason Bool) (_ : ExistenceFact Bool) : Prop := False

/-- Every being's existence is explained by its own nature (intrinsic token). -/
def selfNature (_ : Bool) (r : Reason Bool) (f : ExistenceFact Bool) : Prop :=
  match r, f with
  | .intrinsic z, .fact x => z = x
  | .circumstance _, .fact _ => False

/-- The moved thing `x` (`false`), as a circumstance, is a reason for the
existence of the mover `f` (`true`), and nothing else is explained. -/
def occasion (_ : Bool) (r : Reason Bool) (f : ExistenceFact Bool) : Prop :=
  match r, f with
  | .intrinsic _, .fact _ => False
  | .circumstance y, .fact x => y = false ∧ x = true

/-- Both `selfNature` and `occasion`. -/
def selfAndOccasion (w : Bool) (r : Reason Bool) (f : ExistenceFact Bool) : Prop :=
  selfNature w r f ∨ occasion w r f

/-- **B2 support options, the rival and their boundaries.**

Laws:
* each support bundle gives B2 (so each is a support option, stated here for
  the rival test), and the local existence PSR for all existents gives the
  contingent-only form;
* the rival excludes B2, the contingent existence PSR, and each support bundle;
* under BX1, a being with an own-nature reason token
  (NECESSARY_EXISTENCE_BY_OWN_NATURE_4) at `w` is not contingent at `w`;
* for the own-nature model in the essence–esse sense, BX1 is exactly B6
  (contrapositive form) at `w`;
* the rival's arena form: in the `ofModel` embedding of the frame's reason model,
  a being's existence fact is a brute contingent truth at `w` exactly when the
  being is contingent at `w` and its existence has no reason there.

Models over the existing first-mover frames (`bruteFirst`: the mover `f`
contingent at `true` with no esse-cause; `conserved`: the moved thing causes
`f`'s esse), at the reading world `true`:
1. `bruteFirst`, no reasons: BX1, BX2 hold; the contingent existence PSR, B2
   fail; the rival holds, with `f` as its witness.
2. `bruteFirst`, own-nature reasons: the existence PSR and BX2 hold; BX1 and
   B2 fail; `f` is contingent with an own-nature token.
3. `bruteFirst`, the moved thing as occasion: the existence PSR and BX1 hold;
   BX2 and B2 fail.
4. `conserved`, occasion: all three hold and B2 holds (nonvacuity).
5. `conserved`, no reasons: B2 holds and the existence PSR fails, so B2 does
   not give the existence PSR.
6. `conserved`, own nature and occasion: B2 holds and BX1 fails, so B2 does not
   give BX1.
7. `bruteFirst`, all concrete, no grounding: the interface and the ground
   bridge hold; the closure and B2 fail.
8. `bruteFirst`, all concrete, `x` grounds `f`: the interface and the closure
   hold; the ground bridge and B2 fail.
9. `bruteFirst`, nothing concrete: the closure and the ground bridge hold
   vacuously; the interface and B2 fail.
10. `conserved`, all concrete, `x` grounds `f`: the interface, closure and
    ground bridge hold, and B2 holds (nonvacuity). -/
def B2SupportControls : Prop :=
  -- laws
  (∀ (W B T R : Type) (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W),
    NoBruteContingentExistenceAt (reasonModel F ex) w →
    ContingentExistenceNotSelfExplained (reasonModel F ex) w →
    ExistenceReasonSourceCausesEsse F (reasonModel F ex) w →
    ContingentHasDistinctEsseCause F w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W),
    ContingentsConcrete F concrete w →
    EveryContingentGroundedAt (groundProfile F concrete grounds) w →
    ActualGroundIsDistinctEsseCause (groundProfile F concrete grounds) w F.CausesIn F.esse →
    ContingentHasDistinctEsseCause F w) ∧
  (∀ (W B : Type) (m : Model W B) (w : W),
    TruthCore.Explanation.NoBruteExistence.NoBruteExistenceAt m w →
    NoBruteContingentExistenceAt m w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W),
    BruteContingentBeingAt F (reasonModel F ex) w →
      ¬ ContingentHasDistinctEsseCause F w ∧
      ¬ NoBruteContingentExistenceAt (reasonModel F ex) w ∧
      ¬ (ContingentExistenceNotSelfExplained (reasonModel F ex) w ∧
          ExistenceReasonSourceCausesEsse F (reasonModel F ex) w ∧
          NoBruteContingentExistenceAt (reasonModel F ex) w) ∧
      ∀ (concrete : B → Prop) (grounds : W → B → B → Prop),
        ¬ (ContingentsConcrete F concrete w ∧
          EveryContingentGroundedAt (groundProfile F concrete grounds) w ∧
          ActualGroundIsDistinctEsseCause (groundProfile F concrete grounds) w F.CausesIn
            F.esse)) ∧
  (∀ (W B : Type) (m : Model W B) (w : W) (x : B),
    ContingentExistenceNotSelfExplained m w → m.explains w (.intrinsic x) (.fact x) →
      ¬ ContingentAt m.ontic w x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (essenceOf esseOf : B → P) (w : W),
    ContingentExistenceNotSelfExplained (natureModel F essenceOf esseOf) w ↔
      ContingentHasDistinctEsse F w essenceOf esseOf) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W) (x : B),
    BruteAt (ofModel (reasonModel F ex)) w (.inl (.fact x)) ↔
      ContingentAt F.history.ontic w x ∧ ¬ ∃ r, ex w r (.fact x)) ∧
  -- 1. brute first mover, no reasons
  (ContingentExistenceNotSelfExplained (reasonModel bruteFirst noReasons) true ∧
    ExistenceReasonSourceCausesEsse bruteFirst (reasonModel bruteFirst noReasons) true ∧
    ¬ NoBruteContingentExistenceAt (reasonModel bruteFirst noReasons) true ∧
    ¬ ContingentHasDistinctEsseCause bruteFirst true ∧
    BruteContingentBeingAt bruteFirst (reasonModel bruteFirst noReasons) true ∧
    ContingentAt bruteFirst.history.ontic true true ∧
    BruteAt (ofModel (reasonModel bruteFirst noReasons)) true (.inl (.fact true))) ∧
  -- 2. own-nature reasons
  (NoBruteContingentExistenceAt (reasonModel bruteFirst selfNature) true ∧
    ExistenceReasonSourceCausesEsse bruteFirst (reasonModel bruteFirst selfNature) true ∧
    ¬ ContingentExistenceNotSelfExplained (reasonModel bruteFirst selfNature) true ∧
    ¬ ContingentHasDistinctEsseCause bruteFirst true ∧
    ContingentAt bruteFirst.history.ontic true true ∧
    selfNature true (.intrinsic true) (.fact true)) ∧
  -- 3. occasion without causing
  (NoBruteContingentExistenceAt (reasonModel bruteFirst occasion) true ∧
    ContingentExistenceNotSelfExplained (reasonModel bruteFirst occasion) true ∧
    ¬ ExistenceReasonSourceCausesEsse bruteFirst (reasonModel bruteFirst occasion) true ∧
    ¬ ContingentHasDistinctEsseCause bruteFirst true) ∧
  -- 4. nonvacuity
  (NoBruteContingentExistenceAt (reasonModel conserved occasion) true ∧
    ContingentExistenceNotSelfExplained (reasonModel conserved occasion) true ∧
    ExistenceReasonSourceCausesEsse conserved (reasonModel conserved occasion) true ∧
    ContingentHasDistinctEsseCause conserved true ∧
    ContingentAt conserved.history.ontic true true) ∧
  -- 5. B2 without the existence PSR
  (ContingentHasDistinctEsseCause conserved true ∧
    ¬ NoBruteContingentExistenceAt (reasonModel conserved noReasons) true) ∧
  -- 6. B2 without BX1
  (ContingentHasDistinctEsseCause conserved true ∧
    ¬ ContingentExistenceNotSelfExplained (reasonModel conserved selfAndOccasion) true) ∧
  -- 7. grounding: no ground
  (ContingentsConcrete bruteFirst allConcrete true ∧
    ActualGroundIsDistinctEsseCause (groundProfile bruteFirst allConcrete noGround) true
      bruteFirst.CausesIn bruteFirst.esse ∧
    ¬ EveryContingentGroundedAt (groundProfile bruteFirst allConcrete noGround) true) ∧
  -- 8. grounding: ground without esse-cause
  (ContingentsConcrete bruteFirst allConcrete true ∧
    EveryContingentGroundedAt (groundProfile bruteFirst allConcrete xGroundsF) true ∧
    ¬ ActualGroundIsDistinctEsseCause (groundProfile bruteFirst allConcrete xGroundsF) true
      bruteFirst.CausesIn bruteFirst.esse) ∧
  -- 9. grounding: nothing concrete
  (EveryContingentGroundedAt (groundProfile bruteFirst noneConcrete noGround) true ∧
    ActualGroundIsDistinctEsseCause (groundProfile bruteFirst noneConcrete noGround) true
      bruteFirst.CausesIn bruteFirst.esse ∧
    ¬ ContingentsConcrete bruteFirst noneConcrete true) ∧
  -- 10. grounding nonvacuity
  (ContingentsConcrete conserved allConcrete true ∧
    EveryContingentGroundedAt (groundProfile conserved allConcrete xGroundsF) true ∧
    ActualGroundIsDistinctEsseCause (groundProfile conserved allConcrete xGroundsF) true
      conserved.CausesIn conserved.esse)

/-- **Symmetric parity, the comparison of explanations of existence, and which
stances the argument binds.**

* The fork, reused from #756 through `whyView`: a stance that requires a reason
  why for `t`, meets its ontic demand in its picture at `w` and accepts a brute
  contingent truth `o` there is not uniform on `t` and `o`, is selective
  relative to every feature on which they agree and restricted relative to every
  feature on which they differ.
* Both sides alike (#746 second core, reused): with factive reasons that are
  well-founded at `w` and some truth at `w`, not every truth at `w` has a reason.
  So a picture with no unexplained existent needs reasons that are not
  well-founded there: a self-reason, a circle or an infinite chain. In the scene
  it is a self-reason at the terminus ("existence by its own nature"); a circle
  (#755 `mutualReasons`) and an endless regress of contingents each explained by
  its predecessor (#746 `cofinite`, no terminal fact) are not scene pictures,
  and the regress faces the whole-series question (#755 collapse core, attempt
  a5958e25).
* Scene-relative tallies, at the reading world `false`, listing exactly the
  unexplained existents. They rank nothing by themselves: a bare preference for
  fewer unexplained facts favours copying reasons (#746 count control); ranking
  needs an open comparative principle such as the adequacy norm (#750).
  `manyBrute` the atom and the star (two diverse contingents);
  `naturalist` the initial state (one contingent); `bruteBase` the base (one
  necessary); `bruteGod` God (one necessary); `natureBase` and `theist` none.
  Counting only necessitating reasons: `bruteBase` and `bruteGod` leave their
  terminus and the initial state (the free choice or indeterministic output);
  `natureBase` and `theist` leave the initial state. The four pictures with an
  unexplained existent have factive, well-founded reasons; `natureBase` and
  `theist` are factive and contingent-irreflexive with a self-reason, so not
  well-founded, and their lists agree under God ↔ base: the arena does not
  separate a necessary personal ground from a necessary physical one.
* Evidence is not explanation: in `naturalist`, the observation supports that
  the initial state exists and the initial state has no reason why it exists;
  the evidential stance meets its epistemic demand there and still holds the
  initial state as a brute contingent truth.
* The scene's readings: under the atheist reading, God's existence and the
  initial state's agree on the reason-status feature (both posited with no
  reason); under the theist reading they differ (God's existence has a
  self-reason, and is true at every world).
* Symmetric binding, through the stronger sibling `ExcludesUnreasonedAcceptance`:
  the naturalist `uniformRejector` and the theist `reasonStatusTheist` both
  satisfy P1-P3 in the reason-status feature (the naturalist with target God,
  the theist with target the initial state), and neither can accept an
  unreasoned existent: the initial state in `naturalist`, God in `bruteGod`.
  For the necessary God of `bruteGod` the weaker `ExcludesBruteRival` holds only
  vacuously (God is not `BruteAt`). `baseNaturalist` meets its demand with the
  self-explained base and not with the unreasoned one.
* `godOnly` meets its demand in `naturalist` and holds the foundation as a
  brute rival. It is uniform in `idle` and not uniform in the reason-status
  feature, selective relative to the latter and restricted relative to `idle`.
  So the argument binds it exactly when its ground for rejecting God is the
  reason status, not idleness.
* Deletions of the parity bundle: without P3 (`godOnly`, reason-status feature);
  without P1 (`evidential`, `symmetric`, each uniform in every feature since
  they require nothing); without P2 (`godOnly` and `idle`); without meeting the
  demand (`uniformRejector` in `naturalist`); without bruteness (`uniformRejector`
  in `theist`, where the foundation has a reason).
* The theist under the same test: `theistStance` meets its demand in `theist`
  (some reason) and fails it with necessitating reasons, as every stance must
  whose contingent fact has only a reason true at every world; in `bruteGod` it
  fails the demand (God unexplained), while `contingentOnlyTheist` meets it
  there. Its self-reason counts as a reason under contingent irreflexivity in
  `theist` and not in `contingentGod`, where God is contingent.
* Same witness: in the `ofModel` picture of the brute first-mover frame, the
  First Way's mover `f`'s existence is a brute contingent truth at `true`; a
  stance that requires nothing and accepts it holds the rival, and one that
  requires a reason why for it does not meet its demand. -/
def ParityMap : Prop :=
  -- the fork
  (∀ (W B F : Type) (S : WhyStance F) (A : Arena W B F) (w : W) (t o : F) (k : F → Prop),
    S.requiresWhy t → WhyHonors S A w → S.accepts o → BruteAt A w o →
      ¬ Uniform (whyView S) t o ∧
      ((k t ↔ k o) → Selective (whyView S) k t o) ∧
      (¬ (k t ↔ k o) → Restricted (whyView S) k t o)) ∧
  -- necessitating demands and necessary reasons
  (∀ (W B F : Type) (S : WhyStance F) (A : Arena W B F) (w : W) (f : F),
    WhyHonorsNecessitating S A w → S.requiresWhy f → S.accepts f → Contingent A w f →
    (∀ r, A.explains w r f → ∀ v, Access A w v → A.holds v r) → False) ∧
  -- both sides: well-founded factive reasons leave a truth unexplained
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (t : F),
    A.holds a t → TruthCore.Explanation.PSRStrength.Factive A →
      WellFounded (A.explains a) → ¬ TruthCore.Explanation.PSRStrength.FactPSR A a) ∧
  -- the comparison
  (UnexplainedAre manyBrute false [.atom, .star] ∧
    UnexplainedAre naturalist false [.found] ∧
    UnexplainedAre bruteBase false [.base] ∧
    UnexplainedAre bruteGod false [.god] ∧
    UnexplainedAre natureBase false [] ∧
    UnexplainedAre theist false [] ∧
    UnnecessitatedAre bruteBase false [.base, .found] ∧
    UnnecessitatedAre bruteGod false [.god, .found] ∧
    UnnecessitatedAre natureBase false [.found] ∧
    UnnecessitatedAre theist false [.found] ∧
    TruthCore.Explanation.PSRStrength.Factive manyBrute ∧ WellFounded (manyBrute.explains false) ∧
    TruthCore.Explanation.PSRStrength.Factive naturalist ∧
    WellFounded (naturalist.explains false) ∧
    TruthCore.Explanation.PSRStrength.Factive bruteBase ∧ WellFounded (bruteBase.explains false) ∧
    TruthCore.Explanation.PSRStrength.Factive bruteGod ∧ WellFounded (bruteGod.explains false) ∧
    TruthCore.Explanation.PSRStrength.Factive natureBase ∧
    ¬ WellFounded (natureBase.explains false) ∧ IrreflexiveContingent natureBase ∧
    TruthCore.Explanation.PSRStrength.Factive theist ∧ ¬ WellFounded (theist.explains false) ∧
    IrreflexiveContingent theist) ∧
  -- evidence is not explanation
  (TruthCore.Explanation.PSRSelfApplication.Supported observation false .found ∧
    BruteAt naturalist false .found ∧ ¬ naturalist.explains false .atom .found ∧
    TruthCore.Explanation.PSRSelfApplication.Honors evidential.toStance observation false ∧
    HoldsBruteRival evidential naturalist false .found) ∧
  -- the readings
  (ShareFeature (PositedWithoutReason atheistReading) .god .found ∧
    PositedWithoutReason atheistReading .god ∧
    ¬ ShareFeature (PositedWithoutReason theistReading) .god .found) ∧
  -- symmetric binding, through the stronger sibling
  (FeatureUniform uniformRejector (PositedWithoutReason atheistReading) ∧
    RequiresWhyFor uniformRejector .god ∧
    ShareFeature (PositedWithoutReason atheistReading) .god .found ∧
    ExcludesUnreasonedAcceptance uniformRejector naturalist false .found ∧
    FeatureUniform reasonStatusTheist (PositedWithoutReason atheistReading) ∧
    RequiresWhyFor reasonStatusTheist .found ∧
    ShareFeature (PositedWithoutReason atheistReading) .found .god ∧
    ExcludesUnreasonedAcceptance reasonStatusTheist bruteGod false .god ∧
    reasonStatusTheist.accepts .god ∧ ¬ Explained bruteGod false .god ∧
    ¬ WhyHonors reasonStatusTheist bruteGod false ∧ WhyHonors reasonStatusTheist theist false ∧
    ExcludesBruteRival reasonStatusTheist bruteGod false .god ∧ ¬ BruteAt bruteGod false .god ∧
    WhyHonors baseNaturalist natureBase false ∧ ¬ WhyHonors baseNaturalist bruteBase false) ∧
  -- godOnly: bound in the reason-status feature, not in idleness
  (HoldsBruteRival godOnly naturalist false .found ∧ RequiresWhyFor godOnly .god ∧
    FeatureUniform godOnly idle ∧ ¬ ShareFeature idle .god .found ∧
    ¬ FeatureUniform godOnly (PositedWithoutReason atheistReading) ∧
    Selective (whyView godOnly) (PositedWithoutReason atheistReading) .god .found ∧
    Restricted (whyView godOnly) idle .god .found ∧
    Selective (whyView godOnly) existence .god .found) ∧
  -- deletions: without P1
  (HoldsBruteRival evidential naturalist false .found ∧ ¬ RequiresWhyFor evidential .god ∧
    evidential.demands .god ∧ ShareFeature (PositedWithoutReason atheistReading) .god .found ∧
    FeatureUniform evidential (PositedWithoutReason atheistReading)) ∧
  (HoldsBruteRival symmetric naturalist false .found ∧ ¬ RequiresWhyFor symmetric .god ∧
    ¬ symmetric.demands .god ∧ FeatureUniform symmetric (PositedWithoutReason atheistReading)) ∧
  -- without meeting the demand, and without bruteness
  (RequiresWhyFor uniformRejector .god ∧
    FeatureUniform uniformRejector (PositedWithoutReason atheistReading) ∧
    uniformRejector.accepts .found ∧ BruteAt naturalist false .found ∧
    ¬ WhyHonors uniformRejector naturalist false) ∧
  (RequiresWhyFor uniformRejector .god ∧
    FeatureUniform uniformRejector (PositedWithoutReason atheistReading) ∧
    WhyHonors uniformRejector theist false ∧ uniformRejector.accepts .found ∧
    ¬ BruteAt theist false .found ∧ Contingent theist false .found) ∧
  -- the theist under the same test
  (WhyHonors theistStance theist false ∧ ¬ WhyHonorsNecessitating theistStance theist false ∧
    Contingent theist false .found ∧ theist.explains false .god .found ∧
    (∀ v, theist.holds v .god) ∧
    ¬ WhyHonors theistStance bruteGod false ∧ WhyHonors contingentOnlyTheist bruteGod false ∧
    IrreflexiveContingent theist ∧ theist.explains false .god .god ∧
    ¬ IrreflexiveContingent contingentGod ∧ Contingent contingentGod false .god ∧
    contingentGod.explains false .god .god) ∧
  -- same witness: the brute first mover
  (BruteAt (ofModel (reasonModel bruteFirst noReasons)) true (.inl (.fact true)) ∧
    HoldsBruteRival (⟨⟨fun f => f = .inl (.fact true), fun _ => False, fun _ => False⟩,
        fun _ => False⟩ : WhyStance (ExistenceFact Bool ⊕ Reason Bool))
      (ofModel (reasonModel bruteFirst noReasons)) true (.inl (.fact true)) ∧
    ¬ WhyHonors (⟨⟨fun f => f = .inl (.fact true), fun _ => False, fun _ => False⟩,
        fun f => f = .inl (.fact true)⟩ : WhyStance (ExistenceFact Bool ⊕ Reason Bool))
      (ofModel (reasonModel bruteFirst noReasons)) true)

end TruthCore.Explanation.BruteContingencyParity
