module

public import TruthCore.Causality.RootClosure
public import TruthCore.Explanation.StoppingPoints

/-! # Does inquiry commit us to closure at the root? (#2145, horizontal lane H2)

Analyst formulations, attribution deferred. The question is whether the
principle of sufficient reason, in the forms the repository already derives
from or ties to rational inquiry (#756: `TrackingBridge`, `SupportCoverage`,
`EvidenceBridge`, `GlobalDefeat`; #755: `ContingentPSR`, `NoBrute` and the
quality conditions), reaches the necessary intrinsic profile facts of an
actual root, in particular its absences, and so supports E
(`RootPerfectionExclusion.NoUnexplainedAbsenceAtRoots`, `9281317d`) or its
carriage premise LE (`RootClosure.RootEssentialConditionsCarried`,
`682e6436`).

Three gaps are separated.

* **Scope.** Every inquiry bridge of #756, the contingent-fact PSR, `NoBrute`,
  the reason qualities `ReasonIndependent` and `IrreflexiveContingent`, and the
  skeptical-alternative formulation `NoBruteEvidenceAlternative` below
  quantify over facts that are contingent at the world of evaluation.
  `AgreeOnContingent` states that two reason relations agree there; the
  results module proves that each of these conditions is then unchanged,
  whatever the relations say about necessary facts. The skeptical mechanism
  itself has no purchase on a necessary hypothesis.
* **Cheap extension.** `necessaryReasons` adds, to any reason relation, the
  necessary truths as reasons for the necessary truths. With excluded middle
  it meets the unrestricted `FactPSR` wherever `ContingentPSR` held, keeps
  every #755 quality condition (distribution under the conjunct law), and
  turns `GlobalDefeat` into its unrestricted form. The one quality condition that reaches necessary targets,
  `StoppingPoints.WorkIndependent` at every reason, forces every explained
  necessary truth to have a contingent reason, for every root alike.
* **Sense.** E says that no absence at an actual root is unexplained in the
  admissibility sense (EXPLAINED_ABSENCE_3: fixed by the admissibility
  constraints with the root's profile, case i or ii). `PositivelyFixedAbsence`
  (EXPLAINED_ABSENCE_2) adds a carried exclusion; it equals sense 3 under the
  necessity direction of member grounding. `RootLackReasonsPositive` is the
  bridge to sense 2 from the admitted-reason sense (`PSRStrength.Explained`,
  EXPLAINED_ABSENCE_1). With a PSR for root lack facts, the lack facts
  represented and the necessity direction of member grounding it gives E, and
  E alone gives it back.
  `RootLackReasonsEssential` (a reason for a root's lack requires a nature
  excluding it) factors the bridge through LE.

`lack r d` is a fact of the supplied arena; `RootLackFactsAt` and
`LackFactsRepresent` say what it is the fact of. Nothing here says that the
arena's reasons are genuine explanations; `explains` remains the
uninterpreted #755 parameter. -/

@[expose] public section

namespace TruthCore.Explanation.InquiryClosure

open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.PSRSelfApplication
open TruthCore.Explanation.StoppingPoints (NecessaryFact WorkIndependent)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPerfectionExclusion (ActualProfile)
open TruthCore.Causality.RootClosure (ProfileEssentialCondition)
open TruthCore.Causality.SourceIntellectControls (HasCompatibleExtension)

variable {W B F D : Type}

/-! ## Part 1. What the inquiry family reads of the reason relation -/

/-- The same arena, the same worlds, truths and conjunct relation, with the
reason relation replaced by `e`. -/
def withReasons (A : Arena W B F) (e : W → F → F → Prop) : Arena W B F :=
  { A with explains := e }

/-- `e` agrees with the reasons of `A` on every target that is contingent at
the world of evaluation. Nothing is said about necessary targets. -/
def AgreeOnContingent (A : Arena W B F) (e : W → F → F → Prop) : Prop :=
  ∀ v r f, Contingent A v f → (A.explains v r f ↔ e v r f)

/-- The skeptical alternative of the inquiry argument for a PSR, in an analyst
formulation (Koons–Pruss style, navigation only, attribution deferred): at a
world accessible from `w`, the evidence `e` obtains as a brute contingent truth
while the hypothesis `p` it supports fails there. -/
def BruteEvidenceAlternative (A : Arena W B F) (w : W) (e p : F) : Prop :=
  ∃ v, Access A w v ∧ BruteAt A v e ∧ ¬ A.holds v p

/-- The presupposition that inquiry needs on this argument: no claim supported
at `w` has a brute-evidence alternative. It is an analyst formulation of the
mechanism "if brute facts were allowed, evidence could obtain for no reason
while the hypothesis fails". -/
def NoBruteEvidenceAlternative (A : Arena W B F) (I : Inquiry W F) (w : W) : Prop :=
  ∀ e p, I.supports w e p → ¬ BruteEvidenceAlternative A w e p

/-- `GlobalDefeat` (#756) extended from brute contingent truths to every
unreasoned truth: if some accessible world has a true fact with no reason,
nothing supports anything at `w`. It is the strongest inquiry bridge with the
unrestricted scope. Nothing here asserts it. -/
def GlobalDefeatUnreasoned (A : Arena W B F) (I : Inquiry W F) (w : W) : Prop :=
  (∃ v f, Access A w v ∧ A.holds v f ∧ ¬ Explained A v f) → ¬ ∃ e p, I.supports w e p

/-- The reasons of `A`, together with every true necessary fact as a reason for
every true necessary fact (necessity read at the world of the reason, with the
existing `StoppingPoints.NecessaryFact`). It is the cheapest way to meet an
unrestricted scope: it adds no reason for any contingent fact. It does not say
that a necessary truth explains another in any genuine sense. -/
def necessaryReasons (A : Arena W B F) : W → F → F → Prop := fun w r f =>
  A.explains w r f ∨
    (A.holds w r ∧ NecessaryFact A w r ∧ A.holds w f ∧ NecessaryFact A w f)

/-! ## Part 2. Root lack facts and the two senses of "explained" -/

/-- OPEN, fact-to-profile bridge at `w`: for every actual root `r` at `w` and
determination `d`, the arena's fact `lack r d` holds at `w` exactly when `r`
lacks `d` at `w`. It puts the root's absences among the facts that a fact PSR
quantifies over. -/
def RootLackFactsAt (m : Profile W B) (w : W) (A : Arena W B F)
    (HasAt : W → B → D → Prop) (lack : B → D → F) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, (A.holds w (lack r d) ↔ ¬ HasAt w r d)

/-- The same representation at every world and for every bearer, used by the
modal diagnostics. -/
def LackFactsRepresent (A : Arena W B F) (HasAt : W → B → D → Prop) (lack : B → D → F) :
    Prop :=
  ∀ v r d, A.holds v (lack r d) ↔ ¬ HasAt v r d

/-- OPEN, the PSR for root lack facts at `w`: every lack fact of an actual root
that holds at `w` has an admitted reason there (EXPLAINED_ABSENCE_1). It is the
restriction of `FactPSR` to the absences of actual roots, the "PSR for the
closure of a necessary root's profile" that #2153 found missing from the graph.
It is not restricted to contingent facts. -/
def RootLackPSR (m : Profile W B) (w : W) (A : Arena W B F) (lack : B → D → F) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, A.holds w (lack r d) → Explained A w (lack r d)

/-- EXPLAINED_ABSENCE_3, an absence excluded by admissibility: no admissible
profile contains all of `x`'s determinations together with `k` (case i or ii
of #2153). For a lacked `k` it is the negation of
`RootPerfectionExclusion.UnexplainedAbsence`, and it is the sense of E
(`NoUnexplainedAbsenceAtRoots`). It is the first disjunct of
`PositivelyFixedAbsence`, so it gives EXPLAINED_ABSENCE_2 outright; the converse
needs the necessity direction of member grounding. -/
def AbsenceExcludedByAdmissibility (Admissible : Set D → Prop) (Has : B → D → Prop)
    (x : B) (k : D) : Prop :=
  ¬ HasCompatibleExtension Admissible (ActualProfile Has x) k

/-- EXPLAINED_ABSENCE_2, a positively fixed absence:
either no admissible profile contains all of `x`'s determinations together
with `k` (case i or ii of #2153), or some determination `t` of `x` requires
the lack of a set `S` containing `k` whose other members `x` has (a carried
exclusion, LE's sense). E's sense (EXPLAINED_ABSENCE_3) is the first disjunct;
the two coincide under the necessity direction of member grounding. It is not
"some reason for the absence is admitted": a
bare negative clause in a nature is an admitted reason in the #755 arena and
fixes nothing here. -/
def PositivelyFixedAbsence (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop)
    (Has : B → D → Prop) (x : B) (k : D) : Prop :=
  AbsenceExcludedByAdmissibility Admissible Has x k ∨
    ∃ t S, Has x t ∧ k ∈ S ∧ S ⊆ insert k (ActualProfile Has x) ∧ RequiresLack t S

/-- OPEN sense bridge, analyst formulation: at every actual root `r` at `w`, an
absence of `r` that has an admitted reason in the arena is positively fixed.
It passes from EXPLAINED_ABSENCE_1 (`PSRStrength.Explained`) to
EXPLAINED_ABSENCE_2. Its rationale is the thesis that negative facts at a root
have positive grounds. With the PSR for root lack facts, the lack facts
represented and the necessity direction of member grounding it gives E, and E
alone gives it back. -/
def RootLackReasonsPositive (m : Profile W B) (w : W) (A : Arena W B F)
    (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop)
    (HasAt : W → B → D → Prop) (lack : B → D → F) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, ¬ HasAt w r d → Explained A w (lack r d) →
    PositivelyFixedAbsence Admissible RequiresLack (HasAt w) r d

/-- Some ESSENCE_6 condition on `x`'s profile fails at every profile that
contains `x`'s determinations together with `k`: a nature excludes `k` given
what `x` has. A bare negative clause "lacks `k`" is such a condition. -/
def EssentiallyExcludes (Ess : B → B → (Set D → Prop) → Prop) (Has : B → D → Prop)
    (x : B) (k : D) : Prop :=
  ∃ y C, ProfileEssentialCondition Ess y x C ∧ ∀ q, ActualProfile Has x ⊆ q → k ∈ q → ¬ C q

/-- OPEN, analyst formulation: an absence of an actual root at `w` has an
admitted reason only if some nature excludes the missing determination given
the root's profile. Its rationale: a root has no actual concrete ground, so
whatever counts as a reason why it lacks `d` does so because some nature
excludes `d`. It does not say that the reason is the condition. -/
def RootLackReasonsEssential (m : Profile W B) (w : W) (A : Arena W B F)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F) :
    Prop :=
  ∀ r, ActualRoot m w r → ∀ d, ¬ HasAt w r d → Explained A w (lack r d) →
    EssentiallyExcludes Ess (HasAt w) r d

/-- OPEN, analyst formulation: every absence of an actual root at `w` is
excluded by some nature, given the root's profile. Essentialism about a root's
absences, without a modal premise. -/
def RootLacksEssentiallyExcluded (m : Profile W B) (w : W)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, ¬ HasAt w r d → EssentiallyExcludes Ess (HasAt w) r d

/-- The reference-class generalization of lane E's objection to LE, as an
assumption to test: only determinations that are not pure require a lack. -/
def CarriersImpure (RequiresLack : D → Set D → Prop) (Pure : D → Prop) : Prop :=
  ∀ t S, RequiresLack t S → ¬ Pure t

/-! ## Part 3. The epistemic reading -/

/-- The inquirer's support for a root's lack at `w` is profile-sound: it supports
the lack of `d` only where the admissibility constraints and the root's
determinations settle it (no admissible profile adds `d` to them). This is the
inference "it has `t`, and nothing admissible has `t` with `d`, so it lacks
`d`". -/
def ProfileSoundLackSupport (m : Profile W B) (w : W) (I : Inquiry W F)
    (Admissible : Set D → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, Supported I w (lack r d) →
    ¬ HasCompatibleExtension Admissible (ActualProfile (HasAt w) r) d

/-- Every absence of an actual root at `w` is supported for the inquirer. A
completeness demand on knowledge of the root's profile. -/
def RootLacksKnown (m : Profile W B) (w : W) (I : Inquiry W F)
    (HasAt : W → B → D → Prop) (lack : B → D → F) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, ¬ HasAt w r d → Supported I w (lack r d)

/-! ## Finite controls

The #2153 carrier (worlds and beings `Bool`, universal access, the source
`true` the only actual root at `true`, the five #1970 determinations, the open
admissible family), with lane E's `hasAt` profile assignment. The arena has
one fact per bearer and determination, "the bearer lacks it", and one
contingent `event` that holds only at `true`. The source's necessary lack of
`limiter` is the admitted (non-necessitating) reason for the event; an
inquirer at `true` takes the event as evidence for the event and for the
source's lacking `noesis`. These are assignments of the stated relations,
not models of inquiry, evidence or explanation. -/
namespace Control

open TruthCore.Causality.SourceIntellectControls.ProfileControls (Determination)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)

/-- Facts of the control arena. -/
inductive CFact
  | lack (x : Bool) (d : Determination)
  | event

/-- The fact that `x` lacks `d`. -/
def lackOf (x : Bool) (d : Determination) : CFact := .lack x d

/-- Truth in the control arena, for the source profile `src` at both worlds. -/
def cHolds (src : Set Determination) : Bool → CFact → Prop
  | v, .lack x d => ¬ TruthCore.Causality.RootClosure.Control.hasAt src src v x d
  | v, .event => v = true

/-- The base reasons: at `true`, the source's lack of `limiter` is admitted as
the reason for the event. -/
def cExplains (w : Bool) (r f : CFact) : Prop :=
  w = true ∧ r = .lack true Determination.limiter ∧ f = .event

/-- The base arena on the #2153 frame, with identity as the conjunct relation. -/
def base (src : Set Determination) : Arena Bool Bool CFact where
  ontic := rootProfile.ontic
  holds := cHolds src
  exist := fun _ => .event
  explains := cExplains
  conjunct := fun g f => g = f

/-- The base arena with the necessary truths as reasons for the necessary
truths. -/
def extended (src : Set Determination) : Arena Bool Bool CFact :=
  withReasons (base src) (necessaryReasons (base src))

/-- Truth in `unrepresented`: no lack fact holds anywhere. -/
def uHolds : Bool → CFact → Prop
  | _, .lack _ _ => False
  | v, .event => v = true

/-- The base arena with no lack fact true anywhere: the arena does not represent
the root's absences. -/
def unrepresented (src : Set Determination) : Arena Bool Bool CFact :=
  { base src with holds := uHolds }

/-- At `true` the event is evidence for itself and for the source's lacking
`noesis`. Stipulated support edges, the rival's inquiry. -/
def inquiry : Inquiry Bool CFact :=
  ⟨fun w e p => w = true ∧ e = .event ∧ (p = .event ∨ p = .lack true Determination.noesis)⟩

/-- Essential exclusion of root lacks on the control carrier, the source's
profile `s` at both worlds. -/
abbrev cXN (ess : Bool → Bool → (Set Determination → Prop) → Prop) (s : Set Determination) :
    Prop :=
  RootLacksEssentiallyExcluded rootProfile true ess
    (TruthCore.Causality.RootClosure.Control.hasAt s s)

/-! ### The classical selection carrier

Lane E's `hasSel` (every pure #1970 determination at both worlds, and "has
selected outcome `v`" at world `v`, read as a REAL intrinsic determination).
The family admits a profile with `esse`, without `limiter`, and without both
selections; each selection requires the lack of the other; the source's nature
imposes only admissibility. -/

open TruthCore.Causality.RootClosure.Control (SelDet)

/-- Admissible profiles of the selection carrier. -/
def selAdmissible (q : Set SelDet) : Prop :=
  Sum.inl Determination.esse ∈ q ∧ Sum.inl Determination.limiter ∉ q ∧
    ¬ (Sum.inr true ∈ q ∧ Sum.inr false ∈ q)

/-- Having selected `b` requires the lack of having selected `!b`. -/
def selReq (t : SelDet) (S : Set SelDet) : Prop :=
  ∃ b, t = Sum.inr b ∧ S = {Sum.inr (!b)}

/-- Only the source's nature constrains its profile, and only by admissibility. -/
def essSel (y x : Bool) (C : Set SelDet → Prop) : Prop :=
  y = true ∧ x = true ∧ C = selAdmissible

end Control

/-! ## The certificate -/

open TruthCore.Causality.RootPerfectionExclusion (UnexplainedAbsence NoUnexplainedAbsenceAtRoots)
open TruthCore.Causality.RootPerfectionIntellect (AdmissibleIsExclusionFree)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.RootClosure (RootAbsencesNecessary
  EssenceGroundedRootProfileModality RootEssentialConditionsPositive
  RootEssentialConditionsCarried)
open TruthCore.Logic (ExcludedMiddle)

/-- **What the inquiry family reaches at a root, and what would carry it to E.**

1. Scope, blindness: for any reason relation `e` that agrees with `A` on
   contingent targets, the contingent-fact PSR, `NoBrute`, `TrackingBridge`,
   `SupportCoverage`, `EvidenceBridge`, `GlobalDefeat`,
   `NoBruteEvidenceAlternative`, `ReasonIndependent` and
   `IrreflexiveContingent` hold of `withReasons A e` exactly when they hold of
   `A`. The unrestricted `FactPSR` is not invariant (`allNecessary` with every
   reason removed).
2. Scope, the mechanism: no brute-evidence alternative exists for a hypothesis
   true at every accessible world, and the contingent-fact PSR at every
   accessible world meets the skeptical presupposition, with any admitted
   reason.
3. Cheap extension: `necessaryReasons A` agrees with `A` on contingent
   targets; with excluded middle it meets `FactPSR` wherever `A` meets
   `ContingentPSR`, and turns `GlobalDefeat` into `GlobalDefeatUnreasoned`; it
   keeps factivity, necessitation, distribution (under the conjunct law),
   contingent irreflexivity and reason independence.
3b. The why-stances of `BruteContingencyParity` are not covered by 1:
   `WhyHonors` and `ExcludesUnreasonedAcceptance` quantify over whatever the
   stance accepts and requires a reason why for, necessary facts included
   (`ExcludesUnreasonedAcceptance` is written for a necessary `o`). Under the
   cheap extension, with excluded middle, the contingent-fact PSR and a
   stance that accepts only facts true at `w`, both hold: the stance's demand
   is met for every accepted fact, a root's necessary lack included, by an
   admitted reason. (`FeatureUniform` mentions no arena and is unaffected.)
4. Quality at necessary targets: with excluded middle, factive reasons that
   are `WorkIndependent` at every reason give every explained necessary truth
   a contingent reason; so with `FactPSR` at a world with a true fact and no
   contingent fact they are inconsistent.
5. Root lacks under N: on the profile's frame, with lack facts represented,
   every lack of an actual root is a fact true at every accessible world and
   not contingent, so the nine conditions of 1 are blind to its reasons.
6. The contingent branch: with lack facts represented, EM and EP (lane E), the
   contingent-fact PSR gives every unexplained absence at an actual root an
   admitted reason, and the lack is contingent.
7. Factorization: `RootLackReasonsEssential`, LE and the necessity direction of
   member grounding give the sense bridge `RootLackReasonsPositive`.
8. The epistemic reading: profile-sound support never supports an unexplained
   absence, and profile-sound support of every absence of an actual root
   gives E.
9. Reference class, both sides: if only impure determinations require lacks
   and an actual root's determinations are all pure, every positively fixed
   absence at that root is fixed at the admissibility level (case i or ii),
   for the classical root as for any other.
10. The rival with the full inquiry stance (#2153 carrier, open family,
    nothing requires a lack, the source's profile `{esse, a, b}` at both
    worlds, the extended arena): N, the lack facts, the unrestricted fact PSR
    at both worlds with factive, distributing, contingently irreflexive and
    independent reasons, the nine conditions of 1 including
    `GlobalDefeatUnreasoned`, support for the source's lacking `noesis`, and
    the necessity direction of member grounding all hold; E and the sense
    bridge fail.
11. The same carrier with the base arena, in which no lack fact has a reason:
    every contingent-scoped inquiry condition of 1 still holds (by 1, since the
    base and extended arenas agree on contingent targets), and the PSR for
    root lack facts and `FactPSR` fail. No inquiry condition of the #756 family
    implies a reason for a root's necessary lack. -/
def InquiryScopeMap : Prop :=
  -- 1. blindness
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (e : W → F → F → Prop),
    AgreeOnContingent A e →
      (∀ w, (ContingentPSR A w ↔ ContingentPSR (withReasons A e) w) ∧
        (NoBrute A w ↔ NoBrute (withReasons A e) w) ∧
        (TrackingBridge A I w ↔ TrackingBridge (withReasons A e) I w) ∧
        (SupportCoverage A I w ↔ SupportCoverage (withReasons A e) I w) ∧
        (EvidenceBridge A I w ↔ EvidenceBridge (withReasons A e) I w) ∧
        (GlobalDefeat A I w ↔ GlobalDefeat (withReasons A e) I w) ∧
        (NoBruteEvidenceAlternative A I w ↔
          NoBruteEvidenceAlternative (withReasons A e) I w)) ∧
      (ReasonIndependent A ↔ ReasonIndependent (withReasons A e)) ∧
      (IrreflexiveContingent A ↔ IrreflexiveContingent (withReasons A e))) ∧
  (AgreeOnContingent allNecessary (fun _ _ _ => False) ∧ FactPSR allNecessary false ∧
    ¬ FactPSR (withReasons allNecessary (fun _ _ _ => False)) false) ∧
  -- 2. the skeptical mechanism
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (e p : F),
    NecessaryFact A w p → ¬ BruteEvidenceAlternative A w e p) ∧
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W),
    (∀ v, Access A w v → ContingentPSR A v) → NoBruteEvidenceAlternative A I w) ∧
  -- 3. the cheap scope extension
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W),
    AgreeOnContingent A (necessaryReasons A) ∧
    (ExcludedMiddle → ContingentPSR A w → FactPSR (withReasons A (necessaryReasons A)) w) ∧
    (ExcludedMiddle → GlobalDefeat A I w →
      GlobalDefeatUnreasoned (withReasons A (necessaryReasons A)) I w) ∧
    (Factive A → Factive (withReasons A (necessaryReasons A))) ∧
    (Necessitating A → Necessitating (withReasons A (necessaryReasons A))) ∧
    (ConjunctSound A → Distribution A → Distribution (withReasons A (necessaryReasons A))) ∧
    (IrreflexiveContingent A →
      IrreflexiveContingent (withReasons A (necessaryReasons A))) ∧
    (ReasonIndependent A → ReasonIndependent (withReasons A (necessaryReasons A)))) ∧
  -- 3b. the #756 why-stances with an ontic demand under the cheap extension
  (∀ (W B F : Type) (A : Arena W B F) (w : W)
    (S : TruthCore.Explanation.BruteContingencyParity.WhyStance F),
    ExcludedMiddle → ContingentPSR A w → (∀ f, S.accepts f → A.holds w f) →
      TruthCore.Explanation.BruteContingencyParity.WhyHonors S
        (withReasons A (necessaryReasons A)) w ∧
      ∀ o, TruthCore.Explanation.BruteContingencyParity.ExcludesUnreasonedAcceptance S
        (withReasons A (necessaryReasons A)) w o) ∧
  -- 4. independence at necessary targets
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (r f : F),
    ExcludedMiddle → Factive A → (∀ s, WorkIndependent A w s) → A.explains w r f →
      NecessaryFact A w f → Contingent A w r) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (f : F),
    ExcludedMiddle → FactPSR A w → Factive A → (∀ s, WorkIndependent A w s) →
      A.holds w f → (∀ g, ¬ Contingent A w g) → False) ∧
  -- 5. root lacks under N
  (∀ (W B F D : Type) (m : Profile W B) (A : Arena W B F) (w : W)
    (HasAt : W → B → D → Prop) (lack : B → D → F),
    A.ontic = m.ontic → LackFactsRepresent A HasAt lack → RootAbsencesNecessary m w HasAt →
      ∀ r, ActualRoot m w r → ∀ d, ¬ HasAt w r d →
        A.holds w (lack r d) ∧ NecessaryFact A w (lack r d) ∧ ¬ Contingent A w (lack r d)) ∧
  -- 6. the contingent branch
  (∀ (W B F D : Type) (m : Profile W B) (A : Arena W B F) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (lack : B → D → F),
    A.ontic = m.ontic → LackFactsRepresent A HasAt lack →
    EssenceGroundedRootProfileModality m w Ess HasAt →
    RootEssentialConditionsPositive m w Admissible Ess HasAt → ContingentPSR A w →
      ∀ r, ActualRoot m w r → ∀ d, UnexplainedAbsence Admissible (HasAt w) r d →
        Contingent A w (lack r d) ∧ Explained A w (lack r d)) ∧
  -- 7. factorization of the sense bridge through LE
  (∀ (W B F D : Type) (m : Profile W B) (A : Arena W B F) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (RequiresLack : D → Set D → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F),
    RootLackReasonsEssential m w A Ess HasAt lack →
    RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack →
    AdmissibleIsExclusionFree Admissible RequiresLack →
      RootLackReasonsPositive m w A Admissible RequiresLack HasAt lack) ∧
  -- 8. the epistemic reading
  (∀ (W B F D : Type) (m : Profile W B) (I : Inquiry W F) (w : W)
    (Admissible : Set D → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F),
    ProfileSoundLackSupport m w I Admissible HasAt lack →
      (∀ r, ActualRoot m w r → ∀ d, UnexplainedAbsence Admissible (HasAt w) r d →
        ¬ Supported I w (lack r d)) ∧
      (RootLacksKnown m w I HasAt lack → NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w))) ∧
  -- 9. the reference-class generalization binds both sides
  (∀ (W B D : Type) (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (HasAt : W → B → D → Prop) (Pure : D → Prop),
    CarriersImpure RequiresLack Pure → ActualRootDeterminationsArePure m w (HasAt w) Pure →
      ∀ r, ActualRoot m w r → ∀ d,
        PositivelyFixedAbsence Admissible RequiresLack (HasAt w) r d →
          ¬ HasCompatibleExtension Admissible (ActualProfile (HasAt w) r) d) ∧
  -- 10. the rival with the full inquiry stance
  (let rival := Control.extended
      TruthCore.Causality.SourceIntellectControls.ProfileControls.positive
   let hasAt := TruthCore.Causality.RootClosure.Control.hasAt
      TruthCore.Causality.SourceIntellectControls.ProfileControls.positive
      TruthCore.Causality.SourceIntellectControls.ProfileControls.positive
   let open_ := TruthCore.Causality.SourceIntellectControls.ProfileControls.openProfile
   let noReq := TruthCore.Causality.RootClosure.Control.noReq
   let root := TruthCore.Causality.IntentionalExemplarExtension.Control.rootProfile
   let noe := TruthCore.Causality.SourceIntellectControls.ProfileControls.Determination.noesis
   rival.ontic = root.ontic ∧ LackFactsRepresent rival hasAt Control.lackOf ∧
    RootAbsencesNecessary root true hasAt ∧
    RootLackFactsAt root true rival hasAt Control.lackOf ∧
    RootLackPSR root true rival Control.lackOf ∧
    FactPSR rival true ∧ FactPSR rival false ∧ Factive rival ∧ Distribution rival ∧
    IrreflexiveContingent rival ∧ ReasonIndependent rival ∧
    ContingentPSR rival true ∧ NoBrute rival true ∧
    TrackingBridge rival Control.inquiry true ∧
    SupportCoverage rival Control.inquiry true ∧
    EvidenceBridge rival Control.inquiry true ∧
    GlobalDefeat rival Control.inquiry true ∧
    GlobalDefeatUnreasoned rival Control.inquiry true ∧
    NoBruteEvidenceAlternative rival Control.inquiry true ∧
    Contingent rival true Control.CFact.event ∧
    Supported Control.inquiry true (Control.lackOf true noe) ∧
    Explained rival true (Control.lackOf true noe) ∧
    AdmissibleIsExclusionFree open_ noReq ∧
    ¬ NoUnexplainedAbsenceAtRoots root true open_ (hasAt true) ∧
    ¬ RootLackReasonsPositive root true rival open_ noReq hasAt Control.lackOf) ∧
  -- 11. the contingent-scoped conditions without any reason for a root lack
  (let base := Control.base TruthCore.Causality.SourceIntellectControls.ProfileControls.positive
   let root := TruthCore.Causality.IntentionalExemplarExtension.Control.rootProfile
   ContingentPSR base true ∧ NoBrute base true ∧
    TrackingBridge base Control.inquiry true ∧ SupportCoverage base Control.inquiry true ∧
    EvidenceBridge base Control.inquiry true ∧ GlobalDefeat base Control.inquiry true ∧
    NoBruteEvidenceAlternative base Control.inquiry true ∧
    ReasonIndependent base ∧ IrreflexiveContingent base ∧
    ¬ RootLackPSR root true base Control.lackOf ∧ ¬ FactPSR base true)

end TruthCore.Explanation.InquiryClosure
