module

public import TruthCore.Explanation.InquiryClosure
public import TruthCore.Causality.PossibiliaContent

/-! # Carriage from the unity of a simple root? (#2145, lane U)

Analyst formulations, attribution deferred. The target is LE
(`RootClosure.RootEssentialConditionsCarried`, `682e6436`): an ESSENCE_6
condition on an actual root's profile can fail at an admissible extension of
that profile only where some determination of the root requires the lack of
members of it. Lanes E (#2174) and H2 (#2182) left LE unsupported at a pure
root. The owner-selected question: can LE be argued from the *unity* of a
simple being? In a being without real composition there seems to be nothing
other than its one nature for an essential exclusion to be carried by.

**Reused.** Constitutive simplicity (`ObjectiveEminence.ConstitutivelySimple`,
DEF `d6912ecb`: at most one real constituent) and its root reading
`PossibiliaContent.RootsConstitutivelySimple` (`f4180d0c`); ESSENCE_6
(`RootClosure.ProfileEssentialCondition`); the requirement relation
`RequiresLack` of `RootPerfectionIntellect` (DEF `88f7c656`); the necessity
direction of member grounding (`89c988d9`); essential exclusion of root
absences (XN, `b2d6ac16`) and E (`9281317d`).

**Two new primitives.** `Seat x C k` reads "the condition `C` on `x`'s profile
belongs to what `x`'s constituent `k` is". `Realizes x k d` reads "`x` has the
determination `d` by its constituent `k`" (`k` is the reality of `d` in `x`).
Neither is defined; their meanings, examples and distinguishing conditions are
in the doc comments of `SeatedIn` and `RealizedBy` and in their DEF records.

**Two senses of requiring a lack (REQUIRES_LACK).** The existing relation is
REQUIRES_LACK_1, `RequiresLackAsSuch`: it belongs to what the determination
`d` is, *as such*, that a bearer of `d` does not have every member of `S`. It is
type-level: it binds every bearer of `d`, and it is the sense in which member
grounding and the purity of requirements (`0c8631bd`) speak. The unity argument
also reaches a second, bearer-relative relation, REQUIRES_LACK_2,
`RequiresLackIn`: it belongs to what `d` is *as realized in* `x` that `x` does
not have every member of `S`. On the classical identity thesis for a simple
being (its one constituent is, in reality, each determination it has), what
belongs to the constituent belongs to each of its determinations as realized in
it, so the unity transfer is natural in sense 2. Neither sense is defined from
the other; the passage from 2 to 1 at actual roots is the explicit open bridge
`RootRequirementsInHoldAsSuch`.

**The unity premises.** For actual roots at `w`:
* `RootOwnConditionsSeated` (SEAT): every ESSENCE_6 condition in a root's own
  nature on its profile belongs to what some real constituent of it is;
* `RootDeterminationsRealized` (REAL): every determination a root has, it has
  by some real constituent of it;
* `RootsHaveSomeDetermination` (ESSE): every root has some determination;
* `RootSeatedExclusionsRequiredAsSuch` (TRANSFER_1) and
  `RootSeatedExclusionsRequiredIn` (TRANSFER_2): a seated condition holds at
  every admissible extension of the root's profile in which no determination
  that its seat realizes requires (in the respective sense) the lack of members
  of that extension, provided the seat realizes some determination of the
  root.

The results module derives own-nature carriage from simplicity and these
premises in each sense, shows that at a simple root TRANSFER_1 and own-nature
carriage are equivalent (the relocation), derives E from own-nature exclusion,
own-nature carriage and member grounding, derives every pure perfection at the
roots from carriage in the root and the purity of requirements in the root
(`RootPureRequiresNoPureLackIn`) without carriage as such, the sense bridge or
member grounding, and gives finite controls.
-/

@[expose] public section

namespace TruthCore.Causality.SimpleUnityCarriage

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPerfectionExclusion (ActualProfile)
open TruthCore.Causality.RootClosure (ProfileEssentialCondition)

variable {W B D K : Type}

/-! ## Senses and primitives -/

/-- REQUIRES_LACK_1, requiring a lack *as such*: it belongs to what the
determination `d` is that a bearer of `d` does not have every member of `S`
(DEF `88f7c656`). A parameter wrapper over the primitive `RequiresLack` of
`RootPerfectionIntellect`. It is type-level: it binds every bearer of `d`.
Example: having exactly two units of extent requires the lack of having exactly
three, in any bearer. Non-example: a bearer's lacking `noesis` because of
something peculiar to that bearer, while other bearers of `d` have `noesis`. -/
def RequiresLackAsSuch (RequiresLack : D → Set D → Prop) (d : D) (S : Set D) : Prop :=
  RequiresLack d S

/-- REQUIRES_LACK_2, requiring a lack *in a bearer*: it belongs to what `d` is
as realized in `x` that `x` does not have every member of `S`. A parameter
wrapper over a declared PRIMITIVE `ReqIn : B → D → Set D → Prop`. It is
bearer-relative: `d`'s requiring a lack in `x` says nothing about other bearers
of `d`. Examples: in a simple being whose one nature excludes `k`, each
determination of that being, as realized in it (being, on the identity thesis,
that one nature), requires the lack of `k` in it. Every requirement as such of
a determination `x` has is plausibly also one in `x` (the converse bridge,
not asserted here). Non-example: a requirement of a determination in another
bearer. Distinguishing condition: unlike REQUIRES_LACK_1 it does not bind the
bearer-neutral admissible family through member grounding, which is stated
with REQUIRES_LACK_1. -/
def RequiresLackIn (ReqIn : B → D → Set D → Prop) (x : B) (d : D) (S : Set D) : Prop :=
  ReqIn x d S

/-- SEATED_IN: the ESSENCE_6 condition `C` on `x`'s profile lies in `x`'s own
nature and belongs to what `x`'s constituent `k` is. A wrapper over the
declared PRIMITIVE `Seat : B → (Set D → Prop) → K → Prop`, conjoined with the
own-nature ESSENCE_6 condition. Intended meaning: the constituent `k` is where
the condition is in `x`, its content being part of what `k` is. Examples: a
triangle's having exactly three sides belongs to what its form is; in a simple
being, every condition of its nature belongs to what its one nature is.
Non-examples: a condition in another being's nature (not own); a negation
considered as an item, which is not a real constituent (DEF `d6912ecb`).
Distinguishing conditions: it is not requiring a lack (it relates a condition
to a constituent, not a determination to a set), and it is not realization (it
does not say which determinations the constituent is the reality of). -/
def SeatedIn (Ess : B → B → (Set D → Prop) → Prop) (Seat : B → (Set D → Prop) → K → Prop)
    (x : B) (C : Set D → Prop) (k : K) : Prop :=
  ProfileEssentialCondition Ess x x C ∧ Seat x C k

/-- REALIZES: `x` has the determination `d` by its constituent `k`; `k` is the
reality of `d` in `x`. A wrapper over the declared PRIMITIVE
`Realizes : B → K → D → Prop`. Examples: a body has its shape by its form; on
the classical account, a simple being has its being, its wisdom and its power
each by its one nature. Non-examples: a constituent that is a principle of
limitation (prime matter, a bare limit) realizes no actuality. Distinguishing
conditions: it is not identity of `k` with `d` (one constituent may realize
several determinations distinguished by reason), and it is not causation.
Whether realization at a simple being is real identity, and whether it is the
same at every world, are not encoded. -/
def RealizedBy (Realizes : B → K → D → Prop) (x : B) (k : K) (d : D) : Prop :=
  Realizes x k d

/-! ## The unity premises -/

/-- OPEN (SEAT): every ESSENCE_6 condition in an actual root's own nature on its
profile belongs to what some real constituent of it is. No condition of a
root's nature floats free of everything real in it. -/
def RootOwnConditionsSeated (m : Profile W B) (w : W) (Ess : B → B → (Set D → Prop) → Prop)
    (RealConstituent : B → K → Prop) (Seat : B → (Set D → Prop) → K → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ C, ProfileEssentialCondition Ess r r C →
    ∃ k, RealConstituent r k ∧ SeatedIn Ess Seat r C k

/-- OPEN (REAL): every determination an actual root has at `w`, it has by some
real constituent of it. Every real determination has a real constituent as its
reality. -/
def RootDeterminationsRealized (m : Profile W B) (w : W) (HasAt : W → B → D → Prop)
    (RealConstituent : B → K → Prop) (Realizes : B → K → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ t, HasAt w r t → ∃ k, RealConstituent r k ∧ RealizedBy Realizes r k t

/-- OPEN (ESSE): every actual root has some determination at `w` (for example
its being). -/
def RootsHaveSomeDetermination (m : Profile W B) (w : W) (HasAt : W → B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∃ t, HasAt w r t

/-- OPEN (TRANSFER_1), in REQUIRES_LACK_1: for every actual root `r`, a
condition seated in a real constituent `k` of `r` that realizes some
determination of `r` holds at every admissible extension `q` of `r`'s profile
in which no determination of `r` realized by `k` requires, as such, the lack of
some members of `q`. Read contrapositively (classically): where such a seated
condition fails at an admissible extension `q`, some determination of `r` that
its seat realizes requires, as such, the joint lack of some members of `q`. A
seat that realizes nothing (a bare limit) is exempt. -/
def RootSeatedExclusionsRequiredAsSuch (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RealConstituent : B → K → Prop) (Seat : B → (Set D → Prop) → K → Prop)
    (Realizes : B → K → D → Prop) (RequiresLack : D → Set D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ C k, RealConstituent r k → SeatedIn Ess Seat r C k →
    (∃ t, HasAt w r t ∧ RealizedBy Realizes r k t) →
    ∀ q, Admissible q → ActualProfile (HasAt w) r ⊆ q →
      (∀ t, HasAt w r t → RealizedBy Realizes r k t → ∀ S ⊆ q,
        ¬ RequiresLackAsSuch RequiresLack t S) → C q

/-- OPEN (TRANSFER_2), the same with REQUIRES_LACK_2: where a seated condition
fails at an admissible extension `q`, some determination of the root that its
seat realizes requires, *in the root*, the joint lack of some members of `q`. Its rationale is the identity
thesis for a simple being (its one constituent is, in reality, each
determination it realizes), with the closure of what belongs to a constituent
under the exclusion that a failing condition expresses. -/
def RootSeatedExclusionsRequiredIn (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RealConstituent : B → K → Prop) (Seat : B → (Set D → Prop) → K → Prop)
    (Realizes : B → K → D → Prop) (ReqIn : B → D → Set D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ C k, RealConstituent r k → SeatedIn Ess Seat r C k →
    (∃ t, HasAt w r t ∧ RealizedBy Realizes r k t) →
    ∀ q, Admissible q → ActualProfile (HasAt w) r ⊆ q →
      (∀ t, HasAt w r t → RealizedBy Realizes r k t → ∀ S ⊆ q,
        ¬ RequiresLackIn ReqIn r t S) → C q

/-! ## Own-nature carriage and exclusion -/

/-- OPEN (LE_own), the own-nature restriction of LE in REQUIRES_LACK_1: every
ESSENCE_6 condition in an actual root's own nature on its profile holds at every
admissible extension of that profile in which no determination of the root
requires, as such, the lack of some members of the extension. LE quantifies
over conditions in any being's nature and gives this one. -/
def RootOwnEssentialConditionsCarried (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RequiresLack : D → Set D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ C, ProfileEssentialCondition Ess r r C →
    ∀ q, Admissible q → ActualProfile (HasAt w) r ⊆ q →
      (∀ t, HasAt w r t → ∀ S ⊆ q, ¬ RequiresLackAsSuch RequiresLack t S) → C q

/-- OPEN (LE_in), own-nature carriage in REQUIRES_LACK_2: the same with
requirements in the root. A bare negative clause "lacks `k`" in a simple
root's one nature, carried by that nature as realized in the root, satisfies
it. -/
def RootOwnEssentialConditionsCarriedIn (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (ReqIn : B → D → Set D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ C, ProfileEssentialCondition Ess r r C →
    ∀ q, Admissible q → ActualProfile (HasAt w) r ⊆ q →
      (∀ t, HasAt w r t → ∀ S ⊆ q, ¬ RequiresLackIn ReqIn r t S) → C q

/-- OPEN sense bridge from REQUIRES_LACK_2 to REQUIRES_LACK_1 at actual roots:
whatever a determination of an actual root requires to be lacking in the root,
it requires to be lacking as such, in every bearer. It is false for a
determination that the root shares with a bearer that has the excluded items
(whatever the root's nature excludes in it, the shared determination as such
does not). It is near-analytic for a determination that only bearers of the
root's nature can have (a "this nature" determination). -/
def RootRequirementsInHoldAsSuch (m : Profile W B) (w : W) (HasAt : W → B → D → Prop)
    (RequiresLack : D → Set D → Prop) (ReqIn : B → D → Set D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ t S, HasAt w r t → RequiresLackIn ReqIn r t S →
    RequiresLackAsSuch RequiresLack t S

/-- OPEN (XN_own): every absence of an actual root at `w` is excluded by some
ESSENCE_6 condition in the root's own nature, given its profile. The own-nature
restriction of XN (`b2d6ac16`). Its rationale: a root has no actual concrete
ground, so a nature that excludes what it lacks is its own. -/
def RootLacksExcludedByOwnNature (m : Profile W B) (w : W)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, ¬ HasAt w r d →
    ∃ C, ProfileEssentialCondition Ess r r C ∧
      ∀ q, ActualProfile (HasAt w) r ⊆ q → d ∈ q → ¬ C q

/-- OPEN (purity of requirements in the root, REQUIRES_LACK_2): no pure
determination of an actual root requires, in the root, the lack of pure
determinations. The in-root counterpart of `PureRequiresNoPureLack`
(`0c8631bd`), restricted to actual roots. Its rationale is the same:
requiring the lack of a positive actuality is a limitation of the requirer,
here of the determination as realized in the root. It is restricted to roots
because a pure determination realized in a finite bearer can require there the
lack of a pure one (a finite knower's knowing excludes knowing everything at
once). With the bridge from REQUIRES_LACK_2 to REQUIRES_LACK_1 it follows from
`0c8631bd`. The Plotinian line (the unity of the first excludes the duality of
thought, and this is no limitation) denies it. -/
def RootPureRequiresNoPureLackIn (m : Profile W B) (w : W) (HasAt : W → B → D → Prop)
    (Pure : D → Prop) (ReqIn : B → D → Set D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ t S, HasAt w r t → Pure t → (∀ e ∈ S, Pure e) →
    ¬ RequiresLackIn ReqIn r t S

/-- Every real constituent of an actual root realizes some determination it has.
Lean-only: the reading on which constituents are themselves real determinations
(DEF `3aba5f19`: "an intrinsic constituent or a real relation"). On this reading
simplicity is idle in the derivation of own-nature carriage. -/
def RootConstituentsRealize (m : Profile W B) (w : W) (HasAt : W → B → D → Prop)
    (RealConstituent : B → K → Prop) (Realizes : B → K → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ k, RealConstituent r k → ∃ t, HasAt w r t ∧ RealizedBy Realizes r k t

/-! ## Finite controls

The #2153 carrier (worlds and beings `Bool`, universal access, the source `true`
the only actual root at `true`, the five #1970 determinations, the open
admissible family `openProfile`), lane E's `hasAt` assignment (the effect has
`esse` and `noesis`), and constituents `Bool`: `true` is the source's nature,
`false` a second constituent used only in the composite row. These are
assignments of the stated relations, not models of essence, constituency,
realization or requirement. -/
namespace Control

open TruthCore.Causality.SourceIntellectControls.ProfileControls
  (Determination openProfile positive)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootClosure.Control (hasAt noNoesis essOpen essNeg noReq)

/-- The source's only real constituent is `true` (simple). -/
def simpleRC (x k : Bool) : Prop := x = true ∧ k = true

/-- The source has two real constituents (composite). -/
def compositeRC (x _ : Bool) : Prop := x = true

/-- Every condition of the source's nature is in its one constituent `true`. -/
def seatAll (x : Bool) (_ : Set Determination → Prop) (k : Bool) : Prop := x = true ∧ k = true

/-- Composite seating: admissibility in the nature constituent, the clause
"lacks `noesis`" in the second constituent (a limit). -/
def seatSplit (x : Bool) (C : Set Determination → Prop) (k : Bool) : Prop :=
  x = true ∧ ((C = openProfile ∧ k = true) ∨ (C = noNoesis ∧ k = false))

/-- Only admissibility is seated; the clause floats free. -/
def seatOpenOnly (x : Bool) (C : Set Determination → Prop) (k : Bool) : Prop :=
  x = true ∧ C = openProfile ∧ k = true

/-- The constituent `true` realizes every determination in `src`. -/
def realizesSrc (src : Set Determination) (x k : Bool) (d : Determination) : Prop :=
  x = true ∧ k = true ∧ d ∈ src

/-- Nothing realizes anything. -/
def realizesNone (_ _ : Bool) (_ : Determination) : Prop := False

/-- No requirement in a bearer. -/
def noReqIn (_ : Bool) (_ : Determination) (_ : Set Determination) : Prop := False

/-- In the source, its `esse` (as realized in it, that is, its one nature)
requires the lack of `noesis`. -/
def esseExcludesNoesisIn (x : Bool) (d : Determination) (S : Set Determination) : Prop :=
  x = true ∧ d = Determination.esse ∧ S = {Determination.noesis}

/-- Determinations of the fine-grained carrier: the #1970 determinations and
`inr ()`, the source's "this nature" determination (had only by the source). -/
abbrev NatDet := Determination ⊕ Unit

/-- Fine-grained admissibility: `esse`, no `limiter`, and not the source's nature
together with `noesis`. -/
def natAdmissible (q : Set NatDet) : Prop :=
  Sum.inl Determination.esse ∈ q ∧ Sum.inl Determination.limiter ∉ q ∧
    ¬ (Sum.inr () ∈ q ∧ Sum.inl Determination.noesis ∈ q)

/-- The source has `esse`, `a`, `b` and its nature determination; the effect has
`esse` and `noesis`; the same at both worlds. -/
def natHas (_ : Bool) : Bool → NatDet → Prop
  | true, d => d = .inl .esse ∨ d = .inl .a ∨ d = .inl .b ∨ d = .inr ()
  | false, d => d = .inl .esse ∨ d = .inl .noesis

/-- The condition "lacks `noesis`" on the fine-grained carrier. -/
def natNoNoesis (q : Set NatDet) : Prop := Sum.inl Determination.noesis ∉ q

/-- The source's nature imposes fine-grained admissibility and "lacks `noesis`". -/
def natEss (y x : Bool) (C : Set NatDet → Prop) : Prop :=
  y = true ∧ x = true ∧ (C = natAdmissible ∨ C = natNoNoesis)

/-- Every condition of the source's nature is in its one constituent. -/
def natSeat (x : Bool) (_ : Set NatDet → Prop) (k : Bool) : Prop := x = true ∧ k = true

/-- The one constituent realizes every determination of the source. -/
def natRealizes (x k : Bool) (d : NatDet) : Prop := x = true ∧ k = true ∧ natHas true true d

/-- The source's nature determination requires, as such, the lack of `noesis`. -/
def natReq (d : NatDet) (S : Set NatDet) : Prop :=
  d = Sum.inr () ∧ S = {Sum.inl Determination.noesis}

/-- The same requirement in the source. -/
def natReqIn (x : Bool) (d : NatDet) (S : Set NatDet) : Prop := x = true ∧ natReq d S

/-- Purity on the fine-grained carrier with the nature determination pure (the
Plotinian reading: excluding `noesis` is not a limitation of it). -/
def natPurePlotinian (d : NatDet) : Prop := d ≠ Sum.inl Determination.limiter

/-- Purity on the fine-grained carrier with the nature determination impure. -/
def natPureStrict (d : NatDet) : Prop :=
  d ≠ Sum.inl Determination.limiter ∧ d ≠ Sum.inr ()

/-- Selection carrier (lane E's `hasSel`, H2's `selAdmissible`, `selReq`,
`essSel`): every condition of the source's nature is in its one constituent. -/
def selSeat (x : Bool) (_ : Set TruthCore.Causality.RootClosure.Control.SelDet → Prop)
    (k : Bool) : Prop :=
  x = true ∧ k = true

/-- The one constituent realizes every determination the source has at `true`
(its pure determinations and, on the real-determination reading, its selection
of `true`). Realization is encoded at the actual world only. -/
def selRealizes (x k : Bool) (d : TruthCore.Causality.RootClosure.Control.SelDet) : Prop :=
  x = true ∧ k = true ∧ TruthCore.Causality.RootClosure.Control.hasSel true true d

end Control

open Control
open TruthCore.Causality.SourceIntellectControls.ProfileControls
  (Determination openProfile positive)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootClosure.Control (hasAt noNoesis essOpen essNeg noReq)
open TruthCore.Causality.RootClosure (RootEssentialConditionsCarried)
open TruthCore.Causality.RootPerfectionIntellect (AdmissibleIsExclusionFree PureRequiresNoPureLack)
open TruthCore.Causality.RootPerfectionExclusion (NoUnexplainedAbsenceAtRoots)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.PossibiliaContent (RootsConstitutivelySimple)

/-- The unity premises (S, SEAT, REAL, ESSE) on the #2153 carrier with source
profile `src` at both worlds. -/
abbrev cUnity (ess : Bool → Bool → (Set Determination → Prop) → Prop)
    (src : Set Determination) (rc : Bool → Bool → Prop)
    (seat : Bool → (Set Determination → Prop) → Bool → Prop)
    (rl : Bool → Bool → Determination → Prop) : Prop :=
  RootsConstitutivelySimple rootProfile true rc ∧
    RootOwnConditionsSeated rootProfile true ess rc seat ∧
    RootDeterminationsRealized rootProfile true (hasAt src src) rc rl ∧
    RootsHaveSomeDetermination rootProfile true (hasAt src src)

/-- The certificate of lane U. Clauses:
1. On the constituents-realize reading simplicity is idle: SEAT, every
   constituent realizing a determination, and TRANSFER_1 give own-nature
   carriage, for any carrier.
2. Classical row: source with every pure determination, nature imposing only
   admissibility, one constituent seating it and realizing everything, no
   requirement. The unity premises, TRANSFER_1, TRANSFER_2, own-nature carriage
   in both senses, LE, the necessity direction, own-nature exclusion and E hold.
3. Rival row: source with `{esse, a, b}`, nature also containing "lacks
   `noesis`", one constituent seating both and realizing `esse`, `a`, `b`, its
   `esse` requiring the lack of `noesis` in it, nothing requiring a lack as
   such. The unity premises, TRANSFER_2, LE_in, own-nature exclusion, the
   necessity direction and the purity of requirements hold; TRANSFER_1, LE_own,
   LE, the bridge from sense 2 to sense 1, E and the purity of requirements
   in the root fail.
4. Joint compossibility: on the open family, with the necessity direction,
   whatever the requirement relation, own-nature carriage as such fails for
   the source of clause 3 (the admissible `pure` contains its determinations
   and `noesis`), and `esse`, which the thinking effect shares, does not
   require the lack of `noesis` as such (the effect's profile `{esse, noesis}`
   is admissible).
5. Simplicity omitted: two constituents, the clause seated in a second
   constituent that realizes nothing. SEAT, REAL, ESSE and TRANSFER_1 hold,
   simplicity and own-nature carriage fail.
6. SEAT omitted: the clause is seated nowhere. S, REAL, ESSE, TRANSFER_1 hold,
   SEAT and own-nature carriage fail.
7. REAL omitted: nothing realizes anything. S, SEAT, ESSE, TRANSFER_1 hold,
   REAL and own-nature carriage fail.
8. ESSE omitted: the source has no determination. S, SEAT, REAL, TRANSFER_1
   hold, ESSE and own-nature carriage fail.
9. The necessity direction is independent of the unity package: the clause
   carried by the pure `a` as such, with the open family. The unity premises,
   TRANSFER_1, own-nature carriage hold; the necessity direction and E fail.
10. Fine-grained rival: the source's own "this nature" determination requires
   the lack of `noesis` as such. The unity premises, TRANSFER_1, own-nature
   carriage, the necessity direction and E hold (the lack is case ii). With the
   nature determination pure, the purity of requirements fails and strict
   purity holds; with it impure, the purity of requirements holds and strict
   purity fails.
11. Classical selection carrier (lane E, H2 row 5): a classical source with
   every pure determination whose selection of an outcome is read as a real
   determination varying across worlds, its nature imposing only
   admissibility, one constituent seating it and realizing at `true` everything
   the source has there. The unity premises, TRANSFER_1, own-nature carriage,
   the necessity direction, own-nature exclusion and E hold; N fails.
   Realization is encoded at the actual world only, so whether one world-
   invariant constituent can realize different selections at different worlds
   is not tested.
12. The in-root route to every pure perfection: the classical source of
   clause 2 meets the purity of requirements in the root and has every pure
   determination; the source of clause 3 meets strict purity, the
   admissibility of its profile, the admissibility of each pure determination
   and joint compossibility on the open family (together with own-nature
   exclusion and carriage in the root from clause 3), fails the purity of
   requirements in the root (clause 3), and lacks a pure determination. -/
def SimpleUnityCarriageMap : Prop :=
  (∀ {W B D K : Type} (m : Profile W B) (w : W) (Admissible : Set D → Prop)
      (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
      (RealConstituent : B → K → Prop) (Seat : B → (Set D → Prop) → K → Prop)
      (Realizes : B → K → D → Prop) (RequiresLack : D → Set D → Prop),
      RootOwnConditionsSeated m w Ess RealConstituent Seat →
      RootConstituentsRealize m w HasAt RealConstituent Realizes →
      RootSeatedExclusionsRequiredAsSuch m w Admissible Ess HasAt RealConstituent Seat Realizes
        RequiresLack →
      RootOwnEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack) ∧
  (cUnity essOpen TruthCore.Causality.SourceIntellectControls.ProfileControls.pure simpleRC
      seatAll (realizesSrc TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essOpen
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) simpleRC seatAll
      (realizesSrc TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) noReq ∧
    RootSeatedExclusionsRequiredIn rootProfile true openProfile essOpen
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) simpleRC seatAll
      (realizesSrc TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) noReqIn ∧
    RootOwnEssentialConditionsCarried rootProfile true openProfile essOpen
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) noReq ∧
    RootOwnEssentialConditionsCarriedIn rootProfile true openProfile essOpen
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) noReqIn ∧
    RootEssentialConditionsCarried rootProfile true openProfile essOpen
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) noReq ∧
    AdmissibleIsExclusionFree openProfile noReq ∧
    RootLacksExcludedByOwnNature rootProfile true essOpen
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) ∧
    NoUnexplainedAbsenceAtRoots rootProfile true openProfile
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure true)) ∧
  (cUnity essNeg positive simpleRC seatAll (realizesSrc positive) ∧
    RootSeatedExclusionsRequiredIn rootProfile true openProfile essNeg (hasAt positive positive)
      simpleRC seatAll (realizesSrc positive) esseExcludesNoesisIn ∧
    RootOwnEssentialConditionsCarriedIn rootProfile true openProfile essNeg
      (hasAt positive positive) esseExcludesNoesisIn ∧
    RootLacksExcludedByOwnNature rootProfile true essNeg (hasAt positive positive) ∧
    AdmissibleIsExclusionFree openProfile noReq ∧
    PureRequiresNoPureLack noReq TruthCore.Causality.RootPerfectionExclusion.Control.isPure ∧
    ¬ RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) simpleRC seatAll (realizesSrc positive) noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq ∧
    ¬ RootEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq ∧
    ¬ RootRequirementsInHoldAsSuch rootProfile true (hasAt positive positive) noReq
      esseExcludesNoesisIn ∧
    ¬ NoUnexplainedAbsenceAtRoots rootProfile true openProfile (hasAt positive positive true) ∧
    ¬ RootPureRequiresNoPureLackIn rootProfile true (hasAt positive positive)
      TruthCore.Causality.RootPerfectionExclusion.Control.isPure esseExcludesNoesisIn) ∧
  (∀ req : Determination → Set Determination → Prop,
    AdmissibleIsExclusionFree openProfile req →
      ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
        (hasAt positive positive) req ∧
      ¬ RequiresLackAsSuch req Determination.esse {Determination.noesis}) ∧
  (¬ RootsConstitutivelySimple rootProfile true compositeRC ∧
    RootOwnConditionsSeated rootProfile true essNeg compositeRC seatSplit ∧
    RootDeterminationsRealized rootProfile true (hasAt positive positive) compositeRC
      (realizesSrc positive) ∧
    RootsHaveSomeDetermination rootProfile true (hasAt positive positive) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) compositeRC seatSplit (realizesSrc positive) noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq) ∧
  (RootsConstitutivelySimple rootProfile true simpleRC ∧
    ¬ RootOwnConditionsSeated rootProfile true essNeg simpleRC seatOpenOnly ∧
    RootDeterminationsRealized rootProfile true (hasAt positive positive) simpleRC
      (realizesSrc positive) ∧
    RootsHaveSomeDetermination rootProfile true (hasAt positive positive) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) simpleRC seatOpenOnly (realizesSrc positive) noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq) ∧
  (RootsConstitutivelySimple rootProfile true simpleRC ∧
    RootOwnConditionsSeated rootProfile true essNeg simpleRC seatAll ∧
    ¬ RootDeterminationsRealized rootProfile true (hasAt positive positive) simpleRC
      realizesNone ∧
    RootsHaveSomeDetermination rootProfile true (hasAt positive positive) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) simpleRC seatAll realizesNone noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq) ∧
  (RootsConstitutivelySimple rootProfile true simpleRC ∧
    RootOwnConditionsSeated rootProfile true essNeg simpleRC seatAll ∧
    RootDeterminationsRealized rootProfile true (hasAt ∅ ∅) simpleRC (realizesSrc ∅) ∧
    ¬ RootsHaveSomeDetermination rootProfile true (hasAt ∅ ∅) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt ∅ ∅) simpleRC seatAll (realizesSrc ∅) noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt ∅ ∅) noReq) ∧
  (cUnity essNeg positive simpleRC seatAll (realizesSrc positive) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) simpleRC seatAll (realizesSrc positive)
      TruthCore.Causality.RootClosure.Control.aExcludesNoesis ∧
    RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) TruthCore.Causality.RootClosure.Control.aExcludesNoesis ∧
    ¬ AdmissibleIsExclusionFree openProfile TruthCore.Causality.RootClosure.Control.aExcludesNoesis ∧
    ¬ NoUnexplainedAbsenceAtRoots rootProfile true openProfile (hasAt positive positive true)) ∧
  (RootsConstitutivelySimple rootProfile true simpleRC ∧
    RootOwnConditionsSeated rootProfile true natEss simpleRC natSeat ∧
    RootDeterminationsRealized rootProfile true natHas simpleRC natRealizes ∧
    RootsHaveSomeDetermination rootProfile true natHas ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true natAdmissible natEss natHas simpleRC
      natSeat natRealizes natReq ∧
    RootOwnEssentialConditionsCarried rootProfile true natAdmissible natEss natHas natReq ∧
    RootRequirementsInHoldAsSuch rootProfile true natHas natReq natReqIn ∧
    AdmissibleIsExclusionFree natAdmissible natReq ∧
    RootLacksExcludedByOwnNature rootProfile true natEss natHas ∧
    NoUnexplainedAbsenceAtRoots rootProfile true natAdmissible (natHas true) ∧
    (¬ PureRequiresNoPureLack natReq natPurePlotinian ∧
      ActualRootDeterminationsArePure rootProfile true (natHas true) natPurePlotinian) ∧
    (PureRequiresNoPureLack natReq natPureStrict ∧
      ¬ ActualRootDeterminationsArePure rootProfile true (natHas true) natPureStrict)) ∧
  (RootsConstitutivelySimple rootProfile true simpleRC ∧
    RootOwnConditionsSeated rootProfile true TruthCore.Explanation.InquiryClosure.Control.essSel
      simpleRC selSeat ∧
    RootDeterminationsRealized rootProfile true TruthCore.Causality.RootClosure.Control.hasSel
      simpleRC selRealizes ∧
    RootsHaveSomeDetermination rootProfile true TruthCore.Causality.RootClosure.Control.hasSel ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true
      TruthCore.Explanation.InquiryClosure.Control.selAdmissible
      TruthCore.Explanation.InquiryClosure.Control.essSel
      TruthCore.Causality.RootClosure.Control.hasSel simpleRC selSeat selRealizes
      TruthCore.Explanation.InquiryClosure.Control.selReq ∧
    RootOwnEssentialConditionsCarried rootProfile true
      TruthCore.Explanation.InquiryClosure.Control.selAdmissible
      TruthCore.Explanation.InquiryClosure.Control.essSel
      TruthCore.Causality.RootClosure.Control.hasSel
      TruthCore.Explanation.InquiryClosure.Control.selReq ∧
    AdmissibleIsExclusionFree TruthCore.Explanation.InquiryClosure.Control.selAdmissible
      TruthCore.Explanation.InquiryClosure.Control.selReq ∧
    RootLacksExcludedByOwnNature rootProfile true
      TruthCore.Explanation.InquiryClosure.Control.essSel
      TruthCore.Causality.RootClosure.Control.hasSel ∧
    NoUnexplainedAbsenceAtRoots rootProfile true
      TruthCore.Explanation.InquiryClosure.Control.selAdmissible
      (TruthCore.Causality.RootClosure.Control.hasSel true) ∧
    ¬ TruthCore.Causality.RootClosure.RootAbsencesNecessary rootProfile true
      TruthCore.Causality.RootClosure.Control.hasSel) ∧
  (RootPureRequiresNoPureLackIn rootProfile true
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure)
      TruthCore.Causality.RootPerfectionExclusion.Control.isPure noReqIn ∧
    TruthCore.Causality.PureActRoot.ActualRootHasEveryPureDetermination rootProfile true
      (hasAt TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure true)
      TruthCore.Causality.RootPerfectionExclusion.Control.isPure ∧
    ActualRootDeterminationsArePure rootProfile true (hasAt positive positive true)
      TruthCore.Causality.RootPerfectionExclusion.Control.isPure ∧
    TruthCore.Causality.RootPerfectionExclusion.RootProfilesAdmissible rootProfile true
      openProfile (hasAt positive positive true) ∧
    TruthCore.Causality.RootPerfectionExclusion.PureDeterminationsAdmissible openProfile
      TruthCore.Causality.RootPerfectionExclusion.Control.isPure ∧
    TruthCore.Causality.RootPerfectionExclusion.PureExtensionsAdmissible openProfile
      TruthCore.Causality.RootPerfectionExclusion.Control.isPure ∧
    ¬ TruthCore.Causality.PureActRoot.ActualRootHasEveryPureDetermination rootProfile true
      (hasAt positive positive true) TruthCore.Causality.RootPerfectionExclusion.Control.isPure)

end TruthCore.Causality.SimpleUnityCarriage
