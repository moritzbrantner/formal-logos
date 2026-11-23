# Horizontal support for concurrent actualization (2026-11-19)

**Question.** Do argument families other than the Thomist esse/act-potency
family bear on weak concurrent actualization `40a97664` (and its strong form
`76d2cc96`), or on its denial, existential inertia, *independently*: with
warrant that does not come through `40a97664` or a restatement of it? For each
family: (a) does it entail `40a97664`, or a premise inertia must deny, on
independent warrant; (b) does it reach a God-relevant conclusion while avoiding
`40a97664`; or (c) is it neutral, or does it presuppose `40a97664`?

**Reused, not repeated.** [sustaining-vs-existential-inertia.md](sustaining-vs-existential-inertia.md)
§§1–5 and its §4 judgment (attempt `21883b61`); the present-receipt test
(§5, attempt `50e08b09`); the Schmid 2021 and Feser 2021 readings in
[eternity-dependence-connection.md](../eternity-dependence-connection.md)
(both pinned and read). Schmid's passage `SCHMID-INERTIA-REPLY-3-ARTICLE` was
materialized and re-read for this note, for the exact form of the PSR-like
principle he accepts. The q.45 a.3 re-reading belongs to a parallel lane and is
not used. Every vertical test so far (parity/onset, essence–esse union,
present-tense receipt, the holding reading of C\*, and the relational receipt
after q.45 a.3 merged in PR #1798) restated the crux.

## 1. Formal work

Module `TruthCore.Causality.TimeSymmetricGiving`, spec
`specs/time-symmetric-giving.toml`. Analyst formulations, attribution deferred.
Same history frame as `ConcurrentActualization` (`History`, `BeingGiving`,
STRICT `GivesAt`, inclusive presence). It does not use the unmerged causality
frame of PR #1795; an adapter can be added once it merges.

| Record | Lean | Content |
| --- | --- | --- |
| `9a14bdd8` momentary PSR | `MomentaryPSR` | whatever has received esse has, at each moment of its presence, some explanation of its presence then (primitive `Explains`, definition `261516e9`) |
| `d86c9de9` productive bridge | `ExplanationNeedsGiver` | any such explanation comes with a giver of being at that moment |
| `c186cee4` | `concurrentOfMomentaryPSR` | PSR + bridge ⊢ `40a97664` (transcription) |
| `2b8b48d1` / `c12e30dd` | `psrBridgeCarriesTheCrux` | for every interpretation: under the momentary PSR, bridge ⇔ `40a97664` |
| `4bc853db` coverage | `ReceivedEsseHasCauseOfBeing` | whatever has received esse has its being caused by another (tenseless) |
| `7005560a` exercise | `CausesOfBeingAreExercised` | a cause of another's being gives it being at *some* moment of its presence |
| `488263b0` time symmetry | `GivingRespectsTimeSymmetry` | an order automorphism of time preserving the history (presence and supplied non-giving facts) preserves giving |
| `eb928359` | `ConcurrentlyActualizedIfHomogeneous` | `40a97664` restricted to *homogeneous* things: any two moments of presence related by such an automorphism (definition `6d0f77a2`) |
| `4f0c026d` | `homogeneousConcurrentOfSymmetry` | coverage + exercise + symmetry ⊢ `eb928359` (not a transcription) |
| `76dc5abc` | `homogeneousOfConcurrent` | `40a97664` ⊢ `eb928359` (strength order, relation `7bb5ce58`) |
| `f49ba264` / `ae450cd0` | `controls` | parts 1–6 below |

*Controls* (`TimeSymmetricGiving.Control.Certificate`; one world, integer
times, `false` alone has received esse; `true` is the other individual):

1. **Eternal inertia** (both present at every moment, no giving, no cause of
   being). Schmid's origin-or-inertia explanation (definition `8c20c988`)
   satisfies the momentary PSR and the cessation law. The bridge and `40a97664`
   fail. `false` is homogeneous. Coverage fails; exercise and symmetry hold; the
   homogeneous conclusion fails.
2. Eternal, `true` causes `false`'s being and gives at moment 0 only (Clarke's
   arbitrary moment): coverage and exercise hold; symmetry fails.
3. Eternal, `true` causes `false`'s being and never gives: coverage and
   symmetry hold; exercise fails.
4. **Begun inertia** (`false` present from 0, given being at 0 only):
   coverage, exercise, symmetry, the momentary PSR on Schmid's explanation, the
   cessation law and received onset is given (`fa3e228b`) all hold;
   `40a97664` fails, while the homogeneous conclusion holds because `false` is
   not homogeneous. An automorphism preserving its presence fixes moment 0.
5. Eternal sustaining (`true` gives at every moment): everything holds.
6. No explanations: the bridge holds vacuously; the PSR and `40a97664` fail.

`truth countermodel` does not handle the `Preorder` instance and `OrderIso`
binders of these theorems ("unsupported parameter inst : Preorder T"). Finite
*linear* times have no non-identity order automorphisms, so a finite linear
model can witness homogeneity only for a thing present at one moment. The
controls are therefore written by hand over integer time. Comparator and NanoDa
accepted `4f0c026d` and `f49ba264` locally (`scripts/verify-result.sh`); CI
checks all five results.

## 2. Per-family classification

### PSR family at matching (time-indexed) scope: (c) neutral

**Schmid's principle, exact form.** In the paragraph beginning "And this
discovery especially helps", Schmid says that one of Feser's theses "was a PSR
or PSR-like explanatory principle, which I accept". The thesis is Feser's
"auxiliary thesis — that something must explain the fact that the water
continues to exist". What Schmid rejects is the other thesis: "if there is no
sustaining cause, then there is no extrinsic explanation". His explanation of
S's existence at m (paragraph beginning "For S to fail") cites three things:
S's existence before m, the absence of any factor inducing its cessation, and
the law that a change occurs only if some factor induces it.

- `MomentaryPSR` is the first thesis, typed, and extended from continuing
  existence to every moment of presence. The extension covers first moments
  and the moments of a beginningless thing. It is the analyst's, not Schmid's.
- `ExplanationNeedsGiver` is the second thesis together with Feser's premise
  that, with inertia denied, nothing intrinsic explains persistence. Any
  explanation of a received-esse thing's presence then comes with a giver.
- `originOrInertia` is his explanation, with an originating giver added for a
  first moment.

**Test of the brief's example.** Is a PSR variant strong enough to explain each
moment's existence one that inertia must reject? No. The momentary PSR *is*
that variant, and inertia satisfies it: in eternal inertia (part 1) with no
giver ever, and in begun inertia (part 4) with a giver at onset only. Once the
PSR is shared, `psrBridgeCarriesTheCrux` shows that what separates the two
sides is exactly `40a97664`. The bridge is the crux restated, and the PSR adds
nothing toward it. This is checked for every interpretation, not only the
controls. Feser's argument as Schmid reports it (`c186cee4`) is a
transcription whose second premise is the crux.

### Contingency, modal necessary-being and other routes to GOD_4: (b) for six routes

On this base `40a97664` is not an open premise of any of the 15 routes to
GOD_4 (`truth frontier --routes --frontier-root STMT-GOD-EXISTS --json`).
`2068f91c` appears in the premise lists of 7 routes: `2bd7ee56`, `5e8e6054`, `c98328f1`,
`3367bf93`, `72391d4d`, `fc46b7f9` and `92ab7c94`, two of them transcription
projections. On those routes `40a97664` enters only through one *support
option* of `2068f91c` (via `ce55210c`, contact and `ffcb81fb`). Its direct
option remains.

**But the crux also enters in other vocabulary.** The world-indexed dependence
premise `3ef67739` ("every actual contingent concretum depends on some actual
concretum for its being") is an open premise of four routes: `1c154f2f`,
`72391d4d`, `0a639ec4` and `fc46b7f9`. On its strict sustaining reading,
existential inertia is recorded as its standing rival
([causal-dependence-support-investigation.md](causal-dependence-support-investigation.md),
rival row 3: the premise "owes that present received esse needs a concurrent
actualizer"). On the originating reading of dependence (the fork of #1626) the
inertialist need not contest it: the modal spine's rival table records Schmid
as uncontesting if an earlier existent can be the ground. On that reading the
origin counterexample (rival row 2) bears on other dependence premises, not on
inertia. So these four routes share the crux whenever `3ef67739` is read as
sustaining dependence.

**Six routes contain neither `2068f91c` nor `3ef67739`:**

- the prima via `ed7c588a`, whose subject is motion. Motion is change, which
  Schmid's own law (iii) says needs an inducer. Whether an inertialist accepts
  the prima via's further premises is not examined here.
- the quarta via `5d2b7c6e`, `678ff65f` and `661ce61d`, from grades;
- `fd1f7e75` and `beec1dc1`.

In stage one of the modal spine ([modal-spine.md](modal-spine.md)) the
premises that do the work are other ones:

- Arrival B rests on a possible beginning and its cause (B1/B2).
- A2ab has an originating-cause derivation. The table records that it uses
  only causes an inertialist can grant *on the inclusive reading of `GivesAt`*,
  and that this is not shown on the strict esse-giving reading used here.
- The contingency premise "every contingent concrete thing has a ground" is
  recorded as uncontested by Schmid if an earlier existent can be the ground
  (open bridge, rival table).

The world-indexed existence PSR (`TruthCore.Explanation.ExistencePSR`) has no
moments. The caused-universe family (`NaturalismConsequences`, #1109) reasons
to a cause of the existence of the spacetime whole and makes no claim about
moment-by-moment giving.

**Finding.** The God-existence routes on this base **do not all share the CA
dependency**. Six routes reach GOD_4 with no premise that is the crux or is
recorded as contested by inertia. The dependency, with its reading conditions,
is confined to:

- the immensity presence step `9469ab62` / `8bf775e9`;
- the sustaining readings `ce55210c` and `23e04ae5`;
- one support option of `2068f91c`;
- `3ef67739` on its sustaining reading (four routes);
- A2ab's originating route on the strict reading, where it is not shown free
  of the crux;
- the holding First Way.

Caveat. The caused-universe family's `CausingWholeCausesParts` (definition
`b08eee83`, owner bridge #1109) would bear on `40a97664` if two bridges were
built: temporal parts as spacetime parts, and causing a part's existence as
giving it being at its moment (`Ontic.Causes` to `GivesAt`). Neither bridge is
built. This is a connection plan, not a route. Its recorded rival is the
Hume–Edwards view.

### Leibnizian contrastive principle with coverage and exercise: (a) as an entailment, scoped to homogeneous things; partly horizontal

**Entailment, checked.** Three premises give `40a97664` for every received-esse
thing that is homogeneous in its history (`homogeneousConcurrentOfSymmetry`):
coverage, exercise and time symmetry. Each is needed (parts 1–3), and all
three hold together with the conclusion (part 5). The proof carries one moment
of giving to every other moment by an automorphism, so it yields one cause of
being that gives at every moment of presence.

**Logical independence from `40a97664`, checked.** No premise is the crux
restated. Each holds in an interpretation where `40a97664` fails: exercise and
symmetry in part 1, coverage in parts 2 and 3. All three hold together in begun
inertia (part 4), where `40a97664` fails: coverage and exercise are satisfied
there by the originating cause, and the symmetry step is idle on the begun
thing.

**Warrant: only time symmetry is horizontal.** Logical independence is not
warrant independence. Coverage and exercise belong to the Thomist esse family,
so the shared dependency on that family stays.

- *Time symmetry*: a contrastive PSR over moments, in the shape of Leibniz's
  temporal-shift argument (`2bd8f0e3`, sourced; uniform space `7dd2af35`). Its
  warrant has nothing to do with esse. The analyst applies it to the schedule
  of giving.
- *Exercise*: a cause of a thing's being bears on it at some moment of its
  presence; the time index of `GivesAt` is on the effect side. An originating
  cause satisfies it at onset, and the inertialist grants that *if* it grants
  that the originating cause gives being on the strict reading at the first
  moment (the conditional grant recorded at `fa3e228b`).
- *Coverage*: the tenseless De ente c.4 principle that what has esse not from
  its essence has it from another. Its argument is tenseless and does not
  distinguish begun from beginningless things, so its warrant does not come
  through `40a97664`. An inertialist accepts it for begun things through the
  originating cause if it counts the originator as a cause of the thing's
  *being*, not only of its becoming (the same conditional grant as for
  exercise), which is why the sustaining note's §2 classed it as
  independent.
  - In the beginningless case there is no originator. There coverage says that
    received esse needs a cause as such, whether or not it began. That is the
    tenseless core of the Avicennian "need follows possibility, not novelty"
    (below).
  - An inertialist who restricts coverage to begun things does so on the same
    change-only rationale on which it rejects `40a97664`.
  - So the result **relocates** the dispute in the homogeneous case. It moves
    from per-moment giving to tenseless coverage for beginningless things. It
    does not defeat the rival independently. What it adds is that the
    relocation target is a principle with its own tenseless argument, one the
    rival accepts for begun things on that condition. That argument is not a statement about giving at
    moments.

**Why it is not parity restated.** Parity `5b24ef26` reaches every begun thing
from its onset. Time symmetry cannot. In the begun control, an automorphism
that preserves the begun thing's presence fixes its first moment (part 4). This
is checked there only; the general fact for linear orders is not formalized.
The symmetry step is idle exactly where onset `fa3e228b` speaks, except for a
thing present at a single moment, which is trivially homogeneous. It bites only
where onset is silent, on beginningless things whose moments nothing
distinguishes. This fills the gap named in `strong_version_needed` of argument
`366a6ea3` ("things with no first moment of presence"), for the homogeneous
case only.

**The rival's price.** Consider an extrinsic inertialist who holds that a
received-esse thing never needs a giver except at an onset, including in a
beginningless stationary history. Schmid's explanation, applied by the analyst
to that case, covers it (part 1). Take such a thing that is given being at no
moment. The proof of `homogeneousConcurrentOfSymmetry` runs thing by thing, so
at least one of the following fails: coverage for that thing, exercise for its
cause, or symmetry of its history. (The theorem's type is global. This
per-thing reading is taken from the proof.) The three options:

1. **Reject coverage** (part 1). The thing has received esse and no cause of
   its being. Each moment is explained by the one before, so its esse is *not
   brute* moment by moment. What is lost is a cause of its being as a whole.
   This is the inertialist's change-only rationale applied to a history with no
   change anywhere. For the whole history it is closest to the Hume–Edwards
   view that explaining every member explains the series. That view is the
   recorded rival of `b08eee83` and one of the whole-series standards retained
   in PR #1297 (attempt `a5958e25`). The analogy is inexact, since the members
   here are moments of one thing, not members of a series. It also rejects, by
   analogy, the world-indexed De ente coverage `d1f3ffcc`; that premise is
   stated over `DistinctEsseAt` and no bridge is built. The inertialist avoids
   all this for begun things through the originator, but no originator is
   available here.
2. **Reject time symmetry** (part 2). A cause gives being at some moments
   rather than others with nothing in the history's presence pattern or
   supplied facts to distinguish them. Two rivals are recorded:
   - Clarke's reply, a will that chooses without an external difference
     (`81ec01fe`). It is available only to a voluntary giver and concedes a
     cause of being that acts in time.
   - Noncontrastive, intrinsic or probabilistic explanation that leaves
     alternatives (`e35adb5f`). It rejects contrastive PSRs in general.

   The typed premise is also stronger than a contrastive principle in two
   ways: through an incomplete `Facts`, and because `History.now` need not be
   preserved.
3. **Reject exercise** (part 3). A cause of the thing's being whose activity
   bears on it at no moment of its presence. No account is on file of what that
   causing would consist in, and none against it. This option is open with no
   substantive support either way.

The price is conditional on two things:

- **The possibility of a homogeneous beginningless received-esse thing.**
  - For it there are only unread leads, with no weight: Aquinas's grant that an
    eternal created world is not shown impossible (ST I q.46 a.2); Avicenna's
    eternal caused world; stationary cosmological models.
  - Against it, Leibniz draws from the same temporal argument that instants
    without things are nothing, so that a shifted creation "would not differ
    from, nor be discernible from" the actual state (`2bd8f0e3`). On a
    relationalist view of time, distinct indiscernible moments of a
    stationary history may not exist, and then the case is empty.
  - Attempt `05c7e8d0` rejected "PSR alone → relationalism", so this point is
    not decisive. It bears on the condition, not on the entailment.
- **Modal scope.** Coverage is applied as holding in every possible history,
  as a principle about received esse.

The actual world changes, so the theorem is silent on actual persisting
things. An inertialist can confine inertia to begun or changing things and
concede concurrent giving for homogeneous eternal ones. That avoids the price.
But it also concedes that, *given* coverage, exercise and symmetry, a thing
that undergoes no change at all is given being at every moment. That concedes
the point against the change-only rationale in the case where the rationale
applies most cleanly.

### Avicennian preponderance: (c), restates parity; historical anchor of the symmetry case

There is no corpus record. The Ilahiyyat argument that the possible needs a
preponderator for as long as it exists, because its possibility is permanent,
was **not read** here: a lead with no weight. On an analyst reconstruction,
the thesis "need follows possibility, not novelty" yields parity given onset.
Its decomposition argument (prior non-existence needs no cause, so what is
caused is existence as such) yields only onset, which the inertialist grants.
So its per-moment form is parity re-presented (c). Its tenseless core, that a
possible needs a cause of its existence whether or not it began, coincides
with coverage applied to beginningless things, the premise on which the
symmetry result relocates the dispute (above). That core is not parity: it
asks for a cause, not for giving at every moment. Avicenna's eternal and
eternally caused world is exactly the homogeneous case of the symmetry family,
the case in which causation of being cannot be onset-only.

### Scotist essential order: (c) for CA; (b) for God-relevance, unread

There is no corpus record of the De primo principio or Ordinatio argument
(the only Scotus records concern self-motion). Unread, so no weight. On its
usual reconstruction the triple-primacy argument runs from the *possibility*
of production and so would not use `40a97664` (b). The simultaneity of
essentially ordered causes concerns causing. It bears on `40a97664` only if
conservation is already counted as an essentially ordered causing, which
presupposes the crux (c). The corpus's own per se series (`97f5850f`,
prima via) concerns motion and is covered by the change law both sides share.

### Grounding and dependence: (c) neutral or presupposing

- Composites depend synchronically on the present arrangement of their parts.
  Both sides accept this (sustaining note §3). It relocates to the fundamental
  constituents and gives no giver of their being.
- Feser's constituent argument (eternity note, paragraph beginning "Rather, a
  critique") says that past combination does not actualize present
  combination. That is `40a97664` restated for composites.
- `DependsForBeing` (DEF-DEPENDS-FOR-BEING) reaches `40a97664` only through
  the co-presence bridge connection of §1 of the sustaining note, so it
  presupposes the crux.
- The cross-world contrastive notions already on file
  (`ExplanatoryAdequacy.UniformContrast`, `HistoryContrastive.Discriminates`)
  compare worlds, not moments. They were inspected and not reused, because
  their meaning differs from time symmetry.

### Physics at matching scope: (c) neutral, unchanged

The sustaining note §3 stands. Two additions:

- For the momentary PSR, physical laws are one more explanans of the inertial
  kind, and Schmid names them.
- For the symmetry family, physics bears only on whether homogeneous
  beginningless histories are possible (stationary models), not on giving.
  That is a lead, unread here.

## 3. Updated provisional judgment on `40a97664` (2026-11-19, scoped)

This is scoped to the horizontal families above. It stands beside the
2026-11-19 assessment of attempt `21883b61` and the 2026-11-18 cluster
assessment, and does not replace them.

- **The dependency is avoidable for God's existence on six routes, not all.**
  - No route to GOD_4 has `40a97664` as an open premise.
  - Six routes (prima via, quarta via and two others) contain neither
    `2068f91c` nor `3ef67739`, and no recorded rival table lists inertia
    against their premises. One support of their premise `09c6d5f0`,
    `19882fa9`, has inertia as a kept rival
    ([esse-cause-efficiency-1633.md](esse-cause-efficiency-1633.md)); the
    recorded bypass `5c5b794f` avoids it, so it is a support option with an
    inertia rival, like that of `2068f91c`, not a route premise.
  - The crux enters four routes through `3ef67739` on its strict sustaining
    reading, where inertia is the recorded standing rival.
  - It also enters the sustaining/immensity attribute step, one support option
    of `2068f91c`, and the holding First Way.
  - A2ab's originating route is shown free of it only on the inclusive reading
    of `GivesAt`.
- **The PSR family adds nothing at matching scope.** The momentary PSR is
  shared, in its continuation form, and under it the remaining bridge is
  `40a97664` (checked for every interpretation).
- **One partly horizontal item, scoped.** Coverage, exercise and time symmetry
  entail `40a97664` for homogeneous received-esse things (not a transcription).
  Each premise is logically independent of `40a97664`, and inertia satisfies
  all three for begun things.
  - Only time symmetry is horizontal. Coverage and exercise come from the esse
    family.
  - In the homogeneous beginningless case the result **relocates** the dispute.
    It moves from per-moment giving to tenseless coverage for beginningless
    things (equivalently, the tenseless Avicennian core). That principle has
    its own tenseless argument and is accepted by the rival for begun things if it counts the
    originator as a cause of being.
    The rival restricts it on the same change-only rationale on which it
    rejects `40a97664`.
  - So a general extrinsic inertialist must, in the possible eternal-stationary
    case, give up one of three things:
    1. a cause of the thing's being as a whole (the Hume–Edwards analogue);
    2. time symmetry (Clarke, or noncontrastive explanation);
    3. exercise.
  - The item holds at modal scope only. It is conditional on the possibility
    of such a thing, which is unassessed and on which Leibniz's own
    relationalism presses. It does not bear on actual persisting things, whose
    histories are not homogeneous.
  - The actual-world crux is unchanged: no discriminating test at matching
    scope. The grade of `40a97664` moves from "both stand, one price item each"
    to "both stand; the general form of extrinsic inertia must, in the
    eternal-stationary case, restrict a tenseless principle it otherwise
    accepts, or reject time symmetry or exercise". That is a relocation with a
    modest cost, not an independent defeat.
  - Nothing is established or defeated.

**Revision conditions.**

- An independently justified account of why a homogeneous eternal
  received-esse thing needs no cause of its being would remove the item.
- So would an independently justified reason why causes of being need not be
  exercised at any moment of their effect.
- So would an independently supported case for noncontrastive explanation
  (`e35adb5f`) applied to the schedule of giving, or Clarke's voluntarist reply
  (`81ec01fe`) extended to a non-voluntary giver.
- A demonstration that homogeneous beginningless received-esse things are
  impossible would void the item's condition. A relationalist account of time
  on which a stationary history has no distinct moments would be a candidate.
- A bridge from `CausingWholeCausesParts` to effect-side `GivesAt` would add
  a second horizontal route.

**Next test.** Extend the symmetry family from homogeneous things to
beginningless *changing* histories. Typing the inertialist's change-only
asymmetry as a constraint on which supplied facts may distinguish moments for
giving would show whether a beginningless thing in a changing world must be
given being at changes only, and whether that schedule satisfies coverage and
exercise without concurrent actualization. A second test is the
caused-universe connection (`CausingWholeCausesParts` with temporal parts).

## Self-sweep

The claim-vs-type table is in the PR body. No source claim is added. Schmid is
cited only through his pinned and read passage, and no claim attributes a
typed premise to him or to Feser. Leibniz is cited through the sourced
statements `2bd8f0e3` and `7dd2af35`, and their application to giving is the
analyst's. Aquinas q.46 a.2, Avicenna, Scotus, stationary cosmology and Clarke
beyond `81ec01fe` are marked as leads with no weight. An independent semantic
challenge of the first draft found 4 P1 and 12 P2 findings, which were
repaired; see the PR. The objections above name their target premise, their mechanism and
their status. No hypothetical objection is presented as evidence.


## 4. Which existential-inertia theses genuinely negate C3? (2026-11-23)

**Destination and target.** This review continues #1801's question about whether
an actually received-esse bearer can survive without positive concurrent
being-giving. It reuses the existing `TimeSymmetricGiving.Control.eternal`,
`givesAlways`, `falseReceived` and weak `ConcurrentlyActualized`
(`40a97664`) rather than changing the meaning of that established open
premise. The source-facing issue remains #1616. #1895 owns the matched-past
withdrawal/no-positive-loss comparison, and #1891 the full #1614 priority
source-bundle controls. Neither is replaced or made a dependency here.

### A critical scope distinction from the pro-inertia literature

In his public 2021 response to Hsiao and Sanders, Joseph Schmid explicitly
distinguishes a universal existential-inertia thesis from one restricted to a
**nonempty subset of temporal concrete things** (§2.1), notes that some
non-fundamental things may receive concurrent sustaining causes even if their
foundation persists inertially, and proposes the **necessary temporal foundation**
(NTF) package (§4.1): one or more actually necessary temporal foundations do
not themselves require sustaining, while the rest of reality may be caused,
grounded or constituted by them at every moment. The response also distinguishes
lack of required sustenance from lack of *actual* sustenance (§2.2).
Navigation: [Schmid, response to Hsiao and Sanders (2021), §§2.1–2.4, 4.1](https://josephschmid.com/response-to-hsiao-and-sanders-on-existential-inertia-and-the-thomistic-contingency-argument/).
This is a consulted public textual comparison, **not a newly pinned passage or
a new formal attribution**. No new source claim or verified passage is asserted.

Consequently the mere proposition

> **S:** Some temporal concrete being persists without external sustaining.

is **not** the genuine logical negation of

> **C3:** Every *presently existentially derivative* bearer of received esse
> has an appropriately concurrent actualizer of its being.

One possible witness to S is the **underived necessary source** N, which is
outside C3's antecedent. C3 and S may both be true. The fact that N itself
needs no external giver says nothing about whether N's *effects* need
continuing support. A classical view with an underived N and concurrently
dependent creatures is therefore not ruled out by this restricted EIT
formulation, although it may deny some other inertialist worldviews.

**Checked formal surrogate.** The newly added unregistered theorem
`Results.Causality.TimeSymmetricGiving.subsetInertiaCompatibleWithC3`
proves `Control.SubsetInertiaCompatibleWithC3` on ONE already-existing
`Int`-indexed history:

- `falseReceived` holds of `false` only; this received bearer has a distinct
  giver `true` at **every** moment;
- the same `true` bearer is present at every moment and is **never** the
  recipient of any strict `GivesAt` in the supplied dictionary;
- `true` does not have received esse in the tested predicate.

This is a **scope compatibility model**, not a full model of NTF or EIT.
Its one-world modal necessity is trivial, and it does **not** type
fundamentality, real intrinsic esse, source nature, absence of every possible
external grounding relation or the productive semantics of the giver. The
independently important distinction is the antecedent: a universally
quantified requirement over *received* concreta is consistent with one
*non-received* concretum having no giver. The theorem is a conditional
structural check, not a fresh argument for C3 or a ground of N's necessity.
The older controls already establish each conjunct separately; composing them
on the **same** existing model makes the scope comparison explicit and adds
no independent warrant.

### The genuine ¬C3 rival and its stronger obligations

The strongest relevant ¬C3 account instead says of the **same actually
received-esse bearer x** that it was originated, retains its numerical
identity and actuality under an independently operative persistence rule,
and at a later moment has **no appropriately concurrent productive giver**.
The previously checked `C3ActualWorld` and #1891's necessary-origin control
supply structural examples of the weak non-giving claim. They do not thereby
settle the metaphysical meaning of `EsseReceivedIn` or the full
source/ground relationship. In particular:

1. **No-giver versus no-extrinsic-ground.** A no-`GivesAt` model can still
   carry an `ActualConcreteGround` edge (as #1885 showed). Schmid's **refined**
   EIT in the same 2021 response (§2.3 and §3) excludes concurrent extrinsic
   ontological dependence of its selected inertial bearer, potentially
   including grounding and realization, not merely current *efficient
   production*. A model falsifying only `40a97664` is therefore not
   automatically a model of this full EIT. A necessary originator's being
   present at every world also cannot by itself test the dependence
   counterfactual; a ground relation is separate from co-presence.
2. **No corruption versus no production.** Aquinas himself formulates
   the *positive-corruption-only* objection in ST I q.104 a.1 **objection 3**:
   failure of a creature's existence appears to demand an active cause of
   corruption, especially for naturally incorruptible substances. In the
   **body** and **reply 3**, he restricts that objection to preservation by
   warding off corruption and argues separately for direct per-se conservation
   of being. The affirmative argument is that a thing's esse may depend
   on a cause of *being as such*, not only a past cause of *becoming*.
   These are two causal claims with distinct explananda, **not** a theorem
   that all cessation is a positive destructive process.
   Existing pinned claim `da9c82ed` records direct conservation and
   `40aefb2e` becoming/being separation; the English passage
   `AQUINAS-ST-I-Q104-A1-EN` was read in the earlier campaign. **Reuse the
   C2 source investigation** in
   [foundational-absence-warrant.md](foundational-absence-warrant.md),
   §2.2: ST I q.104 a.3 **reply 1** expressly separates the absence of
   existence (no directly productive non-being) from corruption; **reply 3**
   says divine annihilation, if it occurred, would be cessation of an action
   rather than another positive divine action. These are source-specific
   statements of the conservation theory, **not** independent evidence
   that a derivative being is unable to retain its esse under an inertial
   law. In q.104 a.4 Aquinas additionally denies that actual creatures
   will be annihilated; a model where one vanishes is a test of a
   counterfactual, not a prediction on his view. The q.104 a.3 reading
   already exists in the C2 note: this is a **cross-family connection,
   not a new source reading or attributed corpus claim**.
3. **Source of positive warrant on each side.** The strongest inertialist
   explains later survival by previous real existence, an applicable
   no-positive-loss rule and the absence of such a loss inducer; it is **not**
   committed to an intrinsic present power of x grounding its own being.
   Feser's same-time circularity objection to a *persistence property*
   therefore does not by itself defeat the prior-stage/no-change variant.
   Conversely, the source account argues that an essence unable to originate
   esse is also unable by itself to account for **its present actuality**,
   but this last step needs a substantive present dependence/retention
   principle; naming the bearer `received` or using an illumination analogy
   is insufficient. This is the crux in §§4–6, not a newly proved bridge.

### Cumulative effect and positive revision conditions

The scope correction **does not lower or strengthen** C3's warrant merely
because a weak or differently scoped inertialist thesis is compatible with it.
It sharpens which rival is genuinely contradictory:

- **C1/C2 and C3 together** may admit an unreceived necessary source and
  continuously derivative creatures. Restricted subset EIT of that source
  is compatible; it is *not* a competing worldview on the actual
  dependence of the creatures.
- **Genuine ¬C3 of a received bearer** is a live alternative that a
  positive causal/conservation account must confront. #1895's
  no-destruction-law success and its withdrawal-as-loss counter-reading test
  that alternative at one interval, without metaphysical source certification.
- **EIT on a fundamental temporal N** and **EIT on a derivative created x**
  have different consequences for God-existence routes. The former may
  coexist with the necessary source; the latter bears directly on sustaining
  interpretations of `23e04ae5`, `2068f91c` and `cb1cdea9`. Neither
  alone negates all C1/C2 routes, and they must not be counted as one
  independent objection plus another.

**Provisional assessment.** The actual received-esse case remains
underdetermined. The subset-NTF account has a positive role as a model of
*how an unsustained foundation and sustained derivatives could coexist*, but
is not an answer to the disputed received-bearer continuation question.
The genuinely opposed account has the local explanatory successes and
unsatisfied application burdens recorded in #1801. There is no warrant here
for ranking whole worldviews by the number of inertial bearers or for
equating necessary existence with causelessness, pure actuality or simplicity.

**Next discriminating test:** fix one **currently derivative** x, its
essence/esse interpretation and exact selected actual world. Test the
no-positive-destruction law over x's own **existential** cessation—not a
property of x—under a source withdrawal that does not import a positive
corruption process. Separately test whether the same concrete source's
*productive*, strictly present dependence is independently warranted or
whether historical origination plus a real present nonproductive ground
suffices. If a fundamental N is the only inertial item, the test has
not yet opposed C3; record that as a scope mismatch, not as a failed
inertialist account.

**Integration boundary.** This adds one unregistered, directly checked
structural certificate, one scoped reading comparison and no new corpus
statement, definition, claim, argument or result. Intended `frontier-diff`:
**no change**. The independent semantic challenge of this full section and
the final-head CI are required before publication as reviewed support.

