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
present-tense receipt, the holding reading of C\*) restated the crux.

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
linear times have no non-identity order automorphisms, so finite models could
not witness homogeneity in any case. The controls are therefore written by hand
over integer time, and Comparator and NanoDa checked them.

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
the law that a change occurs only if some factor induces it. `MomentaryPSR` is
the first thesis, typed. `ExplanationNeedsGiver` is the second, contraposed.
`originOrInertia` is his explanation, with an originating giver added for a
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

### Contingency, modal necessary-being and other routes to GOD_4: (b) avoid CA

On this base `40a97664` is not an open premise of any of the 15 routes to
GOD_4 (`truth frontier --routes --frontier-root STMT-GOD-EXISTS --json`).
`2068f91c` appears in the premise lists of 7 routes: `2bd7ee56`, `5e8e6054`, `c98328f1`,
`3367bf93`, `72391d4d`, `fc46b7f9` and `92ab7c94`, two of them transcription
projections. On those routes `40a97664` enters only through one *support
option* of `2068f91c` (via `ce55210c`, contact and `ffcb81fb`). Its direct
option remains. Eight routes do not contain `2068f91c`:

- the prima via `ed7c588a`: motion, which inertia's own causal law on change
  covers;
- the quarta via `5d2b7c6e`, `678ff65f` and `661ce61d`: grades;
- `fd1f7e75`, `beec1dc1`, `1c154f2f` and `0a639ec4`.

In stage one of the modal spine ([modal-spine.md](modal-spine.md)) the
premises that do the work are other ones:

- Arrival B rests on a possible beginning and its cause (B1/B2).
- A2ab has an originating-cause derivation that uses only causes an
  inertialist can grant.
- The contingency premise "every contingent concrete thing has a ground" is
  recorded as uncontested by Schmid if an earlier existent can be the ground
  (open bridge, rival table).

The world-indexed existence PSR (`TruthCore.Explanation.ExistencePSR`) has no
moments. The caused-universe family (`NaturalismConsequences`, #1109) reasons
to a cause of the existence of the spacetime whole and makes no claim about
moment-by-moment giving.

**Does inertia touch these premises?** None of their recorded rival tables
lists inertia against them. The stage-one table records inertia only against
the *sustaining* derivation of A2ab, which has an originating alternative.
Finding: the God-existence routes on this base **do not share the CA
dependency**. It is confined to:

- the immensity presence step `9469ab62` / `8bf775e9`;
- the sustaining readings `ce55210c` and `23e04ae5`;
- one support option of `2068f91c`;
- the holding First Way.

Caveat. The caused-universe family's `CausingWholeCausesParts` (definition
`b08eee83`, owner bridge #1109) would bear on `40a97664` if two bridges were
built: temporal parts as spacetime parts, and causing a part's existence as
giving it being at its moment (`Ontic.Causes` to `GivesAt`). Neither bridge is
built. This is a connection plan, not a route. Its recorded rival is the
Hume–Edwards view.

### Leibnizian contrastive principle with coverage and exercise: (a), scoped to homogeneous things

**Entailment, checked.** Three premises give `40a97664` for every received-esse
thing that is homogeneous in its history (`homogeneousConcurrentOfSymmetry`):
coverage, exercise and time symmetry. Each is needed (parts 1–3), and all
three hold together with the conclusion (part 5). The proof carries one moment
of giving to every other moment by an automorphism, so it yields one cause of
being that gives at every moment of presence.

**Independence from `40a97664`.** No premise is the crux restated. Each holds
in an interpretation where `40a97664` fails: exercise and symmetry in part 1,
coverage in parts 2 and 3. All three hold together in begun inertia (part 4),
where `40a97664` fails, because they are silent on begun things. Their
warrants are separate:

- *Coverage*: the tenseless De ente c.4 principle that what has esse not from
  its essence has it from another. The inertialist accepts it for begun things
  through the originating cause. The sustaining note's §2 already classifies the
  tenseless reading as independent.
- *Exercise*: a cause of a thing's being bears on it at some moment of its
  presence; the time index of `GivesAt` is on the effect side. An originating
  cause satisfies it at onset, which the inertialist grants.
- *Time symmetry*: the contrastive PSR over moments, in the shape of Leibniz's
  uniform-space argument (`7dd2af35`). Its warrant has nothing to do with
  esse.

**Why it is not parity restated.** Parity `5b24ef26` reaches every begun thing
from its onset. Time symmetry cannot: on integer time an automorphism that
preserves a begun thing's presence fixes its first moment (part 4). The new
premises bite exactly where onset `fa3e228b` is silent, on things with no
first moment, and only on those whose moments nothing distinguishes. This
fills the gap named in `strong_version_needed` of argument `366a6ea3`, "things
with no first moment of presence", for the homogeneous case only.

**The rival's price.** Consider an extrinsic inertialist who holds that a
received-esse thing never needs a giver except at an onset, including in a
beginningless stationary history (Schmid's explanation covers that case,
part 1). By the theorem, this inertialist must reject at least one of the
three premises for every *possible* homogeneous beginningless received-esse
thing. The three options:

1. **Reject coverage** (part 1): such a thing has received esse and no cause of
   its being at all. Each moment is explained by the one before. This is the
   inertialist's own change-only rationale applied to a history with no change
   anywhere. It amounts, for the whole, to the brute-esse position that the
   corpus records as the rival of the world-indexed De ente coverage
   `d1f3ffcc`, or to the Hume–Edwards view that explaining every member
   explains the series, the recorded rival of `b08eee83` and one of the whole-series
   standards retained in PR #1297 (attempt `a5958e25`). The inertialist avoids
   this for begun things through the originator; here no originator is
   available. (`d1f3ffcc` is stated over `DistinctEsseAt` at a world, so the
   identification is by analogy; the bridge is not built.)
2. **Reject time symmetry** (part 2): a cause gives being at some moments
   rather than others with nothing in the history to distinguish them.
   Clarke's reply, a will that chooses without an external difference
   (`81ec01fe`), is the recorded rival. It is available only to a voluntary
   giver, so it does not help an inertialist who denies a giver, and it
   concedes a cause of being acting in time.
3. **Reject exercise** (part 3): a cause of the thing's being whose activity
   bears on it at no moment of its presence. No account is on file of what
   causing a thing's being would then consist in, when its being is its
   presence at its moments. A timeless cause read on the effect side gives at
   each moment, which is concurrent actualization. Recorded as an open option
   with no substantive support either way.

The price is conditional on two things:

- **The possibility of a homogeneous beginningless received-esse thing.** For
  it there are only unread leads, with no weight: Aquinas's grant that an
  eternal created world is not shown impossible (ST I q.46 a.2); Avicenna's
  eternal caused world; stationary cosmological models.
- **Modal scope.** Coverage is applied as holding in every possible history,
  as a principle about received esse.

The actual world changes, so the theorem is silent on actual persisting
things. An inertialist who confines inertia to begun or changing things and
concedes concurrent giving for homogeneous eternal ones avoids the price. But
that concession gives up the change-only rationale where it applies most
cleanly, since the homogeneous thing undergoes no change at all and still
needs a giver at every moment.

### Avicennian preponderance: (c), restates parity; historical anchor of the symmetry case

There is no corpus record. The Ilahiyyat argument that the possible needs a
preponderator for as long as it exists, because its possibility is permanent,
was **not read** here: a lead with no weight. On an analyst reconstruction,
the thesis "need follows possibility, not novelty" yields parity given onset.
Its decomposition argument (prior non-existence needs no cause, so what is
caused is existence as such) yields only onset, which the inertialist grants.
So it is parity re-presented (c). Avicenna's eternal and eternally caused world
is, though, exactly the homogeneous case of the symmetry family: the case in
which causation of being cannot be onset-only.

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

- **The dependency is not unavoidable for God's existence.** No route to GOD_4
  has `40a97664` as an open premise. The contingency, modal-spine, motion and
  grades routes do their work with other premises, none of which inertia is
  recorded as contesting. The shared dependency is confined to the
  sustaining/immensity attribute step, one support option of `2068f91c` and
  the holding First Way.
- **The PSR family adds nothing at matching scope.** The momentary PSR is
  shared, and under it the remaining bridge is `40a97664` (checked).
- **One horizontal support item, scoped.** Coverage, exercise and time
  symmetry entail `40a97664` for homogeneous received-esse things. Their
  warrants are independent of `40a97664`, and inertia satisfies all three for
  begun things. So a general existential inertialist pays a disjunctive price
  in the possible eternal-stationary case: brute or Hume–Edwards esse for the
  whole, an arbitrary-moment giver, or a cause of being exercised at no
  moment. This adds a priced item to inertia only at modal scope, and only on
  the possibility of such a thing (unassessed). It does not decide actual
  persisting things, whose histories are not homogeneous. The actual-world
  crux is unchanged: no discriminating test at matching scope. The grade of
  `40a97664` moves from "both stand, one price item each" to "both stand; the
  general form of extrinsic inertia carries one further, conditional item".
  Nothing is established or defeated.

**Revision conditions.**

- An independently justified account of why a homogeneous eternal
  received-esse thing needs no cause of its being would remove the item.
- So would an independently justified reason why causes of being need not be
  exercised at any moment of their effect.
- So would a case against the contrastive PSR over moments beyond Clarke's
  voluntarist reply.
- A demonstration that homogeneous beginningless received-esse things are
  impossible would void the item's condition.
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
typed premise to him or to Feser. Aquinas q.46 a.2, Avicenna, Scotus,
stationary cosmology and Clarke beyond `81ec01fe` are marked as leads with no
weight. The objections above name their target premise, their mechanism and
their status. No hypothetical objection is presented as evidence.
