# Efficiency of causes of esse: the q.3 a.4 claim-vs-type gap (#1633)

**Status:** conditional formal results, prose repairs of existing records and a
provisional judgment. Formal home: `TruthCore/Causality/EsseCauseEfficiency.lean`,
results in `TruthCore/Results/Causality/EsseCauseEfficiency/`, spec
`specs/esse-cause-efficiency-1633.toml`, attempt `5e6464c6`.

## The gap

`STMT-DISTINCT-ESSE-REQUIRES-EXTERNAL-CAUSE` (`33ad148b`) said that every
actual thing whose esse differs from its essence has its esse *efficiently*
caused by another actual being. Its Lean type, `DistinctEsseRequiresExternalCauseReading`,
unfolds to `∀ x, DistinctEsseAt p x → ∃ y, y ≠ x ∧ InAct y esse ∧ CausesIn y x esse`.
`CausesIn` (DEF-CAUSE-OF-PERFECTION) does not fix the mode of causing, so
"efficient" lived only in the paraphrase, the claim, two definitions
(DEF-EXTERNAL-CAUSE-OF-ESSE, DEF-Q3A4-EXTERNAL-ESSE-CAUSE-MODEL), the dichotomy
premise `be639b3f` and the downstream participation statement `7561e216`
(recorded as an open gap in [de-ente-extrinsic-source-1629.md](de-ente-extrinsic-source-1629.md)).

**The source does not state efficiency either.** The pinned witness
(`AQUINAS-ST-I-Q3-A4`, materialized and read) concludes "oportet ergo quod
illud cuius esse est aliud ab essentia sua, habeat esse causatum ab alio";
the dichotomy reads "vel sit causatum ab aliquo exteriori, vel a principiis
essentialibus". Neither names the mode. Two features of the same proof suggest
an agent: the example of an exterior cause ("calor in aqua causatur ab
igne") and the application ("Hoc autem non potest dici de Deo: quia Deum
dicimus esse primam causam efficientem"). On the analyst's reading, that
application bites only if the excluded cause of God's esse would stand before
God in the efficient order; that is an interpretation of the inference, not a
sentence of the text.

## What the downstream types need

The route through `33ad148b` is `4876dc46` (`participatedExternalEsseCause`,
to `7561e216` = `ParticipatedHasExternalEsseCause`, again `HasExternalEsseCause`)
and then `d3c6a6f7` to `STMT-PARTICIPATED-HAS-OTHER-CAUSE` (`2b25a78c`,
`ComponentFirstness.ParticipatedHasOtherCause` over `CausesIn`), a premise of
the efficient-regress route `3b0f4fa5` through the no-component-first-being
step `09c6d5f0`. **Every statement type on this chain is mode-unspecified.**
So the honest repair is to make the prose say what the types say, and to put
efficiency in a separate type where it can be stated and fail. No frozen
Challenge, theorem or binding changes.

**Where efficiency is still assumed.** Two of the arguments for `09c6d5f0`,
`e7b4c683` and `358d8c6e`, combine `2b25a78c` with
`STMT-EFFICIENT-CAUSE-IS-PRIOR-TO-EFFECT` (`e078f07b`), whose Lean
declaration takes its cause relation as a parameter; in
`ComponentFirstness.Premises` it is instantiated with the mode-unspecified
`CausesIn` (`EfficientCauseIsPriorToEffectReading CausesIn Prior`). So "an
efficient cause is prior to what it causes" is applied to every cause of
being, and `e7b4c683`'s meaning says so ("a distinct cause of its being,
which as efficient cause is prior to it"). The efficiency gap is therefore not
closed on the route: it sits in that reading step, not in `33ad148b`. The
third argument for `09c6d5f0` (`5c5b794f`, esse-cause priority) does not use
`e078f07b`. Next test 1 below targets this step.

**`33ad148b` and `457698e4` are the same proposition.** On the same profile
both unfold to "every actual distinct-esse x has some y other than x, in act
as to being, that causes x's esse" (`otherActualCauseIffExternalCause`,
`Iff.rfl`, Comparator-checked with the controls result; relation
`3c2d5bb0`, `logically_equivalent_to`). They stay two records because their
sources differ. No argument is registered between them: each direction would
be an identity transcription.

## Change

**Prose aligned with types (existing records).** `33ad148b`, `be639b3f`'s
exterior horn, `7561e216`, DEF-EXTERNAL-CAUSE-OF-ESSE, DEF-Q3A4-EXTERNAL-ESSE-CAUSE-MODEL,
the claims `d5239ffd` and `7b708e93` (with `attribution` fields), the
meanings of `af503cd7`, `4876dc46`, `d3c6a6f7` (and their inferences and
results, via `specs/term-sense-forks-2.toml`), the doc comments of
`Article4.HasExternalEsseCause` and `TermSenseForks2.ParticipatedHasExternalEsseCause`,
and `457698e4`'s paraphrase now say "caused by another, mode unspecified".
`be639b3f`'s essential-principles horn stays efficient: its primitive is
stipulated as sufficient efficient causation (DEF-Q3A4-ESSENTIAL-PRINCIPLES-CAUSE-ESSE).

**Efficiency typed.** `EfficiencyProfile` extends the q.3 a.4 `Profile` with
one primitive, `EfficientlyCausesEsse y x` (definition `8934912c`): y is an
agent cause of x's esse, tenseless (originating or sustaining), with no
structural law. It is deliberately **not** the secunda via's
`EfficientlyCausesIn` (DEF-EFFICIENT-CAUSING), which is read here and now;
reusing it would import present causing, the conservation question of
#1604/#1616. `HasExternalEfficientEsseCause` (definition `d8963cdd`) is the
q.3 a.4 external cause plus the efficiency conjunct; it is appended to
DISAMB-BECOMING-BEING-CAUSE as `CAUSING_AN_EFFECT_6`, beside the
mode-unspecified senses 2 (`HasExternalEsseCause`) and 3 (`CausesIn`).

| Statement | Lean | Status |
|---|---|---|
| `1ff08418` efficient reading of q.3 a.4 | `DistinctEsseRequiresExternalEfficientCause` | derived (two routes), strengthens `33ad148b` |
| `58e6ec63` OPEN bridge: every actual cause, other than x, of an actual distinct esse is efficient | `DistinctActualEsseCauseIsEfficient` | derived from `0cc3a136` |
| `0cc3a136` OPEN: whatever causes another's esse is an efficient cause of it | `CausingAnothersEsseIsEfficient` | bare |
| `06f2f6b9` controls | `EsseCauseEfficiencyControls` | closed |

| Result | Theorem | Content |
|---|---|---|
| `95b40fad` | `externalEfficientEsseCauseFromDeEnte` | De ente's `457698e4` + bridge `58e6ec63` → `1ff08418` |
| `10c1d8d1` | `externalEfficientEsseCauseFromQ3A4` | `be639b3f` + `61bd42e5` (through the existing transcription theorem) + bridge → `1ff08418` |
| `a2d5d89d` | `externalCauseFromExternalEfficientCause` | `1ff08418` → `33ad148b` (strengthens, backing) |
| `3f0a91c1` | `distinctActualEsseCauseEfficientFromUnrestricted` | `0cc3a136` → `58e6ec63` (strengthens, backing) |
| `23792412` | `esseCauseEfficiencyControls` | three finite interpretations, strictness of both registrations |

All zero-axiom; Comparator and NanoDa accepted locally. Claim `d5239ffd`
`supports` `1ff08418` (relation `037b1f68`) with a gap note: the sentence
states the mode-unspecified conclusion, so efficiency stays unattributed.

**Controls (existence claims on `Bool`; each has `false` as an actual
distinct-esse being).** The types certify only the listed conjuncts; the
witnesses named in parentheses are the interpretations built in the proof.

- *Non-efficient cause*: the q.3 a.4 dichotomy and no-self-sufficiency, no
  self-causation, the actuality of causes of being, `33ad148b` and `457698e4`
  all hold; both bridges and `1ff08418` fail. (Witness: `true`, in act,
  causes `false`'s esse; nothing is an efficient cause.) So the efficient
  reading does not follow from either source route without a bridge, and it
  strictly strengthens `33ad148b`. "Non-efficient" is a label for an
  unconstrained primitive: this is logical independence, not a model of
  formal causation.
- *Restricted bridge only*: `58e6ec63` holds and `0cc3a136` fails.
  (Witness: `false` causes `true`'s esse non-efficiently; `true`'s esse is
  its essence.)
- *Nonvacuity*: every input of both derivations, both bridges and the
  conclusion hold.

## Which existing premises exclude the non-efficient model

None on the route. Certified: the q.3 a.4 inputs of `af503cd7` and the De
ente conclusion `457698e4` hold in the non-efficient control. Not certified
(the control builds no De ente nature source), but read off the types: none
of `457698e4`'s inputs (`d1f3ffcc`, `b62a64ab`, `4ccb319f`) or of their De
ente decomposition (`75919560`, `600f91cb`, `8592601e`, `a2800f45`)
mentions efficiency of a cause other than x; the De ente efficiency bridge
`600f91cb` concerns the thing's own nature. The closest existing premise is
`STMT-PERFECTION-CAUSING-IN-ANOTHER-IS-EFFICIENT` (`e0088de9`, every respect),
which would exclude the model if its `EfficientlyCausesIn` were this tenseless
relation; it is the secunda via's here-and-now relation, so using it here
would be an equivocation. With an OPEN tense bridge (a here-and-now
efficient cause of x's esse is a tenseless one), `e0088de9` at esse would
entail `0cc3a136`; that bridge is not stated here (next test 4). `0cc3a136` is the esse-specific, tenseless analogue,
registered as a new open premise. The agent-or-identical principle of the
#1629 next test reduces to it: with `y ≠ x`, "the cause of x's esse is an
agent or is x" says that the cause is an agent.

**Weaker bridge not used.** "If an actual distinct esse has an actual other
cause, it has an actual other efficient cause" is weaker than `58e6ec63` and
also suffices, but its consequent is the conclusion instance, so the
derivations through it would be transcriptions (invariant 16). The
per-cause bridge is kept, and its extra strength is what the exemplar rival
below prices.

## Rivals (Substantive Objection Standard)

Same actual x, same explanandum: x's esse; target is the bridge `58e6ec63`
unless stated.

| Account | Mechanism and independent justification | Price under its own commitments |
|---|---|---|
| Efficient extrinsic source (Thomistic) | The other actual cause of a distinct esse is an agent from which x's being proceeds, as heat from fire. Justification: the q.3 a.4 context (fire example, God as first *efficient* cause). | It must defend `0cc3a136` (the agent-or-identical principle at esse) or the restricted bridge: that nothing other than x accounts for x's actuality except by acting. That is the open specify-versus-actualize question below, not yet a derivation. |
| Constituent formal principle counted as a being | `c ≠ x` is numerical distinctness, not exteriority. On the Thomist account form is a principle of being (the De ente note records the standard gloss, "forma dat esse materiae", as the analyst's, not the passage's), so if a subsisting form were counted as an actual being other than the composite, it would cause the composite's esse formally, not efficiently. Relevant because the bridge's antecedent uses only `c ≠ x`. | Not a rival to the q.3 a.4 text, which says "ab aliquo **exteriori**": it shows that the typed bridge is broader than the text. Repair (next test 2): restrict the bridge to non-constituent causes; that needs a constituency relation on the profile. |
| Non-agent exterior exemplar (Platonic participation) | A separate Form that x participates in accounts for x's being without acting (the Phaedo-style "by the Beautiful all beautiful things are beautiful"; attribution deferred, not re-read). It falsifies the *universal* bridge only if such a Form is an actual being that causes x's esse while no agent does, or alongside one. | If an agent also causes x's esse, only the per-cause bridge fails and the weak existential form survives. If no agent does, the account owes how a non-acting exemplar makes x actual rather than specifying what x is; that is #1621's adequacy question and #1629's specify-versus-actualize question. Unpaid, not refuted. |
| Structural or global explanation (#311/#750) | Unsupported suggestion, no evidential weight here: no concrete case is identified of a structure that accounts for a particular bearer's existence without acting, so the Standard's independent-justification item is not met. Recorded only because the issue names it. | If such a structure acts, it is an efficient cause and satisfies the bridge; if it only characterizes x, the burden is the one recorded in #311 (EXP-LOCAL-TO-GLOBAL) and #750. |
| Brute esse, infinite regress | Not rivals to this bridge: they reject the antecedent (`d1f3ffcc`, `fd12ad3d`). See the #1629 and #1628 notes. | — |

No substantive objection was identified to the strength-order steps or to the
prose repairs: they drop a conjunct or align prose with an unchanged type.

## Overall provisional judgment (2026-11-14)

**Claim.** Every actual distinct esse is efficiently caused by another
actual being (`1ff08418`).

**Judgment.** Conditionally supported, not established. Formally it follows
from either source route exactly with the OPEN per-cause efficiency bridge,
which the controls show is needed. The q.3 a.4 text gives contextual evidence
that an agent is meant (fire example, efficient-order application) but does
not state it, and De ente rejects only *efficient* self-causation by the
quiddity, which is neutral on the mode of another's causing. The strongest
standing rival to the bridge is a non-agent principle of esse, either a
constituent form (which the bridge's `c ≠ x` does not exclude, a defect of
the typed bridge's breadth rather than of the Thomist view) or a non-agent
exterior exemplar; its price is to show how a non-agent accounts for x's
being actual rather than specifying it. **For the root route nothing is
discharged:** no statement type downstream of `33ad148b` mentions
efficiency, and the place where the route does assume it, `e078f07b`
applied to the mode-unspecified `CausesIn` in `e7b4c683` and `358d8c6e`, is
not yet connected to `1ff08418` (next test 1). The efficient route into
`33ad148b` adds no support to it: `33ad148b` is the same proposition as
`457698e4`, and the route discards the efficiency it adds.

**Would revise.** Upward: a derivation of the bridge for non-constituent
causes from a specify-versus-actualize principle, or a verified tense bridge
connecting `e0088de9`'s here-and-now efficient causing to this relation.
Downward: a worked non-agent account of actualizing (not specifying) a
distinct esse.

**Boundaries.** No conservation, present sustaining, uniqueness, necessity
or God identification follows; `33ad148b` closing (frontier "stated ->
closed") means proved from open premises, not established.

## Computed premise delta

`truth frontier-diff --base 2524680bd`: open premises reaching the root
480 -> 480 (341 -> 342 bare, 49 -> 48 stated); verified support alternatives
473 -> 477 (both routes to `1ff08418`, `1ff08418` → `33ad148b`, `0cc3a136` →
`58e6ec63`); bare premise added `0cc3a136`; `33ad148b` moved stated ->
closed (proved from open premises). Route costs unchanged.

How to read it: the strength registration `1ff08418` → `33ad148b` counts as
a derivation in `frontier`, so `33ad148b` now closes from the De ente
premises plus the efficiency bridge, and `0cc3a136` becomes a root-reaching
bare premise. Both are artifacts of a dominated route. `33ad148b` follows
from `457698e4` alone (same proposition, `otherActualCauseIffExternalCause`),
and the bridge does no logical work for it; the identity is recorded as a
`logically_equivalent_to` relation, not as an argument, because each
direction would be an identity transcription. No root premise is defended or
discharged.

## Remaining prose debt

Records and comments outside this diff that still read
`HasExternalEsseCause` or the q.3 a.4 witness as efficient, listed for a
follow-up: argument `root-essence-identity` ("supplies a distinct efficient
esse cause"), `GENUS-CAUSE-BOUNDARY` and its statement ("q3a4 positive
efficient-cause witness"), the label of DISAMB-ANSELM-THROUGH-VS-EFFICIENT-CAUSE,
the omission-model statement `q3-a4-esse-cause-omission-models`, the doc
comments of `EssenceEsseExternalCause.premiseOmissionsAndControl`,
`UnderivedEssenceEsse.lean` (line 56) and `DeEnte/ExtrinsicSource.lean`
(module doc, owned by #1635), and the frozen `TermSenseForks2/Challenge.lean`
doc comments (lines 131 and 141), which cannot be edited. None of them changes
a type.

## Next tests

1. **Efficient priority at `09c6d5f0`.** Done in the follow-up slice below
   for `358d8c6e`; `e7b4c683` keeps no sibling.
2. **Non-constituent bridge.** Add a constituency relation to the profile
   (reuse `ComponentOf` vocabulary if its meaning matches), restrict
   `58e6ec63` to causes that are not constituents of x, and test whether the
   constituent-form counterexample is then excluded while the non-agent
   exemplar model survives.
3. **Specify versus actualize.** Split the cause-of-being relation into
   "specifies the actuality x has" and "accounts for x's being actual", and
   test whether `0cc3a136` (restricted to accounting causes) follows from
   "an accounting principle is an agent or is the act it accounts for".
4. **Secunda via connection.** State the tense bridge between the secunda
   via's here-and-now `EfficientlyCausesIn` at esse and `EfficientlyCausesEsse`
   and test whether `1ff08418` then feeds the secunda via's order of efficient
   causes.

## Semantic challenge

An independent reviewer challenged the committed diff (not these
conclusions). Accepted and repaired: (1) the efficient route into
`33ad148b` adds no support, since `33ad148b` and `457698e4` are the same
proposition; the identity is now verified (`otherActualCauseIffExternalCause`)
and recorded as `logically_equivalent_to`, `457698e4`'s paraphrase says so,
and the delta above is read as a dominated-route artifact. (2) The first draft
said no root-route consumer needs efficiency; false, because `e7b4c683` and
`358d8c6e` apply `e078f07b` to `CausesIn`. Retracted everywhere and recorded
as the remaining gap and next test 1. (3) The dichotomy `be639b3f` is a
declared sense bridge only because it pairs the two forks; said so in the
argument's meaning. (4) The claims' attributions now record that the
actuality of the cause (and, for `be639b3f`, the efficient reading of the
essential-principles horn) is the encoded reading, not stated. (5) The
`supports` note marks the efficient-order reading of the God sentence as the
analyst's. (6) Control prose now separates the certified conjuncts from the
proof witnesses, and the De ente inputs are no longer said to be checked in
the control. (7) Three disambiguation resolutions that read the q.3 a.4
cause as efficient were aligned; the rest are listed above. (8) The
structural rival is recorded as an unsupported suggestion. Not done: a
certified-difference `strength_comparison` for the two registrations
(optional; no non-degenerate delta was found for the efficient pair, since
the restricted bridge is not equivalent to the difference).

## Follow-up: efficient priority at `09c6d5f0`

Formal home: `TruthCore/Causality/EsseCauseEfficiencyPriority.lean`, results
in `TruthCore/Results/Causality/EsseCauseEfficiencyPriority/`, spec
`specs/esse-cause-efficiency-priority-1633.toml`, attempt `c6dfd231`.

**The gap.** `e7b4c683` and `358d8c6e` conclude `09c6d5f0` (no component is
the first being) from, among others, `2b25a78c` (a participated being has a
cause of its being other than itself, `CausesIn`, mode unspecified) and
`e078f07b` ("an efficient cause is prior to what it causes"), whose Lean
declaration `EfficientCauseIsPriorToEffectReading` takes the cause relation
as a parameter; both arguments instantiate it with `CausesIn`. So they read
every cause of being as efficient.

**The sibling.**

| Record | Content |
|---|---|
| `811c2e98` `ParticipatedHasOtherEfficientEsseCause` | whatever has being by participation has an efficient cause of its esse other than itself (`∃ c, c ≠ x ∧ EfficientlyCausesEsse c x`) |
| `b0cd6015` `EfficientEsseCauseIsPrior` | OPEN: an efficient cause of a thing's esse (tenseless) is simply prior to it |
| `19882fa9` `EfficientEsseCauseActsHereAndNow` | OPEN tense bridge: every efficient cause of a thing's esse is, here and now, an efficient cause of it at esse (secunda via sense, DEF-EFFICIENT-CAUSING) |
| `a2ae4358` `participatedEfficientCauseFromQ3A4` | `cbb068e8` + `1ff08418` → `811c2e98`; `strong_version_needed` records why `33ad148b` does not suffice |
| `5769b268` `noComponentFirstEfficientEsseOfWeak` | `86f10ec3`, `61ad11f3`, `c6d6379b`, `811c2e98`, `b0cd6015` → `09c6d5f0`: sibling of `358d8c6e`, composing `noComponentFirstOfWeak` with the cause relation `EfficientlyCausesEsseIn q` (`r = esse ∧ EfficientlyCausesEsse c x`) |
| `2b0c43c0` `efficientEsseCausePriorityFromHereAndNow` | `e078f07b` (at the here-and-now relation) + `19882fa9` → `b0cd6015` |
| `b7e3cc74` `efficientPriorityControls` | three finite interpretations |

**Why a separate priority premise (Codex review on #1640).** The first draft
bound the sibling's priority hypothesis to `e078f07b` itself, instantiated
with the tenseless efficient relation. But `e078f07b`'s evidence is read for
the secunda via's here-and-now relation: its claim `3ed048c0` grounds
priority of nature in per se causes that "act together", and its derivation
`8c629064` rests on `c0d99549` ("it would not be if c were not"), while
`EfficientlyCausesEsse` also admits merely originating agents. Binding the
tenseless instance to `e078f07b` would let the graph supply it from the
secunda via support without the tense step. So the tenseless priority is its
own OPEN premise `b0cd6015`, and its derivation from `e078f07b` goes through
the explicit OPEN tense bridge `19882fa9` (every agent cause of esse is a
present, conserving cause; #1604/#1616 territory). `e078f07b` is now used
only at a here-and-now relation, as its evidence reads it.

No sibling of `e7b4c683` is registered: its inputs `a4d3261a` and `86f10ec3`
use two senses of POTENCY_CAPACITY_AND_POWER_ACROSS_ADOPTED without a bridge
(legacy allowlist), and a new argument may not inherit that.

**Controls (existence claims; witnesses are labels for unconstrained
primitives).**

- *Non-efficient participation*: participated distinct esse, `33ad148b`,
  `2b25a78c`, the component kinds, both act-priority premises, non-overlap
  and `b0cd6015` hold, while priority over `CausesIn`, `1ff08418` and
  `811c2e98` fail and a component is first. So the efficient participation
  premise is not supplied by the mode-unspecified route, and priority over
  every cause of being is not implied by the priority of efficient causes of
  esse. (In the witness the efficient relation is empty, so `b0cd6015` holds
  trivially.)
- *Nonvacuity*: a component exists, every input of the sibling route, the
  secunda via priority at a here-and-now relation and the tense bridge hold,
  and so does the conclusion.
- *Tense gap*: the secunda via priority holds at a here-and-now relation while
  the tense bridge and `b0cd6015` fail. So `b0cd6015` does not follow from
  `e078f07b` without the bridge.

**Effect (computed `truth frontier-diff --base origin/main`).** Open premises
reaching the root 489 → 490 (bare 348 → 349); verified support alternatives
486 → 489 (`09c6d5f0` from the efficient sibling; `811c2e98` from `1ff08418`
+ `cbb068e8`; `b0cd6015` from `e078f07b` + `19882fa9`); bare premise added:
the tense bridge `19882fa9`. The efficiency the route assumed in a reading
step is now a typed premise chain: `09c6d5f0` ← `811c2e98` ← `1ff08418` ←
`58e6ec63` (OPEN) ← `0cc3a136` (bare), and ← `b0cd6015` (OPEN, supported
through `19882fa9`). The existing arguments are unchanged; this is an
additional support option, not a discharge.

**Remaining.** `e7b4c683`'s reading step stays untyped (sense debt). The
tense bridge is open; a merely originating agent of esse falsifies it, so
its warrant is the conservation question. Items 2–4 of the next tests are
otherwise unchanged.

**Semantic challenge (this slice).** An independent reviewer found no P1.
Accepted and repaired: the scope gap in reusing `e078f07b` for the tenseless
relation (then stated in prose; after the Codex review, separated into
`b0cd6015` and `19882fa9`); the overstatement of what the non-efficient
control shows; one disambiguation sentence narrowed to the existing route.
Recorded, not repaired here: the label of `c6d6379b` says POTENCY_1 while it
links the POTENCY_2 definition `3ea2762f` (pre-existing). Checked and
declined: a reported missing link to definition `8934912c` on the sibling
argument (it is present).

## Current cluster assessment under the substantive objection standard (2026-11-18)

**Scope and boundary.** Issue #1751, bottom-out walk of the cheapest GOD_4
route (prima via argument `ed7c588a`), family E: composition, esse and
necessity. The twelve open leaves are `86f10ec3`, `ca55ed3a`, `d017b6b0`,
`f3b79f16`, `75919560`, `600f91cb`, `a2800f45`, `ef068f46`, `19882fa9`,
`b8d21cd0`, `d483248e` and `3c20c835`, drafted on main
`df4909cb025d2e53fee6071a32defe9cf2721284`. At that revision nine were
`legacy_only` and three (`b8d21cd0`, `d483248e`, `3c20c835`) had no attempt.
This note hosts the section because the question that unites the cluster is
the one this note is about: the **mode and tense of causing esse** (efficient,
formal or material; originating or sustaining). That question also decides the
De ente nature-source step formalized in
[de-ente-extrinsic-source-1629.md](de-ente-extrinsic-source-1629.md), whose
records this section reads but does not change. Already-current neighbours are
reused, not reassessed: `6b80cfe4`, `58445bd6`, `27d15954` and `fbee7f15`
(attempt `dd24400b`); `cbb068e8` and `10cd24ed` (`5c7bc356`); `3c468121`
(`386cc16c`); `3b2d2d46`, `61ad11f3`, `8288ff1e`, `09c6d5f0`, `ee74c678` and
`e078f07b` (`383d23ad`). Earlier sections stay unchanged under their own dates.
No theorem, Challenge, claim, statement, definition, relation, closure or
formal status changes.

### (a) Fixed meanings

- `CausesIn c x esse` is the tenseless, mode-unspecified cause of being
  (DEF-CAUSE-OF-PERFECTION `211a6432`, CAUSE_2). `EfficientlyCausesEsse` is
  the tenseless agent-cause primitive of the q.3 a.4 efficiency profile, which
  admits merely originating agents. `EfficientlyCausesIn` (DEF-EFFICIENT-CAUSING
  `8934912c`) is the secunda via's here-and-now efficient causing.
- NATURE_SOURCE (DISAMB `87ac7ae0`): NATURE_SOURCE_1 `fromNature` (definition
  `b5ca3837`, an unconstrained primitive) is the literal disjunct "causatum ex
  principiis naturae suae"; NATURE_SOURCE_2 `quiddityEfficientlyCauses`
  (`4d6a0f0e`) is efficient causation by the thing's own quiddity.
- CORRUPTIBLE_INCORRUPTIBLE_1 (`051fe0e7`, DISAMB `ed4f1f3f`):
  `IncorruptibleSimply` is `¬ CanFailToBe x esse`, failing to be in substance
  only. NECESSARY_1/NECESSARY_3 (`d77ab971`, DISAMB `83264cf5`): `IsNecessary`
  is `¬ Possible (fun t => ¬ IsAt x t)` with `Possible` a parameter; the
  temporal step "quod possibile est non esse, quandoque non est" is a separate
  statement (`WhatCanNotBeSometimeIsNotReading`) and is not imported here.
- Participation is PARTICIPATION_4 (definition `14d30c53`, DISAMB `54f33165`),
  q.44's derivative esse. `Participated` is a primitive predicate with no
  distinct Lean declaration for the sense.
- Uniting, efficient causing and causing esse are kept apart (DISAMB
  `57f80020`).

### (b) Where each leaf sits

| Leaf | Consumer(s) | Conclusion and its other support |
| --- | --- | --- |
| `75919560`, `600f91cb` | `16654a70` (result `42a89226`) | `8592601e`, then with `a2800f45` (`05c81e70`, result `44eef980`) causal coverage `d1f3ffcc`. `d1f3ffcc` keeps its direct option; this slice does not assess it. |
| `a2800f45` | `05c81e70` | as above |
| `ef068f46` | `9355c3db` (result `d7c9cadd`, with `7067553d`) | `4ccb319f`, also concluded by `9126bd28` from `d0fc96b7`; consumed by `42908cf8` (result `8477d8c7`) for `457698e4` |
| `19882fa9` | `90e120ab` (result `2b0c43c0`, with `e078f07b`) | `b0cd6015`, used only by `8a3a4577` (result `5769b268`), one of four bundles for `09c6d5f0` |
| `86f10ec3` | `358d8c6e`, `e7b4c683`, `5c5b794f`, `8a3a4577` | `09c6d5f0` (all four registered derivations); `09c6d5f0` is itself source-stated (claim `b3b55883`) |
| `ca55ed3a` | `983fd86b` (result `c62c4ec3`), `ae809bfd`, `27d7cebb` (plus `6df393c4`, `d812acaa` off the routes) | `8288ff1e` (only derivation `983fd86b`); `61ad11f3` (also `4bcf25b5`, from `3b2d2d46` alone, and `15fce38f`/`11b24e97`, both via `8288ff1e`) |
| `d017b6b0` | `983fd86b`, `83be8aad` (result `26c9ca8b`), `ae809bfd`, `27d7cebb` | `8288ff1e`; `79281639` (only derivation `83be8aad`); `61ad11f3` |
| `b8d21cd0` | `83be8aad` | `79281639` |
| `f3b79f16` | transcriptions `fcb4b871` (result `7cb451cc`, with calibration `1ad18c70`) and `e79971d9` (with `4133bd12`) | `27d15954` and `8e44a618`, both transcriptions; `dd24400b` judged `27d15954` dispensable for `ca07cae9` |
| `d483248e`, `3c20c835` | transcription `142d6218` (result `a445f274`, with `f8ba2429`) | `3c468121`, also concluded by transcription `30c06bc2` from `651a68d4` and `0014afa4` |

### (c) Per-leaf end state, warrant and shared dependencies

| Leaf | End state | Strongest positive warrant and scope | Defeaters, blocker and shared dependencies |
| --- | --- | --- | --- |
| `a2800f45` quiddity efficiently causing esse is self-causation | **Defended primitive, source-stated; first grade strong.** | Claim `ce55e563` states the conditional (De ente [69874], "sic aliqua res esset sui ipsius causa"). A quiddity is a principle of x, not a being other than x, so its efficient causing is x's causing. | No substantive objection identified. It needs `b62a64ab` (no self-causation) to do any work. |
| `75919560` nature or another | **Defended direct option, source-stated; first grade moderate.** | Claim `676bdaeb` states the disjunction. Both of the passage's examples, risibility flowing from human nature and light in the air from the sun, are cases where the source is enough to account for the feature. | Only the instance at actual distinct esse is used (`42a89226`); the all-respects, all-beings version is stronger than any consumer needs, and a weak version is not registered. At the first being, where esse is the nature, `fromNature` must cover identity rather than causing (the docstring of `600f91cb` says so); the weak version avoids that strain. Kept: brute esse at a distinct esse (#312/#746), the stopping-policy dispute this premise shares with `d1f3ffcc`. |
| `600f91cb` nature source of a distinct esse is efficient | **Open, concrete blocker.** | On the sufficient-account reading of NATURE_SOURCE_1 (finding N below), its support is the 2026-11-17 positive reply in the #1629 note: a specifying nature misses the target, and an adequate necessary or underived version concedes the intermediate. | It is the own-nature instance of the agent-or-identical principle, whose other-being instances `0cc3a136` and `58e6ec63` are open. They share one general warrant (the agent-or-identical principle); neither entails the other, so they are not two independent pieces of evidence. Kept: the non-efficient intrinsic nature account (target `600f91cb`; mechanism: a nature as a non-agent principle that accounts for its subject's esse; independent justification: the formal-cause gloss recorded as the analyst's in the #1629 note and in the rival table above). Its price is the intrinsic-adequacy question #1621, restricted to distinct esse. |
| `ef068f46` a cause of being is in act in some respect | **Defended primitive, strong for efficient causes of being; open at the full CAUSE_2 scope the route uses.** | Agency in act (q.75 a.2 "non enim est operari nisi entis in actu", claim `f4b1c499`, and q.25 a.1, claim `a5d11a9e`, neither attributed this statement) warrants it for efficient causes. The extension to formal causes (a formal principle counted as a being is itself an act) is the analyst's. | Its own paraphrase reads `CausesIn` at esse "for extrinsic (efficient) causes", while `d1f3ffcc`, `457698e4` and the #1629 records read the same relation as mode-unspecified and allow constituents. Meaning condition, not a kept objection: open at full CAUSE_2 scope pending the meaning choice left open by `dd24400b` (principles in the Being domain). If material causes count, the Thomist thesis that prime matter is pure potency (not on file) would falsify it. |
| `19882fa9` every efficient cause of esse acts here and now | **Open, concrete blocker; dispensable for `09c6d5f0`.** | The q.104 a.1 distinction between a cause of becoming and a cause of being as such, on whose action the effect's being depends (claim `40aefb2e`, which does not state this bridge; #1616 territory). | Kept: existential inertia and merely originating agents (target `19882fa9`; mechanism: an efficient cause of x's esse that originates x and then ceases; independent justification: the persistence of products after their producers cease, established for causes of coming-to-be (the builder of claim `40aefb2e`), together with the profile's own definition of `EfficientlyCausesEsse`, which admits originating agents). The Thomist reply restricts the relation to causes of esse in the q.104 a.1 sense, which moves the burden to conservation (#1616, #1626). Bypass: `5c5b794f` (result `764f43fe`) concludes `09c6d5f0` without `b0cd6015` or `19882fa9`. It is single-sense, and none of its inputs (`61ad11f3`, `732302a1`, `86f10ec3`, `c6d6379b`, `ee74c678`) derives from `19882fa9`. |
| `86f10ec3` every component is in potency or participated | **Open, missing bridge: exhaustiveness of the two component kinds is not warranted on file.** | Relation `bde98cf1` records only support (q.3 a.8 names matter and a participated form), not exhaustiveness. Unread source lead, to materialize from the pinned q.3 witness before any weight is given: ST I q.3 a.7 co., fourth proof (in every composite there are potency and act: either one part is act to another, or all parts are as in potency to the whole). | Load-bearing in all four registered derivations of `09c6d5f0`, each a reductio that applies it to a component supposed first. Its denial there is the rival's thesis, so its warrant must come from the structure of composition. The named rival (God as form or component of the world, the view q.3 a.8 rejects) has no independent justification on file. It is restated, not evidence against the premise, but that does not supply the missing warrant. The "forma participata" to PARTICIPATION_4 reading is recorded only in `bde98cf1`'s note, and the sense has no Lean declaration, so bind-check cannot catch an equivocation there. |
| `ca55ed3a` every first being is simply incorruptible | **Derivable by a specified short derivation (next test), conditional on unassessed inputs; no direct warrant on file; dispensable.** | The orientation passage, as the statement's own paraphrase gives it ("the necessary beings are first"), runs in the converse direction (necessary to first). Derivation: if a first f could fail to be, take a necessary e (`2023273e`, the tertia via's conclusion); by `b8d21cd0` e cannot fail to be; by `418f337d` e is prior in substance to f; by `9226c6af` e is simply prior; and e ≠ f, contradicting firstness. | Inputs `9226c6af` and the tertia-via premises behind `2023273e` are not assessed here. The derivation would make this prima via step depend on the tertia via, which is horizontal support, not an independent check. The `truth semantics` preflight fails on an over-link (finding S4). The checked shortcuts through `a4d3261a` or `3b2d2d46` do not type-fit (package P3). Contingent first being (`124ff6a9` rival (a)): restated. It names a mechanism; the only justification on file is a control, a fact about one interpretation, plus unread literature. Dispensable: `8288ff1e` keeps its weaker direct option (the ContingentFirst control shows it does not entail `ca55ed3a`), and `61ad11f3` keeps `4bcf25b5` (from `3b2d2d46` alone), and also `15fce38f` and `11b24e97` (both via `8288ff1e`). |
| `d017b6b0` the simply incorruptible is in act in substance | **Defended primitive, source-stated; first grade strong.** | Claims `3c6af940` (Met. Θ.8 1050b16-18) and `be153747` (In Metaph. IX lect. 9 n. 5-6). The Lean type is the contrapositive of "whatever is not in act as to being can fail to be": the actuality-to-possibility principle for `CanFailToBe`. | Meaning condition, not an objection: `CanFailToBe` must count present non-being as failing to be. Otherwise the premise would carry an unwarranted step from possibility to actuality. No substantive objection identified. It is the only derivation input of `79281639` together with `b8d21cd0`. |
| `b8d21cd0` what can fail to be in substance possibly is not | **Defended primitive (meaning bridge); first grade strong.** | "Potest non esse secundum substantiam" and "possibile non esse" render the same modal content. Supporting claim `c69afccc` (every potency is of the contradictory). Only the safe direction is assumed. The consumer uses its contrapositive (necessary to incorruptible), which stays valid even if the tertia via's possibility is broader (through a power in another, DISAMB `557d8e44`). | No substantive objection identified. A temporal reading of `Possible` would turn it into the contested "quandoque non est" step; that step is a separate statement and is not used. |
| `f3b79f16` the composer is an efficient cause (time-neutral) | **Defended direct option, source-stated; first grade strong as time-neutral.** Its route contribution is gated. | Claim `e017e2d6` (SCG I.18 n.4, "componens autem est causa efficiens compositi"). | It reaches the route only through two calibration transcriptions whose calibrations `1ad18c70` and `4133bd12` are unassessed. Immanent constitution: kept only conditionally, with the same mechanism as `dd24400b`'s row: it bites if a component may stand as the uniter in `Unites`. This is a relocation, not new evidence. The legacy blocker in `f3722322`, framed as route cost, is superseded. |
| `d483248e` necessity is a perfection the necessary being is in act in | **Open, contested reading; dispensable.** | No positive warrant on file beyond the analyst stipulation linking `IsNecessary` to a respect `nec`. | "Necessity is a mode of being, not a perfection" is an interpretation fork, not an objection: the mode reading is registered as sibling `651a68d4`, and `30c06bc2` reaches the same `3c468121` without `d483248e` or `f8ba2429`. `3c468121` is current (`386cc16c`) as an open dictionary bridge. |
| `3c20c835` causing in respect nec causes necessity | **Defended primitive as a meaning postulate, conditional on `d483248e`.** | Given `d483248e`'s reading, causing x to be in act in nec is causing x's necessity. It is the r = nec analogue of `0014afa4`; no relation is registered between them. | No substantive objection identified. Consumed only by transcription `142d6218`. |

### (d) Findings

**N. The NATURE_SOURCE step.** The sense passage is correctly bridged. `truth
semantics 16654a70` reports NATURE_SOURCE as *bridged* by the declared premise
`600f91cb`, and `05c81e70` uses only NATURE_SOURCE_2. The equivocation the
bridge prevents is real. The preflight `truth semantics --premise 75919560
--premise a2800f45 --conclusion d1f3ffcc` (the literal disjunction plus the
rejection, with no bridge) fails with "unbridged mixing" of NATURE_SOURCE_1 and
NATURE_SOURCE_2.

There is a residual sub-ambiguity inside NATURE_SOURCE_1, which no tool can
see because `fromNature` is an unconstrained primitive. It sharpens the
specify-versus-accounts fork already drawn in the #1629 rival table (row
"Non-efficient intrinsic nature account") and next test 3 above. "From its
nature" can be read three ways:

- (a) the nature *specifies* the actuality x has;
- (b) the nature *contributes* to x's esse as a formal, partial principle;
- (c) the nature *suffices* to account for x's having the feature.

The three premises fare differently under them:

- On (a), `fromNature x esse` holds of every actual distinct-esse x. Then `600f91cb`, `a2800f45` and `b62a64ab` jointly give that no actual distinct-esse being exists (package P1). That contradicts the existence inputs of the De ente route (`5ab6cc2b`): two actual beings `33f3c4c5` with at most one `a576300f` give an actual distinct-esse being.
- On (b), the analyst's formal-cause gloss recorded in the #1629 note makes `600f91cb` false wherever a form formally contributes to its composite's esse.
- On (c), the reading the passage's examples fit, `600f91cb` can hold together with the route's existence inputs. It then says exactly that no nature by itself sufficiently and non-efficiently accounts for a distinct esse.

So the step does not equivocate *between* the two senses. It needs sense 1 fixed to (c) for 75919560's textual warrant and 600f91cb's plausibility to concern one proposition. Given `a2800f45` and `b62a64ab`, `8592601e` and `d1f3ffcc` are interderivable: `44eef980` derives `d1f3ffcc` from `8592601e` and `a2800f45`, and `d1f3ffcc` with `b62a64ab` gives the other-cause horn of `8592601e` at once, so `8592601e` adds no content beyond `d1f3ffcc`. The decomposition's value lies in its premises: it assigns the brute-esse rival to `75919560` and the intrinsic-nature rival to `600f91cb`. At reading (c), `600f91cb` is the denial of the latter, so the decomposition relocates the intrinsic-account dispute rather than independently corroborating coverage. Its positive support there is the source disjunction plus the 2026-11-17 reply.

**S. Other sense findings.**

1. `e7b4c683`'s allowlisted POTENCY_1/POTENCY_2 mixing (`a4d3261a` with
   `86f10ec3`) is a genuine equivocation risk with no bridge, as recorded
   above. Its single-sense siblings `358d8c6e`, `5c5b794f` and `8a3a4577`
   avoid it.
2. The allowlisted UNITING_CAUSE_1/_2/_4 mixing in `fcb4b871` is a
   multi-sense passage carried by its premises, not an equivocation:
   `f3b79f16` carries _1 to the attribution frame and `1ad18c70` carries the
   frame to here-and-now efficient causing. The preflight passes once
   `1ad18c70` is declared for both _1→_4 and _2→_4. The _1 tag on `f3b79f16`
   under-describes its frame. `e79971d9` passes with `4133bd12` declared for
   _1→_4.
3. The UNITING_CAUSE_3 to _2 passage in `ae809bfd` and `6df393c4` is correctly
   bridged by `e0088de9`.
4. `418f337d` links the CORRUPTIBLE_INCORRUPTIBLE_2 definition. Its Lean type
   uses only the simple sense, as DISAMB `ed4f1f3f`'s resolution says. This is
   an over-link, but it makes the `ca55ed3a` derivation's preflight fail;
   PRIOR_3 to PRIOR_1 is bridged by `9226c6af`.
5. `ef068f46` and `4ccb319f`: a prose-scope gap on one Lean relation (row
   above), not a type equivocation.

**P. Small premise sets tested from the Lean bodies** (analyst derivations of
a few lines, not Lean-checked):

- P1: `600f91cb`, `a2800f45` and `b62a64ab`, under reading (a), entail that no
  actual distinct-esse being exists, against the existence inputs of the De
  ente route `5ab6cc2b`.
- P2: `ef068f46` is inconsistent with a prime-matter Being that causes the
  composite's esse and is in act in no respect (the meaning condition in its
  row).
- P3: corruptibility encoded as `InPotency x esse`, with `c6d6379b` and an
  actual corruptible x, is inconsistent. This is why `ca55ed3a` has no short
  derivation from the act/potency premises: the profile has no respect for
  potency to not-be.
- P4: `19882fa9` contradicts any merely originating `EfficientlyCausesEsse`
  edge, which the profile admits.

**Strength and duplicate notes.**

- Weak versions that would suffice are unregistered for `75919560` (the
  distinct-esse instance at esse) and `86f10ec3` (components supposed first).
- `ef068f46` is weaker than `4ccb319f` (lemma `inActOfHasBeing`, unregistered).
- `d017b6b0` with `b8d21cd0` gives `79281639` as actuality-to-possibility for
  the tertia via's modality.
- `600f91cb` shares one principle with `0cc3a136` and `58e6ec63`.
- Transcription-only support: `d483248e`, `3c20c835` and `f3b79f16`.

**Objection classification.** Kept 4, all conditional or restricted:

1. brute esse against `75919560` at distinct esse;
2. the non-efficient intrinsic nature account against `600f91cb`;
3. existential inertia and originating-only agents against `19882fa9`;
4. immanent constitution against `f3b79f16`, conditional on the `Unites`
   meaning choice.

Restated 3:

1. contingent first being against `ca55ed3a`;
2. God as a component against `86f10ec3`;
3. the mode-of-being reading against `d483248e`, as an interpretation fork.

Meaning condition (1): prime matter against `ef068f46`, pending the
`dd24400b` modelling choice.

Facts about single interpretations, listed separately and not counted as
objections: the ContingentFirst, HeavenlyFirst, FormalNatureControl and
efficient-priority controls. (The first draft counted them as a fourth
restated item.)

No substantive objection identified for `a2800f45`, `d017b6b0`, `b8d21cd0` or
`3c20c835`.

### (e) Overall provisional judgment

The cluster bottoms out unevenly, and its weight sits in two places.

- **Well supported (three) plus one conditional meaning postulate:** the
  necessity-to-act chain `d017b6b0` + `b8d21cd0` → `79281639`, and
  `a2800f45`, are strong defended primitives. `3c20c835` is a meaning
  postulate conditional on `d483248e`.
- **Source-stated direct options (two):** `75919560` (moderate) and
  `f3b79f16` (strong as time-neutral, but reaching the route only through
  unassessed calibrations).
- **Conditional on a meaning choice (one):** `ef068f46` is strong for
  efficient causes of being; its extension to formal causes is the analyst's.
- **Dispensable and open (three):** `ca55ed3a`, `19882fa9` and `d483248e`.
  Each has a non-circular bypass or a weaker direct option, checked above.
  `ca55ed3a` also has a specified horizontal derivation.

The two load-bearing open leaves are:

- `600f91cb`, on the De ente decomposition of `d1f3ffcc`. Its strongest rival is
  the non-efficient intrinsic nature account; its blocker is the unregistered
  sufficient-account reading and the own-nature agent-or-identical principle.
- `86f10ec3`, in every derivation of `09c6d5f0`. Exhaustiveness of the two
  component kinds is not warranted on file.

Neither is refuted and neither is established. Both have direct routes around
them: `d1f3ffcc` and `09c6d5f0` keep their own direct options, the latter
source-stated.

**Conditions on other lanes and slices.** `9226c6af` and the priority family
(`732302a1`, `ee74c678`, `61ad11f3`, `a4d3261a`) belong to other assessments.
The tertia-via inputs behind `2023273e` and the calibrations `1ad18c70` and
`4133bd12` are unassessed. The principles-in-the-Being-domain choice
(`dd24400b`) governs `ef068f46` and `f3b79f16` jointly. Causal coverage
`d1f3ffcc` is not assessed in this slice.

**Would revise.**

- Upward: a registered sufficient-account sense with a derivation of
  `600f91cb` from an independently warranted specify-versus-actualize
  principle; a derivation of `86f10ec3` from a composition-structure premise
  (every composite is of a receiver and a received, receivers are in potency
  `7fcfcee8`, received acts are participated) that also covers integral
  parts, for which ST I q.3 a.7 co.'s fourth proof (in every composite
  potency and act: one part act to another, or all parts as in potency to the
  whole) is the unread source lead to materialize from the pinned q.3 witness;
  a meaning decision that excludes material causes from CAUSE_2 at
  esse.
- Downward: a worked case of a nature that sufficiently and non-efficiently
  accounts for a distinct esse; a positive argument for a pure-act,
  unparticipated component.

**Next test (most discriminating).** Define NATURE_SOURCE_1(c)
non-primitively, through an explicit adequacy relation shared with #1621, so
that a sufficient non-agent model is a substantive constraint test rather than
an unconstrained one. Rerun the `676bdaeb` attribution check against it. Then
compare `600f91cb` and `0cc3a136` as instances of one agent-or-identical
principle, and record whether any warrant attaches to the own-nature instance
alone.

Further tests:

- certify the `ca55ed3a` derivation after repairing the over-link on
  `418f337d`;
- register the weak versions of `75919560` and `86f10ec3`;
- decide whether `CausesIn` at esse includes material causes.
