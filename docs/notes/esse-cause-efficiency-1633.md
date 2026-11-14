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
