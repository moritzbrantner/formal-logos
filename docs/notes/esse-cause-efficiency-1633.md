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
step `09c6d5f0`. **Every type on this chain is mode-unspecified.** No consumer
uses efficiency. So the honest repair is to make the prose say what the types
say, and to put efficiency in a separate type where it can be stated and fail.
No frozen Challenge, theorem or binding changes.

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

**Controls (on `Bool`; `false` is the only actual distinct-esse being).**

- *Non-efficient cause*: `true`, in act, causes `false`'s esse; nothing is an
  efficient cause. The q.3 a.4 dichotomy and no-self-sufficiency, no
  self-causation, the actuality of causes of being, `33ad148b` and `457698e4`
  all hold; both bridges and `1ff08418` fail. So the efficient reading does
  not follow from either source route without a bridge, and it strictly
  strengthens `33ad148b`. "Non-efficient" is a label for an unconstrained
  primitive: this is logical independence, not a model of formal causation.
- *Restricted bridge only*: `false` causes `true`'s esse non-efficiently;
  `true`'s esse is its essence, so `58e6ec63` holds and `0cc3a136` fails.
- *Nonvacuity*: every input of both derivations, both bridges and the
  conclusion hold.

## Which existing premises exclude the non-efficient model

None on the route. Checked: the inputs of `457698e4` (`d1f3ffcc`, `b62a64ab`,
`4ccb319f` and their De ente decomposition `75919560`, `600f91cb`, `8592601e`,
`a2800f45`) and of `af503cd7` all hold in the non-efficient model; the De
ente efficiency bridge `600f91cb` concerns the thing's own nature, not a
cause other than it. The closest existing premise is
`STMT-PERFECTION-CAUSING-IN-ANOTHER-IS-EFFICIENT` (`e0088de9`, every respect),
which would exclude the model if its `EfficientlyCausesIn` were this tenseless
relation; it is the secunda via's here-and-now relation, so using it here
would be an equivocation. With an OPEN tense bridge (a here-and-now
efficient cause of x's esse is a tenseless one), `e0088de9` at esse would
entail `0cc3a136`; that bridge is not stated here (next test 3). `0cc3a136` is the esse-specific, tenseless analogue,
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
| Efficient extrinsic source (Thomistic) | The other actual cause of a distinct esse is an agent from which x's being proceeds, as heat from fire. Justification: the q.3 a.4 context (fire example, God as first *efficient* cause) and the agent-or-identical principle (`0cc3a136`). | It must defend `0cc3a136` or the restricted bridge: that nothing other than x accounts for x's actuality except by acting. That is the open specify-versus-actualize question below, not yet a derivation. |
| Constituent formal principle counted as a being | `c ≠ x` is numerical distinctness, not exteriority. On the Thomist account form is a principle of being (the De ente note records the standard gloss, "forma dat esse materiae", as the analyst's, not the passage's), so if a subsisting form were counted as an actual being other than the composite, it would cause the composite's esse formally, not efficiently. Relevant because the bridge's antecedent uses only `c ≠ x`. | Not a rival to the q.3 a.4 text, which says "ab aliquo **exteriori**": it shows that the typed bridge is broader than the text. Repair (next test 1): restrict the bridge to non-constituent causes; that needs a constituency relation on the profile. |
| Non-agent exterior exemplar (Platonic participation) | A separate Form that x participates in accounts for x's being without acting (the Phaedo-style "by the Beautiful all beautiful things are beautiful"; attribution deferred, not re-read). It falsifies the *universal* bridge only if such a Form is an actual being that causes x's esse while no agent does, or alongside one. | If an agent also causes x's esse, only the per-cause bridge fails and the weak existential form survives. If no agent does, the account owes how a non-acting exemplar makes x actual rather than specifying what x is; that is #1621's adequacy question and #1629's specify-versus-actualize question. Unpaid, not refuted. |
| Structural or global explanation (#311/#750) | x's esse is accounted for by its place in an actual structure that, counted as a being, would satisfy `CausesIn` without acting. Justification: non-causal structural and grounding explanation in science and metaphysics. | If the structure acts, it is an efficient cause and satisfies the bridge. If it only characterizes x, it must show explanatory direction and sufficiency for the actual obtaining of this bearer (#311 EXP-LOCAL-TO-GLOBAL, #750). Unpaid, not refuted. |
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
being actual rather than specifying it. **For the root route nothing
changes in substance:** no root-route consumer needs efficiency, so the
efficient reading is a typed sibling for routes that do (identification with
the first *efficient* cause), not a new discharge.

**Would revise.** Upward: a derivation of the bridge for non-constituent
causes from a specify-versus-actualize principle, or a verified tense bridge
connecting `e0088de9`'s here-and-now efficient causing to this relation.
Downward: a worked non-agent account of actualizing (not specifying) a
distinct esse.

**Boundaries.** No conservation, present sustaining, uniqueness, necessity
or God identification follows; `33ad148b` closing (frontier "stated ->
closed") means proved from open premises through the efficient sibling, not
established.

## Computed premise delta

`truth frontier-diff --base 2524680bd`: open premises reaching the root
480 -> 480 (341 -> 342 bare, 49 -> 48 stated); verified support alternatives
473 -> 477 (both routes to `1ff08418`, `1ff08418` → `33ad148b`, `0cc3a136` →
`58e6ec63`); bare premise added `0cc3a136`; `33ad148b` moved stated ->
closed (proved from open premises). Route costs unchanged.

## Next tests

1. **Non-constituent bridge.** Add a constituency relation to the profile
   (reuse `ComponentOf` vocabulary if its meaning matches), restrict
   `58e6ec63` to causes that are not constituents of x, and test whether the
   constituent-form counterexample is then excluded while the non-agent
   exemplar model survives.
2. **Specify versus actualize.** Split the cause-of-being relation into
   "specifies the actuality x has" and "accounts for x's being actual", and
   test whether `0cc3a136` (restricted to accounting causes) follows from
   "an accounting principle is an agent or is the act it accounts for".
3. **Secunda via connection.** State the tense bridge between the secunda
   via's here-and-now `EfficientlyCausesIn` at esse and `EfficientlyCausesEsse`
   and test whether `1ff08418` then feeds the secunda via's order of efficient
   causes, the one place where efficiency of esse-causes would be load-bearing.
