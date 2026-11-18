# De ente: does a really distinct esse need a source other than the thing? (#1629)

**Status:** conditional formal results plus a provisional judgment, revised
after an independent semantic challenge. Source: Thomas Aquinas, *De ente et
essentia*, pinned Corpus Thomisticum witness `AQUINAS-DE-ENTE-C3-4` (passage
`7070ccdd`), anchor [69874]. That witness uses the Baur/Koch numbering, where
the passage is **c.3**; it is **c.4** in the Leonine numbering the issue cites.
The materialized text of capp. 3–4 was read in full before the claims below
were made.

Formal home: `TruthCore/Latin/Aquinas/DeEnte/ExtrinsicSource.lean`, results in
`TruthCore/Results/Aquinas/DeEnte/ExtrinsicSource/`, spec
`specs/de-ente-extrinsic-source-1629.toml`, attempt `fbc68d10`.

## The passage and its steps

> Omne autem quod convenit alicui vel est causatum ex principiis naturae suae,
> sicut risibile in homine, vel advenit ab aliquo principio extrinseco, sicut
> lumen in aere ex influentia solis. Non autem potest esse quod ipsum esse sit
> causatum ab ipsa forma vel quiditate rei (dico sicut a causa efficiente) quia
> sic aliqua res esset sui ipsius causa et aliqua res seipsam in esse
> produceret, quod est impossibile. Ergo oportet quod omnis talis res, cuius
> esse est aliud quam natura sua habeat esse ab alio.

1. A disjunction over everything that belongs to a thing: from the principles
   of its nature, or from an extrinsic principle (claim `676bdaeb`, statement
   `75919560`).
2. A conditional: if esse were caused by the thing's quiddity *as by an
   efficient cause*, the thing would be its own cause and produce itself in
   being (claim `ce55e563`, statement `a2800f45`).
3. That this is impossible (claim `85857e47` on the existing
   `STMT-NOTHING-CAUSES-ITS-OWN-BEING`, `b62a64ab`). The impossibility is said
   under the efficient supposition; the statement's generic scope (no cause
   of its own being in any mode) rests on "sui ipsius causa", as the claim
   records.

The conclusion, "habeat esse ab alio", is registered as its own
mode-unspecified statement `457698e4` (`DistinctEsseHasOtherActualCause`): for
every actual x with `esseOf x ≠ essenceOf x`, some c with `c ≠ x`, in act as
to being, causes x's esse (`CausesIn`, DEF-CAUSE-OF-PERFECTION, mode of
causation not fixed). `c ≠ x` does not exclude a constituent counted as a
being. The q.3 a.4 profile is reused, so the witness, the `CausesIn` relation
and the represented essence/esse are the same as in q.3 a.4.

**Why not `33ad148b`.** The existing q.3 a.4 statement
`STMT-DISTINCT-ESSE-REQUIRES-EXTERNAL-CAUSE` (`33ad148b`) has the *same* Lean
type up to unfolding (`HasExternalEsseCause` is `∃ y, y ≠ x ∧ InAct y esse ∧
CausesIn y x esse`), but its paraphrase and its q.3 a.4 module read `CausesIn`
as an efficient cause, and downstream `4876dc46` advertises an external
efficient cause. Its own route (transcription `af503cd7`) gets efficiency only
from that interpretation of the q.3 a.4 premises, not from any type condition.
The first draft of this PR concluded `33ad148b` through a definitional bridge;
Codex review (#1631) rightly objected that this certified efficiency by
definition. That bridge and argument were withdrawn: nothing here supplies
efficiency, and the vocabulary has no efficiency predicate on arbitrary causes of being with
which an OPEN generic-to-efficient bridge could be stated so that it could
fail. (Resolved in #1633: `33ad148b`'s prose is now mode-unspecified like its
type, and the efficient reading is typed behind an OPEN bridge; see
[esse-cause-efficiency-1633.md](esse-cause-efficiency-1633.md).)

## The gap: "not self-produced" is not "produced by another"

**Exact extra premise.** Given no self-causation, "caused by another" needs
only `DistinctEsseHasSomeCause` (`d1f3ffcc`): every actual distinct-esse x has
*some* cause of being. This is the vocabulary-free answer to the issue's
question; it is OPEN. Brute esse rejects it, and so does a non-causal intrinsic
or structural account unless its explainer counts as a being that causes x's
esse.

**De ente's decomposition of it.** Step 2 rejects only *efficient* causation
by the quiddity ("dico sicut a causa efficiente"); step 1's nature disjunct is
not restricted to efficient causation. Two senses are therefore kept apart
(`DISAMB` `87ac7ae0`, term `NATURE_SOURCE`):

| Sense | Lean | Meaning |
|---|---|---|
| `NATURE_SOURCE_1` | `NatureSource.fromNature` | caused from the principles of x's nature, mode unspecified (literal disjunct) |
| `NATURE_SOURCE_2` | `NatureSource.quiddityEfficientlyCauses` | x's own quiddity is an efficient cause (the sense of the rejection) |

In De ente's vocabulary the extra premise comes from
`DistinctEsseNatureOrOtherCause` (`8592601e`: every actual distinct esse is
efficiently caused by its quiddity or caused by another, esse only) plus the
self-causation reading. The literal disjunction gives `8592601e` only through
the OPEN sense bridge `NatureSourcedDistinctEsseIsEfficient` (`600f91cb`). Why
the bridge is not definitional: the qualifier in step 2 suggests that a
non-efficient causation of esse is in view, and the standard Thomist gloss
counts a form as a formal, non-efficient principle of being. That gloss is the
analyst's: the passage's own "forma dat esse materiae" concerns form and
matter, not a nature and its own subject's esse.

## Formal results (all zero-axiom; Comparator and NanoDa checked locally)

| Result | Theorem | Content |
|---|---|---|
| `8477d8c7` | `distinctEsseOtherCauseFromCaused` | some cause + no self-causation + causes of being are in act → `457698e4` (another actual cause of being, mode unspecified) |
| `44eef980` | `distinctEsseCausedFromDeEnte` | weak exhaustiveness + self-causation reading → some cause |
| `42a89226` | `distinctEsseExhaustionFromDeEnte` | literal disjunction + efficiency bridge → weak exhaustiveness |
| `08275113` | `extrinsicSourceControls` | six finite interpretations on `Bool` |

The controls are interpretations in which `false` actually exists with esse
distinct from its essence:

- **Brute esse**: nothing causes anything, nothing is from its nature. The
  literal disjunction, the weak exhaustiveness and some-cause fail; the other
  inputs hold; no other cause.
- **Formal nature**: `false`'s esse is from its nature (sense 1) without its
  quiddity efficiently causing it; nothing causes anything. The literal
  disjunction, the self-causation reading, no self-causation and the actuality
  of causes of being all hold, and there is no other cause. "Formal" is a
  label: `fromNature` is an unconstrained primitive, so this is a structural
  surrogate. It shows that the two nature senses are independent, so the
  source's three steps read literally do not yield the conclusion without the
  efficiency bridge; it does not model formal causation.
- **Self-cause**, **unrealized quiddity**, **nonactual cause**: drop
  no-self-causation, the self-causation reading (with some-cause downstream)
  and the actuality of causes of being respectively; the conclusion fails.
- **Nonvacuity**: every input holds and an actual `true` causes `false`'s esse.

These show logical underdetermination under the encoded predicates only. They
are not evidence that brute or formally sourced esse is possible or plausible.

## Existing routes and root connection

`33ad148b` (efficient external cause) keeps only its q.3 a.4 transcription
`af503cd7` from the stated dichotomy `be639b3f` and the stated
no-sufficient-self-cause premise `61bd42e5`. The De ente route is not a support
option for it (see "Why not `33ad148b`"). Both share one underlying commitment,
causal coverage of distinct esse. The participation route (`732302a1`) reaches
a distinct esse-cause from `Participates x`, a different antecedent; nothing
here relates participation to real essence–esse distinction.

**No root connection yet.** Computed `truth frontier-diff --base origin/main`:
"open premises reaching the root: 477 ... -> 477"; "distinct verified support
alternatives: 469 -> 469"; "no change". The new statements do not reach the
root. Connection plan and blocker: `33ad148b` reaches the root through
`4876dc46` on the designated efficient-regress route `3b0f4fa5`; reaching it
from `457698e4` needs (a) a typed efficiency predicate on arbitrary causes of being in
the q.3 a.4 vocabulary and (b) an OPEN bridge from a distinct actual cause of a
distinct esse to an efficient one, defended against the non-efficient
(formal/structural) rivals below. Alternatively `457698e4` composes directly
with `cb1cdea9` (which uses the same mode-unspecified `CausesIn`) for #1496;
see the plan at the end.

## Rivals on the same actual being and explanandum

Each row names its target, mechanism and the independent justification
offered, per the Substantive Objection Standard.

| Account | Target | Mechanism and justification | Price under its own commitments |
|---|---|---|---|
| Thomistic received esse | — (the route) | A distinct esse has some cause (`d1f3ffcc`); in De ente's terms, a nature that is not its esse supplies it, if at all, only as an efficient agent (bridge `600f91cb`), and an agent quiddity would make the thing its own cause (steps 2–3). So the cause is another being, and in act as to being (`4ccb319f`); its mode (efficient or not) is not derived. | Needs causal coverage of distinct esse and, for the De ente decomposition, the efficiency bridge; the conclusion is tenseless, so it says nothing about present sustaining (#1604/#1616). |
| Brute esse (#312/#746) | `d1f3ffcc` / the disjunction | x's esse has no cause and no nature source. Justification offered in the corpus: explanation must stop somewhere, and unrestricted PSR has recorded costs (#312/#746). | Consistent (brute control). By the brute hypothesis, it stops at an actual composite whose nature is not its esse and which has no account of its actuality, and it must give a stopping criterion that selects this composite rather than a source. That is the open #746 stopping-criterion question; no view-internal contradiction is shown here. |
| Non-efficient intrinsic nature account | efficiency bridge `600f91cb` (and `d1f3ffcc`) | A nature may be a formal, non-efficient principle of its own subject's esse, so a distinct esse may be from the nature without efficient self-causation. Justification: the standard Thomist gloss of form as formal principle of being; step 2's qualifier motivates it. | It must say whether the nature *accounts for* x's actuality or only *specifies* an actuality it presupposes. If it only specifies, the actuality is still unaccounted for (brute row) or from another. If it accounts for it without being an agent, a principle that is not x's esse supplies x's actuality, which is #1621's intrinsic-adequacy question applied to distinct esse. Not refuted here. Also note: a form encoded as a distinct being that causes x's esse would satisfy the conclusion as typed. |
| Constitutive or global structural explanation (#311/#750) | `d1f3ffcc` (the cause-of-being reading of "from another") | x exists because of its place in an actual structure that does not cause its esse. Justification: non-causal structural and grounding explanation in science and metaphysics. | If the structure is an actual being distinct from x that causes x's esse, it satisfies the conclusion (a candidate source, not a rival to the bridge). If it only characterizes x, it must show explanatory direction and joint sufficiency for the actual obtaining of this bearer (#311 EXP-LOCAL-TO-GLOBAL, #750). Unpaid, not refuted. |
| Modal necessity | none separately | A necessary existent with really distinct esse faces the same question; this passage says separate substances receive esse (it does not assert their necessity). Necessity from the nature falls under the intrinsic row; brute necessity under the brute row. No separate mechanism identified. | — |
| Merely conceptual distinction | the antecedent `DistinctEsseAt` | If essence and esse differ only in concept, `esseOf x = essenceOf x` and the bridge is silent. The De ente argument for a real distinction (understanding a nature without knowing whether it exists) is not formalized here; a conceptual difference does not by itself prove a real one. | Rejects the antecedent, not the inference. |

**Existential inertia.** It targets present sustaining, not this route: the
conclusion's `CausesIn c x esse` is tenseless and holds of an originating
source. Inertia bears on "a source once" only if x also has no origin; that
combination is the brute-esse row. No separate objection identified.

## Overall provisional judgment (2026-11-14, this revision)

**Claim.** For an actual x whose esse is really distinct from its essence,
x's esse is caused by another being in act (mode of causing unspecified; that the cause is efficient is a further, unregistered step).

**Judgment.** The inference is valid exactly with one further premise, causal
coverage of distinct esse (`d1f3ffcc`); the De ente text supplies that
premise only when its nature disjunct is read efficiently (formal-nature
control). The claim is therefore provisionally supported to the degree that
causal coverage of distinct esse is: it is not established. Against brute
esse, the received-esse account has an explanatory-scope advantage (it
accounts for the actuality where brute esse accounts for none). That is a
comparison of explanatory performance, not a substantive test that brute esse
failed; both are consistent under the encoded predicates, and the stopping
criterion burden is shared with #746. No further comparative advantage is
shown here. The **strongest standing rival to the De ente inference** is the
non-efficient intrinsic nature account; its price is to show that a principle
that is not x's esse can account for x's actuality without being an agent,
#1621's adequacy question restricted to distinct esse. The **strongest rival
overall** is brute esse, at the price stated in its row.

**Would revise.** Downward: a worked account in which a non-efficient
principle accounts for (not merely specifies) the actuality of a distinct
esse, or a principled stopping criterion selecting brute composites. Upward:
a checked derivation of the efficiency bridge or of causal coverage from a
specify-versus-actualize principle (below).

**Boundaries.** No premise is established; no conservation, uniqueness,
concreteness at a world, efficiency of the cause, or God identification
follows; the real distinction is an input, not proved.

## Next discriminating test and connection plan

1. **Efficiency bridge from a specify-versus-actualize principle.** Split
   sense 1 into "specifies the actuality x has" and "accounts for x's being
   actual", and test whether `600f91cb` follows from: an accounting principle
   either is an agent or is identical with the act it accounts for. Under real
   distinction, identity is excluded, leaving agency, which steps 2–3 exclude
   for the thing itself. A finite model of a non-agent, non-identical
   accounting principle would show the extra principle is needed.
2. **#319 connection.** The root-essence identity compositions
   (`RootEssenceIdentity.identityOfActualRoot` and its consumers) take the
   q.3 a.4 pair `be639b3f`/`61bd42e5` directly. A sibling consuming `33ad148b` (or, after an efficiency bridge, `457698e4`)
   would let this route feed #319's necessary-root chain; blocker: those
   arguments are frozen, so it needs new sibling arguments, not edits.
3. **#1496 connection.** Composing `457698e4` with `cb1cdea9` (same mode-unspecified `CausesIn`) gives an actual
   concrete ground for actual distinct-esse concreta at w, given the existing
   presence/actuality bridge. Reaching `c71c068c` (contingent concreta) still
   needs a contingency-to-real-distinction bridge, which is not available.

## Semantic challenge

An independent reviewer challenged the first draft (staged diff, this
branch). Accepted and repaired: the conclusion's "efficient" and "extrinsic"
are prose, not type conditions (stated above and in the records); "forma dat
esse materiae" was overread as the passage granting a formal source of a
nature's own esse (now the analyst's gloss); the generic scope of
no-self-causation is noted on its claim; the weakest premise is the
vocabulary-free `d1f3ffcc`, now certified as the step's only extra premise;
the formal-nature control is labelled a structural surrogate; nonvacuity was
removed as a comparative reason, and "gains relative standing" was withdrawn
in favour of an explanatory-scope comparison. No disagreement was left
unresolved.

**Codex review on #1631 (P1, accepted).** The first published head concluded
`33ad148b`, whose paraphrase requires an efficient cause, from premises that
give only a mode-unspecified cause, through a definitional bridge into
`HasExternalEsseCause`. That would have let the corpus count the efficient
statement as proved and feed `4876dc46`. Repair: the conclusion is now its own
statement `457698e4`; the definitional bridge (`bfae6584`) and the arguments
into `33ad148b` were withdrawn; the frontier diff is now "no change". The
existing q.3 a.4 route binds `33ad148b` to the same mode-unspecified Lean type;
its efficiency also rests on interpretation, not on a type condition. That is
recorded here as an existing gap, not repaired in this PR.

## Follow-up (#1628)

The step concluded here is consumed by the three-stage reconstruction in
[de-ente-esse-source-1628.md](de-ente-esse-source-1628.md): at most one being
whose esse is its essence, every distinct esse descending from one, and a
root-purity sibling that makes `457698e4` reach the root without any
efficiency claim.

## Intrinsic actuality and the alternative's own commitments (2026-11-17)

**Target.** Causal coverage `d1f3ffcc-04f2-4683-b385-2bfb2baf3f10` and the
nature-source interpretation `600f91cb-ac5e-4283-b078-26b941fe2211`, as used by
`8477d8c7` / `42a89226` to reach the mode-unspecified
other-cause statement `457698e4`. The question is whether an intrinsic principle
is an adequate alternative account of the **same actual individual's esse**.
The owner's reply is strongest when it concerns that actuality, rather than
requiring an external explanation of every difference between essential kinds.

**Reuse and source boundary.** Re-read the exact `ExtrinsicSource` and
`EsseSource` types, [intrinsic-existence-reason-1595.md](intrinsic-existence-reason-1595.md),
[necessary-being-five-senses.md](necessary-being-five-senses.md), and the full
n.6 continuation of [scg-i22-contingent-conjunction.md](scg-i22-contingent-conjunction.md#the-full-n6-belonging-source-location-and-a-co-constitutive-rival-1623-2026-11-14).
Their essential-existence, explanation, underivedness and essence–esse identity
distinctions remain in force. Re-read the public Latin *De ente* [69872],
[69874] and *SCG* I.22 [23715–23718] as orientation alongside the retained
source records. This continuation creates no attribution or source claim.
Canonical context for `8477d8c7`, related/dossier/brief for `d1f3ffcc`,
dossier for `600f91cb`, and a combined novelty search were inspected at baseline
`c1037682`. Retrieval reconfirmed the existing conditional work; it does not
certify this judgment. No issue snapshot was supplied, so absent issue hits
are not treated as evidence of novelty.

### The positive reply, without an efficient-cause shortcut

1. **An essential specification does not actualize its own instance merely by
   being intrinsic.** A nature can explain what an instance is and what follows
   if it exists. The same account does not yet explain why this individual is
   actual. Spinoza's individual-versus-nature test, retained in #1595, already
   distinguishes these questions. This is a substantive explanatory shortfall,
   not just a failed implication between unconstrained predicates.
2. **Actual exercise cannot be obtained by repeating the explanandum.** If the
   principle explains existence only when it is already realized in this
   individual, the account still owes that realization, unless it positively
   explains why this realization needs no further source. Existing
   `TargetCopyExpansion` supplies the logical warning: copying the target's truth
   into a reason and then assigning sufficiency supplies no explanatory direction.
   It does not prove that every intrinsic explanation is such a copy.
3. **Intrinsic location does not defeat the actual-other-cause conclusion.** If
   an intrinsic constituent is itself a distinct actual being and causes x's esse
   in the selected `CausesIn` sense, it already satisfies `457698e4`. The statement
   requires numerical otherness, not non-constituency. A mere principle in the
   `Principle` carrier is not automatically such a being, however; nor is a formal
   explanation automatically the prohibited efficient self-production.
4. **An actual self-subsistent answer may concede the sought intermediate.** If
   the proposed whole is already actual and its esse is genuinely unreceived
   from any distinct source in the relevant order, it grants an underived
   actual being in that order. This is useful convergence with the foundation
   route even if the rival calls the bearer natural. If the account instead
   treats the whole's actuality as a primitive fact, its stopping point is brute
   actuality; describing its internal constitution has not removed that choice.

The first two steps favor the received-esse account over a merely specifying
intrinsic principle. The third prevents an artificial dispute over where the
source is located. The fourth tests what an alternative actually concedes. None
assumes that all possible explanations are efficient causes, or proves that
every account must fall into these four descriptions.

There is a real limit to the owner's contrastive question. Different natures
can account for why one kind has a feature another lacks; demanding a further
external cause solely because the natures differ would need an additional
principle. Also, an intrinsic property need not be essential. The relevant
proposal here specifically selects an **own-nature principle**. Its hard test
is existential adequacy for its actual bearer, not the mere fact that another
nature lacks it.

### When the alternative grants necessary existence

The exact reusable inference is
`BruteFoundationExplanations.necessaryReasonAndNecessitation`: a reason present
throughout the accessible worlds, together with its sufficient entailment of
**this same individual's** existence there, yields `NecessaryAt` for that
individual. The theorem is existing library code; this continuation neither
registers a new result nor freshly certifies it. For an **actually existing**
necessary bearer, actuality must also be retained: `NecessaryAt` alone uses an
arbitrary accessibility frame and does not supply actual presence without a
suitable frame condition.

| What the intrinsic account supplies | What is conceded |
| --- | --- |
| A definition or a predicate called necessary existence | No instance from the name alone. |
| Existence placed in the bearer's essence (`OwnEssentialExistence`) | The source-indexed essence claim; its existential adequacy and modal realization remain distinct. |
| An actual bearer plus an independently characterized, necessary reason necessarily sufficient for its existence | That same actual necessary bearer. Calling this a non-theistic alternative does not remove the concession. |
| An actual bearer whose esse needs no distinct source in the selected order | Underived actuality in that order; modal necessity does not follow just from underivedness. |
| Both preceding substantive commitments | An actual necessary, underived bearer; uniqueness, universality of sourcehood and the God-description still require their own arguments. |

If reason-presence is defined as the individual's existence, the modal inference
reduces to assuming its conclusion. If the account starts from a concept without
an actual witness, it needs a warranted possibility-to-actuality argument and
the relevant modal assumptions. Thus the owner's ontological reply is correct
**conditionally**: a genuinely existentially sufficient essential-necessity
account can supply a necessary-being route. Adding a predicate cannot do so.
This also avoids treating the a posteriori concession of an already actual
necessary being as though it were an a priori existence proof.

### The remaining concrete challenge and current judgment

The retained immanent-constitution challenge has more substance than a tag:
Aristotle H.6 and *De ente* c.1 explain a composite through potential matter
and actual form without a further constituent tying two already actual objects
together. It defeats an unrestricted “distinct principles require a third
uniter” shortcut. It does **not** yet explain a first bearer's esse outside
its quiddity: the paradigm's matter/form are within the composite essence,
their roles are asymmetric, and productive causation is allowed. As #1623
records, applying that mechanism to a pure-act first bearer also encounters
the separate potency objection of *SCG* I.22 n.7. That objection requires real
act/receptive-potency interpretation, not inequality of two labels.

**Overall provisional judgment:** the generic “intrinsic principle” reply is
not an established alternative complete explanation. Its specifying version
misses the target, its actual-other-source version satisfies the selected
conclusion, and its adequate necessary/underived version may concede the central
intermediate. The immanent-constitution mechanism remains a targeted challenge
to causal coverage's application; its extension to an unreceived first esse is
not supplied by the inspected evidence. This improves the positive case and
narrows the live comparison without declaring coverage or efficiency proved.
Brute actuality remains a substantive stopping-policy dispute. There is no
independent-proof quota: coverage may be accepted as a primitive for its
explanatory merits, with these commitments visible.

**Current root connection.** Historical “no root connection” and untyped-
efficiency blockers above are superseded. #1628's `e6337182` consumes
`457698e4` on the root-purity route. #1633 aligns `33ad148b` with the same
mode-unspecified proposition and separately types efficiency; its bridge
`58e6ec63` remains substantive. Neither change establishes the real application
of coverage `d1f3ffcc` or its nature-source bridge `600f91cb`; their existing
derivational statuses are unchanged. The source-first path through common
source `c35b1a5c`, fixed-esse
causality `da09703b` and the twelve-input GOD_4 consumer `c98328f1` (or main's
witness-retaining `d9ee967a`, which replaces population/whole-roster with the
De ente source `ce7edf53`) still needs
its actual-grounding, priority, grading, causal transfer, component and nominal
interfaces. A necessary/underived concession alone cannot replace that bundle.

**Next test / stop.** Reuse #1623's same-bearer substantial-belonging test:
does the proposed intrinsic principle account for actual esse without
presupposing it, and, if so, is the source its own nonreceived actuality or a
genuinely distinct principle? Preserve the formal/efficient and
principle/bearer distinctions. Reopen for a positively specified first-esse
co-constitution that answers this test, or a general adequacy argument excluding
it; another arbitrary `fromNature` assignment will not discriminate. No new
Lean vocabulary is needed for the present explanatory judgment. Statement types,
proofs, definitions, senses and premise statuses are unchanged; existing formal
evidence is reused, not certification of this prose.

**Integration review (2026-11-17):** fresh independent semantic challenge of
this dated continuation and the coordinator conclusions found no substantive
defects; no repair round was required. This supersedes the pending-review
wording of this dated section. See the [integration record](unique-feedback-explanation-311.md#reviewed-owner-reply-integration-2026-11-17)
for verification, source scope and unchanged formal status.
