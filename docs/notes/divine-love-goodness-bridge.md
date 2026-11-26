# Divine love of all existing things: bounded q.20 bridge

[Original PR #1458](https://github.com/moritzbrantner/formal-logos/pull/1458)

## Target and source reading

This is an analyst reconstruction of Thomas Aquinas, *Summa theologiae* I q.20
a.2, connected to `STMT-GOD-IS-SUPREMELY-GOOD`
(`e0dae79f-c042-5a08-a148-725d0468df91`) and `STMT-GOD-HAS-WILL`
(`66aecdd7-ea4e-55c6-9377-10db08893854`). Both are existing
root-reaching case nodes, but the new conclusion is **not** itself a premise of
the current `STMT-CATHOLICISM-TRUE` route. This is a **candidate supporting
bridge**, not a root-premise discharge: the named next consumers are
`STMT-HIDDENNESS-GOD-LOVES` (a stronger perfectly-loving, relationship-capable
God) and `STMT-CLASSICAL-ATTRIBUTES-INCLUDE-PERFECT-INTELLECT-AND-GOOD-WILL`
(an actual good will without deceptive assertion). Universal willing of some
good does not entail either perfect interpersonal accessibility or veracity;
those are additional disputed normative/cognitive bridges. This checkpoint
is therefore lower-priority exploratory support until such a bridge is built.

Sources originally consulted for orientation and semantic review:

- [ST I q.20 a.2 co. and ad 3–4](https://www.newadvent.org/summa/1020.htm):
  every existing thing has existence and perfections as goods; God's will
  causes their existence/good (by q.19 a.4); so God wills some good to each
  thing; to love something is to will good to it. Love of irrational creatures
  is not friendship; sinners are loved under their existing nature and opposed
  under the aspect of sin. Ad 2 explicitly separates the eternal divine love
  from the temporal existence of creatures.
- [ST I q.20 a.1 co., ad 1, ad 3](https://www.newadvent.org/summa/1020.htm):
  love as first act of will, unlike a bodily passion; willing good for someone
  is distinct from merely willing a good.
- [ST I q.19 a.1 co., ad 2](https://www.newadvent.org/summa/1019.htm):
  will follows intellect and includes possessing, loving and delighting in
  good, not only seeking an absent object. `GodHasWill` is nevertheless an
  opaque one-place predicate in the existing Lean case.
- [ST I q.19 a.4 co., ad 3–4](https://www.newadvent.org/summa/1019.htm):
  divine will is the cause of things; divine goodness is a reason for willing
  other things, and natural or essential causation is not freely interchangeable
  with an act of will.

The pinned Latin readings of I q.19 aa.3–4 and q.20 a.2 now support the
self-willing and recipient-willing premises. The self-case still needs to
identify divine goodness with the selected `GOOD_4` respect, and the
recipient case still needs causation through will. The source records and
scope of the third reply are linked in the
[willing](../../corpus/attempts/16fbb043-05cc-43cc-a944-9c9a33c4cf7d.json)
and [love](../../corpus/attempts/e551ce3e-a8db-40c4-bbca-e9fbb84be9d7.json)
reading records.

The argument **does not** say that God loves irrational creatures with
friendship, loves all recipients in the same degree, approves of moral
wrongdoing, needs creatures, experiences affective changes, or necessarily
wills any particular finite creature. Q.19 a.3 distinguishes absolute and
suppositional necessity. Neither `Loves` nor `WillsGoodFor` has a time index:
the formalization does not prove the eternality/temporal-creation distinction
in q.20 a.2 ad 2. The conclusion is quantified over the actual things in
`InAct x esse`; it is not over all merely possible entities. It is vacuous if
`IsGod` is empty; the finite controls supply an actual God and an actual
distinct other for diagnostic purposes.

## Formal route and explicit OPEN inputs

In `TruthCore.Case.Catholicism.DivineLoveBridge`:

1. `GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse` is precisely
   `∀ g, IsGod g → GoodIn g esse ∧ ∀ x r, x ≠ g → InAct x r → CausesIn g x r`.
   Its goodness is metaphysical participation/causal-perfection goodness,
   **not** a predicate of moral benevolence. In particular, it does not
   quantify over intentional acts and excludes self-effects.
2. `GodHasWill IsGod HasWill` is just `∀ g, IsGod g → HasWill g`. It does not
   say what God wills, what an act of will causes, or that any exercise occurs.
3. `GoodnessIsActualityReading GoodIn InAct` is the already recorded
   `STMT-GOODNESS-IS-ACTUALITY`: `∀ x r, GoodIn x r ↔ InAct x r`.
4. **OPEN `CausalExistenceWilling`:** For a distinct actual `x`, if God has
   will and effectively causes `x` in `esse`, then God wills the existence-good
   *for that x*. This intentional step is **not** in `CausesIn` and is not
   obtained merely from causal maximality or supreme-goodness.
5. **OPEN `DivineOwnGoodWilling`:** A God who has will and is good in `esse`
   wills that good for Himself. Needed because the existing causal goodness
   predicate explicitly excludes self-causation. It expresses a q.19 a.1 /
   q.20 a.1 theme, not an inference from the opaque `HasWill` flag alone.
6. **OPEN `WillingGoodEntailsLove`:** If God wills an actual good *to its
   recipient*, then God loves that recipient in the non-passional sense of
   willing some good to it in q.20 a.2. Ad 3 restricts *friendship* (amicitia)
   to rational creatures, who can return love; irrational creatures are loved
   "as it were" with love of desire, as ordered to rational creatures and to
   God. Ad 3 does not restrict the thin willing-good sense itself. This one-way sufficient rule adds neither
   universal friendship nor affection, equal degree or unqualified desire.

`divineWillsGoodForAllExisting` proves that for each God and each actual `x`,
there is a good of `x` which God wills for `x`. The witness is `esse`: for
`x ≠ g` the universal causal-perfection predicate supplies causation of
existence and the open causal-to-intentional bridge supplies willing; for
`x = g` the independent self-good bridge applies. The theorem then uses
coextension of actual being and good. `godLovesAllExisting` adds the final
love-meaning bridge to obtain
`∀ g, IsGod g → ∀ x, InAct x esse → Loves g x`.

These are Lean-checked **conditional** conclusions (not registered or
Comparator-verified corpus results), not a derivation
from supreme goodness plus bare will alone and not independent confirmation
of the Catholicism root. The `GoodIn`/`InAct` dictionaries and the causal
`CausesIn` relation are the ones supplied to the existing case statements;
no new identification with moral goodness, divine intention, or mental
activity is smuggled into their definitions. Nor does the theorem prove the
stronger q.19 a.4 thesis that willing itself efficiently *causes* the
creature's good; `CausesIn` and `WillsGoodFor` are separately typed and merely
connected by an explicit bridge. `WillsGoodFor` is a primitive
recipient-directed volition, not a relation defined in terms of `Loves`;
`Loves` is another primitive, not an alias for `WillsGoodFor`.

## q.19 a.4's positive support options, and rival

Q.19 a.4 offers three distinguishable reasons to take the causal bridge
seriously, **not** generic proof rules for `CausesIn`:

1. **Priority of intellect/volition over natural teleology.** A natural
   agent's end and means are directed by an antecedent intellectual agent;
   God as first agent acts intellectually and voluntarily. This needs a
   defended hierarchy of intentional determination and first agency; a bare
   causing relation has neither.
2. **Determinate effects vs. necessary uniform natural emission.** A natural
   agent has a fixed effect unless impeded, whereas the indeterminate fullness
   of the first divine source produces determinate finite effects through
   intellectual-volitional specification. This requires the relevant
   metaphysical indeterminacy, an account of the effects' diversity, and
   an objection-resistant distinction between nature and choice.
3. **Intellectual preexistence of effects.** Effects are conceived in the
   intellectual cause and are actualized through the cause's will. This
   gives a particularly direct intentional explanation but needs
   preexistence-as-conceived and willing-as-actualizing, neither of which
   follows from the extant `CausesIn` relation.

The strongest rival *to this specific causal-to-willing step* grants that the
first source has will and wills its own good, but says its effects flow from
its nature without an additional recipient-directed act of willing. This
natural-diffusion account preserves the existing `HasWill` and `CausesIn`
predicates and is directly instantiated by the `omitCausalWill` control. Its
philosophical price relative to Aquinas is a denial that q.19 a.4's account
of divine essence as intellect/will, its reasons for determination of effects,
or its goodness-as-reason-for-willing explanation suffices for volition toward
each effect. This remains open, not a demonstrated incoherence.

The broader, historically motivated rival is a **first intellect acting by
necessary emanation without will**:
`corpus/statements/2537adb1-fca8-4a76-93a7-18a688cb4507.json` and
`TruthCore/Causality/SpineRivalsAttributes.lean`. It disputes even the earlier
move from cognition/first causation to divine will itself and must reject at
least one of q.19 a.4's three philosophical routes or their applicability.
Neither rival violates the existing generic `CausesIn` semantics merely by
disagreeing with its intentional interpretation.

For `CausalExistenceWilling`, a mundane positive illustration is a builder
causing a shelter to exist because she chooses that shelter for its
occupants; a contrast is an unintended byproduct of a machine with an
operator who also happens to have will. These are conceptual examples of
distinct causation and intending, not evidence that divine creation is
exactly like either. Efficient causation, mere enabling, natural emanation,
formal/exemplar preexistence and choosing an outcome are different roles.
No transitivity, well-foundedness, asymmetry, or causal uniqueness is assumed
of `WillsGoodFor`; nor is any such property supplied for generic `CausesIn`
by this module. **OPEN applicability** is precisely the step from those
ordinary volitional examples or Thomistic metaphysical arguments to every
existing creature's intentional dependence on the first cause.

## Nonvacuity, omissions, and revision conditions

`LoveControls` uses `Being = Bool` (false = God, true = distinct creature),
`Respect = Unit`, `esse = ()`, both beings in act and good, and exactly the
God-to-creature `CausesIn` assignment. `GodIsSupremelyGood`, `GodHasWill` and
the existing goodness/actuality coextension hold in **every** profile.

| Profile | OPEN bridge omitted | Actual failure |
| --- | --- | --- |
| `complete` | none | Both God and creature are loved |
| `omitCausalWill` | causal existence → willing good for creature | Creature is unloved; own-good willing and love entailment survive |
| `omitOwnWill` | God's self-good → self-directed willing | God Himself is unloved; creature is loved |
| `omitLoveMeaning` | willing good for recipient → loving | Both are willed good but neither is loved |

These are proposed populated finite **structural surrogates**, not metaphysical
possibility proofs. The q.19 a.4 intellectual and teleological positive
commitments are not encoded in the surrogate. Restoring those richer
commitments could eliminate the omissions. The comparison establishes the
specific insufficiency of the existing stage-2 predicate types (the Lean
control `loveControls` is kernel-checked by `decide` after unfolding), not a
global non-entailment under all Thomist interpretations.

Axiom footprint (`#print axioms`, this module imports no Mathlib):
`divineWillsGoodForAllExisting` and `godLovesAllExisting` use `propext`,
`Classical.choice` and `Quot.sound`, because the proof splits classically on
whether the loved `x` is God Himself; `loveControls` uses `propext`. None is a
registered corpus result. Registering the theorems would require either an
explicit decidable-identity input on `Being` or a bridge reformulated to avoid
the self/other case split, under the zero-axiom policy for non-Mathlib results
(`docs/axiom-policy.md`).

The current provisional assessment is therefore that Aquinas supplies a
coherent conditional argument *under an intentional-creative causality
reading*, but the existing corpus's generic causality/goodness and opaque
will premises do not yet warrant it. A useful next test would formally
instantiate one of q.19 a.4's three positive subroutes with independent
claims about an intellect's practical determination of effects, then check
it against the necessary-emanation rival and the surviving `HasWill`-without-
recipient-directed-volition model. A new source claim should wait for a
pinned witness and exact attribution review; this note is a navigation and
interpretation record only.


## Intentional-creation reassessment for #1459 (proposed, 2026-11-12)

This is a complete proposed bounded assessment for the coordinator's independent
semantic challenge, not an accepted challenge review or a new formal result.
Baseline: `8ff62893c42e3dfc6fc72559318bd099f34c71a8`. PR #1458 is merged
(merge `9699a826229aa8b77a1abe4e834278789d5af3d3`); its declarations and controls
are present unchanged. The #1571 warning still applies: no statement binds
`CausalExistenceWilling`, and no separate creative-goodness note is present.
Reuse this note and the existing module, not hypothetical branch records.
No source was acquired or newly attributed in this reassessment.

### Exact reuse and connection boundary

The existing capacity argument is `13338e9c-3e2f-56ee-8400-7523d47fe46c`
(`CATHOLICISM-STAGE2-GOD-HAS-WILL`). It concludes
`66aecdd7-ea4e-55c6-9377-10db08893854`, not any exercise relation.
Its `WillFollowsIntellectReading` premise has the type
`∀ x, HasIntellect x → HasWill x`. Definition `7c64b499-6dba-5e03-bdf3-5acea95d8836`
(`corpus/definitions/will.json`) explicitly calls `HasWill` primitive and denies
that this implication defines intellectual appetite internally. Thus the richer
prose about appetite is an interpretation obligation, not an elimination rule
for producing any `WillsGoodFor g x esse`.

Causal goodness has the existing alternatives
`279e9475-5b86-5190-8664-a6604dc4e1af` (stage-2 goodness) and
`0011703b-aac5-533b-88ef-a6140dc343f9` (restricted perfection transfer).
Neither conclusion mentions willing. The immediate candidate consumer remains
`divineWillsGoodForAllExisting`, then `godLovesAllExisting` in the module above;
neither is a registered corpus argument. Root connection remains a plan:
actual recipient-directed willing → appropriate love/good-will bridge →
root-connected normative or hiddenness node. In particular, veracity argument
`ab3f4165-87f2-574b-8eef-2a63df5fcbbc` consumes
`7cffee54-a87d-504e-80d1-81ada7387696`, a cognitive/assertoric bridge, not this
love conclusion. Hiddenness argument `0a722d94-3332-420b-b07a-95cc9e842230`
projects global perfect love `0edc0b38-46b0-567a-9f72-64e16b30c77b` to actual
love `5e5aa271-d500-41c7-a470-32969b00a5af`; supplying only actual some-good
willing cannot reverse that implication or supply its interpersonal meaning.
These are explicit downstream blockers, not established new routes.

### Why the three candidate routes do not yet discriminate

The following are analyst tests of the routes already summarized above, not
fresh historical claims about q.19 a.4.

- Teleological priority can motivate a prior intellect directing natural ends.
  Even granting that director, an object-specific practical determination must
  connect it to each effect and to the recipient's good. A first intellect that
  determines a productive nature while willing only its own good is not excluded
  by a capacity conclusion. The missing test is whether the director thesis
  requires intending the effect, rather than merely explaining its order.
- Diversity of finite effects does not distinguish choice from a necessarily
  structured productive nature: a fixed rule can produce several unequal
  effects, and conditional responses to different inputs need not be choices.
  Excluding this account needs a substantive restriction on what that nature
  can determine, not merely the assertion that its effects are diverse.
  Even actual contingency would exclude necessary emission only with fixed
  background and transport conditions; it would not exclude nonintentional
  contingent production. No such modal test is encoded by Bool/Unit controls.
- Intellectual exemplars distinguish represented effects from blind production,
  but representation alone does not distinguish practical adoption from
  theoretical cognition or foreseen byproducts. The discriminating commitment
  is that actual production is governed by adoption of the represented effect
  as an end or means. To obtain the existing bridge, one must additionally show
  that this adoption wills existence as a good of the recipient. That last step
  does not require ultimate, noninstrumental concern for the recipient, but it
  cannot be replaced by a mere benefit accidentally resulting from production.

The third route isolates the most direct next logical test, without yet earning
higher independent warrant. Introduce no generic claim that every knower
intends every known effect. First inspect practical-versus-theoretical cognition
and causal governance at the same agent, effect, respect and actual frame.
If practical adoption is independently defended, factor the inference into
representation, actual governance by adoption, and recipient-good application;
retain each as a visible premise. A predicate defined simply as
`CausesIn → WillsGoodFor` would relocate the target without explanatory gain.

### Strongest standing rival and its commitments

The local rival grants actual source and creature, causal production of the
creature's being, goodness/actuality, intellect, possession of will, and willing
of the source's own good. It supplies a positive replacement: the source's
productive nature determines the effect, without adoption of that effect as
recipient-directed good. Necessary emanation is one stronger variant; necessary
production and intentional production are not contradictories. One could will
necessarily, or produce nonintentionally without necessity. The existing
`omitCausalWill` control represents only the local intentional omission, not
this richer productive nature or any necessity claim.

This rival conflicts with `CausalExistenceWilling` when instantiated at the
actual distinct effect, but the target itself is not independent evidence
against it. It conflicts with a universal practical-adoption/application bundle
only if that bundle is supplied. It does not conflict with the exact goodness,
capacity, own-good-willing or love-meaning inputs preserved by `LoveControls`.
The broader `IntellectWithoutWillReading` in `SpineRivalsAttributes` instead
conflicts with `WillFollowsIntellectReading` at its witness. Refuting that broader
rival would leave the local rival untouched. Likewise the newer
`DeiFiliusOperationFromIntellect.IntellectualPureActOperates` concludes unary
immanent operation; it does not specify an external effect or its recipient.

### Weaker-premise test and proposed assessment

The existing consumer needs only some actual good willed for each recipient,
not necessarily willing of existence itself. A candidate weaker input for
*distinct* actual recipients is therefore: for each God and distinct actual x,
there is some respect r with `GoodIn x r ∧ WillsGoodFor g x r`. Together with
the existing own-good and love-meaning inputs this is sufficient in informal
reasoning for the existing love consumer. It is a proposed formula, not a new
Lean-checked theorem or registered strength relation. Its independent warrant
is no better merely because it is weaker; in isolation it largely restates the
distinct-recipient part of the desired conclusion. Do not register this as a
new explanation or attribute it to an unread text.

Proposed assessment: the inspected evidence underdetermines intentional
creation. Retain the conditional support option and the natural-diffusion rival;
withdraw no theorem and claim no God-existence or root establishment. Reopen
this assessment on an independently supported object-specific governance rule,
a faithful richer model violating such a rule, or an actual downstream bridge.
Next concrete test: formalize practical adoption with an independently stated
causal-governance premise; compare a knower who merely foresees the effect with
a practical adopter while keeping actual production and self-willing fixed.
Then test recipient-good application separately. A modal necessity claim needs
a separate world-indexed encoding. This checkpoint contains no new proof or
source verification; the coordinator must challenge this complete draft before
using its judgments as reviewed support.

## Practical adoption at fixed production (proposed continuation)

Evidence baseline: `f41abae72b8736de1b36c013c043667222b5eb95`, same #1459
slice and PR #1577. This section is a complete proposed outcome for parent
semantic challenge. The previous scoped pass is reused only for unchanged
sections; it does not review this extension. Shared conventions resolved at
`15f348b072188255da837578eaafc8a98f12fdf0`.

### A sufficient route with two separate application burdens

Keep the same actual agent g, distinct existing effect x, existence respect
esse, causal production, self-willing and goodness/actuality fixed. Contrast
these analyst descriptions, without treating them as certified models:

1. **Foresight:** g represents that its productive activity yields x. That
   representation can be a true prediction of its nature's output without
   functioning as a reason for producing x. Nothing here supplies a practical
   commitment to x's existence.
2. **Object-specific practical adoption:** g represents x's existence as an
   end or means and the represented outcome figures in the practical rationale
   governing the productive activity that actually brings x about. The
   activity implements that rationale concerning x, rather than merely
   producing x as a known collateral result of pursuing another outcome.
   Adoption here is occurrent practical commitment, not capacity, prediction,
   approval after the event, or the fact that an outcome happens to be good.

The proposed sufficient route is: object-specific adoption in this practical
sense, together with its actual implementation, supports describing x's
existence as intended. A distinct **recipient-good application** must then
connect intended existence to `WillsGoodFor g x esse`. The first route is not
an exhaustive definition of agency or intention: habitual, non-deliberative
and other accounts remain available. It does not require a temporal decision,
a change in God, alternatives accessible to God, or a separate act for each
creature. These exclusions prevent importing creaturely deliberation into
atemporal divine willing; they do not establish that the account applies there.

The recipient-good application cannot be obtained by conjoining an intention
that x exist with the external fact `GoodIn x esse`. A producer might intend
x solely as useful to something else; whether intending its existence thereby
counts as willing that intrinsic good *to x* is exactly the thin-good reading
needing defense. Ultimate concern for x is stronger than the existing bridge
requires, but an incidental benefit is weaker. Nor does intending existence
under one description automatically supply willing under every true description.
Keep the description of the intended object explicit.

### Discriminating consequence and the coverage objection

On this sufficient route, a genuinely merely foreseen collateral effect fails
the object-specific governance condition even when it is actual, known, caused,
and good in the metaphysical sense. Calling it 'adopted' merely because it was
knowingly produced would erase the discrimination. A concrete conceptual test
is a producer making an instrument while knowing that its operation emits a
harmless light: intending the instrument's operation does not without argument
mean taking the light as an end or means. An alternative plan that uses that
light as its signal changes its practical role while leaving the actual light
and production fixed. This illustrates a contrast in explanations, not a claim
that such alternative plans are metaphysically available to God.

Consequently, even a first intellect's practical adoption of a **whole productive
order** leaves a universal coverage burden. To derive `CausalExistenceWilling`
through this proposed sufficient route, object-specific adoption and
recipient-good application must cover every qualifying distinct actual effect.
Other routes to recipient-directed willing remain open. Foreknowledge or a
plan's causal consequences alone do not supply this proposed route. One plan could intentionally
specify many effects without many separate decisions; that possibility does
not show that every consequence is specified in the required practical way.
Universal knowledge and lack of surprise do not remove this burden. A stronger
account on which divine practical cognition specifies each effect precisely
as produced could supply it, but that is a substantive premise requiring its
own defense, not the existing unary intellect or immanent-operation result.

The discriminatory result is thus a proposed **conditional exclusion**: mere
foresight cannot satisfy this selected sufficient route without additional
practical-role evidence. It is not a proof that no other route can establish
intention, or that foresight and intention cannot coexist. No new Lean theorem,
registered definition, certified countermodel or rival defeat is claimed.

### Warrant, rejected encodings and next test

Practical adoption has explanatory value over bare prediction because it
locates the represented outcome within the rationale actually implemented by
production. Its application to God remains OPEN. The ordinary example offers
no independent evidence that every divine effect has that role, and the
recipient-good reading remains an additional OPEN interpretation bridge.
Necessary production is compatible with this account: necessity says nothing
by itself about whether production implements an object-specific rationale.
No freedom or contingency result follows.

The positive natural-diffusion rival can retain perfect foresight and
self-willing while grounding production in nature's determinate activity.
A richer variant can grant adoption of the whole order while disputing
object-specific coverage or recipient-good application. Neither has been
certified here. Their exact disagreement is with those proposed universal
premises, not with the unchanged goodness/capacity/coextension/self-willing/
love bundle witnessed by `omitCausalWill`. Treating that finite control as a
model of the richer rival remains invalid.

Rejected encodings: a free `Adopts g x` flag; defining adoption by the desired
`WillsGoodFor` conclusion; identifying all represented outputs with adopted
ends; requiring 'would refrain if x were absent' as a universal intention
criterion. The last test imports accessible alternatives, can fail for necessary
intentional action, and ignores redundant or independently sufficient ends.
None supplies the missing practical explanatory role. A finite selector that
simply switches outputs would demonstrate a policy's extensional behavior,
not yet intentional governance or its divine applicability. Accordingly no
sibling proof is added merely to certify these restatements.

Proposed outcome: this sufficient route sharpens the exact missing bridge but
does not improve its independent warrant automatically. No premise change.
The next concrete research test is the universal coverage claim: compare
practical specification of each effect with adoption of an order that includes
foreseen collateral effects, under an explicit account of divine practical
cognition. Its required evidence is an independently motivated account of
practical explanatory role and effect individuation; the inspected capacity,
immanent-operation and generic causal declarations do not supply one. The
coordinator can assign that semantic dependency or select the separate
recipient-good application question. Hiddenness's interpersonal/world scope
and veracity's cognitive/assertoric bridges remain additional downstream work.
Attribution remains deferred and source checks offline.

### Owner stopping instruction, 2026-11-12

Finish this reviewed #1459 checkpoint and stop further research. The causal-to-
willing bridge remains unresolved: this analyst comparison supplies no new
theorem, premise warrant or rival defeat. The independent challenge accepted
the adoption comparison after qualifying it as a sufficient route. A future
resumption should independently specify effect identity and practical role,
compare universal effect specification with foreseen collateral production,
and assess recipient-good application separately. No such continuation is
authorized by this stopping instruction.

## Group 7 integration: recipient-good route (#1732, 2026-11-18)

Status: complete proposed integration outcome for independent semantic
challenge, baseline `354540f92e4139d445355f6e3f49374fdb151b39`. This is a
registration of the existing composition, not a resumption of the #1459
research stopped by the owner instruction above; it reuses that section's
findings unchanged and adds no new theorem content, premise or source claim.
Assertion half: [veracity note](divine-veracity-1410.md#group-7-integration-assembled-assertion-branches-1732-2026-11-18).

### Registered support option

Batch `specs/divine-love-route-1732.toml` (module
`TruthCore.Results.Case.Catholicism.DivineLoveRoute`) registers the PR #1458
composition as two corpus results:

1. `willsGoodForAllExisting`: supreme goodness e0dae79f, will 66aecdd7, the
   goodness/actuality coextension 00e962ae, and the two OPEN volitional
   bridges (`CausalExistenceWilling`, `DivineOwnGoodWilling`) give
   `DivineWillsGoodForAllExisting`: every GOD_4 wills some good to every
   being in act in esse.
2. `lovesAllExisting`: the same five inputs and the OPEN one-way
   love-meaning bridge `WillingGoodEntailsLove` give `GodLovesAllExisting`.

Corpus IDs: results `7209fa2f` and `a2366ca4`; statements a94c5dfc
(`CausalExistenceWilling`, OPEN), 2a168a36 (`DivineOwnGoodWilling`, OPEN),
16ab027e (`WillingGoodEntailsLove`, OPEN), c691e3d0 (willing some good to all
existing) and e3d5bece (love of all existing).

Both are zero-axiom. The classical self/other split of the unregistered
originals is replaced by an explicit `[DecidableEq Being]` instance argument:
a decidability-of-identity input (restricted excluded middle) supplied by the
caller; classically always available, constructively valid only where
identity of beings is decidable. It is listed as a parameter, not hidden. The originals and `LoveControls` are
unchanged. This is not a transcription: neither bridge's antecedent is a
premise; the causal field of supreme goodness supplies causation of each
distinct actual being, the coextension supplies its good in esse, and the
self-case uses a separate bridge. Each of the three bridges is shown needed
by the existing omission profiles, with goodness, will and coextension fixed.

New terms: `08b826db` (willing good to a recipient), `1ca75ad2` (willing a
being as ordered to another) and `ac87be3d` (thin non-passional q.20 love),
all stipulative. Their sense carriers are primitive structure fields in
`TruthCore.Case.Catholicism.DivineLoveSenses`. Disambiguation 28c9980e
(LOVE) separates LOVE_1 thin q.20 love (`ThinLove.Loves`), LOVE_2 hiddenness
PerfectLove 4b2943ad and LOVE_3 love of a possessed good 9f448669.
`lovesAllExisting` proves LOVE_1 only; any transfer to LOVE_2 is an OPEN
sense bridge owned by #1735. The carriers are tied to the parametric
registered theorems by instantiated corollaries (follow-up, below): results
54a9ccd9 (`willsGoodForAllExistingAtCarrier`, CREATURE_WILLING_1) and
a66e4ce3 (`lovesAllExistingAtCarriers`, CREATURE_WILLING_1 and LOVE_1),
whose `term_senses` are bind-checked against those constants.
Cognition alone is not used: no intellect premise occurs.

### Connection boundary

The premises reach the root through the stage-2 case nodes; the conclusions
do **not** yet feed a root route. Named consumers and the exact missing bridge:

- Hiddenness/evil (#1735): `GodLovesAllExisting` is thinner than global
  perfect love 0edc0b38 and actual love 5e5aa271 (interpersonal relationship
  with capable creatures). The projection, if any, is an OPEN bridge owned by
  #1735; causal goodness and willing some recipient-good do not
  automatically identify those predicates.
- Recipient goods and authority (#1733): may consume
  `DivineWillsGoodForAllExisting` directly; no bridge exists yet.
  *Update 2026-11-18 (#1733):* consumed. `DivineWillsGoodForAllExisting`
  c691e3d0 entails the restricted premise 47c6da1b (GOD_4 wills some good to
  every distinct intellectual being whose being it causes), which feeds the
  LORD_3 Dei Filius root route; the same premise also follows from
  `CausalExistenceWilling` with the coextension, without the self-case. Both
  supports go through `CausalExistenceWilling` a94c5dfc (c691e3d0's only
  derivation uses it). The premise is consistent with the strong (exclusive) ordered-love variant 1dd68893, an unattributed analyst strengthening of ad 3,
  on non-rational effects, but a94c5dfc is not; so if that strong variant holds
  and non-rational creatures exist, 47c6da1b has no verified derivation and
  stands only as a direct assumption. The conflict with a94c5dfc holds for that strong variant only (checked: result 400893a0). The weak, ad-3-faithful reading 7f6a2e91 (ordered willing without the exclusion of recipient-directed willing) is compatible with a94c5dfc (checked witness 5d93ac09, result ef387145), so neither verified derivation of 47c6da1b is excluded under the weak reading. See
  [group 8 integration](natural-goodness-function-and-authority.md#group-8-integration-from-reasons-and-goods-to-moral-authority-and-god-1733-2026-11-18).
  The warrant assessment below is unchanged.
- Veracity: the assertion route does not consume love; willing good to the
  audience is not itself a norm against beneficial false assertion (see the
  assertion half and #1737).

### Cumulative provisional assessment (proposed)

Positive warrant: q.19 a.4's three routes (priority of intellectual over
natural determination, determinate effects from an indeterminate source,
intellectual preexistence of effects), the practical-adoption sufficient route
of the continuation above, and q.20 a.2's own love meaning. The
self-good bridge has comparatively strong direct support from q.19 a.1's
account of will as possessing and loving the good; the love-meaning bridge is
a thin interpretive sufficiency rule whose prima facie plausibility is high
once friendship, affection and degree are excluded. The load-bearing and
weakest step is `CausalExistenceWilling`: the causal-to-recipient-willing
application. Shared premises with other routes: supreme goodness e0dae79f
and will 66aecdd7 (also used by the classical-attribute consumers), and the
coextension 00e962ae.

Holding the effect (a distinct actual x), the explanatory target (x's
existence in esse), production, foresight and self-willing fixed, the
strongest surviving alternative is **natural diffusion / foreseen collateral
production**: the source's productive nature (or its adoption of a whole order)
determines x, and x is known but not adopted as an end or means with its good
willed to it. Its price: it must deny that the divine practical specification
covers each effect, and so accept effects that the first intellect knows and
produces without intending; it must also answer q.19 a.4's claim that an
intellectual first agent determines effects through intellect and will
rather than nature. The q.20 a.2 ad 3 **ordered-love reading** is relevant
here: irrational creatures are loved "as it were" with love of desire, as
ordered to rational creatures and to God. It is registered in two strengths
(strength fork, #1017), forked from a94c5dfc by the disambiguation dd7ff973
(CREATURE_WILLING_1 recipient-directed, CREATURE_WILLING_2 ordered):

- **Weak, the ad 3 reading** 7f6a2e91 (`OrderedExistenceWillingWeak`): God
  wills a distinct non-rational effect's esse as ordered to some rational
  being or to God. It neither asserts nor denies recipient-directed willing,
  and it is compatible with a94c5dfc at one willing relation (witness 5d93ac09,
  result ef387145). It is therefore no rival to the registered route. On the
  weak reading, ad 3 concerns the order of love; the a.2 body supports not
  reading it as exclusion.
- **Strong, unattributed analyst variant** 1dd68893 (`OrderedExistenceWilling`):
  the weak reading plus the denial that God wills that good to the effect as
  recipient. Its separate motivation is to read love of desire (willing a
  thing's good for another) as excluding love of friendship (willing good to
  the beloved itself) for non-rational things. The q.20 a.2 body ("God loves
  all existing things") counts against the denial. It strengthens the weak
  reading (relation; result 0e665ad9, sole premise), and together with
  a94c5dfc at one recipient-directed willing relation it excludes any
  distinct non-rational caused actual effect (result 400893a0). It is the
  source-adjacent form of the non-recipient-directed production the
  foreseen-collateral rival needs, restricted to non-rational effects.

No registered love argument uses either sibling. The natural-diffusion /
foreseen-collateral rival is not shown incoherent, and the existing
`omitCausalWill` control witnesses only the local omission, not this richer
rival. Overall: a **coherent conditional support option** with a comparatively
well-supported self-good bridge, a prima facie plausible thin love-meaning
bridge (subject to the ad 3 qualification) and one open application bridge, whose warrant is
underdetermined at universal effect specification and recipient-good
application. No premise established; no rival defeated.

Revision conditions: strengthen on an independently supported account of
divine practical cognition specifying each effect as produced (effect
identity and practical role), or on an argument that foreseen collateral
production is incompatible with the first agent's intellectual determination
of effects; weaken on a faithful richer model retaining production,
foresight, self-willing and whole-order adoption while omitting object-specific
adoption, or on a reason why intending a creature's existence does not count
as willing that good to it. Per the owner stopping instruction, further #1459
research requires a new assignment; this integration authorizes none.

## Research attempts citing this note

- [Group 7 integration: assembled assertion branches and registered q.20 love route (#1732)](../../corpus/attempts/e641ca1d-d06b-461a-8270-c9030fa4fc29.json)
- [Intentional creation bridge route and emanation audit](../../corpus/attempts/intentional-creation-1459.json)

## Through-will checkpoint (2026-11-26)

The new conditional support concerns the mode of giving **each distinct actual
effect** of the same universal esse cause, with intellect and will held fixed.
[Rational exercise](../../TruthCore/Causality/ThroughWill.lean) means that the
cause gives the effect being at some moment of the selected world, and that this
giving exercises an owned rational power (WILL_CAPACITY_VERSUS_WILLED_GIVING_3).
This can hold with fixed output. Sense 1 is possession of will, and sense 2
adds accessible withholding with the same set-up. The agency dictionary reads rational
power as an inclination that follows intellectual apprehension of good. It
classifies the power using a primitive. Practical content and its governance of
this effect remain open. A builder deliberately constructing a shelter
illustrates rational exercise. Her body warming the air illustrates production
in a respect in which her possessed intellectual appetite supplies no exercise.
Both examples involve finite processes within an existing world. Generalizing
to esse itself is a separate commitment.

| Step | Exact commitment and warrant |
| --- | --- |
| Actual exercise | An esse edge from g to a distinct x in act as to esse supplies giving at the selected w. The sustaining and concurrence results motivate the step if the effect is present and their assumptions hold on this dictionary. The generic, tenseless CAUSE_2 edge and world-relative exercise are distinct inputs. |
| Classified exercise | Giving at w exercises an owned power which is rational or non-rational. This is the existing own-power idea with classification explicit at the witness. Multiple powers may be exercised. |
| Firstness | A universal cause with intellect and will has no distinct simply prior being. Universality supplies a reverse esse edge if the putative prior is actual in esse. To use that to infer firstness, the route needs an account of which prior beings are actual, simple priority as a cause of esse, and the exclusion of mutual esse causation. Existing proofs of firstness at a selected root have narrower scope. |
| Natural priority | Non-rational exercise in giving requires a distinct simply prior intellect. ST I q.19 a.4 co., first reason, motivates this by reference to a natural agent's end and means being set by a higher intellect, as an archer sets an arrow's end and path. The existence of a prior intellect suffices for the formal contradiction. Extending the reason from directed instruments to intrinsic productivity of the ultimate source is the disputed application. |
| One power | Alternatively, require at most one active power for each qualifying cause. The existing one-power result then supplies rational exercise from will following intellect, will supplying an owned rational power, and giving exercising an owned power. ST I q.19 a.4 ad 4 motivates unity of knowledge directing, will commanding, and power executing for God. Equating that unity with identity of all owned active powers for every qualifying cause remains open. |

The [two proofs](../../TruthCore/Results/Causality/ThroughWill/Solution.lean)
share the esse adapter. The second consumes 5c1aba17, whose proof is the
[existing one-power result](../../TruthCore/Results/Causality/WillVersusChance/Solution.lean).
Each of the four priority inputs has an omission control. The adapter omission
deletes giving and the classifier omission deletes exercise. The priority
omission retains firstness and fixed giving by an owned non-rational power
while the cause also owns a rational power. In the firstness omission, the
actual effect is simply prior to the source in the assignment. The assignment
tests the type, which specifies no directing by that effect. The positive
control retains the fixed output, exercises the rational power, and permits
empty direction and recipient-willing relations. These are structural
non-entailment tests with actual relata and a populated causal edge.

### Rival mechanisms

*Enneads* V.4.1–2 gives a positive mechanism of derivative activity without a
prior director. Plotinus appeals to the productivity of mature beings and
distinguishes the activity constitutive of a substance from an outward activity
that follows from it, illustrated by the heat of fire and the heat it imparts.
The outward effect proceeds while the source remains itself. The One is beyond
intellect in the passage. Extending that mechanism to a source whose intellect
knows the order and whose will rests in its own good is an analyst variant.
If its productive power is non-rational, the variant denies natural priority.
If it grants the other one-power premises, it must distinguish the rational
capacity from the active power of non-rational production. HAS_WILL_1 supplies
neither power identity nor exercise for this effect. The finite priority
omission checks that distinction. It leaves the rival's applicability to a
single universal esse cause and its account of power unity open.
[Pinned Plotinus witness](../../corpus/passages/plotinus-enneads-v-4.json)

An Avicennian-style necessary procession gives the first determinate effect
from the First's self-intellection and accounts for subsequent multiplicity
through the derived intellects' distinct objects or aspects of intellection.
This offers a mechanism for derivative determinate effects from a simple
source and disputes the second q.19 a.4 reason's claim that natural necessity
in an infinite cause would require an effect indeterminate and infinite in
being. The point of disagreement is whether a determinate first effect can
proceed in this way.
Whether the proposal also denies rational exercise depends on what work the
First's intellection and approval do in production and whether the derived
effects satisfy the case's universal CAUSE_2 coverage. Further source
interpretation is deferred.
[Avicenna, Metaphysics of the Healing IX.4, source lead](https://www.academia.edu/2993314/Avicenna_Meta_9_4)

A Rowe-style argument from perfect goodness and a unique best order can retain
rational operation while making it fixed. On that proposal, the best's goodness
settles the outcome even though the creator's own good needs no created means.
A Kretzmann-style diffusion requirement to produce some good needs a further
premise to fix this particular effect. These proposals bear on
RationalFixedGivingIsRequired (WN) in [NarDerivation](nar-derivation.md),
which assumes rational exercise in its antecedent. In the fixed rational
control WN fails when the required-means relation is empty. Conversely, the
fixed non-rational control has no rational exercise for WN to constrain.
I q.19 a.10 co. limits free choice to what is willed non-necessarily and refers
back to a.3, where absolute and suppositional necessity are distinguished.
A freedom argument needs additional grounds for possible variation or against
a proposed necessitating reason. In particular, the q.19 a.10 source support
for the POWER_OVER_ESSE_1 bridge d1593e5c needs effective willing matched to
the same giver's giving or withholding at accessible worlds. It also needs
the effect's continued being to depend on that giver's exercise. Actual
rational giving alone supplies neither condition.
[Pinned q.19 witnesses](../../corpus/passages/aquinas-summa-theologiae-q19.json)

### Applications and provisional assessment

- **Direction and lordship.** The new result reaches 123d394b with a separate
  premise that rational exercise in giving each effect supplies an end to
  which the giver directs it. This is recorded as an assembly transcription,
  and 123d394b stays open. I q.22 a.1 co. and ad 2–3 distinguish the
  intellectual plan of order, the willed end, and execution. Q.22 a.2 co.
  and ad 1 extend ordering to each effect of the universal first agent.
  Aquinas's example of a cause outside the order of a particular agent
  differs from collateral output within the universal cause's own productive
  order. Coverage still needs a reason to treat each effect as directed by
  this giver. The q.103 rule links direction to LORD_2 government. I q.13
  a.7 co. and ad 5 use real subjection on the creature side for divine
  Lordship. Applying that rationale to bb3d4417, and thence to the
  LORD_2-to-LORD_1 bridge, still requires linking universal causal dependence
  to authority to dispose.
  [Providence witness](../../corpus/passages/aquinas-summa-theologiae-q22.json)
  [Lordship witness](../../corpus/passages/aquinas-summa-theologiae-q13-a7.json)
- **Recipient-directed willing.** The assembly transcription applies the open
  recipient-good bridge to a94c5dfc, which feeds the existing LORD_3 willing
  input. The causal conjunct of supreme goodness supplies universal esse
  coverage, and the GOD_4 intellect premise supplies intellect at that same
  giver. These inputs supply the bridge's antecedent. The bridge itself
  supplies the recipient-directed content. The frontier keeps a94c5dfc open
  with source support.
  I q.20 a.2 co. uses divine will causing esse to argue that God wills good
  to each creature. The ordered-love reading of ad 3 treats irrational
  creatures under quasi-desire in their order to rational creatures and God.
  A productive order can be adopted for another's good, so the rational
  production of a recipient needs a further reason to say the good is also
  willed **to** it.
  [Love witness](../../corpus/passages/aquinas-summa-theologiae-q20.json)

**Provisional judgment for independent challenge.** Instrumental teleology
provides a reason to ask what fixes the end and means of non-rational operation.
The one-power argument adds a distinct reason to exclude a separate natural
capacity doing the productive work if substantive power unity applies. Rational
exercise is thus a coherent conditional account for the universal cause. The
overall inference remains underdetermined at natural priority, the scope of
one-power simplicity, and the esse-to-exercise adapter. The positive grounds
for diffusion concern production without prior selection. Whether the same
mechanism works at the ultimate esse cause while preserving its will in the
selected sense still needs a defense.

The next discriminating test asks whether apprehended order actually specifies
the source's exercise **as practical** for each esse effect. Hold fixed the
outputs and what is known, and test production as the realization of this
effect's apprehended description against mere foresight or adoption of the
whole order. The third reason of q.19 a.4 motivates this by moving from effects
intellectually preexisting to their proceeding according to what is understood,
then to appetite toward realizing it. Correct exemplary representation,
available rational power and universal causal coverage leave the practical
step open. The existing reviewed comparison from I–II q.9 a.1 gives a
specifying role to the apprehended good in proper acts of appetite. The
application here must show that the giving is such an act for the selected
effect. Its defense would advance direction. The narrower recipient-good
test would still ask whose good is willed, as distinct from what is ordered to
a good. Independent grounds for a determinate, non-rational disposition of
an ultimate source would weaken natural priority. An existing productive
dependence test can check that adoption helps supply an exercise without
depending on the product it is meant to explain. Applying it here still needs
an identification of the independently specified adopted content and its
productive role on the same esse edge.
[Actual exercise controls](../../TruthCore/Explanation/ActualExerciseExplanation.lean)
[Apprehended good comparison](will-versus-chance.md#can-a-good-specify-actual-production-without-being-apprehended-2026-11-25)

## Practical specification checkpoint (2026-11-26)

The question at 3655f59f is what makes the recipient's esse a good the giver
wills **for that recipient**. Practical use of an apprehended standard is one
part of the answer. Its operative content is another. The new deductions
start from the rational-exercise sense of giving already used in #2019, at the
same giver, recipient and selected world.
[Practical plan and controls](../../TruthCore/Causality/PracticalSpecification.lean) ·
[Proofs](../../TruthCore/Results/Causality/PracticalSpecification/Solution.lean)

### Two omission tests on the same practical standard

First specify what would count as fulfillment independently of the successful
output. A standard can require producing x, count x's esse as its own good, and
require x to have a place in an order to an end e. A plan may combine these
requirements and may govern many effects at once. The interpretation treats
the chosen standard in this analysis as conjunctive. For a disjunctive plan,
for example, which branch actually governs production would need further
evidence before applying this analysis. The omission tests edit **descriptions
of fulfillment**. They do not assert that one can produce x without its esse,
that a logically impossible output is possible, or that an alternative act
of creation is accessible.

- **Operative coverage (4be0f774).** For a distinct actual effect given being
  by rational exercise, find a standard apprehended as good by that very
  giver, used to specify this giving, and satisfied in the giving's context.
  A clinician's adopted treatment target guides assessment and correction
  even if a dose fails. A forecast can correctly predict a beneficial effect
  whose occurrence the clinician did nothing to secure. Those roles give
  the distinction an independent rationale. The successful-giving
  application to esse itself remains open.
- **Benefit (df6c64a6).** In a GOD_4 giving, erase only the credit for x's
  esse as x's good from the actual assessment. If no such clause were
  required, the edited assessment would still satisfy every requirement.
  Rejection therefore identifies a mandatory benefit clause. The
  recognition premise 437438f0 assigns an operative commitment to that
  benefit to the recipient-willing relation. It is an explicit interpretation
  of the case primitive. It allows the benefit to be desired for x as a
  subordinate good. It cannot be applied merely because the whole plan is
  good or x actually benefits.
- **End (b1d7825e).** Erase every end-placement of x from the actual
  assessment while preserving its bare production and any benefit credit.
  If no end-placement of x were required, the edited assessment would
  still pass. Its rejection and the direction recognition premise f8cd0849
  yield a particular end to which the giver directs x. The same end need
  not serve every effect. The procedure works even when the benefit test
  fails.

The new premises do not mention an existing application bridge as an
assumption. They require an independently assessable content and its use,
then test the content with role omissions. Under the conjunctive semantics
these tests characterize which roles are mandatory. This is a way to locate
and test an open commitment, not independent evidence that a real divine
standard has the tested content. Inferring that content only from x's
actual production or goodness would assume the contested practical role.
Recognition still needs the step from a required content to the corresponding
case relation, whose range and reading are fixed by the existing definitions.
[Evidential basis versus correct performance](explanatory-symmetry-742.md#what-transfers-from-belief-to-action-to-an-origin)

### Rivals and what the controls discriminate

All rows use the original two-world assignment with one fixed rational
giving, the same actual giver and effect, and the same causal edge.
Apprehension is fixed and every clause is assigned realized throughout.
The content also always requires bare production of x and the source's
self-good. The controls vary operative use, the requirements and the case
relations as indicated. Self-willing and self-direction are populated
assignments outside the distinct-effect targets.

| Interpretation tested | Practical use in giving x | Is x's own benefit required? | Is an end-placement of x required? | Finite result for the distinct effect |
| --- | --- | --- | --- | --- |
| Foresight without use | No | Yes, in the apprehended but unused plan | Yes, in that same plan | No coverage. The conditional tests and recognition rules hold vacuously at the distinct effect. Both target bridges fail. |
| Whole-order use with bare production of x | Yes | No | No | Both edited descriptions meet the standard. Both bridges fail with both recognition premises satisfied. |
| Whole-order use assigning x an end | Yes | No | Yes | The end test and direction bridge hold. The benefit test and recipient bridge fail. |
| Recipient benefit as a success criterion | Yes | Yes | No | The benefit test and recipient bridge hold. The end test and direction bridge fail. |
| Full selected content | Yes | Yes | Yes | Both tests, recognitions and bridges hold. Turning off either case relation at x with the full operative plan preserved falsifies its recognition and bridge, independently of the other relation. |

Direction for another's sake is the strongest rival to the recipient
inference **even if** the esse giving is under an adopted order. A familiar
positive mechanism is instrumental placement. A production protocol can
deliberately maintain a microbial strain that performs a needed function
for a larger process, without making the strain's own flourishing a
criterion of success. A producer can likewise attend only to the whole
order as realizing its own final good. The disagreement is whether x's esse
makes a contribution as good **to x**, or only as a component of what
serves a further end. Instrumental placement can retain practical use,
knowledge and per-effect direction, while rejecting the benefit omission
premise. The concrete production example concerns a continuing life process
and does not generalize by itself to giving esse.

The self-loving diffusion proposal is the stronger rival to **operative
coverage**. It explains the output through the source's own intrinsic
generative orientation, with the proper volition directed at the source's
own good. The previous checkpoint's Plotinus comparison supplies the
outward-activity mechanism. Its extension to a rational universal giver
is an analyst variant. Such a giver can be rational in the #2019 classifier
and understand the product while still rejecting that the actual esse
exercise is constituted by use of an apprehended standard. Its explanatory
burden is to substantiate how one source's nature supplies the specific
output and why the proper volition is fulfilled independently of it.
The presence of self-love and an accurate representation do not supply
that productive account. Universal causal coverage puts every distinct
actual producer within the first cause's esse coverage. Even granting that
there is no producer outside its order, the first cause's own activity
could still have a collateral consequence. The absence of an outside
producer therefore does not by itself settle either test.
[Prior diffusion comparison](#rival-mechanisms) ·
[Proper exercise and intrinsic-final rival](will-versus-chance.md#can-a-good-specify-actual-production-without-being-apprehended-2026-11-25)

### Applications and provisional judgment

The strongest positive reason for coverage is the proper-manifestation
analysis in the prior comparison. If giving this esse is the proper
realization of intellectual appetite under an independently specified good,
that good supplies the activity's practical measure. A successfully
satisfied standard of each recipient's esse as its own good would then give
a reason for the benefit test even where the whole order has a further end.
A practically adopted role for x in the order supports the direction test
without settling that beneficiary question. The available reasons warrant
investigating these as distinct support options. They leave actual
governance, the scope and content of the standards and their interpretations
underdetermined. Knowledge of a creature in its own nature could help fix
the description of x in the plan. It would still require knowing by the
same giver, evaluative apprehension, and actual use. No formal inference
from that separate knowledge statement is made here.

The recipient derivation targets 3655f59f, feeding the existing #2019
application to a94c5dfc. The direction derivation targets 2f9a99cc. It uses
actual rational exercise alone in the antecedent. Composing it with
83d8a0e0, which supplies exercise for each distinct actual effect of the
qualifying universal cause, gives the assembly route to 123d394b.
The original Lean specialization at de6a0f86 has possession and actual
exercise as separate antecedents. Its proof uses exercise and does not
infer it from capacity. The specialization remains in the frozen
Challenge and Comparator check. The sense validator cannot represent
co-occurrence of these antecedents without a bridge, so the graph
records the stronger exercise-only theorem and the direct assembly
consumer. The frontier reports 3655f59f and 2f9a99cc as proved, and
a94c5dfc and 123d394b as closed via transcription. Their philosophical
establishment remains open. End-directed government supports the LORD_2
antecedent, and the love route supports the
benevolent willing input of LORD_3. Even their conjunction leaves the
authority-to-dispose premise open. Knowing how creation serves the governed
can strengthen a rationale for authority but does not establish normative
standing from the descriptive roles encoded here.
[LORD_3 and original standing](natural-goodness-function-and-authority.md#group-8-integration-from-reasons-and-goods-to-moral-authority-and-god-1733-2026-11-18)

The next discriminating step is to fix an antecedently interpretable success
criterion for a particular effect, then show from the actual productive
constitution why the giver's **apprehending** it governs the exercise.
Candidates must distinguish a realized recipient good that counts in making
this act successful from a merely foreseeable benefit of the same act. A
productive dependence circle would weaken a proposed account of adoption
that needs its own product. A defended noncognitive source specification
that explains the same actual directed production would weaken a claim
that apprehension must do the work. The finite assignments decide neither
constitutive account.
[Actual exercise dependence test](../../TruthCore/Explanation/ActualExerciseExplanation.lean)

[Derivation attempt](../../corpus/attempts/3fdc09ec-1d28-4b3e-b7aa-a1db6fff0456.json) ·
[Rejected direct inference](../../corpus/attempts/55c9bf7e-8825-4634-9988-2352c019ce76.json)
