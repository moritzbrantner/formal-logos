# Sustaining causation of being versus existential inertia (2026-11-19)

**Question.** Is there discriminating warrant, at matching scope, for the
sustaining reading of the cause of being over existential inertia, or the
reverse? Targets: the weak sustaining reading `ce55210c`
(`ConcurrentActualization.CausingAnothersBeingIsSustaining`), its crux, weak
concurrent actualization `40a97664` (`ConcurrentlyActualized`), and the
esse-dependence premise `2068f91c` (`Round2Grounding.EsseEffectDependsOnItsCause`),
the binding constraint for maximum = root on the esse-root routes `3367bf93`
and `fc46b7f9` and on the dependence spine.

**Reused, not repeated.** The existential-inertia section and the
2026-11-17/18 assessments of
[eternity-dependence-connection.md](../eternity-dependence-connection.md)
(Schmid 2021 and Feser 2021, pinned and read; ST I q.104 a.1, claims
`40aefb2e`, `da9c82ed`), attempts `c94eed5b`, `05bc2722` and `447838c8`, the
controls `955ef523` (`ConcurrentActualization.controls`) and the cessation
certificate `610e21dc`. Their classifications stand: extrinsic inertia is a
kept substantive undercutting objection to `40a97664`; the common causal law on
cessation favours neither side; persistence-power inertia is answered
provisionally by Feser's circularity argument at concurrence `d7f5a528`.
Also read, not edited, and **not merged or verified on this base**: the
2026-11-18 cluster assessments on the open branches of PR #1769 (lane B,
`causal-dependence-support-investigation.md`, rival row 3) and PR #1777 (lane F,
`esse-root-leaves.md`, row 7 and its "most discriminating next test"), and the
`HoldingMotion` module of the unpushed C\* branch `agent/cstar-actualization`,
read in its sibling clone.

## 1. The sustaining sibling of `2068f91c` (formal next test, done)

Module `TruthCore.Causality.SustainingDependence`, spec
`specs/sustaining-dependence.toml`.

| Record | Lean | Content |
| --- | --- | --- |
| `149ed837` sibling | `SustainingEsseCauseIsDependedOn` | if c ≠ x causes x's esse and, in every history, gives x being at every moment at which x is present, then `DependsForBeing x c` |
| `ffcb81fb` co-presence bridge | `CoPresentEsseCauseIsDependedOn` | if c ≠ x causes x's esse and, in every history, is present whenever x is, then `DependsForBeing x c` |
| `1f2ae3c4` | `sustainingSiblingOfCoPresence` | contact `c4661518` + bridge ⊢ sibling (transcription; the contact step is the only typed work) |
| `f8519735` | `esseDependenceOfSustaining` | `ce55210c` + sibling ⊢ `2068f91c` (transcription) |
| `2574412d` | `sustainingSiblingOfEsseDependence` | `2068f91c` ⊢ sibling (strength order, relation `e6d1be09`) |
| `886615a9` | `controls` | parts 1–4 below |

The sibling states the giving profile with `GivesAt` directly (the time profile
of CAUSE_OF_BEING_2 without its presence clause), so that it uses the tenseless
`CausesIn` and the giving profile as two separate conditions with no passage
between them.

**Outcome.** The lane F test succeeds with one explicit extra bridge, as that
note predicted ("a law from `SustainsBeing` to the counterfactual D"). The law
is the co-presence bridge composed with contact. So on this route `2068f91c`
costs exactly `ce55210c` + `c4661518` + `ffcb81fb`. Both composition steps are
transcriptions in the sense of invariant 16, so they record the connection and
close nothing while a premise is open; `frontier-diff` adds the sibling and the
bridge as bare premises and registers the strength order as the one new support
alternative. The checked content that is not a transcription is in the
controls.

*Warrant of the bridge, and its limits.* In the standard counterfactual logics
(Lewis, Stalnaker) a strict conditional over the relevant worlds entails the
counterfactual, vacuously when the antecedent is impossible; DEF-DEPENDS-FOR-BEING
includes impossible antecedents. The antecedent is pointwise in every history,
so it serves both readings of "would not be" (never would have been; would not
be then), the originating/sustaining fork of D (#1626). Two conditions are not
typed:

1. **History coverage.** The model's histories must represent the alternatives
   relevant to the counterfactual. Without it the bridge fails in an ordinary
   case: on a one-history model a parent that only originates its child and
   happens to outlive it is a cause of the child's esse present whenever the
   child is, yet the child would be without the parent. Coverage is a shared
   dependency of the route: `ce55210c`, contact and the bridge are all stated
   over the same model `h`, and only with coverage do they hold over every
   relevant possible history.
2. **The identification** of DEF-DEPENDS-FOR-BEING's agent-cause counterfactual
   with the counterfactual a strict conditional yields. That definition lists
   Lewis-style dependence as an account to test against.

The `CausesIn` antecedent blocks dependence on co-existents with no causal
role. It does not block vacuous dependence on a cause of esse present at every
moment of every history, whatever its mode: an originating cause that is
always present would satisfy the bridge with no sustaining at all. So at the
(maximum, root) instance `2068f91c` might also follow from the bridge, contact
and an always-present root, without `ce55210c`. That alternative route is
recorded as unexamined; the claim that the dispute sits in `ce55210c` holds for
the route registered here only.

Grade: the bridge is positively motivated by counterfactual logic, but its
coverage condition is untyped and unassessed, and without it there is an
ordinary counterexample. It is ungraded beyond that.

*Controls* (`SustainingDependence.Control.Certificate`): (1) parent and child,
the existing `inertia` history (an originating cause gives being at the effect's
first moment only and is then absent; dependence read as co-presence): contact,
the bridge and the sibling hold; `ce55210c` and `2068f91c` fail. This is lane
F's requested check: the parent-child interpretation satisfies every input
except `ce55210c`. (2) no dependence: the bridge is needed. (3) an absent
giver: contact is needed. (4) all inputs and `2068f91c` hold together.

*Consequence for the route.* With the sibling, the origin-without-sustaining
counterexample (lane F row 7, lane B row 2) no longer targets the dependence
step: a parent that only originates does not satisfy the sibling's antecedent once the child persists past its first moment (it holds trivially for an effect present only at its first moment or in no history).
On this route the dispute over `2068f91c` sits in `ce55210c`, and through
`366a6ea3` in `40a97664`. The direct option of `2068f91c` stays available; it
is not removed or penalised by the new derivation.

## 2. The rival's itemised price, by direction of entailment

Owner direction (2026-11-19, via the coordinator): record honestly what
rejecting concurrent actualization forces the rival to reject. Two shapes:
(a) independently plausible propositions that **entail** `40a97664` or
`ce55210c`, so that modus tollens spreads the rejection; (b) routes that merely
**rest** on the premise, single points of failure that add no price.

Of the six candidates below, one entailment (onset/parity) is checked in Lean.
The others are analyst arguments in this note, or come from the unmerged C\*
branch.

### (a) Candidates that would entail the crux

| Candidate | Entailment | Independent of `40a97664`? | Can the rival reject it, and how? | Price item? |
| --- | --- | --- | --- | --- |
| Onset/parity: coming to be needs a present giver, and persistence is the same kind of fact | **Checked in Lean.** Onset `fa3e228b` + parity `5b24ef26` give concurrent actualization for begun things `f4850897` (`d2e4867c`, a transcription); `40a97664` gives `f4850897` (`6d90f126`, relation `413800c5`). With natural-number times `f4850897` and `40a97664` coincide for present things. | **Onset yes, parity no.** Given onset, parity is `f4850897` restated. No warrant for parity beyond that for `40a97664` is on file. | Yes, by the counter-asymmetry that only a change needs an inducer and persistence is no change. That asymmetry is **equally the crux restated from the other side**: the shared causal law requires inducers for changes and is silent on whether only changes need explanation. Neither side's asymmetry claim is independent evidence. | **No new item.** Onset is shared, conditionally: it is accepted by an inertialist who grants that the originating cause gives being at the first moment (control part 5). Schmid's causal requirement on change does not by itself fix that timing, since an inducer acting just before would also satisfy it. |
| Essence/esse union (ST I q.3 a.7, "quae secundum se diversa sunt, non conveniunt in aliquod unum nisi per aliquam causam adunantem"; claim `78cc9f45`, statement `58445bd6`, cited from the corpus's earlier reading, not re-read here) | **Analyst argument, not typed.** Read tenselessly, as `58445bd6` is ("something unites them into it"), it does not require the uniter to act at later moments; an originating cause of the union would satisfy it. `58445bd6` is not typed over histories, so no control checks this. Read synchronically ("at each moment of presence something unites them then"), uniting esse to its receiver at t is giving being at t on the STRICT reading of `158301bc`, and the premise is `40a97664` under another name. | No: the synchronic reading is the crux re-presented (AGENTS: different presentations of one assumption are not more evidence). No Lean statement was added, since it would be a renamed transcription of `ConcurrentlyActualized`. | Rejecting the synchronic reading is rejecting the crux once; it needs no further ground. | **No new item.** |
| De ente c.4 / ST I q.3 a.4: whatever belongs to a thing and is not from its essence is caused by another | **Analyst argument, not typed here.** The same fork as the union row: "is caused by another" read tenselessly is satisfied by an originating cause; read as "is being caused by another at each moment of its presence" it is `40a97664` restated with the reception bridge. The existing De ente material (`docs/notes/de-ente-*`) was not re-read for this question. | The tenseless reading is independent and is on the route as the reception bridge `da72ae93` and the De ente some-cause coverage step `d1f3ffcc`; the synchronic reading is not independent. | As for the union row. | **No new item** on the analysis given; a row to re-examine if a non-tenseless reading with independent warrant is identified. |
| C\* in the holding sense (`HoldingMotion`, unpushed branch) | **No**, as reported by that module's own control (part 3): C\* in the holding sense entails neither the respect-general premise `LackableActsAreHeld` nor its esse instance. Not checked here. | — | — | **No item.** If C\* reduces to concurrent actualization it rests on it (shape (b)). |
| Respect-general holding (`LackableActsAreHeld`, same branch): every lackable act is presently actualized by another | Reported there to give C\*. Its esse instance would give the strong `76d2cc96`, and so `40a97664`, if the instance is aligned with received esse. Not checked here. | Stronger, so not a re-presentation. | **Yes**, if velocity counts as a lackable act in the holding sense. In Newtonian and later mechanics a body keeps its velocity with nothing presently acting on it (the first law; momentum conservation). This is an independently justified objection to a respect-general continuation principle. The Thomist reply that uniform motion is a state, not a change, is the inertialist's own move. | **Low.** The rival can drop it with physics on its side. It shows that the sustaining case must be esse-specific, which `40a97664` already is. |
| Synchronic actualist explanation (presentism, plus "only what exists at t explains what exists at t") | **Analyst argument: no.** It forces *some* present explainer, and a presently holding law or a persistence power satisfies that; it does not force a giver. | — | Not needed, since it does not entail the crux. Note that presentism is itself contested, and a frame-relative "present" would bear equally on the sustaining side's simultaneity of giver and given. | **No item.** |

**Finding.** Among the candidates examined, none was found that is (i)
independently warranted, (ii) not a re-presentation of `40a97664`, and (iii)
shown to entail it. On that evidence the extrinsic inertialist's price at the
crux is **one item**: reject `40a97664` (equivalently parity given onset, or
the synchronic union principle). The respect-general holding principle entails
more, but the rival can reject it on independent physical grounds. The list is
not exhaustive. Only the onset/parity row is machine-checked; the union, De
ente and presentism rows rest on the readings argued above.

### (b) Routes resting on the crux (single points of failure, no added price)

Rejecting `40a97664` removes, through `366a6ea3`: `ce55210c`; the strong
sustaining reading `23e04ae5` (no independent warrant on file); the immensity
presence step `9469ab62` and the IMMENSE_2 → IMMENSE_1 route `8bf775e9`; and,
through §1, the new connection to `2068f91c` and hence the esse-root
identification at (maximum, root) along that connection. It also removes any
C\* route that reduces to concurrent actualization. The rival does not thereby
reject `2068f91c`'s direct option, the reception bridge `da72ae93`, contact
`c4661518`, onset (on the timing it grants) or the shared causal law. These are
losses to the case if the crux fails, not costs to the rival.

### The rival's own positive commitments

1. **Diachronic sufficiency for existence** (its distinctive primitive): prior
   actuality, absence of any inducer of cessation, and the causal law on change
   jointly suffice to explain a contingent thing's actuality at a later moment.
   Schmid accepts a PSR-like principle (closing edit, paragraph beginning "And
   this discovery especially helps") and denies only that the explanation must
   be a concurrent efficient cause.
2. **Coverage of existential loss by inducers** (shared): every existential
   loss has an inducing factor. `610e21dc` shows it is neutral.
3. **Sub-version costs, not costs of inertia as such.** (i) A Humean-law
   version explains a thing's persistence by a regularity that partly consists
   in that persistence. The explanatory-circularity objection to Humean laws
   (Armstrong 1983, *What is a Law of Nature?*; contested by Loewer 2012 and
   Hicks & van Elswyk 2015; none pinned here) bears on that version only. A
   governing-law or primitive-law version avoids it at the price of a
   primitive law, matched by conservation's primitive standing dependence.
   (ii) A persistence-power version rejects concurrence `d7f5a528` and meets
   Feser's circularity reply (`05bc2722`, provisional), which targets a
   simultaneous self-giving power. A diachronic version (earlier stages cause
   later ones, immanent causation) is not on file and would need its own
   assessment. It is recorded here as an unexamined lead with no weight.
4. **Global scope** (shared): both accounts owe an account of the whole
   history's obtaining; neither is exempt (2026-11-17 section, unchanged).

## 3. The other candidate tests

- **Parity**: done in §2. No substantive objection to extrinsic inertia is
  identified from parity alone, and none to sustaining from the change-only
  asymmetry alone.
- **Is inertia's PSR variant stable?** Yes at local scope. The explanandum
  "S exists at m" receives a deductive explanation from S at m−1, no inducer,
  and the causal law. The negative fact is explained by the world's state, and
  the law is shared. No self-undermining was found. The difference from the
  conservation side is not the PSR but whether explanation of present actuality
  must be synchronic; that is the crux again.
- **Physics at matching scope.** For *esse* the physics is neutral.
  - Conservation laws (energy, charge, baryon number) describe what persists
    under the dynamics and derive from symmetries of the laws (Noether). Each
    account can absorb them: inertia as its law, conservation as the
    regularity of the giving.
  - Existential loss in physics always occurs through an interaction (decay,
    annihilation), which both accept.
  - Composite bound states depend counterfactually on present interactions.
    That is dependence on the constituents and the dynamical law, not on a
    giver, and it relocates to the fundamental constituents, whose persistence
    physics treats as lawful.

  For a *respect-general* continuation principle physics is not neutral:
  inertial motion tells against it (§2). At the esse scope the history of
  mechanics is an analogical precedent only.
- **Explanatory depth.** Conservation explains why x is actual now, beyond why
  x has not ceased. That is a gain only if present actuality is a genuine
  explanandum over and above continuation, which is the crux. At local scope
  inertia posits fewer standing relations (no giving after onset). It does not
  have fewer primitive principles, since diachronic sufficiency is its own
  primitive. Parsimony of posited relations is a weak, defeasible tie-breaker
  here and does not touch the global scope.

## 4. Overall provisional judgment (2026-11-19)

On the fixed meanings (STRICT `GivesAt`, inclusive presence, tenseless
`CausesIn`, DEF-DEPENDS-FOR-BEING), **no discriminating test is available at
matching scope; both accounts stand, with prices**. This restates, and does not
revise, the 2026-11-18 cluster judgment for `40a97664` and `ce55210c`. The
price map and the `2068f91c` connection are added on top of it.

- *Strongest warrant for sustaining:*
  - a coherent account in which a received act of being is a standing
    derivative actuality;
  - it unifies origin and persistence under one relation (giving);
  - it has positive explanatory content (why x is actual now);
  - the q.104 a.1 distinction of causes of becoming and of being;
  - no substantive objection to a genuinely identified instance of standing
    productive dependence.

  Price: `40a97664` as a primitive; concurrence `d7f5a528` (no warrant on
  file); reception `da72ae93`. For `2068f91c`, contact and the co-presence
  bridge are added, the bridge with an untyped coverage condition.
- *Strongest warrant for extrinsic inertia:*
  - the shared causal law on change plus prior actuality deductively yields
    persistence;
  - it is PSR-compatible;
  - locally it posits fewer standing relations;
  - the history of mechanics is an analogical precedent that continuation
    principles can fail for states (not matching-scope evidence at esse).

  Price, among the candidates examined: one item at the crux (reject
  `40a97664`; parity given onset and the synchronic union principle are
  re-presentations, not further items), plus its primitive of diachronic
  sufficiency for existence. Its Humean sub-version also carries the
  explanatory-circularity objection.
- `2068f91c` keeps its direct option. Its strong grade on the aligned
  sustaining reading comes from the lane F row, which is unmerged and
  unverified here. Newly, it has a typed connection through `ce55210c`,
  contact and `ffcb81fb`. That connection is a chain of transcriptions, and on
  it `2068f91c` is no better than `ce55210c` and the bridge's coverage
  condition.

**Revision conditions.** Any one of these would move the judgment:

- an independently warranted proposition, not a re-presentation of
  `40a97664`, that entails it (would add a price item);
- an independently justified account of why the present actuality of a
  received act is an explanandum distinct from its continuation (would favour
  sustaining), or of why only changes need explanation (would favour inertia);
- an independently supported case of a received-esse thing persisting with no
  giver, or of redundant givers of esse (would weaken `40a97664` or the bridge);
- a defensible diachronic persistence-power account (would strengthen the
  persistence-power rival);
- an assessment of history coverage for the bridge;
- an examination of the always-present-root route to `2068f91c` noted in §1.

**Next test.** The informative remaining question is the second revision
condition, at the reception premise. Is DEF-ESSE-RECEIVED-IN's "standing to it
as receiving potency to received act" a present-tense receipt or a historical
one? A present-tense receipt, with the correlativity of receiving and giving,
would make `40a97664` close to analytic and move the whole dispute to
`da72ae93`. Typing `ReceivesAt v z x t` and a correlativity premise would show
exactly where the dispute then sits. It needs no new source. (Run in §5. Half
the prediction holds: the derivation goes through. The other half fails: no
price moves onto `da72ae93`, and the tense question resolves into the crux.)

## 5. Present-tense receipt and correlativity (the §4 next test, done)

Module `TruthCore.Causality.PresentReceipt`, spec `specs/present-receipt.toml`,
attempt `50e08b09`. Analyst formulations, attribution deferred.

### Vocabulary

- **Present-tense receipt** `Receipt.ReceivesAt v z x t` (definition
  `506ea036`), an explicitly primitive relation: in history `v`, at `t`, the
  principle `z` is receiving `x`'s act of being. It is the time-indexed
  counterpart of the tenseless `EsseReceivedIn x z`. It names only the
  receiver side and contains no giver. No axiom ties it to `GivesAt`, so the
  unconstrained primitive is not definitionally `40a97664`: for a fixed
  interpretation (Control part 3, no receipt) `40a97664` is true and the
  present-tense reading false. That shows only that the primitive is an
  unconstrained parameter. With the interpretation quantified existentially,
  the present-tense reading plus correlativity is *equivalent* to `40a97664`
  (`someReceiptCarriesTheCrux` below).
- **Two defined senses** (disambiguation `71d3bdb7`, term `RECEIVES_ESSE_AT`):
  - RECEIVES_ESSE_AT_1, *passion* (`passionReceipt`, definition `ac8dbcaa`):
    `z` receives `x`'s esse at `t` iff the esse is received in `z` and
    something gives `x` being at `t`. In Lean this is a bare conjunction, and
    nothing ties the giving to `z`. The intended reading, which is not typed,
    is the patient's side of an occurrent giving, as the air is illumined
    while the sun illumines.
  - RECEIVES_ESSE_AT_2, *standing composition* (`standingReceipt`, definition
    `181bb18f`): `z` receives `x`'s esse at `t` iff the esse is received in `z`
    and `x` is present at `t`, as a vessel holds what was poured into it.

| Record | Lean | Content |
| --- | --- | --- |
| `964928dc` present-tense reading | `ReceptionIsPresent` | received in `z` and present at `t` ⇒ `z` receiving `x`'s esse at `t` |
| `db441b19` onset reading | `ReceptionAtOnset` | received in `z` ⇒ `z` receiving `x`'s esse at a first moment of presence |
| `52b05849` correlativity | `ReceivingIsCorrelativeWithGiving` | receiving `x`'s esse at `t` ⇒ something gives `x` being at `t` |
| `7c62adb5` | `concurrentOfPresentReceipt` | present-tense + correlativity ⊢ `40a97664` (transcription) |
| `2371b373` | `onsetOfOnsetReceipt` | onset + correlativity ⊢ received onset is given `fa3e228b` (transcription) |
| `62947463` | `onsetOfPresentReceipt` | present-tense ⊢ onset (strength order, relation `13c900b6`; single application) |
| `1d52b8f0` | `passionReadingIsTheCrux` | on RECEIVES_ESSE_AT_1: correlativity holds, and present-tense ⇔ `40a97664` |
| `1d91d067` | `standingReadingIsTheCrux` | on RECEIVES_ESSE_AT_2: present-tense holds, and correlativity ⇔ `40a97664` |
| `624967d8` | `someReceiptCarriesTheCrux` | (∃ receipt, present-tense ∧ correlativity) ⇔ `40a97664` |
| `45b3c73b` | `controls` | parts 1–6 below |

The three closed results quantify over every history, giving relation and
reception predicate. The two derivations are transcriptions in the sense of
invariant 16 (the last step applies correlativity), and the strength-order
registration is a single application. The work that is not a transcription is
in the controls and the three closed results.

*Controls* (`PresentReceipt.Control.Certificate`; `false` alone has received
esse; the histories are those of `SustainingCausation.Control`):

1. Inertia with past-tense receipt (receipt at time 1 only): onset reading,
   correlativity and received onset hold; the present-tense reading and
   `40a97664` fail.
2. Inertia with standing receipt: the present-tense and onset readings hold;
   correlativity and `40a97664` fail.
3. Sustaining with no receipt: `40a97664` and correlativity hold; the
   present-tense and onset readings fail.
4. and 5. Each premise of the onset derivation is needed.
6. Everything holds together.

### Outcome of the test

**The derivation holds**: present-tense reading + correlativity ⊢ `40a97664`,
and each premise is needed (parts 1 and 2). For a fixed receipt
interpretation the pair is strictly stronger than `40a97664` (part 3). With
the interpretation left open it is equivalent to `40a97664`
(`someReceiptCarriesTheCrux`): the pair can say more than the crux only
through a fixed reading of receipt.

**But no price moves onto `da72ae93`.** In parts 1 and 2 `EsseReceivedIn`
holds of `false` while `40a97664` fails. So the inertialist keeps reception and
need not reject `da72ae93`'s consequent. (These controls type no `CausesIn`;
the bridge itself holds on the inertial history in `ConcurrentActualization`
Control part 1.) The tense question that `da72ae93`'s sources raise (§2, row 3)
is not dissolved. It is carried by the present-tense reading, and three
checked facts show that on each defined sense it resolves into the crux:

1. **Correlativity alone does not decide between the sides.** With the onset
   reading in place of the present-tense reading, correlativity yields only
   `fa3e228b`, which the inertialist grants. Part 1 is the inertialist's
   profile with correlativity true. The whole difference between the two
   conclusions is the difference between the present-tense and the onset
   reading.
2. **On the passion sense** correlativity is true by definition and the
   present-tense reading is equivalent to `40a97664` (`1d52b8f0`).
3. **On the standing sense** the present-tense reading is true by definition
   and correlativity is equivalent to `40a97664` (`1d91d067`). Part 2 is an
   inertialist who grants present-tense standing receipt and denies
   correlativity.

So on each defined sense exactly one of the two premises is `40a97664`
restated, and the other is trivial. The tense that matters is that of
`EsseReceivedIn` read through `ReceivesAt`. On the defined senses it is not an
independent question: it is the crux.

### Tense assessment

*Present tense, standing sense: "x has esse as received, at each t".*

- **Strongest positive warrant.** DEF-ESSE-RECEIVED-IN defines the relation as
  a principle that "stands to it as receiving potency to received act". That
  is a structural relation of the composite, not an event. If a thing's
  essence/esse composition is real at all, it obtains whenever the thing
  does: a received-esse thing does not stop being composite after its first
  moment. This is good warrant, and it is independent of `40a97664`.
- **It is no item in inertia's price.** The inertialist can grant it, and
  part 2 does. On this sense the crux sits wholly in correlativity, which
  then says that a standing receptive composition needs a present giver. That
  is the synchronic reading of the union principle (§2, row 2), already
  classified as the crux re-presented.

*Present tense, passion sense: "x is being given esse, at each t".*

- **Strongest positive warrant.** Three candidates, none of which reaches
  `40a97664` on independent warrant:
  - The illumination profile (q.104 a.1, read; claims `40aefb2e`, `da9c82ed`).
    Carrying it from light to esse presupposes the crux, as recorded at
    `40a97664`.
  - The actualization principle extended to non-changes: continuing in a
    received act is a potency being actualized at each moment. That is the
    second thesis bundled in `40a97664` (ConcurrentActualization module
    doc), which the rival denies.
  - The thesis that creation taken passively is a relation in the creature to
    the creator as principle of its being (ST I q.45 a.3). It is **not read
    here**, so it is recorded as a lead with no weight. On a relational
    reading it would at most give that the term of the relation is present,
    not that it gives. That would bear on the co-presence bridge `ffcb81fb`,
    not on `40a97664`.
- On this sense the present-tense reading is equivalent to `40a97664` (`1d52b8f0`), so it
  has no warrant beyond that of `40a97664`.

*Past tense: "x received esse at onset".*

- **Strongest positive warrant.**
  - Ordinary use of "received". A gift or a form once received is had after
    the giving ends. q.104 a.1 grants this profile for causes of becoming:
    the house stands after the builder leaves. But carrying the becoming
    profile to esse presupposes the rival, just as carrying the illumination
    profile presupposes the crux, and q.104 a.1 itself uses the house to
    contrast causes of becoming with causes of being.
  - `da72ae93` as typed is tenseless. Its sources (De ente c.4 "recipit ab
    alio", q.7 a.2) admit a tenseless reading, which an onset receipt
    satisfies, and a synchronic reading, which is `40a97664` restated (§2,
    rows 2–3; "recipit" is grammatically present). The tenseless reading is a
    reading choice, not a fact about the texts, and the De ente material was
    not re-read for this question.
  - The onset reading together with correlativity gives exactly the onset
    fact an inertialist can grant (`2371b373`, part 1).
- **Its limit.** The onset reading is weaker than the present-tense reading
  and is entailed by it, so it is not a rival premise. The past-tense reading
  *proper*, that receipt in the passion sense stops after onset, is the
  denial of `40a97664` on that sense, and it gains no warrant beyond the
  rival's.

**What the inertia rival must deny.** On the primitive it must deny either
the present-tense reading or correlativity, by `7c62adb5` and its rejection
of `40a97664`; parts 1 and 2 exhibit the two positions. Which one
depends on the sense of receipt: on the passion sense it denies the
present-tense reading, on the standing sense correlativity. On each sense
that is `40a97664` itself (`1d52b8f0`, `1d91d067`). So the price is **one
item, unchanged**. The present-tense reading is recorded as **the crux
restated, not a new price item**. It has independent warrant only in the
standing sense, where the inertialist accepts it at no cost.

**Judgment.** This confirms the §4 judgment, and §4 is not revised. The test
removes one candidate source of a second price item: the reception premise,
read in either defined tense-sense, does not entail `40a97664` without a
premise that is `40a97664` restated.

**Revision condition.** The judgment would change given a further reading of
present receipt, defined and typed, that meets both conditions:

- receipt carries content beyond reception plus presence. For any receipt
  implied by standing receipt the present-tense reading is trivial, and
  correlativity alone then entails `40a97664`.
- On that reading, correlativity has warrant independent of `40a97664`, and
  is not definitional as it is for passion.

The relational reading suggested by q.45 a.3 is the one candidate in view;
§6 reads it and tests it.

## 6. Receipt as a real relation to the principle of being (the §5 next test, done)

Module `TruthCore.Causality.RelationalReceipt`, spec
`specs/relational-receipt.toml`, attempt `c97afe42`. Analyst formulations,
attribution deferred: the texts below were read in their pinned witnesses, but
no claim is recorded, because the Lean relation is indexed to moments and the
texts do not index the creature's relation to moments.

### The texts (read)

**ST I q.45 a.3**, "utrum creatio sit aliquid in creatura". Passage
`fb7bd7bb`, newly pinned: the SCTA Leonine transcription, same repository and
revision as q.44 and q.46. The objections, sed contra, corpus and ad 1–3 were
read.

- *co.* Creation produces things without motion. With motion taken away from
  action and passion, only relation remains. So "creatio in creatura non sit
  nisi relatio quaedam ad Creatorem, ut ad principium sui esse", "sicut in
  passione quae est cum motu, importatur relatio ad principium motus". The
  analogue is the relation to the principle of motion that a passion with
  motion imports, not the passion itself.
- *ad 1.* The creature's relation to God is real. God's relation to the
  creature is of reason only.
- *ad 2.* "Creatio passive accepta est in creatura, et est creatura." The
  relation needs no further relation to refer it.
- *ad 3.* As a change, creation has the creature as its term. As a relation,
  creation has the creature as its *subject*, and the creature is prior to it
  in being, as a subject is to an accident. "Sed habet quandam rationem
  prioritatis ex parte obiecti ad quod dicitur, quod est principium
  creaturae." Then: "Neque tamen oportet quod, quandiu creatura sit, dicatur
  creari: quia creatio importat habitudinem creaturae ad creatorem cum quadam
  novitate seu incoeptione."
  - This denies the *name* "creari" after onset, not the relation.
  - It plausibly implies that the habitude remains without the novelty. That
    is an implicature, not a statement.
- *obj. 3* holds that when the term of an action exists, action and passion
  cease ("eo existente cessat actio et passio"). Ad 3 does not dispute this
  for creation taken as a change. It moves what remains in the creature to
  the relation.

**ST I q.13 a.7.** Passage `12d8ecc5`, newly pinned in the same SCTA file as
q.13 a.5 and a.8. Read in full.

- *co.* Relations come in three classes:
  1. *Of reason on both sides.* This includes every relation of a thing to
     itself ("idem eidem idem") and every relation between a being and a
     non-being, "quas format ratio".
  2. *Real on both sides*, "secundum aliquid realiter conveniens utrique".
     This includes relations that follow quantity and relations "quae
     consequuntur actionem et passionem, ut motivum et mobile, pater et
     filius".
  3. *Real in one extreme and of reason in the other*, "quandocumque duo
     extrema non sunt unius ordinis". The examples are knowledge and sense
     toward the knowable and the sensible.

  The creature's relation to God is in the third class: "omnes creaturae
  ordinentur ad ipsum, et non e converso".
- *ad 6.* Whether two relatives are simultaneous by nature is settled by
  their significations. "Dominus" and "servus" are simultaneous by nature, so
  God was not Lord before he had a creature subject to him.
  - Ad 6 is silent on whether a real relation's term must exist while the
    relation is borne.
  - Its example of a knowable that pre-exists knowledge concerns a term
    without the relation, not a relation without its term.

**ST I q.104 a.1** (re-read). The corpus and ad 2 argue from the
cause-of-being versus cause-of-becoming distinction and the illumination
profile. Ad 4 says that preservation is "a continuation of that action
whereby He gives existence". This is the text that states the crux. §2 and
§5 record why carrying the profile from light to esse presupposes it.

### Vocabulary

- **Origin relation** `OriginRelation.RelatedAt v x g t` (definition
  `7b28be97`), an explicitly primitive relation. In history `v`, at `t`, `x`
  bears a real relation to `g` as to the principle of its being. It names no
  action of `g`.
- **Irreflexivity** and **non-mutuality** (`Irreflexive`, `NonMutual`). These
  type the structural part of q.13 a.7: a relation of a thing to itself is of
  reason, and the creature's relation is real in the creature only.
- **RECEIVES_ESSE_AT_3**, *relational receipt* (`relationalReceipt`,
  definition `2a7f7142`). It is standing receipt plus "`x` bears the origin
  relation at `t` to something", and it is appended to disambiguation
  `71d3bdb7`. It carries content beyond reception plus presence: a term.

| Record | Lean | Content |
| --- | --- | --- |
| `ef7ef827` foundation | `FoundedOnReceivedEsse` | bearing the relation at `t` ⇒ received esse and present at `t` (a necessary condition suggested by q.45 a.3 ad 3; the priority is not typed) |
| `9fecbef4` accompaniment | `RelationAccompaniesEsse` | received esse and present at `t` ⇒ bears the relation to something at `t` |
| `264b6b5e` coexistence of the term | `TermCoexists` | term of the relation at `t` is present at `t` |
| `6da7d94a` giving by the term | `TermGives` | term of the relation at `t` gives the bearer being at `t` |
| `a0b5227d` | `concurrentOfTermGiving` | accompaniment + giving by the term ⊢ `40a97664` (transcription) |
| `42590821` | `relationalPresentIsAccompaniment` | on RECEIVES_ESSE_AT_3: present-tense reading ⇔ accompaniment |
| `1637b89a` | `relationalReadingIsTheCrux` | on RECEIVES_ESSE_AT_3, given accompaniment: correlativity ⇔ `40a97664` |
| `b5e9b376` | `someRelationCarriesTheCrux` | (∃ founded, accompanying relation with a giving term) ⇔ `40a97664` |
| `b9920133` | `coexistentTermDoesNotCarryTheCrux` | foundation + irreflexivity + non-mutuality + accompaniment + coexistence of the term + received onset given ⊬ `40a97664` |
| `584bac58` | `controls` | parts 1–5 below |

*Controls* (`RelationalReceipt.Control.Certificate`; `false` alone has received
esse; histories and givings of `SustainingCausation.Control` and
`ConcurrentActualization.Control`):

1. *A creator present throughout who gives being at onset only*, with the
   relation persisting. The giving is at time 1 and `true` is always present.
   - Hold: foundation, irreflexivity, non-mutuality, accompaniment,
     coexistence of the term, received onset given, and the relational
     present-tense reading.
   - Fail: giving by the term, relational correlativity and `40a97664`.
2. *The same, with the relation at onset only.* This is an analyst variant.
   It is not a model of q.45 a.3 ad 3, which denies the name after onset, not
   the relation.
   - Hold: giving by the term and relational correlativity.
   - Fail: accompaniment and `40a97664`.
3. *Term absent after onset, relation persisting.* Coexistence of the term
   fails, so a relation to a term that has ceased is excluded.
4. *Sustaining with the relation persisting*: everything holds.
5. *Another giver.* The thing gives itself being from time 1 on, and its
   relation to `true` persists. `40a97664` holds and giving by the term
   fails. So for a fixed relation, giving by the term is strictly stronger
   than `40a97664` requires.

`truth countermodel` does not support structure-typed parameters such as
`History`, so the controls are hand-built and checked by Lean.

### Outcome of the test

**Correlativity gains independently warranted structure, but not enough.**
The relational reading types three features of the creature's relation that
have warrant from q.13 a.7 independent of `40a97664`:

- an existing term (relations to a non-being are of reason);
- no relation of a thing to itself;
- real in the creature only.

These features, together with foundation, accompaniment and a given onset,
do **not** entail `40a97664` (`b9920133`, part 1).

What would suffice, with accompaniment, is giving by the term
(`a0b5227d`). It is not shown to be the minimal addition. It is sufficient,
and for a fixed relation it is strictly stronger than `40a97664`, because it
also makes the giver the related term (part 5). Two results tie the relational
reading to the crux:

- Given accompaniment, relational *correlativity* (some giver at the moment)
  is equivalent to `40a97664` (`1637b89a`), as on the standing sense.
- With the relation left open, accompaniment plus giving by the term is
  equivalent to `40a97664` (`b5e9b376`).

**Each premise, priced:**

- *Foundation.* Suggested by q.45 a.3 ad 3. Both sides grant it.
- *Accompaniment.* The theist inertialist grants it, keeping the creature's
  relation to a creator who exists throughout (part 1). The sustaining side
  grants it too. q.45 a.3 ad 3 gives it some support by implicature.
- *Coexistence of the term, irreflexivity, non-mutuality.* These have
  independent warrant from q.13 a.7.
  - They are cheap for the theist inertialist.
  - Coexistence costs only the variant in which the relation outlives its
    term (part 3).
- *Giving by the term.* This is the sufficient addition. It is stronger than
  `40a97664` for a fixed relation. Its rejection is part of what the theist
  inertialist who grants accompaniment must hold, since that inertialist
  rejects `40a97664`.

**The rival mechanism and the sustaining reply: a standoff** (Substantive
Objection Standard, applied to both).

- *Rival:*
  - *Target:* giving by the term.
  - *Mechanism:* the creature's relation persists, like filiation, with its
    term existing and no present action.
  - *Support:* q.13 a.7 co. lists "pater et filius" among real relations that
    follow on action and passion. Ordinary use has filiation outlast the
    begetting while the father lives; this is not stated in the passage.
  - *Limits:*
    - That example is a relation of the second class (real on both sides),
      and q.13 a.7 places the creature's relation in the third.
    - The father is q.104 a.1's own paradigm of a cause of *becoming* ("man
      begets man").
    - So modelling the creature's relation on filiation carries the becoming
      profile to esse. §5 records that this presupposes the rival.
  - *Unread material that would strengthen it:* Metaph. Δ15 1021a21–26 and
    Aquinas, In V Metaph. lect. 17, divide relations by action according to
    time (having acted, having been acted on). It was not read and carries no
    weight here.
- *Sustaining reply:*
  - *Mechanism:* a relation to a cause of being, as against a cause of
    becoming, holds only while the cause acts (q.104 a.1).
  - *Limit:* that is the illumination profile carried to esse, which
    presupposes `40a97664` (§2, §5).
  - *Textual pointer:* q.45 a.3 co.'s analogy is the relation to the
    principle of motion imported in a passion with motion, the mover–moved
    relation. That points toward the present-action profile. But a textual
    pointer attributes the crux to Aquinas; it is not independent warrant
    for it.
- *Result:* each side carries a causal profile to esse, and each profile
  presupposes its own side. Neither mechanism has independent justification
  that the other lacks.
- *The dead-father variant fails on the text.* A real relation to a father
  who has ceased would be a relation to a non-being, which q.13 a.7 makes a
  relation of reason. Coexistence of the term excludes it (part 3). The rival
  does not need it.

**Classification.** On the relational sense, given accompaniment,
correlativity is equivalent to `40a97664` (`1637b89a`). The independently
warranted structure that the relation adds does not reach giving
(`b9920133`). So this reading adds no item to inertia's price, and §4
stands.

**Branch reassessment, not exhaustion.** Three readings of present receipt
are now typed and characterised:

- passion: the present-tense reading is equivalent to the crux;
- standing composition: correlativity is equivalent to the crux;
- relation with an existing, distinct, non-mutual term: correlativity is
  equivalent to the crux given accompaniment, and the typed structure is too
  weak.

No general result excludes a further reading. The §5 observation, that any
receipt implied by standing receipt makes correlativity alone carry the crux,
covers only receipts *weaker* than standing receipt, and every reading with
added content is stronger. Two vertical readings remain in view, both untyped:

1. *The third-class reading* (ordination, or dependence as measured on
   measure), which is q.13 a.7's own classification of this relation.
   - Its exemplar, knowledge toward the knowable, does not involve the
     knowable acting on the knowledge while the relation is borne.
   - So on the analogy as it stands it does not point toward giving at the
     moment.
   - It is untested whether ordination to a principle *of esse* carries more.
2. *The priority on the side of the term* (q.45 a.3 ad 3: the relation "habet
   quandam rationem prioritatis ex parte obiecti"). It is untested whether
   any typed reading of that priority exceeds coexistence without restating
   giving.

**Side finding on the co-presence bridge `ffcb81fb`.** Accompaniment and
coexistence of the term give only this: a received-esse thing present at `t`
has *some* term present at `t`. The antecedent of `ffcb81fb` needs a single
tenseless cause of esse, distinct from its effect, present whenever its
effect is, in every history. That needs:

- the same term at every moment;
- a term that is a `CausesIn` cause;
- coverage of every history.

Irreflexivity gives distinctness from the effect, but none of the three is
typed. No premise moves. This is a lead, not a connection.

**What would still discriminate.**

Vertical:

- the two untyped readings above.

Horizontal (another lane may take these):

1. An argument from another family that persistence at `t` needs an
   explanation *at* `t` and not only at onset. Candidates are a PSR variant
   for persistence and the contingency family's explanation of a thing's
   existing now. Each must avoid the illumination analogy and the extended
   actualization principle.
2. An account of esse as received act in the participation family (q.104 a.1
   "every creature has being by participation"; De ente c.4) on which
   participated act is not a completed terminus. It counts only if its
   warrant does not already assume `40a97664`.
3. A comparison at matching scope of inertia's positive commitments, that
   persistence needs no cause and conservation laws, against the sustaining
   account, as explanations of the same persistence data.

**Revision condition.** The judgment changes given a typed,
independently warranted premise about relations to a cause of esse, from the
third-class reading, the term-side priority or elsewhere, that entails giving
at the moment without the illumination or actualization premises. Or it
changes given one of the horizontal tests above.

## Self-sweep

The claim-vs-type table for every new record is in the PR body. No source
claim is added. Schmid, Feser and q.104/q.3 are cited only through records
already read and pinned or recorded in the corpus; §5 cites ST I q.45 a.3 and
Physics III.3 (in definition `ac8dbcaa`) as unread leads with no weight. No
objection above is
presented as evidence unless its target, mechanism and independent
justification are named. The diachronic persistence-power account and the
Humean-law literature are labelled as leads or sub-version costs.

§6 adds passages `fb7bd7bb` (ST I q.45 a.3) and `12d8ecc5` (ST I q.13 a.7),
pinned in the admitted SCTA witness and read, and adds no claim. Its readings
of them are reported with locators and are not attributed as statements.
De ente c.4, the PSR variants, Metaph. Δ15 and In V Metaph. lect. 17 are
named only as unread leads or next tests, with no weight.
That filiation lasts after the begetting is marked as ordinary use, not as
text.

## 7. Why an entire populated history obtains: the replaceable-anchor test (#1801, 2026-11-19)

**Target and connection.** This is a separate *ultimate-explanatory-scope* test
of the law-based alternative to `40a97664`, the weak per-moment `GivesAt`
premise. Its consumer `366a6ea3` supports `ce55210c`, in turn used in the
esse-dependence route to `2068f91c` and ultimately the God-existence stage of
#143. The test concerns the actuality of a complete temporal existence
profile, not a proof of a present giver or an inference from God's name to
existence. The previously recorded **local standoff** in §4 is unchanged.

### Exact existential question and a positive local success

Let `x` be one rigidly designated possible substantial bearer, `b ≠ x` an
independently populated background bearer, and times the integers. Write
`Eₓ(t)` for *x exists at t* (not merely has a state at t), `N(s,t)` for no
destructive inducer against x between s and t, and stipulate:

* `P`: for all s < t, `Eₓ(s) ∧ N(s,t) → Eₓ(t)` (one-way existential
  persistence). This is the inertialist's proposed positive local inference,
  **without** its further independence-from-giver claim.
* `H₊`: b exists at all dates, x exists at all dates, no destructive inducer.
* `H₀`: b exists at all dates, x never exists, no destructive inducer.

Both populated histories satisfy `P`. They differ in the positive actuality
fact `Aₓ := ∃t Eₓ(t)`. **They do not agree on an earlier actuality of x.** In
`H₊`, `Eₓ(s)` really does license `Eₓ(t)` for later t by `P` and `N`; `H₀` is
no counterexample to that valid conditional because it lacks its antecedent.
This witnesses only non-entailment of `Aₓ` by `P` and these stipulated
background conditions, **not** metaphysical accessibility of `H₀`, a law for
real received esse, or absence of an actual giver. The two-populated-history
comparison was already reported in #1801; its novelty is **not** a second
history-selection theorem.

For the sharper new test, strengthen `P` expressly to a reversible,
date-independent law `R`: `Eₓ(t) ↔ Eₓ(t+1)` for every integer t. This is **not**
part of existential inertia: its backward direction excludes *any* transition
from nonexistence to existence, whether caused or not, and is a stronger
whole-history restriction. Encode E as a
Bool-valued existence trace `f : Int → Bool`; `R` says
`f (t+1) = f t`. The already verified
`TruthCore.Results.Explanation.PathRelocation.constant_of_stationary`
proves `∀t, f t = f 0`. Consequently, under `R`:

1. `Aₓ` is logically equivalent to `∀t Eₓ(t)`; the single *existential*
   actuality input selects the globally populated x-profile.
2. For **any** date s, `Eₓ(s)` plus `R` determines the complete x-profile;
   one might use any such anchor instead of another. No date is ontically
   privileged by this proof. By itself `R` still admits both constant-true
   and constant-false x-profiles, each together with the ever-present b.
3. Conversely the absence of `Aₓ` yields the never-present x-profile. No
   particular `Eₓ(s)` is *uniquely required as the chosen proof premise*:
   any actual stage substitutes for it. This does **not** show that an actual
   stage is counterfactually dispensable while the same reversible law and
   populated outcome are held fixed—those conditions entail every stage.

The simple proof is finite forward/backward iteration from any s, or the
reused `constant_of_stationary` specialization. It does not require a first
time, a step performed infinitely often, a well-founded grounding graph,
an extra aggregate object, or an inference from temporal precedence to
metaphysical priority. Its positive content is the **quantifier distinction**:
replacing every *particular* anchor still leaves the common positive premise
`∃t Eₓ(t)`; the local law does not supply that premise. This result is an
**analyst application of a previously certified theorem**, not a new Lean
certificate, a proof of real-world lawhood, or a refutation of the wider
inertialist package. #736 already establishes the stronger whole-vector
**entailing** discriminator; #753 already certifies unprivileged dated pins.
Neither result asserts a metaphysical ground for the actual profile.

Finite histories show the same scope difference with an explicit first
condition: `P + Eₓ(first)` explains subsequent non-cessation given `N`, but
does not thereby explain the actuality of the first condition. With no first
moment there is no first-condition debt; instead the analogous explanandum
is `Aₓ`—*why is there an instantiated x at any date?* If temporal order is
eternalist, all dates' existence facts may be equally real while causal
dependence is asymmetric; equal reality alone proves neither production nor
ontological independence. For a **one-way** `P` an anchor determines only
later survival, not x's whole earlier profile. Do not silently use the
reversible control as a theorem about `P`.

The ordinary distinction between “why did this house remain standing?”
(no demolition, given its prior existence) and “why was there a house at all?”
(some positive building or other existence account) motivates asking `Aₓ`
independently of persistence. It does **not** demonstrate that every such
question must have a metaphysical answer or that the house's physically
historical origin generalizes to a beginningless received-esse substance.

### A potential non-question-begging completeness demand, and its limit

One additional **conditional** standard has positive explanatory motivation:

> **No unaccounted indispensable actuality input.** If an account claims to
> *completely and non-circularly explain why Aₓ obtains*, and its explanation
> essentially uses some positive existential condition that already implies
> Aₓ, then it must explain that condition within the claimed scope (or
> defend an independently intelligible holistic/non-well-founded explanatory
> role for the whole package). Otherwise its advertised completeness exceeds
> what its explanation supplies.

This is weaker than demanding a necessitating explanation of every fact, an
external efficient cause, a well-founded grounding order, a first moment, or
the necessity of God. It is motivated by an ordinary causal-scope example:
friction explains a match's ignition, and ignition explains a later flame.
The ignition can legitimately be necessary to the explanation of the flame
even though ignition is one part of the larger episode. A full account of
*both* can explain ignition by friction as well; stopping at “ignition
explains flame” would instead leave ignition unaccounted for at that larger
scope. The example supports an explanatory bookkeeping norm, **not** its
universal metaphysical application. It would be too strong to ban *every*
constituent of a complex explanandum from every intermediate causal
explanans; in the match case that would reject an ordinary, non-circular
multi-step explanation. A proposed stronger `causa sine qua non` condition
requires scrutiny of exactly what is necessary *for the full account* and
whether the ingredient itself receives an explanation. Rota (2007) and the
Pruss (2009) boundary-value discussion are leads for a separately pinned
source inquiry, **not claims newly attributed or treated as verified here**.

The local law can be a **complete explanation of each later occurrence
conditional on earlier actuality** while failing this proposed standard for
the actuality `Aₓ` if the law plus a selected anchor is offered as the whole
ultimate answer. But accepting that `Aₓ` demands a further ultimate answer
is a separate and contested premise. A memberwise or explanatory-holist rival
may treat the complete non-well-founded network, with no ontically preferred
member, as explanatory *without* a further question. It then owes an account
of its explanatory role, but has not been shown inconsistent or self-causing:
the graph of integer predecessor edges is irreflexive and acyclic even though
it is not well-founded. This is **not** a deduction that every satisfactory
explanation must have an externally sourced ingredient. In particular, an
entailing selector is not required for a real probabilistic, intentional or
other nonnecessitating explanation of `Aₓ`; #736's positive-weight control
already records that formal limit.

### Three distinct law explanations and a matched sustaining comparison

| Actuality proposal | What is positively explained | What is still owed for a *complete* answer to `Aₓ` |
| --- | --- | --- |
| **Humean history-summary law.** Lawhood obtains in virtue of patterns in the actual mosaic. | Scientific unification/prediction; with earlier x it may explain later x on a scientific level. | If one and the **same fact D** (e.g. the exact H fact) grounds the lawhood fact L *and* L is offered as metaphysically grounding **D itself** in the same asymmetric grounding relation, a forbidden ground-cycle follows. `Aₓ` grounding L while L grounds a larger H is **not** that cycle without a further bridge back from H to `Aₓ`. The law's dependence on that **identical** target fact must be demonstrated. Part-to-whole membership, Humean supervenience, and scientific explanatory usefulness alone do not show it. If L depends only on other facts, or explanation is scientific rather than grounding, the strict cycle is not established. |
| **Governing law / independent constraint.** A primitive restriction can govern complete possibilities, even without temporal production; it may be paired with actual basic matter. | Which histories comply and, if it independently requires some instantiation, why `Aₓ` is secured or favored. | A merely conditional persistence rule like `P` or `R` does not instantiate x. A richer constraint might necessitate or nonnecessitatingly support `Aₓ`; test its actual ontic meaning, independently motivated constraint content and application to *received esse*. A primitive actual matter + laws package may instead openly take `Aₓ` as a primitive. Its primitiveness is not a refutation. |
| **Real bearer powers/natures.** Actual x has dispositions which secure continuation under appropriate conditions. | Conditional behavior of already actual x; if immanent causation is defended, genuine diachronic activity rather than a Humean summary. | A token disposition whose being presupposes actual x cannot by that fact alone independently account for x's initial or beginningless instantiation; a nature/essence with independently warranted intrinsic existential sufficiency could be different. Do not assume powers' existence is metaphysically grounded in x's existence just from co-instantiation, or treat every immanent cause as efficient self-creation. |

The strongest live competitor is therefore the **governing-law-plus-ontology**
package described in the #1801 Chen–Goldstein research comment, along with
the holist's memberwise completeness reply. These supply positive replacement
answers, not mere denial. Equally, a proposed necessary or nonnecessitating
productive **source** of x's complete history could explain `Aₓ`, but cannot
be credited just for the name “God”. It needs an independently characterized
actual source, a genuinely productive same-bearer/esse bridge, and (if its
decree, power or explanatory action depends on this very H) a reply to the
**same** no-unaccounted-input test. On the currently selected weak premise,
`GivesAt` permits intrinsic or varying givers; eliminating an **external**
sustainer would not refute `40a97664`. A timeless source is not automatically
one actual concurrent giver at every t, and an ontological ground is not yet
strict esse-giving. #1800 retains the separate temporal-content bridge.

### Finding, assessment, rejected paths and revision conditions

**Checked status.** The reusable `constant_of_stationary` and #736/#753
certificates are verified at their existing formal types. The specialization
to x's *substantial existence* and the completeness norm are **analyst
interpretations** without a new Lean, source, or corpus claim. The two
Bool-presence histories are structural surrogates, not complete metaphysical
worlds or a concrete independent test of existential inertia. The actual
supplement to #736 is the explicit distinction between a **replaceable dated
anchor** and the shared existential precondition `Aₓ`, combined with a
non-entailing, same-fact explanatory adequacy audit.

**Overall provisional judgment (2026-11-19, base `ed7558145`).** A local
earlier-existence/no-destruction explanation is a coherent positive success;
beginninglessness and eternalism do not erase it. The isolated persistence
rule does not **entail** the complete populated x-profile's actuality, because
`Aₓ` is not its consequence; neither that failure of entailment nor an
unanswered further question proves that the rule supplies *no* nonnecessitating
or holistic explanation. This supplies a *specific conditional pressure* on a
claim of **non-circular ultimate ontological completeness**, not an independent
victory for sustaining causation. The strength of the global
pressure depends on warrant for the completeness norm and the rival's exact
global package. A genuinely independent primitive-law/ontology or holistic
account still stands; neither side has shown why its own fundamental actuality
obtains under a criterion agreed by both. No new independent price item on
inertia at `40a97664`, no `2068f91c` discharge, no new necessary-being or
God-existence support, and no change to §4's local relative judgment.

**Rejected as unsupported lifts:** (i) local explanation therefore excludes
a concurrent giver; (ii) a beginningless series necessarily lacks an
explanation; (iii) the absence of a first time entails the absence or presence
of an ontic foundation; (iv) temporal earlier-than entails metaphysical
grounding; (v) any law with multiple models fails to explain; (vi) every
Humean law circularly grounds each of its token outcomes; (vii) an ultimate
answer must entail one history; (viii) a strict ban on subfacts being needed
in *any* explanation of a complex fact; (ix) a necessary source automatically
produces temporal content or strictly gives it esse. None follows from the
certificates, and the positive rivals above block any elimination by labeling.

**Next discriminating test / reopening condition.** Pin and read the
Rota/Pruss source pair before any new attribution; test the strongest
non-question-begging subfact/sine-qua-non criterion against the match-style
mixed internal/external account and a genuine non-well-founded holistic
explanation *of the same positive `Aₓ`*. Independently specify a primitive
governing constraint with actual existential scope, and ask whether it
accounts for `Aₓ` without just copying `Aₓ` into a “law”; hold the sustaining
proposal to the identical test on the actual source and source-to-esse
bridge. If a supported norm forces non-circular existential coverage and a
live rival demonstrably violates it, the comparative judgment could change.
If a non-WF, primitive-law or probabilistic account meets that norm at the
same scope, the claimed ultimate gap would narrow. None of these tests is a
requisite source campaign for already established local laws.

**§7 claim/type self-sweep.** `P` and `R` are distinct stipulations; only
`R` inherits `constant_of_stationary`. Boolean presence of one rigid x is a
structural surrogate, not `ConcurrentActualization.GivesAt`, a world-level
`SameHistory`, an actual concrete bearer, or a genuine candidate-world
accessibility proof. `Aₓ` is existential quantification over that same x's
times, not an extra aggregate existent. The strict circle uses the *identical*
grounding relation and identical fact D in both directions; the optional
completeness norm is a normative premise, not a Lean theorem. Historical
source claims and passage records added: **none**; the Rota/Pruss leads are
not newly attributed. Existing proof records and root premises remain
unchanged. The added attempt is the record of this analyst test, not a new
supporting inference or a claim to historical fidelity.


## 8. C3 at an actual world: grounded, ungrounded and sustained controls (2026-11-23)

**Scope.** C3 concerns a bearer with *presently derivative* actuality, not merely
a contingent bearer; the proposed conclusion is an appropriately present
productive actualizer. The present test reuses the original
`CausesIn`/`GivesAt`/received-esse relations, the selected
`ActualConcreteGround` from the God-route profile, and the shared
`CausalityFrame`. It is a new **structural model comparison**, not a
new derived source of metaphysical warrant. It neither modifies the
`40a97664` bridge nor discharges `cb1cdea9`.

**Labels.** In this section *C3* means weak concurrent actualization,
`40a97664` (whatever has received esse is given being by something whenever
it is present), together with its proposed strict-present-actualizer
conclusion. The C1 note (`unique-feedback-explanation-311.md`, "C1 with C2
and C3") reads the labels differently: there C2 is "the underived source
exists necessarily" and C3 is "the source is one". Those readings are not
used here. Where the bullets under "Cumulative impact" below name C2, they
mean the C2 of merged #1884 (`6508c239`: every contingent being at w is
existentially receptive or has a prior distinct esse cause), and C1 means the
#1724 question whether an entirely derivative reality can account for its own
actuality.

### Model and formal separation

`ConcurrentCessation.C3ActualWorld` represents the following *single
selected world* (`w=true`) and accessible alternative (`w=false`):

| Feature | Origin-only inertia, at w=true | Concurrent conservation, at w=true |
| --- | --- | --- |
| Rigid source `true`, effect `false` | Source at every sampled moment, effect from t=1 | Identical presence history |
| Modal status | Both present here, absent in alternative world; both contingent | Identical |
| `CausesIn true false esse` | Yes; selected strict-origin interpretation | Identical relation |
| `GivesAt true true false 1` | Yes, at onset | Yes, at onset |
| `GivesAt true true false 2` | **No**, despite source still being present | **Yes** |
| Persistence rule | Already-present bearer survives each next step | Identical |
| `EsseReceivedIn false ()` | Yes (a selected receiver sense, not identified with modal contingency) | Identical |
| `40a97664` / weak concurrent actualization | False | True |
| `ce55210c` (`CausingAnothersBeingIsSustaining`: `23e04ae5` restricted to distinct `CausesIn` causes, which `23e04ae5` entails) | False | True |
| Selected actual `grounds true true false` | Either yes (grounded profile) or no (ungrounded profile) | May be yes |

The profile's `ontic` is *exactly the temporal history's* `ontic`;
`CoherentAtNow` holds in **both** worlds at `now=2`. Thus this control
does not exploit a mismatch between temporal and world-relative existence, a
different effect at later moments, a missing actual originator, an unpopulated
actual world, or the trivial absence of a `CausesIn` edge. The target itself
is an actual contingent concretum. Both giving assignments satisfy contact,
and the origin-only assignment has no giver identical to its effect.

The sustained comparator satisfies weak C3 only because the contingent source
`true` has no received esse (`falseReceived` makes only the effect a
receiver), so `40a97664` asks for no giver of the source. Neither model covers
the source's own status, and merged C2 (#1884, `6508c239`: contingency
requires receptivity or prior reception) contests exactly that: on C2 a
contingent source would itself be receptive or received from something prior.

Two assignments of the same `grounds` relation are deliberately
distinguished:

- **Grounded inertia:** the direct `cb1cdea9` formula, *a distinct cause of
  an actual concrete effect's esse is its actual concrete ground at w*, holds
  even though `40a97664` fails. This is possible at the *typed level*
  because actual grounding is not defined as strict present productive
  `GivesAt`. It is **not** a model of a further interpretation requiring
  all actual grounds to exercise concurrent esse-giving. Which position the
  edge illustrates depends on the reading of `grounds w`. On the
  complete-history (ancestry) reading that the `cb1cdea9` record's note
  allows, an inertialist can accept the edge: the originator is in the
  effect's actual history. On a present-existential-grounding reading, the
  profile witnesses ground without giving, which is not the inertialist's
  own position but a structural separation of the two relations.
- **Ungrounded inertia:** keep the *same* history, actual originating
  `CausesIn`, recipients and giving assignment but delete the selected
  `grounds` edge. Then `cb1cdea9` fails, with both its actual/concrete
  relatum conditions still met. This is a falsifying model of `cb1cdea9`
  with its antecedent instantiated under origin-only giving; no other
  #1614 bundle premise is checked (issue #1616).

The active alternative world has no concrete existent; the selected actual
world has two. Consequently **no bearer in this model is de re necessary**;
the model is not an application of a real-world PSR or of C1/C2, and it is
not a counterexample to a theorem whose additional premises force a necessary
source. It shows that, on the existing semantics, modal contingency does not
entail continuous existential dependence (nor does actual co-existence plus a
grounding edge entail present productive exercise); any such passage needs an
explicit bridge.

**Formal boundary:** the added `C3ActualWorld.Certificate` is discharged
by `Results.Causality.ConcurrentCessation.c3ActualWorldControls` when that
module is built. It is an unregistered Lean helper/model (no new Comparator
result), and carries no reality-applicability claim. CI run 45154506898 at
head `b3b1c8c18` of PR #1885 passed the corpus-and-lean, comparator-library
and comparator jobs, and its frontier-diff reported no change; the CI of the
final PR head is the verification of record.

### What the rival positively explains

The origin-only account supplies: (i) an actual originating esse-cause,
(ii) numerical identity of the effect before and after time 2, (iii) a
consistent forward persistence constraint, (iv) an actually existing source
whose productive activity ends, and (v) an optional world-level ground
assignment. It offers a positive diachronic explanation of later survival
from prior existence and a rule, without needing a present `GivesAt` (the
recorded provisional judgment in the C1 note `unique-feedback-explanation-311.md`,
supplier-rule selection test, "Comparative result at matching explanatory
scope", row "Existential inertia with past bearer plus law"); the model
certifies only that the history satisfies the rule. **It does not by that rule alone produce** `∃t, IsAt w x t`:
the rule is conditional on a positive earlier actuality and does not choose
between a never-existing and an existing bearer. That is the already
recorded #1801 §7 distinction; no fresh independent evidence or
equivalence is counted here. An inertialist can take prior actuality and a
primitive law/nature as its ultimate package, or offer a non-well-founded
whole-history explanation. Neither is defeated by a conditional law's
failure to *entail* the whole history.

A law describing the actual mosaic, a primitive governing modal restriction
and a bearer-intrinsic disposition play different roles. The same-fact
grounding-cycle objection applies only if the **identical lawhood/actuality
fact** both grounds and is grounded by the alleged law. An independently
governing law plus basic ontology is the strongest surviving alternative to
a complete productive-source explanation. A persistence power cannot explain
its *own* instantiation merely by being a power of an already instantiated
bearer; an independently grounded essential existential sufficiency would
have more content and must be evaluated on its merits.

### C3's weakest proposed bridge and the remaining philosophical choice

A sufficient typed package for **weak** C3 is simply present-tense
reception + correlativity of receiving/giving (`7c62adb5`), but PR #1785
proves that each of the two supplied receipt interpretations hides
`40a97664` in one conjunct. The original same-bearer
no-giver/no-continuation and continued-giving formulations are equivalent
(#1709, `ConcurrentCessation.Consequences`; #1856's separate equivalence is
`nonexternalIffExternalOpportunity`). Repeating those is **not**
new warrant.

The explanatory argument would instead need a non-circular, substantively
warranted claim:

> A currently instantiated act of esse whose bearer has no intrinsic
> existential sufficiency is not merely the post-origin outcome of a
> persistence rule; its actuality at that stage is itself existentially
> productive or presently grounded by a source, and the selected grounding
> sense is capable of supplying the act rather than only tracing the bearer.

This is an **OPEN analyst proposal**, not a proved weaker premise or an
attribution. The step from *has received* to *still presently receives*
requires a warrant beyond a choice of grammatical tense. Even if an
appropriate **present ground** is granted, an additional typed
**ground-to-productive-giving** bridge is needed to infer the strict
`GivesAt` relation. Aquinas ST I q.104 a.1 gives the positive direct
conservation picture by separating direct causation of *being* from causation
of *coming-to-be*. An inertialist can accept the separation but deny that
all received existents are of the former ongoing-cause kind; source
interpretation cannot simply stipulate that exception away.

**F2/non-efficient causes.** `CausesIn` is still mode-unspecified. An
exemplar or final cause can explain an effect under one philosophical sense
without exercising strict productive being-giving at the effect's time. The
new controls use an originating efficient *reading* of the same free
`CausesIn` relation; they do **not** certify a universal exclusion of
exemplar/final cases. The full #1616 F2 and all-other-#1614-premises
acceptance items remain open.

**Time semantics.** The parameter `GivesAt v c x t` indexes the time of
the *effect's* reception; it does not place the causal agent in temporal
succession. The two-world control has natural-number effects and therefore
does not test a beginningless world or an atemporal source. Neither a
timeless ground nor an impersonal governing constraint implies one indexed
`GivesAt` event without its own scope bridge (#1800).

### Cumulative impact on C1, C2, necessity and God routes

- **Accept C3:** when a received-esse bearer really has nonintrinsic
  actuality, it has at least *some* concurrent `GivesAt` giver. The weak
  theorem permits self-giving, multiple/alternating sources, infinite chains
  and cycles. An *underived necessary source* does **not** follow without
  separate anti-self-actualization, supplier-completeness/groundedness,
  well-founded or explanatory-adequacy conditions, and a same-witness
  actual-world/modal-necessity bridge.
- **Reject C3:** a fully explicit model still supplies local persistence,
  an originating concrete source and contingent current existence. The
  independent conditional C1/C2 arguments are not *invalidated*: their
  theorems survive when their own ground/supplier, termination and modal
  premises are accepted. Routes specifically needing `40a97664`,
  `23e04ae5` or `cb1cdea9` cannot silently carry those bridges over
  from the originating sense. Whether the rival accepts a *brute* global
  actuality, governing selection law or non-well-founded actualizing
  structure remains a substantive separate choice.
- **Convergence:** under a separately defended interface from concurrent
  giving to one and the same actual concrete/source/priority relation, C3
  can strengthen the *warrant* and selected-witness contact on routes
  through `2068f91c` and `cb1cdea9`. It is not another derivation
  of necessary being until that mapping and its other premises are typed
  and checked. (The control's frame leaves `DependsForBeing` empty as an
  unused placeholder; it does not model the q.44 dependence of `2068f91c`.)
  The current model shows that `cb1cdea9` alone does not
  prove C3 on the existing formal semantics.

**Provisional assessment.** At the narrow comparison of an originated,
contingent, received-esse bearer already known to exist, the inertialist's
earlier-actuality-plus-persistence account and the direct-conservation
account each give a positive but different explanation. No new evidence here
establishes C3 or ¬C3 of reality. The next discriminating task is to
type and defend a real present-ground-to-productive-`GivesAt` principle
for the *same received-esse bearer*, and check its explanatory force against
an independently governing persistence law **under identical ultimate
actuality standards**. Do not count the resulting formal implication as
independent confirmation if it simply redescribes C3.

**Record and review.** Attempt `c03f097e-1c78-4cba-8ba5-ea5746b90387`
links this section and `c3ActualWorldControls` to `cb1cdea9`, `40a97664`,
`ce55210c` and `23e04ae5`. An independent semantic challenge found the formal
claims correct; its prose findings are repaired here.

**Open implementation/issue obligations:** a full #1614-bundle-except-`cb1cdea9` model or impossibility
argument; source-positive origin-to-conservation reason at matching scope;
and F2 efficient/exemplar/final typed discrimination. No new registered
root-path premise or `frontier-diff` effect is intended by this structural
checkpoint.


## 9. ¬C3 with a necessary originating source and the full #1614 source bundle (2026-11-23)

**Labels.** C3 is `40a97664`, as in §8 (not the C1 note's "the source is one").

### Positive rival sharpened: existential inertia need not be foundationlessness

A more informative inertialist world than one with two contingent, unexplained
sources is **one necessary concrete originator**, and a contingent concrete
recipient that obtains its first act of existence from that source but then
continues under an existential persistence rule without further `GivesAt`.
For a begun effect, this proposal neither has to declare its initial actuality
brute nor reject ultimate source arguments. It offers two explanatory roles:
productive origination accounts for the recipient's first actual existence,
and prior existence plus the absence of cessation (or a governing persistence
constraint) accounts for its later persistence. This holds only on the
**ancestry** reading of `grounds`: in the strict `withoutGround` profile
`EveryContingentGroundedAt` fails and `false` is a contingent actual root
with no ground, so using ancestry `grounds` for the root premises and strict
`grounds` for `cb1cdea9` would equivocate.

The actual originator's necessary existence does not determine **which effect
it originates, why then, or why this actual world is selected**. The former
role may require selection by agency or an additional causal circumstance;
this model does not type divine freedom or a complete account of creation.
Nor does a stationary law alone explain the originator's necessity. Those
explananda must be distinguished from the later-stage, **same-bearer**
question. The positive no-change argument, defended by Schmid in his
[Feser response](https://josephschmid.com/feser-on-schmid-on-existential-inertia-a-comprehensive-response/),
does not demand that a continuing physical object *intrinsically causes itself
at every time*: a no-cessation causal principle is a different explanatory
proposal from a self-sustaining power. This is a reading of that cited public
argument, not a new pinned corpus attribution.

### Fixed dictionaries and verified targets

The proposed formal comparison lives in
`EsseCausePriority.InertialNecessaryOrigin`, consuming the same
`C3ActualWorld.originGiving` and its `CausesIn` through the shared
`CausalityFrame`. `CausesIn` is tenseless and mode-unspecified in Lean;
reading it as an origin-only cause is a selected interpretation. The selected world is `true`; source
`true` exists at every natural-number time in **both** accessible worlds,
whereas rigid effect `false` begins at t=1 and continues at t=2 and later
only in the actual world. `CoherentAtNow` holds at `now=2`.
`EsseReceivedIn false ()` is interpreted by the existing receiver predicate,
not by contingency itself. The model adds a second respect, heat, to let a
composite effect actually have potency **without** being in act and in
potency in the same respect.

Four exact certificates are proposed:

| Test | Positive joint commitments | Discriminating result |
| --- | --- | --- |
| `necessaryOriginWithoutConservation` | Existing `NecessaryActualRootAt` on the ancestry profile, `EveryContingentGroundedAt` at the actual world, contingent actual recipient, `OriginatesBeing`, giver contact, no cessation in the tested history | `40a97664` fails for the same received-esse recipient at t=2 and the distinct-origin `CausingAnothersBeingIsSustaining` bridge fails. The *source* is still present at t=2 and is de re necessary. |
| `fullSourceOmission` | The other **ten source premises** from PR #1614's esse-priority cluster, reusing their unchanged Lean definitions at the same bearer, cause and respect; an actual source/recipient and positive persistence | The strict branch withholds **both** the grounding edge and the priority edge (`PriorSimply` empty); the grounding clause `ActualGroundingIsSimplePriority` then holds vacuously. `cb1cdea9` fails at cause `true`, effect `false`; the two intermediate priority conclusions fail at the pair `true`/`false`; first-being act-priority and no-potency fail at `false`, and no-component-first at component `false` of `true`, **only because nothing is prior to anything**, so every being, including the caused composite contingent `false`, is vacuously first. This is a test of the complete ten-premise **source-level** remainder, not every ambient premise of an unrestricted God proof. |
| `priorityWithoutGroundEdge` | The same `withoutGround` profile (no grounding edge, `cb1cdea9` false) with the ancestry `PriorSimply` retained | The ten premises and **all** priority, first-being and component conclusions hold. Denying `cb1cdea9` alone removes none of them; the `fullSourceOmission` failures come from the separate choice of an empty priority. |
| `ancestorRouteWithoutConservation` | The same ten source premises, actual ancestry grounding from source to effect and corresponding `PRIOR_1` edge, plus the `cb1cdea9` cause→ground premise | Both derived esse-priority conclusions, the first-being no-potency result and no-component-first result can coexist with **¬`40a97664`**. The source remains necessary and ungrounded. |

These controls distinguish two *assignments of the same* `ActualConcreteGround`
and `PriorSimply` primitives. An **ancestry** reading permits a past
originator to count as an actual cause, historical ground, and simply prior
to its effect in the selected world even when no fresh being is given at
the present moment. A **strict present-existential** reading denies that
grounding edge and does not accept the cause→ground bridge. In
`fullSourceOmission` the strict branch also withholds the priority edge.
Among these eleven premises `cb1cdea9` is the only one that forces any
priority, so denying it leaves priority unconstrained rather than absent
(`priorityWithoutGroundEdge`). Denying origin priority is an **extra
interpretive commitment**; DEF-SIMPLE-PRIORITY's "not in time" does not
settle whether a past originator is simply prior to its effect.

**Inherited component assignment.** `component` reuses
`ComponentFirstness.Control.comp` (`p = false ∧ x = true`), so the received
effect `false` counts as a component of its own necessary originator `true`,
while `composite` holds only of `false`. With two Boolean beings only a third
being would avoid this; it is a structural artifact of the reused control,
not a claim that the originator is composed of its effect.

The types do not
say whether the former matches the intended metaphysical sense of
`ActualConcreteGround`; accepting it cannot bypass this interpretation
choice by calling ancestry "ground" alone.

The omission branch keeps the ten antecedent source claims; it does not
require their *derived* conclusions as additional assumptions (that would
make failure of those very conclusions impossible). Conversely, the positive
ancestry branch composes the existing `actualEsseCausePriority`,
`distinctEsseCausePriority`, `firstBeingNoPotencyOfEssePriority`,
`weakOfEssePriority`, and `noComponentFirstOfEssePriority` theorems,
rather than registering duplicated support alternatives.

### Provisional warrant and cumulative effect

**For ¬C3:** the originator can genuinely explain initial positive actuality
and a persistence rule can furnish a valid conditional explanation of
later existence. This avoids the special complaint that a merely unchanged
history contains *no* positive originating cause. However a primitive
diachronic-sufficiency law is still a substantive commitment, not derived
from source necessity or from the sameness of the bearer. The strongest
version can take such a law as governing, or as grounded in independently
specified powers or natures. The Humean summary version has the different
same-fact explanatory issue already analyzed in §7; do not transfer that
objection to a primitive governing law without argument.

**For C3:** Aquinas's *Summa theologiae* I q.104 a.1 argues that causing a
thing's becoming is different from directly causing its being, and that an
effect dependent on its cause *in the latter respect* requires conservation.
The [article](https://www.ccel.org/ccel/aquinas/summa/summa.FP_Q104_A1.html)
explicitly illustrates the builder's completed activity versus the
underlying form/material powers. That supplies positive motivation for direct
esse-conservation where dependence is already granted. The disputed further
step is **why the contemporary actuality of this particular receiver must be
of the directly dependent sort** rather than being the recipient of an
originating cause and now persisting by law. Reasserting the conservation
reading of `CausesIn`, or simply defining every `grounds` as productive
`GivesAt`, would relocate C3 into the premise.

**Cumulative status:** even a robust *actual necessary root* and the
whole registered #1614 priority spine do **not**, under the supplied
definitions, entail `40a97664`. On the ancestry reading of `grounds`,
rejection of C3 is thus not automatically rejection of a necessary underived
source (on the strict reading the effect is itself an ungrounded contingent
root, and mixing the two readings would equivocate), and adding C3 does not by
itself prove the source necessary or divine. Equally, a successful Lean
countermodel is a logical separation, **not** proof that the inertialist
interpretation of received esse or ancestry is metaphysically admissible.
Source-level confidence must come from the explanatory work, not a Boolean
assignment.

The exact live choice is whether origin plus a defensible persistence
law is **ultimately sufficient for later actuality**, or whether a genuinely
received act has to be supplied contemporaneously in a productive sense.
Neither side has yet supplied a decisive independent comparative test at
matching scope. The next useful investigation is an originator-withdrawal
counterfactual at *fixed original effect history and fixed intrinsic powers*,
compared with a productive-conservation proposal under the same world-selection
standard. For a timeless conserved source, the effect index on `GivesAt`
must remain distinct from the agent's time.

**Verification/ownership:** these are unregistered Lean helper theorems and a
research assessment. Unregistered theorems are checked by `lake build` and by
NanoDa over affected modules, not by Comparator. An independent semantic
challenge of head `7ab412ed7` returned *mergeable after listed repairs* with
no Lean error; it accepted the ten-premise selection, the absence of
`61ad11f3` smuggling, the proofs of every "fails" conjunct, the model and
scope statements, the unchanged root frontier and consistency with C2
(#1884). Its P1 (the strict-branch failures were credited to the grounding
reading rather than the empty priority) and P2s (component assignment,
ancestry-only foundation claim, vacuity wording, verification wording,
labels) are repaired in PR #1891, adding `priorityWithoutGroundEdge`;
re-check and exact final-head CI remain pending. No new source attribution,
claim, closure, registered result, or root-path premise is made. #1616's
universal F2 treatment of non-efficient exemplar/final causes and the
positive sense-3→5 argument remain open; the typed source-premise omission
test addresses its narrower outstanding #1614 configuration.
