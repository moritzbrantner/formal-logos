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
  nisi relatio quaedam ad Creatorem, ut ad principium sui esse". The analogy
  is to the passion that comes with motion, which imports a relation to the
  principle of the motion.
- *ad 1.* The creature's relation to God is real. God's relation to the
  creature is of reason only.
- *ad 3.* As a change, creation has the creature as its term. As a relation,
  creation has the creature as its *subject*, and the creature is prior to it
  in being, as a subject is to an accident. Then: "Neque tamen oportet quod,
  quandiu creatura sit, dicatur creari: quia creatio importat habitudinem
  creaturae ad creatorem cum quadam novitate seu incoeptione."
- *obj. 3* holds that when the term of an action exists, action and passion
  cease ("eo existente cessat actio et passio"). Ad 3 does not dispute this
  for creation taken as a change. It moves what remains in the creature to
  the relation.

**ST I q.13 a.7.** Passage `12d8ecc5`, newly pinned in the same SCTA file as
q.13 a.5 and a.8. Read in full.

- *co.* Relations are of three kinds:
  - of reason on both sides, including every relation between a being and a
    non-being, "quas format ratio";
  - real on both sides, including relations "quae consequuntur actionem et
    passionem, ut motivum et mobile, pater et filius";
  - real on one side and of reason on the other, as knowledge to the
    knowable.

  The creature's relation to God is of the third kind.
- *ad 6.* Whether two relatives are simultaneous by nature is settled by
  their significations, not by the order of the things. "Dominus" and
  "servus" are simultaneous by nature, so God was not Lord before he had a
  creature subject to him.

**ST I q.104 a.1** (re-read). The corpus and ad 2 argue from the
cause-of-being versus cause-of-becoming distinction and the illumination
profile. Ad 4 says that preservation is "a continuation of that action
whereby He gives existence". This is the text that states the crux. §2 and
§5 record why carrying the profile from light to esse presupposes it.

### Vocabulary

- **Origin relation** `OriginRelation.RelatedAt v x g t` (definition
  `7b28be97`), an explicitly primitive relation. In history `v`, at `t`, `x`
  bears a real relation to `g` as to the principle of its being. The relation
  names no action of `g`.
- **RECEIVES_ESSE_AT_3**, *relational receipt* (`relationalReceipt`,
  definition `2a7f7142`). It is standing receipt plus "`x` bears the origin
  relation at `t` to something", and it is appended to disambiguation
  `71d3bdb7`. It carries content beyond reception plus presence: a term.

| Record | Lean | Content |
| --- | --- | --- |
| `ef7ef827` foundation | `FoundedOnReceivedEsse` | bearing the relation at `t` ⇒ received esse and present at `t` (q.45 a.3 ad 3) |
| `9fecbef4` accompaniment | `RelationAccompaniesEsse` | received esse and present at `t` ⇒ bears the relation to something at `t` |
| `264b6b5e` coexistence of the term | `TermCoexists` | term of the relation at `t` is present at `t` |
| `6da7d94a` giving by the term | `TermGives` | term of the relation at `t` gives the bearer being at `t` |
| `a0b5227d` | `concurrentOfTermGiving` | accompaniment + giving by the term ⊢ `40a97664` (transcription) |
| `42590821` | `relationalPresentIsAccompaniment` | on RECEIVES_ESSE_AT_3: present-tense reading ⇔ accompaniment |
| `1637b89a` | `relationalReadingIsTheCrux` | on RECEIVES_ESSE_AT_3, given accompaniment: correlativity ⇔ `40a97664` |
| `b5e9b376` | `someRelationCarriesTheCrux` | (∃ founded, accompanying relation with a giving term) ⇔ `40a97664` |
| `b9920133` | `coexistentTermDoesNotCarryTheCrux` | foundation + accompaniment + coexistence of the term + received onset given ⊬ `40a97664` |
| `584bac58` | `controls` | parts 1–4 below |

*Controls* (`RelationalReceipt.Control.Certificate`; `false` alone has received
esse; histories and givings of `SustainingCausation.Control`):

1. *A creator present throughout who gives being at onset only*, with the
   relation persisting. The giving is at time 1 and `true` is always present.
   Foundation, accompaniment, coexistence of the term, received onset given
   and the relational present-tense reading all hold. Giving by the term,
   relational correlativity and `40a97664` fail.
2. *The same, with the relation at onset only*: creation "cum novitate".
   Giving by the term and relational correlativity hold. Accompaniment and
   `40a97664` fail.
3. *Term absent after onset, relation persisting.* Coexistence of the term
   fails. A relation to a term that has ceased is excluded.
4. *Sustaining with the relation persisting*: everything holds.

`truth countermodel` does not support structure-typed parameters such as
`History`, so the controls are hand-built and checked by Lean.

### Outcome of the test

**Correlativity does gain one piece of independent warrant, but it is not
enough.** The relational reading splits correlativity into two steps:

- *Coexistence of the term.* A real relation needs an existing term, because
  relations between a being and a non-being are of reason only (q.13 a.7 co.).
  This warrant does not depend on `40a97664`, and q.13 a.7 ad 6
  (simultaneity by signification) agrees with it.
- *Giving by the term.* The term is giving now.

Coexistence of the term, together with foundation, accompaniment and a given
onset, does **not** entail `40a97664` (`b9920133`, part 1). What is missing is
exactly giving by the term. Given accompaniment, relational correlativity is
equivalent to `40a97664` (`1637b89a`). With the relation left open, giving by
the term plus accompaniment is equivalent to `40a97664` (`b5e9b376`).

**Each premise of the relational derivation, priced:**

- *Foundation.* Textual (q.45 a.3 ad 3). Both sides grant it.
- *Accompaniment.* The inertialist grants it. Part 1 is the theist
  inertialist who keeps the creature's relation of origin to a creator who
  exists eternally. It is not stated by q.45 a.3. Ad 3 says that creation in
  that article's sense imports novelty, so the article's relation, *as
  creation*, is onset-indexed. That is part 2, and the inertialist grants it
  too.
- *Coexistence of the term.* Independent warrant (q.13 a.7). It is cheap for
  the theist inertialist, whose giver exists throughout. It costs only the
  variant in which the relation outlives its term (part 3).
- *Giving by the term.* This is the whole crux. It says that the creature's
  relation is of the present-action type (mover and moved while the motion
  lasts), not the completed-action type (father and son).

**The strongest rival mechanism** (Substantive Objection Standard):

- *Target:* the step from the q.45 a.3 relation to giving by the term.
- *Mechanism:* the creature's relation to God is a real relation that follows
  on a completed action. Like a son's filiation, it persists while its term
  exists, with no present action of the term.
- *Independent justification:*
  - q.13 a.7 co. lists "pater et filius" among the real relations that follow
    on action and passion. So Aquinas's own classification does not tie a
    real relation of this kind to an ongoing action.
  - q.45 a.3 ad 3 grants that creation, under that name, is not said of the
    creature as long as it exists.
  - That filiation lasts after the begetting while the father lives is
    ordinary use. The passage implies it without stating it.
- *Relevance:* this is the case that `TermGives` must exclude, and part 1
  realises it.
- *The dead-father variant does not survive.* A son's real relation to a
  father who has ceased would be a relation to a non-being, which q.13 a.7
  makes a relation of reason. That is excluded by `TermCoexists` (part 3).
  The rival does not need it, because its creator exists throughout.

**The sustaining reply restates the crux.** The reply is that the
disanalogy matters: a father causes only the son's becoming, while God causes
the creature's being (q.104 a.1 co.: "man begets man" is the cause of
becoming, not of being). That difference bears on the relation's type only
through the thesis that a relation to a cause of *esse* must be of the
present-action type. That thesis is the illumination profile of q.104 a.1
carried to esse, which presupposes `40a97664` (§2, §5). The reply's
analogy in q.45 a.3 co. ("sicut in passione quae est cum motu") is to the
passion that comes with motion, and so to the passion sense
RECEIVES_ESSE_AT_1, on which present receipt is `40a97664` restated
(`1d52b8f0`).

**Classification: the crux restated, for a precise reason.** The relation adds
a term and the term's coexistence, with warrant independent of `40a97664`.
Coexistence does not reach giving (`b9920133`). Once the relation is granted
at every moment of presence, which the inertialist does at no cost, relational
correlativity is `40a97664` (`1637b89a`). The extra content that would close
the gap is the type of the relation, and choosing the present-action type is
`40a97664`. No item is added to inertia's price; §4 stands.

**The vertical approach is exhausted.** Three readings of present receipt
are now typed and characterised:

- passion: the present-tense reading is the crux;
- standing composition: correlativity is the crux;
- real relation to the principle of being: giving by the term is the crux,
  and coexistence of the term, the one independently warranted addition, is
  too weak.

Further re-reading of receipt yields no new discriminating test, since any
receipt implied by standing receipt makes correlativity alone carry the crux
(§5). A sourced statement that the creature's relation is of the
present-action type would attribute the crux to Aquinas. It would not be
independent warrant for it: it would identify that relation with
RECEIVES_ESSE_AT_1.

**Side finding on the co-presence bridge `ffcb81fb`.** Accompaniment and
coexistence of the term give only this: a received-esse thing present at `t`
has *some* term present at `t`. The antecedent of `ffcb81fb` needs one
tenseless cause of esse, present whenever its effect is, in every history.
That needs the term to be the same at every moment and to be a `CausesIn`
cause, and neither is typed. No premise moves. This is a lead, not a
connection.

**What would still discriminate** (horizontal; another lane may take it):

1. An argument from another family that persistence at `t` needs an
   explanation *at* `t` and not only at onset. Candidates are a PSR variant
   for persistence and the contingency family's explanation of a thing's
   existing now. Each must avoid the illumination analogy and the extended
   actualization principle, which are already classified as the crux.
2. An account of esse as received act in the participation family (q.104 a.1
   "every creature has being by participation"; De ente c.4) on which
   participated act is not a completed terminus. It counts only if the
   account has warrant that does not already assume `40a97664`.
3. A comparison at matching scope of inertia's positive commitments, that
   persistence needs no cause and conservation laws, against the sustaining
   account, as explanations of the same persistence data.

**Revision condition.** The judgment changes given a typed, independently
warranted premise that excludes completed-action relations (the father and
son type) for relations to a cause of esse, without the illumination or
actualization premises. Or it changes given one of the horizontal tests
above.

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
De ente c.4 and the PSR variants are named only as next tests, with no weight.
That filiation lasts after the begetting is marked as ordinary use, not as
text.
