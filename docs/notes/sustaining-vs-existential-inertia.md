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
`40aefb2e`, `da9c82ed`), attempts [`c94eed5b`](../../corpus/attempts/c94eed5b-935d-4882-aa84-2894ef066c5b.json), [`05bc2722`](../../corpus/attempts/05bc2722-960f-4ea4-bf1a-f92bb9a77af9.json) and [`447838c8`](../../corpus/attempts/447838c8-601f-4a04-ad65-b50ef9dd3764.json), the
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
price map and the `2068f91c` connection are added on top of it. [Assessment record](../../corpus/attempts/21883b61-1dec-454f-821e-e1c2fb0e37c4.json)

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
attempt [`50e08b09`](../../corpus/attempts/50e08b09-fc52-4cf1-9bd7-4bad25707dc6.json). Analyst formulations, attribution deferred.

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
`specs/relational-receipt.toml`, attempt [`c97afe42`](../../corpus/attempts/c97afe42-c3d3-45be-8367-8ed76b47fe6c.json). Analyst formulations,
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


## The tree analogy and existence at all

Analyst formulation of the owner's argument, with attribution deferred. Fix
one designated bearer x and one history. Write Eₓ(t) for its dated presence
(`History.IsAt`) and Aₓ for ∃t Eₓ(t). For the local comparison keep x,
its origin if it began, its earlier presence, and the independently
specified loss conditions fixed. For the Aₓ comparison use the populated
and omission histories of §7, with the same law and background bearer.
Earlier presence necessarily varies between those histories.

1. **Persistence and actuality are distinct explanatory targets.** The
   objection targets a move from the conditional persistence law to an
   explanation of Aₓ. Every application to x uses earlier Eₓ(s), which
   already entails Aₓ. The H₊/H₀ comparison in §7 shows that the law and
   no-loss background permit both outcomes. The reversible control there
   shows that exchangeable anchors in a beginningless history still
   require some positive anchor. This rules out selection of the populated
   history by that law and background alone. The countermodel concerns
   entailment within the supplied profile class. Its bearing on a proposed
   *complete* explanation comes from the independent demand to account for
   an indispensable actuality input (§7).

2. **The tree analogy transfers a conditional transition.** A position
   report At(x,L,t) entails that the tree is present at t. In the
   [Lean vocabulary](../../TruthCore/Explanation/LocationPersistence.lean)
   that entailment is the explicit `Sound` condition on the report
   `location t = some L`; the trace may also give no report. The
   [proof and application](../../TruthCore/Results/Explanation/LocationPersistence/Solution.lean)
   transport the supplied position across a stationary integer trace by
   the existing `constant_of_stationary`. Soundness projects the
   bearer's presence at both dates. The worked control gives one
   everlasting bearer two sound traces, with the same location at 0 and
   different locations at 1. This checks that fixing presence leaves
   position open, even when an initial location is fixed, unless a
   transition condition is also supplied. The same abstract transition
   form applies to existential persistence: the earlier and later
   conditions are both instances of `History.IsAt`, as in
   `CessationNeedsInducer` and `originOrInertia`. In that application
   the input already asserts the very kind of actuality the output asserts.
   The tree case supplies evidence about conditions for keeping a place.
   An argument by analogy for an existential persistence law needs a
   further premise that the same kind of state-transition warrant governs
   the bearer's very being. Agreeing to represent both as dated predicates
   supplies only the formal similarity.

   The **discriminating premise** is whether the actuality of this same
   substantial bearer has the independence from current production that
   a state of an already-present subject can have. Compare the established
   temporal-presence vocabulary
   ([PRESENCE_NOW_TEMPORAL_PERPETUITY_BEGINNING](../../corpus/disambiguations/temporal-history-existence-axes.json))
   with [DEF-ESSE](../../corpus/definitions/esse.json) and
   [DISAMB-ESSE-RECEPTION](../../corpus/disambiguations/esse-reception.json),
   especially `RECEPTION_OF_ESSE_VERSUS_EXTERNAL_CAUSE_1`
   (`DEF-ESSE-RECEIVED-IN`), reception of an act in a principle.
   The [existence/esse support disambiguation](../../corpus/disambiguations/existence-esse-support.json)
   distinguishes world-relative existence, the respect of esse, and
   support or exercise at a world. The modeled predicate is dated
   presence. Its use leaves open the ontological account of that presence.
   Received act in a principle also leaves external origination and
   concurrent giving to their respective bridge premises (§§5–6 and 11).
   Thus the tree case challenges an inference from ordinary state
   persistence to a law of substantial actuality. It leaves room for an
   independently warranted persistence law, even for received-esse
   bearers, if that law can be justified under a strict-giver cut.

3. **God parity tests the same explanandum.** Grant an everlasting
   candidate g for the test. Temporal perpetuity within an occupied
   history still uses the actuality of g when one date explains another.
   If the proposed inertia law alone were offered for Aᵍ, the same
   H₊/H₀ test would apply: the bare law permits a history without g.
   This is a consequence of the law's conditional form, with no appeal to
   personal assent. The omission profile need not be possible under a
   separate, warranted principle of aseity or nature-based actuality.
   Such a principle would have to supply existence of the relevant
   bearer and explain it, with its own warrant. An uninstantiated
   description and a conditional about a candidate's nature leave that
   obligation open. Aseity addresses the candidate's being through itself
   and temporal inertia addresses continuance under earlier actuality.
   The two occupy different explanatory roles. This is fair to the
   persistence-only rival, which can reserve a nature-based or other
   foundational account for Aᵍ or restrict its law to suitable temporal
   receivers. A timeless candidate is outside the antecedent structure of
   the temporal test.

4. **“External things” has two defensible readings.**
   - **Other bearers.** Target the move from the persistence of a given x
     to the actuality of a distinct y. An x-only conditional has no
     y-actuality input, and even a universal per-bearer rule needs an
     earlier y for its y-instance. Section 7 supplies the control after
     exchanging the roles: keep the background bearer and its persistence
     fixed while varying whether the designated additional bearer is ever
     present. An explanation of y via x's causal powers or activity would
     need a cross-bearer origin or support premise. This is a substantive
     limit on expanding the rule's explanatory scope.
   - **Externally conditioned continuance.** Target a stronger claim of
     independence from every external condition. External prevention of
     destruction is compatible with the rule, since it can secure the
     no-inducer background. The existing q.104 becoming/being distinction
     and the competing readings of withdrawal (§11 and the sibling calibration
     in PR #2094) supply the difference: removal of a protector can allow a
     separate loss process, while withdrawal by a direct cause of being
     would remove its claimed productive contribution itself. The latter
     would bear on existential independence if independently identified
     for the same receiver. No substantive objection identified to the
     conditional persistence law from external conditioning alone.

### Replies at the same scope

| Rival reply | What the objection establishes and what remains |
| --- | --- |
| **Origin for begun bearers, inertia thereafter.** The existing [I q.104 a.1 becoming/being claim](../../corpus/claims/becoming-cause-not-being-cause.json) records a builder whose building can cease while the house persists. | An origin cause can account for Aₓ through a positively explained onset. The temporal chain can start there. The objection to the law alone then leaves the combined account standing. The q.104 distinction sharpens the later dispute: a cause of becoming (*causa fiendi*) need not operate whenever the effect exists. This leaves open whether the effect also has a direct cause of being (*causa essendi*). For a beginningless bearer the origin reply needs a distinct, potentially atemporal actuality account. |
| **Necessary or brute foundation.** The rival can accept substantial dependence on an origin, including a necessary source (§9), and stop at a necessary or brute foundation. | The necessity of a source supplies no specific contingent outcome without a relevance and realization bridge. The rival can add an originating exercise, a positive nonnecessitating selection account, or an independently warranted reason fixing the relevant actuality. Bruteness can reject the demand for a further reason at the foundational level; it supplies no further explanation there. A sustaining account also owes an account of why its source and relevant exercise obtain insofar as its standard calls for one. The objection exposes the shared scope question without choosing a foundation. |
| **Hume–Edwards.** Grant genuinely adequate explanations for each actual member and use their conjunction as the explanation of the series. | The [typed `MemberLift`](../../TruthCore/Explanation/ActualWorldGap.lean) explicitly adds this lifting step. The owner's test rules out the persistence law alone as a selector. It leaves the distributive standard standing on its own terms, because its inputs include actual members and their explanations. An entailing whole-history standard instead asks for an adequate reason that distinguishes Aₓ from the omission profile, or the complete order from its relevant alternatives. Giving the list of actual stages only reintroduces the disputed actuality in the explanans. For the broader series, keep contingent laws and relations in scope as well as presence facts, as in [the whole-series assessment](../../corpus/attempts/a5958e25-0904-46cb-a9e8-62ca5f3f5286.json) and the [existing rival comparison](unique-feedback-explanation-311.md). Deciding between the standards requires an argument about whether member-wise coverage is sufficient for the requested contrast. |

### Provisional assessment and revision conditions

The strongest warrant in the owner's argument is the fixed-law H₊/H₀
contrast joined to the explicit difference between a position report and the
presence it presupposes. That warrant defeats the claim that inertia alone
selects a bearer as actual. It also removes the tree example as sufficient
warrant for applying the existential law to received-esse bearers. For
dated presence, the strongest inertia account still uses the same bearer,
actual earlier presence, and a causal law requiring an inducer of
cessation. For Aₓ, onset explanation remains available where onset is
independently explained. A beginningless account owes a positive
actuality reason if it adopts the contrastive standard, or a defense of
distributive adequacy or its stopping point if it adopts another standard.
Those standards are separate from the question of state persistence versus
received act. Defend the stronger whole-history claim by specifying a
matched positive reason that explains the first actuality or grounds the
beginningless profile, or by independently justifying member-wise coverage
for the precise contrast. An adequate nonnecessitating reason would need
independently identified explanatory relevance and direction even where it
admits alternative outcomes.

The comparison on [`d86c9de9`](../../corpus/statements/d86c9de9-25be-488b-b3b7-69f5f4eb80b8.json)
remains open at its actual scope. Its antecedent already fixes actual
presence at t and an explanation of that presence, and its consequent
requires strict giving then. The Aₓ contrast varies earlier actuality
and cannot decide between the two accounts with it held fixed. The
stronger [`76d2cc96`](../../corpus/statements/76d2cc96-14a0-48bc-bd0b-a5c0ca853265.json)
also asks for a giver distinct from the bearer. The tree proof supplies
neither production nor distinctness. Direct conservation of received
being retains the positive warrant described in §11, conditional on the
cause-of-being interpretation and its calibration. The relevant next
test is the same-bearer comparison in the
[calibrated withdrawal PR](https://github.com/moritzbrantner/formal-logos/pull/2094),
with earlier presence, origin and loss background controlled as specified there.
Warranted survival after independently excluded current giving, with a
reason for presence, would challenge the productive bridge. Warranted
loss under the same controls would challenge the causal cessation law in
that instance.

An Aₓ reformulation would need a separate premise specifying a reason for
`∃t, h.IsAt w x t` against the omission profile, with an explicit
adequacy standard and an actual noncircular basis for that reason. A
productive variant would additionally need a bridge from such a reason
to an actual giver of the same bearer. To compose it with the present
route it would need one further result, showing why the giver exercises
at the selected t whenever x is present, including its bearer, effect and
time binding. The scope test gives no warrant for adding that result as a
hidden premise. The existing bridge supports the God-existence route
through weak concurrent giving, the sustaining reading and `2068f91c`.
The Lean location result is consumed by the two-date presence
application above. The [registered result](../../corpus/results/1371f04e-8b90-4fb2-bda9-56ba9f02d8dc.json)
certifies the anchored transition. Its case connection is a diagnostic of the offered
analogy in the existing attempt
[`176d45ae`](../../corpus/attempts/176d45ae-c023-4c72-b2bb-86a09326b798.json).

[Attempt record](../../corpus/attempts/08713633-1a85-4977-9794-0cca47d9f064.json)


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

**Record and review.** Attempt [`c03f097e-1c78-4cba-8ba5-ea5746b90387`](../../corpus/attempts/c03f097e-1c78-4cba-8ba5-ea5746b90387.json)
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

## 10. Which later individual continues the earlier bearer? (#1801, 2026-11-25)

**Provisional judgment.** For familiar material objects, the history
of what happened to *this* object gives positive, defeasible grounds for
identifying it again. Copying its structure can causally influence a second
object without carrying the first object into the second. This distinction
discriminates accounts of *which individual* survives. It leaves open whether
the continuing individual's existence also requires a present productive source. [Assessment record](../../corpus/attempts/history-actuality-provenance-1801.json)

### Two verdicts with independently checkable grounds

The Natural History Museum identifies its 1905 London plaster cast through
wartime dismantling, a gallery move and changes in neck and tail posture. It
also documents scanning the touring cast in 2021 to design Fern, a separately
fabricated bronze. One can trace the handling of the plaster pieces and,
separately, the data sent to the engineers and the fabrication of new pieces.
These procedures answer which object was moved and which was manufactured
without deciding anything about existential inertia. A rule that identifies
the later object solely by a causal transmission of shape admits the bronze
as well. A rule requiring invariant arrangement loses the London cast across
its documented changes. The museum treats the cast as a collection artifact
through dismantling. Its practice provides no verdict about whether a mounted
structure existed throughout storage, much less about a living animal.
[History of the cast, “War and peace”](https://www.nhm.ac.uk/discover/diplodocus-this-is-your-life.html)
and [making Fern, “Improving on the original”](https://www.nhm.ac.uk/discover/the-making-of-fern-the-diplodocus-engineering-meets-natural-history.html).

There are qualitative differences in this actual case. The argument for the
*exact* duplicate is conditional. Improve the copy while leaving the original
in custody. However accurate the copy becomes, it cannot be numerically
identical to the original alongside a distinct continuing original: equality
with both would identify the two. Destruction of the original after the copy
has been made would remove a competitor without changing how the copy came
into being. In the harder case of destruction *before* reconstruction, the
two-candidate contradiction no longer applies. There the positive reason for
counting a replacement is its fresh production history. Van Inwagen's
manuscript example sharpens the point: the atoms and their arrangement alone cannot distinguish the writer's
inscription from marks assembled later. Given the stipulated reconstruction,
van Inwagen judges the reassembled manuscript a replacement. That is a thought experiment
about a historically individuated artifact. Neither it nor the museum case
proves a universal necessity of uninterrupted material composition.
[Van Inwagen, “The Possibility of Resurrection,” pp. 117–119](https://www.andrewmbailey.com/pvi/Possibility_of_Resurrection.pdf).

The defensible criterion here is a trace of the earlier bearer through the
material changes appropriate to its kind. The actual custody and fabrication
records distinguish transport from copying. Mere equality says that distinct
successors cannot both be the original. It supplies neither the trace nor a
cause of that trace. For a total break with only one successor, an account may
take the individual's identity as primitive or invoke the source's intention
towards that very individual. A specific intention could distinguish two
intended outcomes even with qualitatively identical instructions for making
them. To explain successful reidentification it still needs a reason why its
execution restores the individual rather than faithfully making its intended
likeness. Where only the end product and the assertion of success are given,
the identity judgment remains conditional. The existing Theseus theorem
`incompatible (b) : Gradual b → Material b → ¬ Distinct b` (with its
hypotheses curried) already isolates the equality constraint for competing
claims from gradual replacement and reassembly. Its premises leave the
appropriate criterion open. [Theseus profile](theseus-identity-boundary.md).

### Apply the criterion before varying the source's exercise

Fix one actual history, its source s, the earlier material bearer x at t0,
the recipient principle in which its esse is received, and s's originating
contribution to x's esse. Keep s present at t1. Keep the interpretation of
strict `GivesAt v s x t1` as productive giving of x's being. The question
concerns x's own existence at t1. In each account identify the candidate for
x by the same history of material continuation. The museum comparison
calibrates that procedure. It does not identify a museum object's esse-giver.

| Account applied to this one continuation | Identity verdict and explanatory commitment |
| --- | --- |
| Earlier actual x and an independently governing law of persistence in the absence of a cause of loss | Selects the materially continued x and allows a separately made copy to begin its own history. The law quantifies over an individual already identified. Applied to an uninterpreted pair of matching observations, it supplies no rule for assigning the later observation to x. Applied to the independently traced bearer, it gives a substantive conditional reason for its survival. Its sufficiency for x's **esse** remains disputed. |
| Present giving to the continuously constituted x, with x's prior history contributing to which patient continues | Selects the same x. The source can keep this very patient actual while its history differentiates it from the copy. This avoids treating a prior stage as the efficient producer of its own present prerequisite. On the stronger joint account the prior contribution and present exercise are each indispensable for continuation. Observing their concurrence or tracing the patient establishes neither indispensability. |
| Separate manufacture of a matching successor, even when x supplies the template, with resemblance sufficient for identity | Gives a wrong verdict in the hypothetical exact-copy coexistence control and lacks the provenance that distinguishes continuation from replication. This objection targets the proposed identity rule specifically. Even an account positing a sole producer of esse can retain an intrinsic historical criterion for *which* patient it produces or sustains. |

The primary texts sharpen the disagreement. Feser explicitly appeals to
substantial form and designated matter for the diachronic identity of
substances, while defending conservation. On his account prior combination leaves a present
actual combination to explain. Schmid's local deduction instead uses this
bearer's prior presence, absence of a cessation inducer and a causal
requirement on change. That deduction does explanatory work once the law
covers existential loss. It does not identify one among rival candidates for
the later bearer. Given the museum's independent artifact criterion, both
reconstructed accounts accommodate its identification. The stronger
principle that the earlier existence must itself *cause the later existence*,
rather than contribute to individuation, would put pressure on exclusive
production by the source. Even that principle allows jointly necessary
causal contributions. [Feser, paragraphs beginning “This makes it sound”
and “Rather, a critique,” passage a73919f4](../../corpus/passages/feser-inertia-reply-2021.json),
[Schmid, paragraphs beginning “For S to fail” and “Here, we seem,” passage
79716a2e](../../corpus/passages/schmid-inertia-reply-3.json), and
[Vander Laan, “Persistence and divine conservation,” abstract](https://doi.org/10.1017/S0034412506008262).

**What could discriminate the survivors?** Hold the earlier individual,
source, ordinary material history through t0 and independently specified
destructive conditions fixed. Compare an independently identified withdrawal of s's present exercise,
with every other strict giver excluded, including self-giving. If the existential no-loss law applies independently to
this case and withdrawal supplies no cause of loss, it predicts that x
survives. If this exercise is indispensable to x's esse, x ceases even if a
matching successor appears. Use the provenance test to distinguish the latter
from survival whenever it can be applied. The missing evidence is an
independent way to identify withdrawal of *existential* input and establish
its effects at this bearer. Removing a mount can alter a posture while the
plaster survives. Identifying withdrawal solely by x's disappearance would
assume the dependence in dispute. Conversely, holding the entire successful
continuation fixed in the withdrawal test assumes survival. Identity gives
no new reason to prefer either survivor on this existential question. The
strong case for historical contribution stands at the narrower scope.

**Existing formal evidence and route.** Section 8's
`c3ActualWorldControls : C3ActualWorld.Certificate` uses one rigid
`false` in the same history with origin-only and sustained giving.
PR #1895 varies withdrawal and the classification of loss. In #1899,
`limitPersistenceControls : LimitCertificate` checks the interval law
`∀ v x s t, s < t → h.IsAt v x s → ¬ h.IsAt v x t → ∃ u, s < u ∧ u ≤ t ∧ D v x u`.
Its repeated x already designates the same individual. None of these types
reconstructs a bearer from later observations. Another pair of giving
assignments or a Boolean flag for material continuity would duplicate that
assumption. [Withdrawal comparison](law-actuality-743.md#c3-law-preserving-withdrawal-test-for-the-same-existent-1801-2026-11-23)
and [limit comparison](../eternity-dependence-connection.md#c3-from-finite-survival-to-survival-at-a-limit-2026-11-23).

Weak C3 (`40a97664`) requires *some* giver at every present received-esse
instance. Identity supplies no giver at t1. To get the specified esse-cause
as sustainer, argument `366a6ea3` consumes C3 with reception `da72ae93` and
concurrence `d7f5a528`, yielding `ce55210c`. With contact `c4661518` and
the co-presence-to-dependence bridge `ffcb81fb` this supports `2068f91c`
(§1), which also retains its direct option. Argument `57f22435` needs that
dependence plus `c99f9d23`, `82eeeb3c` and `a8298fbd` for the actual
concrete ground edge `cb1cdea9`. The GOD_4 routes `3367bf93` and
`fc46b7f9` need the edge at their own maximum/root pair and the remaining
root and grading premises. The tracked material x supplies neither that pair
nor a necessary or underived source. The inference from identity to present
production remains open, with no new support option or discharge.
[Instances used by the esse-root routes](esse-root-leaves.md#b-where-the-fourteen-enter-which-instance-each-route-consumes-and-bypasses).

## 11. What turns received esse into giving at the same moment? (2026-11-26)

Fix one history, the same received-esse bearer, and a moment of its presence.
`EsseReceivedIn x z` is receiver-to-received-act composition. Neither the
principle `z` nor the bearer is thereby an efficient giver. The arguments
start with this positive reception predicate. A claim that x's essence
fails to account for its esse would still need to be connected to that
predicate if it were the only premise about composition. The inherited
`GivesAt v g x t` means productive exercise of the causation of x's esse
with t on the effect side. This allows timeless action to be indexed by
its effect's presence, once that interpretation bridge has been defended.
Earlier production, preventing destruction, giving an accidental perfection
and explaining a later fact by an earlier fact are different roles.

| Reading | Premises that suffice for a distinct giver at the recipient's moment | Where onset-only giving survives |
| --- | --- | --- |
| Explanation of presence at each moment | Momentary PSR `9a14bdd8`, productive bridge `d86c9de9`, and scoped direct non-self-giving | The fact explained is the recipient's presence at t. An earlier presence plus a law can explain that very fact without a giver at t. The model keeps the PSR and rejects the productive bridge. |
| Origin relation obtained at each moment | Accompaniment `9fecbef4`, term giving `6da7d94a`, and origin irreflexivity | The originator is present and is still the related term at t, while idle at t. Accompaniment and even term coexistence leave term giving open. An origin relation restricted to onset instead drops accompaniment, as in the earlier relational-receipt controls. |
| Receipt while present | Present receipt `964928dc`, correlativity `52b05849`, and scoped direct non-self-giving | Standing receipt (RECEIVES_ESSE_AT_2) holds throughout and correlativity fails. Passion receipt (RECEIVES_ESSE_AT_1) has correlativity by construction but occurs only at onset in the same giving history. |

The three deductions are assemblies for the strong conclusion `76d2cc96`,
using the same `CausalityFrame` and receipt predicate per argument. Previous
results derive the weaker conclusion `40a97664`, allowing a self-giver.
Direct non-self-giving is restricted here to received bearers when present.
There is prima facie warrant on the productive reading: an operation of x
presupposes x is actual, so that operation is a poor candidate for the direct
source of the very actuality it presupposes. An inertialist who invokes the
bearer's earlier actuality can grant this restriction. A putatively productive
intrinsic power would need an account of how it produces its own bearer at
that moment without the explanatory dependence running both ways. The same
reason motivates origin irreflexivity on the derivative-source reading,
while a reflexive requirement or an account using distinct proper parts
requires its own analysis. Both commitments are open and neither requires
general causal transitivity, well-foundedness, or a denial of self-maintenance.

The [finite Lean controls](../../TruthCore/Causality/ConcurrentGiving.lean)
fix one history and two individuals at both supplied moments. True gives
false esse at moment 0. At moment 1 false is still present with received
esse, still related to true, and has no giver. `JointInertia` checks the
explanatory failure, relational failure and standing-receipt failure jointly;
`OnsetOnlyPassion` checks the passion case with the same history and giving.
The cessation law holds because neither bearer is lost in the model. The
origin-or-inertia explanation at 1 uses prior presence and the lack of an
inducer, so its reason is inhabited even though the productive bridge fails.
These are structural surrogates. The model holds identity fixed and includes
no experiment isolating a conserver and no account of why the persistence
law governs real received esse.

**Positive rival and its price.** The matched no-change reconstruction
takes the same bearer's earlier actuality, no inducer of its loss, and a
law requiring an inducer for existential cessation. If the bearer were
absent later, that would be a loss and hence would require an inducer.
This supplies a conditional explanation of the particular later fact and
targets, in `d86c9de9`, the requirement that some giver act at that same moment whenever the received bearer's presence is explained, and the
equivalent productive burden on standing receipt. The positive rationale
is the causal requirement on changes and the familiar difference between
producing something and keeping it, illustrated by Aquinas's own builder
and house. This illustration concerns a cause of becoming. It supplies no
observed case of an independently identified, strict cause of esse ceasing
to give while the very same effect remains. The law must cover existential
loss, and the no-inducer claim must survive the conservator's reply that
withdrawal of a necessary giver could itself explain loss. Merely having a
deduction from a history and a law leaves open whether they explain the
whole history's actuality and whether further production also occurs.
See the pinned [Schmid reply, part 3](../../corpus/passages/schmid-inertia-reply-3.json)
and §§7–10 above. [Beaudoin's publisher abstract](https://doi.org/10.1007/s11153-007-9113-1)
identifies a narrower scope, the universe's fundamental material; extension
to all received-esse bearers would require a further argument. The
Mackie-style distinction between an earlier origin and a concurrent
sustaining series is used here as an analyst contrast. Schmid supplies the
later-persistence explanation the model uses; the originating-giver branch
at the first moment is this repository's addition. No new attribution record
is created for either author.

**Provisional assessment.** The strongest positive warrant for concurrent
giving is the direct conservation account in I q.104 a.1 co. and ad 4:
given the cause-of-being reading, the dependence is on productive exercise
throughout, and the action continues without motion or time. The approved
[support relation](../../corpus/relations/a32d71ad-483a-4ad4-9afb-80dccbf61004.json)
leaves open the coverage of all route receivers and the effect-side
`GivesAt` calibration. Continuing receipt and the continuing origin
relation are intelligible in both frameworks. All three assemblies put
the contested productive step on the open premise side; they provide no
new independent warrant for that step. Direct concurrent giving remains
a defensible primitive option. To revise this assessment, fix the same
bearer, origin, powers and cessation conditions, then justify either
why withdrawal of productive giving is sufficient for that bearer's loss
or why the prior-state law suffices when that giving is absent. An example
about the loss of an accidental quality needs a further bridge to the
loss of the bearer itself.

**Downstream.** Concurrence `d7f5a528` constrains who gives when some giving
occurs. It holds in the onset-only model while sustaining `23e04ae5` fails.
The q.104 distinction gives a reason to investigate the sustaining reading
for direct causes of being. An uncalibrated tenseless edge could instead be
assigned to an originator whose exercise has ended. The existing
`sustainingOfConcurrentActualization` uses concurrent actualization,
concurrence and `da72ae93` to reach `ce55210c`, the restriction to causes
distinct from their effect. Even strong concurrent giving permits a relay
of distinct givers, as in the existing concurrent-actualization control.
The immensity presence route also uses `c4661518` for contact. I q.8 a.1–2
supports presence by power to an immediate effect, leaving the
[typed co-presence calibration](../../corpus/relations/485c891d-a69b-44eb-ab29-97a4a7d37d30.json)
open. A Second Way application must additionally identify concurrent
giving with the selected per se dependence and supply its relevant ordering
and regress premises. No claim here establishes conservation, omnipresence,
immensity, or that regress step.

[Attempt record](../../corpus/attempts/2bd8f067-5a81-48ac-b8c9-d973ce5609e9.json)

## 12. Contingency when no loss inducer occurs in either modeled history (2026-11-26)

Denying the productive bridge takes one exception: this receiver is present and its presence is explained at this moment, although nobody gives it being then. Schmid's positive account supplies more than that denial. An origin explains how the bearer came to exist. Its earlier presence, a law covering existential loss, and the absence of an inducer together explain why it is still here. This respects the difference between coming into being and continuing as the same thing. The earlier state is explanatory input; the bearer need exercise no efficient causation on its own act of being. The Mackie-style origin/continuation distinction and Beaudoin's narrower proposal about fundamental material motivate testing this account. §11 gives the source boundaries. The all-bearer law below is an analyst reconstruction of the strong version.

A stronger transtemporal proposal gives earlier phases of a self-maintaining physical process a causal role in bringing about its later phases. This gives the Mackie-style account a positive mechanism. Its application to esse needs an argument that phase succession accounts for the continued existence of the bearer. At actual moment 2, the token `.inr 1` cites the same receiver’s presence at moment 1 and the inducer-free interval (1, 2]. A causal contribution by an earlier phase would require a further premise. For the interpretive lead see [Schmid’s discussion of Mackie, *The Cement of the Universe*, p. 156](https://majestyofreason.wordpress.com/2021/07/31/so-you-think-you-understand-existential-inertia/). Direct attribution to Mackie remains deferred.

**What the law costs.** Fix one interval with presence at its start. If the bearer is absent at its end, the law requires an inducer somewhere after the start and through the end. Classically this is exactly equivalent to survival to the end of *each* such clear interval. Multiplying the two formulations supplies no additional warrant. A single exception to concurrent giving needs neither a universal law nor universal indestructibility. A law-based explanation needs coverage for the selected bearer and interval; a general explanation on this basis takes on the corresponding general coverage. The limit case already distinguishes all-interval coverage from finite successor coverage. Counting mere absence as its own inducer loses the explanatory advantage, because absence would then be needed to establish the alleged explanation of loss. [Interval theorem](../../TruthCore/Results/Explanation/InducerFreePersistence/Solution.lean) · [Limit control](../../TruthCore/Explanation/LimitPersistenceLaw.lean)

**Two histories with no loss inducer.** Consider the same recipient in both accessible worlds of §9's necessary-origin model. The inducer predicate is empty by stipulation at every supplied time in both worlds. The model represents occurrences and leaves destroyers’ powers unspecified. Wherever the recipient originates, it survives every subsequent supplied moment. In the alternative it never originates. Its contingency therefore has a witness even though its destruction has none. At actual moment 2, its presence at 1 supplies the same explanatory token under both giving assignments. Standing receipt holds there under both. On origin-only giving there is no giver then; on sustained giving the original giver acts then. Each assignment satisfies the same momentary PSR (dossier `9a14bdd8` records its status as open), even on the stipulated continuation explanation. Neither modal contingency nor the PSR discriminates. This is a result about the two supplied worlds. It supplies no evidence that an actual bearer is indestructible. [Matched assignments](../../TruthCore/Results/Explanation/InducerFreePersistence/Solution.lean)

**Does its nature already include existence?** Give that very receiver a nonempty nature dictionary with one essential truth: if it exists at the designated slice, it owes its origin at moment 1 to this giver. That conditional holds in the world where it never exists as well as where it does. No truth in this dictionary entails its existence. Both giving assignments remain available. This tests the consequential nature-entailment reading (`EXISTENCE_IN_ESSENCE_5`) alongside standing receipt. Neither the dictionary nor the received-esse predicate proves a real distinction between metaphysical constituents. Assuming that receipt *itself* is a current productive passion changes the test: correlativity then follows by definition, and its application at every moment is exactly what the origin-only reading contests. [Receiver nature control](../../TruthCore/Results/Explanation/InertialReceiverNature/Solution.lean)

**Overall provisional judgment.** The encoded contingency and the failure of nature-entailment coexist with either giving assignment. The model contains no induced loss. Inertia’s prima facie case comes from the causal requirement on change in §11: an origin accounts for initial actuality, and a subsequent loss would call for an inducer. The builder example shows why that asymmetry is plausible for causes of becoming: the house can outlast the builder’s work. Extending that reasoning to the loss of the bearer’s esse requires grounds for the law’s existential scope and for deciding whether withdrawal itself induces loss.

The conservationist can grant that prior actuality and a law account for the transition and still ask what accounts for the receiver’s derivative actuality at moment 2. On the cause-of-being reading, the receiver owes its very esse to the giver throughout. ST I q.104 a.1 co. and ad 4 describes the giving action as without motion or time. Applying that account here requires identifying the receiver as within its scope and calibrating strict giving at the effect’s moment. Feser’s circularity objection applies where a present power produces the very actuality that exercising it presupposes. The earlier-state token makes no such claim. [§10’s discussion of Feser](#10-which-later-individual-continues-the-earlier-bearer-1801-2026-11-25) · [q.104 support relation](../../corpus/relations/a32d71ad-483a-4ad4-9afb-80dccbf61004.json)

Both accounts retain positive warrant on their respective readings. The productive bridge requires some giver at each explained moment. Identity across moments, divinity and timelessness require further support. §10 supplies the discriminating test. Fix the same receiver, its initial origin and independently specified destructive conditions. Establish independently of its later fate that the original source has ceased strict giving. Exclude every other strict giver at the tested moment, including the receiver itself. Does that very receiver survive? Explained survival under those conditions supplies an exception to the bridge. Loss favors the conservation reading insofar as withdrawal accounts for it. Whether the inertia law covers existential loss and how withdrawal should be classified remain open.

The same judgment bears on the sustaining reading used by the per se Second Way, the immediate-contact route to presence (`c4661518`), and the exercise of power over esse (`d1593e5c`). The Second Way still needs per se ordering and regress premises. The presence route needs a contact calibration. The power premise concerns a designated giver withholding across accessible worlds and the capacity to unmake this bearer. Ending an exercise between moments, or never originating a bearer in another world, supplies no such withholding-to-unmaking bridge. This comparison supplies no new discharge on those routes.

## Research attempts citing this note

- [Necessary origin with existential inertia against the esse-priority source bundle](../../corpus/attempts/4b051644-666b-451e-8e09-b5b9356932f9.json)

## 13. Finite interventions and the productive bridge

Issue #2053 targets the productive bridge
[`d86c9de9`](../../corpus/statements/d86c9de9-25be-488b-b3b7-69f5f4eb80b8.json).
With the momentary PSR it feeds weak concurrent actualization `40a97664`,
then the sustaining-cause reading `ce55210c` and the esse-dependence premise
`2068f91c`. These are links already in the graph. The [attempt record](../../corpus/attempts/176d45ae-c023-4c72-b2bb-86a09326b798.json)
tracks the open calibration.

[StructuralCausalModel](../../TruthCore/Causality/StructuralCausalModel.lean)
uses directed parent slots and well-founded recursion. A surgery forces a
chosen equation to a constant, keeping the context and remaining equations
fixed. This captures selective experimental control, for example turning off
a represented lamp input while holding the rest of the circuit fixed. An
observationally correlated switch position can instead be a record of a shared
controller. The graph bounds equation reads and can include idle slots. Even
active paths can cancel, as in `BinaryButFor.ancestry_without_butFor`, with
`Y = X` and `Z = (X == Y)`. Each parent is below its child in the selected
recursive evaluation. This warrants well-foundedness of the model's input
relation and leaves well-foundedness of any actual giving relation open.

[Identification](../../TruthCore/Causality/StructuralCausalIdentification.lean)
fixes one pair of Boolean reports and the same finite context law. A fair
bit and a uniform four-way draw have factored point masses. The draw flips
a bit with probability one quarter. The forward model sends the fair bit
through a noisy equation from X to Y, the reverse model sends it from Y to X,
and the confounded model reads the fair bit in both equations. The joint
reports agree in law and all four pairs have positive mass. At
`do(X = true)` the Y masses at true are respectively 3/4, 1/2 and 1/2. The
common observational conditional is 3/4. The first two mechanisms use
separate exogenous inputs for root and child; the confounded mechanism shares
one input even though the two context coordinates are independent. Acyclicity,
full observational support and independence of the distinct noise coordinates
therefore leave the direction open. Identifying the forward effect from its
observational conditional here relies on the forward equation structure and
independence of the X-generating bit from the disturbance in the Y equation.
The intervention separates forward from both controls under the same context
law and surgical readout. The reverse and confounded controls share that
particular intervention outcome.

[Adapters](../../TruthCore/Causality/StructuralCausalAdapters.lean) preserve
the old Boolean but-for test, the two public settings in the response-parity
example, and both paired switches for each selected report. The actual-graph
adapter takes the shared frame, actual carriers, causal adjacency,
well-foundedness, and equations as distinct inputs. The
[productive-deletion adapter](../../TruthCore/Causality/StructuralCausalDeletion.lean)
cuts gates of existing contributor records and preserves the intrinsic basis.
The supply readout is exactly the old inductive supply test on the restricted
groups, in the finite acyclic fragment. Cutting a record's effect on supply
and forcing an event absent are different operations.

**OPEN connection to strict esse-giving.** At a selected later moment, keep
the same received-esse bearer, earlier presence, original origin and absence
of independently specified loss inducers fixed. The matched surrogate uses
the first input as earlier presence, the second as the current operation and
the output as later presence. In `Mechanism.responsive` the output reads
both inputs. In `Mechanism.background` it computes `u.first && u.second`
from the unchanged context: it tracks the earlier-presence bit only when the
second background bit is true, and at `⟨true, false⟩` it returns false
despite earlier presence. The model has no loss-inducer predicate.
`Mechanism.single_channel_contrast` checks their agreement under natural
observation. At the selected all-true context, the background output retains
the earlier-presence value after the cut, while the responsive model loses
it. Interpreting that response as inertia requires independent grounds for
applying the persistence law to this bearer and interval, including grounds
for treating withdrawal as inducer-free. The old positive inertia account
proposes such a law; its application to existential loss remains the open
question of the preceding section. A mere latent lookup is evidence of
formal underdetermination, while the persistence law would do the
explanatory work in the inertia interpretation.

### What a calibrated cut tests

[Calibration](../../TruthCore/Causality/StructuralCausalWithdrawal.lean)
maps the natural and surgically modified valuations to a directed admissible
pair in one `CausalityFrame`. This test uses the earlier point as the
bearer's onset. The earlier bit represents the same bearer beginning at
the same moment, where the same distinct originator gives it being in
both histories. Absence of loss inducers is supplied for that bearer in
both intervals, with the later endpoint included. The current bit is true
iff the designated giver exercises strict `GivesAt` for the bearer at the
later moment of that history. The cut value of this bit excludes that giver
independently of the later report. A separate condition excludes every
other giver at the cut endpoint, including the bearer itself. The later bit
is true iff the same bearer is present there. This last identification
requires a criterion for tracking the bearer of esse across histories, as
in §10. A persistent report for a successor would give the wrong witness.

The directed admissibility criterion is an application input. It licenses
comparing the specified natural history with the cut history under those
controls. Its justification must identify what fixes the giving operation
and the loss background before reading later presence. The lamp illustrates
selective control of a circuit with independently identifiable components and
an illumination readout. A switch that merely records a controller state
supplies a contrasting case, as does a lamp that continues to shine because
a second power source takes over. The strict exercise that produces a
bearer's esse and a criterion that excludes every other such exercise lack
a corresponding independently calibrated case here. The equations are
acyclic in their input graph. Neither the calibration nor its proof
ascribes transitivity, asymmetry or well-foundedness to strict giving or
to admissibility.

[calibratedContrast](../../TruthCore/Results/Causality/StructuralCausalWithdrawal/Solution.lean)
uses the computed responses in `Mechanism.single_channel_contrast`. The two
consequences apply separately, each in the frame of its supplied calibration.

| Cut outcome | Checked consequence | What would revise the assessment |
| --- | --- | --- |
| Background response retains presence | With received esse and a reason for presence at the cut endpoint, this instance falsifies the productive bridge in the matched frame. | Supply independently justified strict withdrawal, giver exclusion, bearer identity and a reason for the continuing presence. |
| Responsive mechanism loses presence | With the earlier presence and no loss inducer in the interval, this instance falsifies `CessationNeedsInducer` in the matched frame. | A warranted calibration of this loss would favor sustaining for the tested bearer. A universal productive premise would still require an argument extending that case to the other receivers and times it covers. |

The survivor uses one reason for presence, which the existing momentary PSR
would supply. The distinct-giver condition is a separate input to the
existing argument for strong concurrent giving. Since the survivor excludes
every giver, it also challenges weak concurrent giving in the same frame.
The stage-1 consumer is the existing route from weak concurrent giving
through the sustaining reading, contact `c4661518` and the co-presence
bridge to `2068f91c`. The registered result diagnoses the contested input
`d86c9de9`; the case has no calibrated instance to use as a refutation.
The direct option for `2068f91c` and other routes require their own assessment.

### Warrant and next test

The conservation account in §11 gives positive warrant for concurrent
exercise insofar as the giver is a direct cause of the bearer's being.
The inertia rival explains continuing presence by earlier actuality and
a law that existential cessation requires an inducer. Prior presence and
an independently established inducer-free interval would give the
`originOrInertia` reason. The law would then rule out absence in that
interval. Applicability of the law to the bearer and interval would give
the explanation force beyond the background equation's latent lookup.
The finite model imposes no law on loss and supplies no independent
classification of withdrawal. If withdrawal itself induces loss, an
observed loss is compatible with the inertial law. That response violates
the specific no-inducer calibration in the table. No conflict with an
accepted floor premise has been identified for inertia at this scope.

**Provisional assessment.** Strict giving remains a defensible direct
commitment. The SCM adds a discriminating test and leaves the positive
warrant and standing of the two accounts as assessed in §§11–12. The
unresolved step is an independently justified interpretation of the
designated giver's later nonexercise as an admissible change in strict
esse-giving with loss conditions held fixed. The next test is to specify
one begun received bearer, a criterion for presence across the compared
histories, and a criterion for that giver's exercise independent of its
effect's fate. Apply the losing or surviving branch only once the same
interval has been checked for independently characterized loss inducers
and alternative givers. A rival that counts withdrawal as inducing loss
must say how that event brings about cessation in this case. A loss readout
alone gives no classification of the mechanism.

`selection_forced` can transport the Boolean assignment only within its
valuation worlds. The operation event here is
`¬ F.GivesAt cut giver bearer later`, which follows from the false bit and
the channel binding. The [agent-absence selector](https://github.com/moritzbrantner/formal-logos/pull/2089)
targets `¬ F.history.ontic.ExistsAt cut giver`; reaching that event would
require an additional implication from nonexercise or an independently
chosen agent-absence history. The existing STIT `Admissible` includes
the giver's continued ontic existence. Using a STIT cell for this cut
would require identifying its mapped history and verifying absence of the
same giver's exercise for the same recipient and effect moment. The
withdrawal result uses no such transport.
