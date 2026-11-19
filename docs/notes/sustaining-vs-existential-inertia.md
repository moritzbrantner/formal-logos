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
step: a parent that only originates does not satisfy the sibling's antecedent.
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
| De ente c.4 / ST I q.3 a.4: whatever belongs to a thing and is not from its essence is caused by another | **Analyst argument, not typed here.** The same fork as the union row: "is caused by another" read tenselessly is satisfied by an originating cause; read as "is being caused by another at each moment of its presence" it is `40a97664` restated with the reception bridge. The existing De ente material (`docs/notes/de-ente-*`) was not re-read for this question. | The tenseless reading is independent and is on the route as the reception and coverage premises; the synchronic reading is not independent. | As for the union row. | **No new item** on the analysis given; a row to re-examine if a non-tenseless reading with independent warrant is identified. |
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
exactly where the dispute then sits. It needs no new source.

## Self-sweep

The claim-vs-type table for every new record is in the PR body. No source
claim is added. Schmid, Feser and q.104/q.3 are cited only through records
already read and pinned or recorded in the corpus. No objection above is
presented as evidence unless its target, mechanism and independent
justification are named. The diachronic persistence-power account and the
Humean-law literature are labelled as leads or sub-version costs.
