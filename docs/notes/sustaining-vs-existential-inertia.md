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
provisionally by Feser's circularity argument at concurrence `d7f5a528`. Also
read, not edited: the 2026-11-18 cluster assessments on the open branches of
PR #1769 (lane B, `causal-dependence-support-investigation.md`, rival row 3) and
PR #1777 (lane F, `esse-root-leaves.md`, row 7 and its "most discriminating next
test"), and the holding-motion module on the C\* branch.

## 1. The sustaining sibling of `2068f91c` (formal next test, done)

Module `TruthCore.Causality.SustainingDependence`, spec
`specs/sustaining-dependence.toml`.

| Record | Lean | Content |
| --- | --- | --- |
| `149ed837` sibling | `SustainingEsseCauseIsDependedOn` | if c ≠ x causes x's esse and sustains x (CAUSE_OF_BEING_2) in every history in which x is present, then `DependsForBeing x c` |
| `ffcb81fb` co-presence bridge | `CoPresentEsseCauseIsDependedOn` | if c ≠ x causes x's esse and, in every history, is present whenever x is, then `DependsForBeing x c` |
| `1f2ae3c4` | `sustainingSiblingOfCoPresence` | contact `c4661518` + bridge ⊢ sibling |
| `f8519735` | `esseDependenceOfSustaining` | `ce55210c` + sibling ⊢ `2068f91c` |
| `2574412d` | `sustainingSiblingOfEsseDependence` | `2068f91c` ⊢ sibling (strength order, relation `e6d1be09`) |
| `886615a9` | `controls` | parts 1–4 below |

**Outcome.** The lane F test succeeds with one explicit extra bridge, as that
note predicted ("a law from `SustainsBeing` to the counterfactual D"). The law
is the co-presence bridge composed with contact. So on this route `2068f91c`
costs exactly `ce55210c` + `c4661518` + `ffcb81fb`; `frontier-diff` moves
`2068f91c` from supported to proved-unestablished, and adds `ffcb81fb` as the
one new bare premise.

*Warrant of the bridge.* In the standard counterfactual logics (Lewis,
Stalnaker) a strict conditional entails the counterfactual, vacuously when the
antecedent is impossible; DEF-DEPENDS-FOR-BEING explicitly includes impossible
antecedents. The `CausesIn` antecedent blocks the overgeneration of purely
modal dependence (dependence on any necessary co-existent). The antecedent is
pointwise in every history, so it serves both readings of "would not be"
(never would have been; would not be then), the originating/sustaining fork of
D (#1626). *Its real condition* is history coverage: the model's histories must
represent the alternatives relevant to the counterfactual. On a one-history
model the bridge would be a co-presence-plus-causation principle that a case of
redundant givers of esse could falsify; no such case is on file (the relay of
`955ef523` part 3 concerns illumination). Grade: strong prima facie *given*
history coverage; coverage itself is the same assumption that makes
`ce55210c`'s "in every history" meaningful, and is not independently assessed.

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
The dispute over `2068f91c` on this route now sits wholly in `ce55210c`, and
through `366a6ea3` in `40a97664`. The direct option of `2068f91c` stays
available; it is not removed or penalised by the new derivation.

## 2. The rival's itemised price, by direction of entailment

Owner direction (2026-11-19, via the coordinator): record honestly what
rejecting concurrent actualization forces the rival to reject. Two shapes:
(a) independently plausible propositions that **entail** `40a97664` or
`ce55210c`, so that modus tollens spreads the rejection; (b) routes that merely
**rest** on the premise, single points of failure that add no price.

### (a) Candidates that would entail the crux

| Candidate | Entailment shown? | Independent of `40a97664`? | Can the rival reject it on independent grounds? | Price item? |
| --- | --- | --- | --- | --- |
| Onset/parity: coming to be needs a present giver, and persistence is the same kind of fact | **Yes**: onset `fa3e228b` + parity `5b24ef26` ⊢ concurrent actualization for begun things `f4850897` (`d2e4867c`); `40a97664` ⊢ `f4850897` (`6d90f126`, relation `413800c5`). With natural-number times `f4850897` and `40a97664` coincide for present things. | **Onset yes, parity no.** The inertial history satisfies onset and fails parity (control part 5). Given onset, parity is `f4850897` restated: its only content is that later moments need a giver like the first. No warrant for parity beyond that for `40a97664` is on file. | Yes, on the ground already recorded against `40a97664`: onset is a change (not being, then being), persistence is not, and the shared causal law requires an inducer for change only. That asymmetry is principled, not ad hoc. | **No new item.** Rejecting parity is rejecting the crux once. Onset is shared; it costs neither side. |
| Essence/esse union: what unites a received esse to its essence at each moment (ST I q.3 a.7, "quae secundum se diversa sunt, non conveniunt in aliquod unum nisi per aliquam causam adunantem"; claim `78cc9f45`, statement `58445bd6`, cited from the corpus's earlier reading, not re-read here) | **Only on a synchronic reading.** Read tenselessly, as the existing statement `58445bd6` is ("something unites them into it"), it is satisfied by the originating cause: `955ef523` part 1 already has the reception bridge, a cause of being and no later giver. Read synchronically ("at each moment of presence something unites them then"), uniting esse to its receiver at t *is* giving being at t on the STRICT reading of `158301bc`, so the premise is `40a97664` under another name. | No: the synchronic reading is the crux re-presented (AGENTS: different presentations of one assumption are not more evidence). No Lean statement was added, because it would be a renamed transcription of `ConcurrentlyActualized`. | Yes: the inertialist accepts the tenseless reading and explains the union's continuation like any other continuation. | **No new item.** |
| C\* in the holding sense (other lane, branch `agent/cstar-actualization`, `HoldingMotion`) | **No.** That module's own control (part 3, as reported in its doc comment) shows C\* in the holding sense entails neither the respect-general premise `LackableActsAreHeld` nor its esse instance. | — | — | **No item.** If C\* reduces to concurrent actualization it rests on it (shape (b)). |
| Respect-general holding (`LackableActsAreHeld`, same branch): every lackable act is presently actualized by another | Reported there to give C\*; its esse instance would give the strong `76d2cc96` and so `40a97664`, provided the instance is aligned with received esse. Not checked here. | Stronger, so not a re-presentation. | **Yes, cheaply**, if velocity counts as a lackable act in the holding sense: in Newtonian and later mechanics a body keeps its velocity with nothing presently acting on it (the first law; momentum conservation). This is an independently justified objection to a respect-general continuation principle. The Thomist reply that uniform motion is a state, not a change, is the inertialist's own move. | **Low.** It adds a principle the rival can drop with physics on its side. It shows the sustaining case must be esse-specific, which `40a97664` already is. |
| Synchronic actualist explanation (presentism + "only what exists at t explains what exists at t") | **No.** It forces *some* present explainer, which a presently holding law or a persistence power (the strong version's rival) satisfies; it does not force a giver. | — | The rival can also reject presentism (relativity of simultaneity is an independent justification). | **No item.** |

**Finding.** No proposition was found that is (i) independently warranted,
(ii) not a re-presentation of `40a97664`, and (iii) entails it. The extrinsic
inertialist's price at the crux is therefore **one item**: reject `40a97664`
(equivalently, parity given onset, or the synchronic union principle). The
respect-general holding principle entails more, but the rival can reject it on
independent physical grounds. This is a clean negative result, not a failure to
look: each candidate's entailment was shown or refuted above.

### (b) Routes resting on the crux (single points of failure, no added price)

Rejecting `40a97664` removes, through `366a6ea3`: `ce55210c`; the strong
sustaining reading `23e04ae5` (no independent warrant on file); the immensity
presence step `9469ab62` and the IMMENSE_2 → IMMENSE_1 route `8bf775e9`; and,
through §1, the new support option for `2068f91c` and hence for the esse-root
identification at (maximum, root). It also removes any C\* route that reduces
to concurrent actualization. The rival does not thereby reject `2068f91c`'s
direct option, the reception bridge `da72ae93`, contact `c4661518`, onset, or
the shared causal law. These are losses to the case if the crux fails, not
costs to the rival.

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
   in that persistence; the explanatory-circularity objection to Humean laws
   (Armstrong 1983, *What is a Law of Nature?*; contested by Loewer 2012 and
   Hicks & van Elswyk 2015; none pinned here) bears on that version only. A
   governing-law or primitive-law version avoids it at the price of a
   primitive law, matched by conservation's primitive standing dependence.
   (ii) A persistence-power version rejects concurrence `d7f5a528` and meets
   Feser's circularity reply (`05bc2722`, provisional), which targets a
   simultaneous self-giving power; a diachronic version (earlier stages cause
   later ones, immanent causation) is not on file and would need its own
   assessment; it is recorded here as an unexamined lead with no weight.
4. **Global scope** (shared): both accounts owe an account of the whole
   history's obtaining; neither is exempt (2026-11-17 section, unchanged).

## 3. The other candidate tests

- **Parity**: done in §2; no substantive objection to extrinsic inertia
  identified from parity alone.
- **Is inertia's PSR variant stable?** Yes at local scope: the explanandum
  "S exists at m" receives a deductive explanation from (S at m−1, no inducer,
  causal law); the negative fact is explained by the world's state, the law is
  shared. No self-undermining was found. The difference from the conservation
  side is not the PSR but whether explanation of present actuality must be
  synchronic; that is the crux again.
- **Physics at matching scope.** For *esse* the physics is neutral: conservation
  laws (energy, charge, baryon number) describe what persists under the dynamics
  and derive from symmetries of the laws (Noether); each account can absorb them,
  inertia as its law, conservation as the regularity of the giving. Existential
  loss in physics always occurs through an interaction (decay, annihilation),
  which both accept. Composite bound states depend counterfactually on present
  interactions, but that is dependence on the constituents and the dynamical
  law, not on a giver, and it relocates to the fundamental constituents, whose
  persistence physics treats as lawful. For a *respect-general* continuation
  principle physics is not neutral: inertial motion tells against it (§2).
- **Explanatory depth.** Conservation explains why x is actual now, beyond why
  x has not ceased; that is a gain only if present actuality is a genuine
  explanandum over and above continuation, which is the crux. At local scope
  inertia has one primitive fewer (no standing giving after onset); parsimony is
  a weak, defeasible tie-breaker here and does not touch the global scope.

## 4. Overall provisional judgment (2026-11-19)

On the fixed meanings (STRICT `GivesAt`, inclusive presence, tenseless
`CausesIn`, DEF-DEPENDS-FOR-BEING), **no discriminating test is available at
matching scope; both accounts stand, with prices**. This restates, and does not
revise, the 2026-11-18 cluster judgment for `40a97664` and `ce55210c`.

- *Strongest warrant for sustaining:* a coherent account in which a received
  act of being is a standing derivative actuality, unifying origin and
  persistence under one relation (giving), with positive explanatory content
  (why x is actual now), the q.104 a.1 distinction of causes of becoming and of
  being, and no substantive objection to a genuinely identified instance of
  standing productive dependence. Price: `40a97664` as a primitive, concurrence
  `d7f5a528` (no warrant on file), reception `da72ae93`, and now, for
  `2068f91c`, contact and the co-presence bridge (strong given history
  coverage).
- *Strongest warrant for extrinsic inertia:* the shared causal law on change
  plus prior actuality deductively yields persistence; it is PSR-compatible, has
  one primitive fewer locally, and has the history of mechanics as a precedent
  that continuation principles can fail for states. Price: one item at the crux
  (reject `40a97664`, re-presented as parity or synchronic union, which adds
  nothing), plus its primitive of diachronic sufficiency for existence; its
  Humean sub-version carries the explanatory-circularity objection.
- `2068f91c`: unchanged as a direct option (strong on the aligned sustaining
  reading, lane F row); newly, a verified conditional support through
  `ce55210c`, contact and `ffcb81fb`. On that support it is no better than
  `ce55210c`.

**Revision conditions.** Any one of these would move the judgment: an
independently warranted proposition, not a re-presentation of `40a97664`, that
entails it (would add a price item); an independently justified account of why
present actuality of a received act is an explanandum distinct from its
continuation (would favour sustaining); an independently supported case of a
received-esse thing persisting with no giver, or of redundant givers of esse
(would weaken `40a97664` or the bridge); a defensible diachronic
persistence-power account (would make the persistence-power rival stronger);
an assessment of history coverage for the bridge.

**Next test.** The informative remaining question is the second revision
condition, at the reception premise: whether DEF-ESSE-RECEIVED-IN's "standing
to it as receiving potency to received act" is a present-tense receipt (which,
with the correlativity of receiving and giving, would make `40a97664` close to
analytic and move the whole dispute to `da72ae93`) or a historical one. Typing
`ReceivesAt v z x t` and a correlativity premise would show exactly where the
dispute then sits. It needs no new source.

## Self-sweep

Claim vs type for every new record is in the PR body. No source claim is added;
Schmid, Feser and q.104/q.3 are cited only through records already read and
pinned or recorded in the corpus. No objection above is presented as evidence
unless its target, mechanism and independent justification are named; the
diachronic persistence-power account and the Humean-law literature are leads or
sub-version costs, as labelled.
