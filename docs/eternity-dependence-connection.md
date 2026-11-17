# External dependence on the eternity path

The current root route uses `STMT-IMMUTABLE-IS-ETERNAL` through the existing
`GodIsEternal` result. That bridge remains an explicit open premise. This reading
preserves the meanings of `PureAct`, `IsImmutable` and primitive `Eternal`.
It neither adds a duration ontology nor changes the default root route.

## Verified source context

The full Latin articles were materialized and read, including objections and
replies. The durable passage records are `AQUINAS-ST-I-Q9-A2` and
`AQUINAS-ST-I-Q10-A3`, `AQUINAS-ST-I-Q10-A4`, `AQUINAS-ST-I-Q10-A5`; q.9 a.1,
q.10 aa.1–2, and q.3 aa.1 and 4 supply context. They reuse the existing SCTA
Leonine diplomatic TEI snapshots, revision
`f9065dc8ce7bc790b8c972e49ee19d661f028be6`, with unchanged Git blob hashes and
license. The records, rather than temporary research exports, locate the text.
Diplomatic transcription noise does not erase the relevant complete clauses.

- Q.9 a.2 distinguishes potency **in the subject** from potency **in another**.
  The creator continually gives creatures esse; withdrawal would reduce them to
  nothing. An incorporeal creature can lack intrinsic potency to nonbeing yet
  remain subject to this external power. See
  `AQUINAS-ST-I-Q9-A2-EXTERNAL-MUTABILITY`.
- Q.10 a.3 distinguishes proper eternity from participated or extended uses:
  never ceasing, long duration, or stable being and operation. These are not
  automatically proper eternity. See
  `AQUINAS-ST-I-Q10-A3-PROPER-PARTICIPATED-ETERNITY`.
- Q.10 a.4 maintains the distinction even if time had no beginning or end:
  temporal succession remains different from proper eternity. That conditional
  comparison does not endorse an eternal world. See
  `AQUINAS-ST-I-Q10-A4-ENDLESS-TIME-SUCCESSIVE`.
- Q.10 a.5 permits aevum to be internally all at once while admitting adjunct
  actual or potential change. Its future existence can remain subject to divine
  withdrawal. Proper eternity excludes that compatibility with before and
  after. See `AQUINAS-ST-I-Q10-A5-AEVUM-ADJUNCT-CHANGE`.

## Conservation reading and its limits

The additional evidence is the pinned Latin `AQUINAS-ST-I-Q44-A1` and the
translated `AQUINAS-ST-I-Q104-A1-EN`. The latter uses the existing New Advent
English Dominican translation mechanism: the admitted SCTA transcription does
not cover q.104. Its response bytes and selected article text matched on two
fetches. Translation-based claims say `basis: translation`; they are not treated
as readings of the Latin q.44 witness.

Q.104 a.1 distinguishes indirect preservation by preventing corruption from
**direct, per-se conservation of esse**. A guardian can preserve a child from
fire without thereby being a direct giver of the child's esse. A builder can
cause a house to come-to-be without remaining the direct cause on which its
continued being depends. The article's divine application describes
conservation as the continuation of the action giving esse, not a new temporal
production at every instant; reply 4 expressly says the action is without
motion or time. These are the bounded readings
`STMT-DIVINE-ESSE-CONSERVATION-CONTINUES-GIVING-ESSE` and
`STMT-BECOMING-CAUSE-NEED-NOT-SUSTAIN-BEING`.

Q.44 a.1, including reply 1, connects participated esse to being caused by
another (`STMT-PARTICIPATED-ESSE-REQUIRES-OTHER-CAUSE`). Its reply 2 also warns
that an effect's necessity does not by itself exclude an efficient cause.
Neither that text nor q.3 a.4 licenses the inverse inference from
**essence–esse identity** to absence of an external cause.

For obligation B the narrow proposed reading is:

> If c directly conserves x's esse as its continuing giver, then c is a cause
> of x's being in the relevant esse sense; to use the maximum exclusion, c must
> also be distinct from x.

`DirectConservesEsse(c,x)` here is a name for a proposed interpretation, not an
introduced Lean predicate or a definition that includes `CausesIn c x esse`.
The exact interpretation into the existing `CausesIn` relation remains open.
Q.104 supports this scope through its giving-esse account; it does not justify
quantifying over every guardian, builder, arbitrary nonexistence counterfactual,
or power described only modally. The universal source reading and its
application to the same maximal root witness would both have to be explicit
before advertising a further derived result.

If that interpretation is defended, the already checked
`maximumHasNoDistinctEsseCause` theorem could rule out a distinct direct
conserver of that same maximum. Its companion `quartaViaWitness` imports the
existing Fourth Way theorem to supply the witness. This identifies a concrete
connection to consume; it does not perform a new inference merely by drawing a
support edge. In particular, it would still not exclude every arbitrary action
or withdrawal power of another being, and it would not supply obligations A or C
below. This source-only change adds no result, changes no primitive predicate,
and closes no frontier node.

## A structural consequence already available

`MAXIMAL-BEING-EXCLUDES-DISTINCT-ESSE-CAUSE` proves that a maximum in being has no
**distinct cause of its being in the existing `CausesIn` relation**. Its only
philosophical input is the already sourced
`STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH`: a distinct cause at `esse` would be
more in being, contradicting `IsMaximumIn`.

`QUARTA-VIA-WITNESS-WITHOUT-DISTINCT-ESSE-CAUSE` imports the existing
`QuartaVia.quartaVia` theorem and applies that consequence to the same witness
which is maximal and causes the being of all other beings. It consumes the four
existing Fourth Way premises plus the existing causal-comparison premise. It
adds no maximum-existence, identification, or independence premise. It is not
another root wrapper, and it does not close the eternity frontier node.

The finite omission model has two maximal beings, no strict comparisons, and a
distinct causal pair. It shows why maximality without causal comparison does not
supply the exclusion. This is an encoded non-entailment example, not an alleged
theological possible world.

Q.3 a.4's first proof gives a different direction:
`STMT-DISTINCT-ESSE-REQUIRES-EXTERNAL-CAUSE`. If a thing's esse differs from its
essence, its esse must be caused by another, since its essential principles
cannot suffice to cause its own caused esse. The application invokes God as
first efficient cause. **Essence–esse identity alone does not yield absence of
an external cause by the inverse of this conditional.**

The existing `GodIsInfinite.godIsInfinite` proof derives esse–essence identity
locally from the imported simplicity result. `FirstMoverIsFirstBeing` derives
absence of distinct `PriorSimply` predecessors through maximality and the
separate priority-to-cause premise. Neither result identifies sustaining
dependence or withdrawal power with `CausesIn`. The new argument uses maximality
directly instead of inventing that identification or reversing q.3 a.4.

## Three remaining obligations

A. Relate genuine intrinsic and adjunct change capacity to the existing
`InPotency` relation. The present `PureAct` quantifies potency in the subject;
q.9 a.2's power in another is a distinct channel, not an implicit extra respect.

B. Relate the relevant **ongoing sustaining dependence** to a **distinct cause
of esse**. Q.9 a.2 motivates the reading for creatures whose esse is continually
given, but the relation and scope have not been encoded or defended. A claim
about efficient causing of esse, actual continual conservation, a power to
withdraw that conservation, and arbitrary modal power are four different
claims. The new exclusion theorem establishes only the first. It does not
exclude all possible actions of another merely because they are called powers.
The full root context supplies a maximal witness; this argument is not a
universal claim about every arbitrary `PureAct` object.

C. Recognize the intended proper eternity from a sufficiently full account of
life, succession and independence. Primitive `Eternal` is not silently defined
as temporal omnipresence, within-life constancy, or an enum label. A recognition
premise cannot be advertised as a derived conclusion while it remains open.

### Obligation C: typed Boethian eternity (#353)

`IMMUTABLE-IS-BOETHIAN-ETERNAL` gives proper eternity typed content
(`DEF-BOETHIAN-ETERNAL`, `TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/BoethianEternity.lean`):
possession of life at some time of a duration frame, no beginning or end of that
life, and no succession of its life-state. It derives the typed specialization
`STMT-IMMUTABLE-IS-BOETHIAN-ETERNAL` from the q.9 a.1 succession principle
(`STMT-SUCCESSION-REQUIRES-POTENCY`), the unattributed boundary premise
`STMT-LIFE-BOUNDARY-REQUIRES-POTENCY` (q.10 a.1 supports only "what begins is not
altogether immutable") and `STMT-PURE-ACT-LIVES` (q.18 a.3 supports it only
through intellect). Omission controls in the same result show that each premise
is needed. Cases 1 and 3 below are excluded by the definition, case 2 by
including operations in the life-state.

This does **not** close `STMT-IMMUTABLE-IS-ETERNAL`. The root routes take
primitive `Eternal` as a separate parameter, and case 5 applies exactly: the
joint model satisfies all three premises and typed eternity while primitive
`Eternal = False`. Closing the root-path node needs either an explicit
recognition premise (Boethian eternity implies primitive eternity) or routes
specialized to `Eternal := BoethianEternal`. The derivation stays within potency
in the subject (`DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER`); obligations A and B,
and case 4's external conservation, are untouched.

## Omission cases to retain

These are descriptions of necessary modeling controls, not newly verified Lean
results or refutations of Aquinas:

1. A constant intrinsic state over a finite lifetime defeats the shortcut from
   within-life constancy to absence of a beginning or end.
2. Stable substantial existence with successive activities defeats the shortcut
   from substantial stability to proper eternity.
3. Unbounded successive motion defeats the shortcut from no beginning or end to
   proper eternity.
4. An internally stable aeviternal subject dependent on external conservation
   defeats the shortcut from internal all-at-once duration to independence.
5. A new duration structure satisfying chosen marks while primitive
   `Eternal = False` exposes the missing recognition commitment. It is not a
   historical or theological counterworld.

Do not eliminate these controls through a convenient lifetime type or an
assumption that every observation exists. A flags-only decomposition would be a
transcription. The candidate keeps A–C open until their source readings and
actual structure support a derivation.

## Existential inertia: the live rival and the remaining bridge

The complete author-published articles `SCHMID-INERTIA-REPLY-3-ARTICLE`
(Joseph C. Schmid, 7 July 2021) and `FESER-INERTIA-REPLY-2021-ARTICLE`
(Edward Feser, 6 July 2021) were pinned, materialized and read, excluding reader
comments. Their passage records locate the exact consulted bytes. These are
primary evidence of each author's position, not independent verification of
metaphysical adequacy. Feser's witness is the author-published Blogger Atom
entry: `source_evidence.py materialize FESER-INERTIA-REPLY-2021-ARTICLE`
returns its pinned XML, whose Atom `content` element contains the complete
article HTML. Its rendered text was reread and exactly matches the earlier
article witness; the final file newline is the only serialization difference.
The rendered webpage failed raw-byte verification in CI run `40776675501`;
the old expected/observed hashes are retained in the passage manifest. The
local narrow refetch still returned the original webpage bytes, so it cannot
establish the content of CI's differing response. Two independent Atom fetches
agreed; raw-byte verification remains enforced on the replacement endpoint.
Schmid's journal PDF and current-domain article returned
HTTP 403 to the evidence fetcher; the original author-published WordPress article
was accessible. Its rendered-page raw bytes then differed in CI run
`40777294225`. The Schmid passage now pins the authoritative WordPress
single-post API response for post `2136` on site `147942385`, restricted by
the server's `fields` parameter to identity, dates, original URL, title and
complete article HTML. Materialization returns JSON; its `content` field is
the article. It was reread and matches exactly the old witness body; the old
page's extra title/byline are separately represented in API metadata. Two
independent selected-field responses matched. Failed expected/observed hashes
remain in the manifest; raw-response verification is unchanged. No claim is
made about the unretained differing CI response's article content. No
journal-paper reading is claimed.

**Rival replacement.** Schmid's paragraphs beginning “For S to fail to exist at
m” and “Here, we seem to have” explain persistence through earlier existence,
absence of a factor causing cessation, and a causal requirement on change. His
closing edit, paragraph beginning “And this discovery especially helps”, accepts
a PSR or PSR-like explanatory principle while disputing the identification of
extrinsic explanation with a sustaining cause. Thus the strongest rival here
is not simply unexplained persistence. Its proposed explanation can include
facts extrinsic to the object at the later time without a concurrent sustaining
efficient cause. Its sufficiency remains disputed. Laws, transtemporal relations
and propositional necessity are further accounts he mentions, not accounts
independently inspected in their linked documents.

**Strongest response in the inspected Feser article.** Under “EIT versus EET”,
the paragraph beginning “Rather, a critique” argues that constituents considered
just as constituents are only potentially the whole at the selected time;
past combination does not suffice to actualize their present combination.
Under “The metaphysics of existential inertia”, the paragraphs beginning
“Now, an objection” and “I find this” argue that a persistence power depends
ontologically on its substance, so the substance cannot depend on that same
power without circularity. The paragraph beginning “Schmid does not attribute”
explicitly allows past events a role in present explanation: the issue is their
sufficiency, not their relevance. Under “An argument against EIT”, paragraphs
beginning “Another problem” and “But this simply ignores” apply the circularity
and present-actualization objections to a proposed emergent persistence power
and the earlier-parts response. This response needs the concurrent-actualization
and dependence-direction premises; it does not follow from the mere fact that
a thing has persisted. Nor does its intrinsic-power criticism by itself answer
every law-based or extrinsic no-change account.

Feser's paragraph beginning “This makes it sound” expressly rejects annihilation
and recreation at every moment. This agrees with q.104 a.1 ad 4's distinction
between continuing esse-giving and a succession of new productions. It blocks
a diachronic-identity objection aimed only at repeated recreation. It does not
establish that conservation occurs.

**What q.104 contributes.** Objection 1 argues from naturally inseparable form
to no need for preservation; ad 1 makes the form's resulting esse conditional
on divine influence. Objection 2 invokes the house and heated water after their
agents cease; the response and ad 2 distinguish causes of becoming from causes
of being. Objection 3 infers persistence from absence of corruption; ad 3 limits
this to preservation against corruption. Objection 4 challenges a preserving
action that adds nothing new; ad 4 answers with continuation of the giving of
esse. The response's paragraph beginning “Now every creature may be compared”
applies the illumination analogy through participated esse and essence–esse
distinction. These are articulated reasons and replies, but their application
to every creature remains a substantive dependence commitment. Treating the
illumination comparison as independently proving all existential dependence
would hide the disputed bridge.

| Existing typed commitment | What this reading establishes about the rival |
|---|---|
| `STMT-BECOMING-CAUSE-NEED-NOT-SUSTAIN-BEING` | Persistence after a maker stops is compatible with both accounts. It does not discriminate them. |
| `STMT-EXISTING-IN-ACT-AT` | The rival does not settle the interpretation from modeled existence into the supplied `InAct`/`esse`. |
| `STMT-UNITING-CAUSES-PRESENT` | The rival does not assert an absent concurrent conserver. Whether a past explanatory factor counts as a typed `CausesIn` cause is precisely unresolved. |
| `STMT-ACTUAL-ESSE-CAUSES-SUPPORT-AT` | A conditional map of already-given actual esse causes can hold even if no such cause is supplied for the persisting object. It does not generate conservation. |
| `STMT-Q3A4-DISTINCT-ESSE-CAUSE-DICHOTOMY` | A noncausal persistence explanation contests causal exhaustiveness only if the same target has the represented distinct essence/esse and lacks both efficient-causal disjuncts. Schmid's article does not fix those assignments; no formal denial is attributed. |

The exact interface types are in `TruthCore/Causality/ExistenceActuality.lean`
and `TruthCore/Causality/UnderivedNonComposite.lean`. The existing theorem
`TruthCore.Results.Causality.UnderivedEssenceEsse.actual_not_not_identity_direct`
requires an actual named target, no incoming support, actuality, cause presence,
typed correspondence, q.3 causal exhaustiveness and efficient self-cause
exclusion. Its constructive conclusion is **double-negated** represented
esse–essence identity. It supplies neither a conserver nor the truth of any
interface. No new theorem or finite graph is needed to rediscover those limits.

Two scope checks matter before formalizing the rival argument. First, from
cessation implying a destructive cause and absence of that cause, one obtains
non-cessation; if cessation is encoded as negated later existence, positive
later existence additionally needs stability/double-negation elimination.
This is an encoding diagnostic, not a claim that Schmid adopts constructive
logic. Second, a pointwise conserving cause `∀ t, ∃ c, ...` is not one fixed
conserver `∃ c, ∀ t, ...`; neither statement identifies that conserver with the
same root witness. Times in an inertia account are not automatically worlds
in `Ontic`, and q.104's timeless action is not automatically a temporal sequence.

The next discriminating obligation is to defend or reject the sufficiency of
prior existence plus no destructive change for the **same** existing bearer,
against the proposed need for concurrent actualization. Separately defend the
interpretation from direct conservation into `CausesIn ... esse`, endpoint
presence and its map to `R`. Efficient cause, ontological dependence, adequate
reason and preventing corruption retain separate meanings. No premise was
added to an argument, discharged or removed; root-route open premises are
unchanged. This reading narrows the rival and the missing bridge, without
advertising a new proof or an elimination of existential inertia.

## Atemporal source-cut component (2026-11-17)

Prepared outcome for independent semantic challenge under #1659/#1652;
research baseline `b419198cbadd7c4201292b078ed31f1eab23d6f3`, shared convention
sourceRevision `15f348b072188255da837578eaafc8a98f12fdf0`.
This follows the existing preservation attempt `dee1c25e-12ee-5fca-bacf-e7bdcfe286c3`.
It adds an analyzed dependency component, without claiming either sourced
PRESERVATION meaning complete or replacing their numbered sense identities.

### Formal content and primitive boundary

`TruthCore.Causality.PreservationMeaning` reuses `JointGroups.Exercise`, its
contributor/enabler sets, separate event/bearer types, alternatives, occurrence
and allowed scenarios. It does not introduce another production flag.
`AvailableRecord m s e` has an explicit body: an admitted record for exactly
**the same event e**, nonempty contributors, and occurrence of **all** contributors
and enablers in s. Available inputs do not establish `m.exercised g`, causal
production, effect occurrence, or the existence of `m.bearer e`.

`SourceCut m e c` requires every admitted record for e to include a contributor
borne by c. `PopulatedCut` separately requires an available record, excluding
vacuous universal success. This distinguishes a required source from a required
episode: different records may use different episodes of one source.
`SourceInactive` suppresses occurrence of all that source's contributor events;
it does not remove the source bearer, add a destructive process, or assert
that such a scenario is metaphysically possible. An enabler alone does not
qualify as a contributor. The interface does not require contributor/enabler
disjointness in arbitrary dictionaries; the fixture assigns them separately.

The conditional theorem `cutConsequences` proves:

1. Every available record has an occurring contributor borne by the cut source.
2. Source inactivity excludes any available record for this effect.
3. **If** every allowed occurrence of this effect has an available record
   (`RecordCovered`), inactivity excludes its occurrence in allowed scenarios.

The third step is not a withdrawal criterion for identifying a cause. It is a
consequence of an independently supplied record interpretation, a source cut
and explicit coverage. Neither coverage nor causal direction is inferred from
a truth table. The cut is a sufficient structural test, not necessary for
metaphysical dependence: an admitted alternative with impossible inputs may
make the test fail. Restricting admission requires separate justification.
No acyclicity, transitivity, asymmetry, well-foundedness, first moment, temporal
sequence, or new production at each instant is used.

The constructive distinction now available is **positive-record membership /
all-alternative source requirement / occurrence coverage**, each independently
inspectable. Positive productive interpretation and genuine exercise remain
the existing explicit primitive application obligations. A primitive is allowed;
calling an available record an actual receipt would conceal its obligation.
The event's interpretation as this bearer's esse, with the same numerical
bearer across the comparison, also remains open. An illumination effect event
borne by air cannot be substituted for the air's existence.

### Populated controls and justified comparisons

The fixture fixes one effect event, two alternative singleton-contributor
records and a receptive enabler. Both contributor events have bearer false;
the effect and enabler have bearer true. The effect occurrence table is
`(left OR right) AND receptive`. All eight Boolean input scenarios are allowed,
and the all-on actual scenario has both admitted records exercised.
Each episode can be absent with the other present and the same effect token
remaining input-supported. Thus losing one episode does not remove the common
source cut. Removing the enabler leaves no available record; its bearer still
fails the source-cut test because it contributes to neither alternative.
Reassigning the right episode to bearer true defeats the cut for bearer false.
These are checked facts about stipulated records, not claims about physical
realization, divine simplicity, or multiple divine acts.

The second dictionary retains all groups, bearer assignments and actual
all-on inputs, but makes effect occurrence unconditional. It still has a
populated cut; in the allowed all-off-source/receptive scenario the effect
occurs while no record is available. `RecordCovered` fails. This is an
established omission model for the claimed inference from cuts to effect loss;
it is **not** evidence against conservation or a model of a complete inertial
worldview. Its mechanism targets precisely coverage, which the first two
cut consequences do not use.

The strongest justified substantive rival remains the previously read
Schmid historical/no-destructive-change account of the **same enduring
bearer**: it replaces concurrent existential production with earlier actuality
and an existential persistence law. Its positive basis and Feser's restricted
persistence-power objection are retained in the existing source audit above;
no texts were newly acquired or authenticated here. The circuit neither
encodes that temporal law nor defeats it. Application of productive record
coverage to esse would need to discriminate that account; coverage cannot be
justified by naming the bearer 'received'. No substantive objection to the
conditional source-cut theorem was identified. Its finite coverage-omission
control does not by itself supply an objection to a real conservation premise.

### Exact consumer coverage and proposed disposition

The existing lexical `preservation` entry
`4e5958f3-f3a5-4c1e-a05d-e760ed8bb031` already points to exactly the two
original sourced definitions and their disambiguation. It is unchanged. The
new record component is not appended as a lexical PRESERVATION sense.
`mere conservation` (`94cddd41-ccdf-460b-b940-468680256524`) selects the separate
perfection-transfer discussion, not an alias for either preservation sense;
that mapping is unchanged. No broad family link becomes a lexical sense.

| Existing explicit definition/disambiguation consumers | Coverage by this change |
|---|---|
| Claims `40aefb2e-c9b3-5bb1-8802-96bbc4e2ed83`, `da9c82ed-e886-5335-81c3-cebad9b27345` | Existing sourced boundaries retained. No attribution edited or source verification claimed. |
| Statements `91062e01-6ddb-5764-8400-ce5d2a30778c`, `303d4ae5-a990-55ea-8b61-173b5ba215d3` | Existing becoming/being and timeless conservation content retained; no new declaration binding. |
| Statement `23e04ae5-98ed-4464-8f9b-dc0dfbad0caa`, `SustainingCausation.CausingBeingIsSustaining` | Concurrence through `SustainsBeing` still lacks productive dependence. The atemporal record component is not automatically its interpretation. |
| Statement `ce55210c-d3b5-4720-bd83-a3f63c5dc884`, `ConcurrentActualization.CausingAnothersBeingIsSustaining` | Same boundary for the distinct-source restriction; no change to its existing derivation or strength relation. |
| Arguments `0681f64a-769f-4b99-a9a7-5c86237f7f90`, `ffef89fd-1b58-430b-85d9-54cc8cbbe84b` | Original sustaining/contact/immensity consumers unchanged; no record-to-GivesAt map added. |
| Arguments `150d634d-b9a0-4260-ac6d-a0971faa7c76`, `2c3e7898-3ad9-41aa-b8d0-e701a0138317`, `366a6ea3-604f-4485-9fdf-2f58a094df84`, `835330d4-3174-4ea8-9a84-96aee10c062b` | Existing weak-sustaining derivations/strength comparison unchanged; none consumes the new cut component. |

This table inventories direct `definition_ids`/`disambiguation_ids` references,
not every transitive family mention. Existing `ProtectiveProcess.safety` and
its populated interruption/bypass controls remain the successful bounded
process option. They need no record source cut for their safety result and
still allow an empty independent `CausesIn`. An agent can protect and give
through distinct episodes; these modes are not exclusive agents.

**Root purpose, not an existing bridge.** Target
`732302a1-f7bf-594d-9a8a-cb4bd00687a7` is still
`∀ x, Participates x → ∃ c, c ≠ x ∧ CausesIn c x esse`, consumed by
`Round2Grounding.contingentGroundedViaParticipation`, result
`b7fbe991-fdff-565b-b708-eae8c4c1c594`. Its other inputs are
contingency-to-participation and the selected actual-concrete-ground bridge.
A record cut supplies neither a productive receipt nor c ≠ x nor CausesIn.
Consequently the new library is presently unconnected to a root route.
Its named connection plan is to analyze the dependence part of a separately
interpreted same-bearer receipt before any local receipt-to-CausesIn bridge;
coverage and positive role interpretation are the blockers. No q44/shared
participation record was edited and no whole root conclusion is assumed.

**Next discriminating tests.** First, on one explicitly interpreted receipt
record, check source cut across all relevant alternative contributors, retaining
all enablers and distinguishing absence of a source's exercise from nonexistence
of its bearer. For the existing illumination U/R/L candidate the endpoint is L,
not bare air: this may calibrate the dependency operation but cannot close the
esse application. For an esse instance, identify a positive contribution to
this same bearer's being independently of the loss condition; then defend
`RecordCovered` against the historical-law account. Nothing in this slice
requires an actual withdrawal world for a necessarily existing source.
Independently test an action-to-process realization for the existing protective
candidate; no new cut theorem removes that obligation. These application tests
need an interpreted record or an existential explanatory argument absent from
the supplied baseline, not another unconstrained occurrence assignment.

**Self-sweep.** New conclusions quantify over the supplied dictionaries and
retain all conditions inside their theorem types. Source means event bearer,
effect means one fixed token, occurrence means scenario occurrence; none means
substantial existence automatically. Membership/exercise, scenario sufficiency,
positive production and full explanation are kept separate. No source claim,
original sense binding/allowance, shared import/status file, frozen existing
Challenge or participation declaration changes. Independent semantic review of
this complete proposed outcome belongs to the coordinator. Local proof and
computed premise evidence are recorded in the existing attempt at handoff;
final integration CI remains required.

### Independent source-cut challenge (2026-11-17)

GPT-6.1 Sol reviewed b59bc8c8d2a45568244de9b5efb4feb74d8e43b9 and its
complete proposed outcome with no findings requiring repair. Source identity,
replaceable episodes, enablers, available records and actual exercise remain
distinct; effect loss retains RecordCovered and allowed-scenario assumptions.
The direct-reference consumer inventory is complete in its declared scope.
The reviewer confirmed that the original sourced senses and lexical mappings
remain unchanged and that no root support or rival defeat is claimed. Supplied
mechanical evidence was reused; this is not a new historical-source audit.
The next assigned test interprets one illumination U/R/L receipt with L as
endpoint, explicit exercise correspondence and justified contributor/enabler
roles, before any same-bearer esse application.
## Interpreting the illumination U/R/L receipt (2026-11-17)

Continuation of the preservation component at
`b59bc8c8d2a45568244de9b5efb4feb74d8e43b9`; the coordinator reports that its
independent review found no findings requiring repair. This follow-up's complete
proposed outcome is below and still requires its own independent review.
The existing source-cut vocabulary and frozen Challenges are unchanged.

### Receipt content and the selected endpoint

The prior U/R/L brief in `docs/power-existence-scope-boundary.md`, “One positive
productive-group brief”, already selects the solar influence **arriving on a
particular region**, its diaphanous receptivity, and that region's illumination.
It does not select bare sunlight-emitter existence or the air's substantial
existence. Existing claims `40aefb2e-c9b3-5bb1-8802-96bbc4e2ed83` and
`da9c82ed-e886-5335-81c3-cebad9b27345` retain their original source boundaries.
For this follow-up the complete already cached English q104 a1 text was read
offline, including the body, ad1 and ad4. Its stripped-text SHA256 matches the
existing passage's `fa09f205616e310f903e8f73d6885a71fae60f148fbed467cbb1cbc0f6010e0f`;
no acquisition, new extraction, source claim or live/raw-byte check was done.
The account distinguishes an active solar influence from the air's receptive
nature and contrasts received illumination with retained heat. It does not
supply the numeric equations, a calibrated optical theory or a named measured
episode. Those are not attributed to Aquinas here.

`IlluminationReceipt` supplies an explicit **analyst** forward quantity model:

- Source emission is an independently given natural-number amount. An open
  path transmits that amount unchanged; a closed path transmits zero. U means
  **positive arriving input**, regardless of whether the receiver responds.
- A receptive region responds with the sum of the arriving solar and lamp
  amounts; a nonreceptive region responds with zero. R is receptivity and L is
  positive response of this same region. There is no receiver-generated term,
  storage state, or equation determining the source from the effect.
- Distinct event constructors represent U, the alternative arrival, R and L.
  The source bearer of U is the sun; R and L have the same air-region bearer.
  The same event `.illumination` is retained in every scenario and scope.
  This formal identity fixes the explanandum; it does not establish actual
  trans-scenario identity or the existence of these bearers.

This supplies positive interpreted content beyond an opaque contribution tag:
emission, transmission and receiving response are separately computed and have
independent inputs. In the bright fixture an amount 3 is transmitted and the
receiver responds with 3. A blocked path leaves emission 3 but arrival and
response zero. Nonreceptivity leaves arrival 3 but response zero. Therefore
neither emitter presence/activity alone nor “whatever makes L succeed” defines
U. R modifies whether input is received; it contributes no emitted amount in
this model. This justifies classifying **U as contributor and R as enabler
within this selected mechanism**. It does not establish that every receiving
medium is causally passive or that physical receptivity never involves active
processes. No such generalization is used.

The primitive application commitments are now precise: the emitted amounts
must correspond to actual activity; the path operation must represent actual
transmission; this region must have the stipulated receptive response; and
these equations must cover its relevant inputs without memory/self-emission.
The directed forward interpretation is supplied with the mechanism, not proved
from the algebra. The equations alone admit noncausal readings and do not
certify an actual producing act. In particular Nat tokens are not measured
energy, the Boolean path neglects attenuation/propagation delay, and the output
is a receiving-response proxy, not a claim about air's own visible brightness
or all modern optical phenomena. These deliberately selected abstractions may
model the prior conditional receipt account; applying them to physical light
needs an optical/measurement bridge. They are not requirements on the original
timeless divine action.

### Alternatives, scope and coverage

`JointGroups` is reused exactly. Each record has one arriving contributor and
R as its enabler, with L as effect. `AvailableRecord`, `SourceCut` and
`RecordCovered` are the existing declarations. There are two explicit scopes:

| Scope | Admitted records | Allowed scenarios | Checked result |
|---|---|---|---|
| Solar-only | `{U,R} → L` | Alternative arriving lamp input is zero | Sun has a cut; every L has its available record. |
| Expanded | Solar and lamp records for the same L | All supplied input scenarios | Every L still has a record; sun no longer has a cut. |

Excluding the lamp in the first row is independently specified as **zero lamp
input at the region**, not as “all cases in which sunlight is indispensable”.
A lamp may be emitted but blocked and still meet that scope; a positive arriving
lamp input does not. This is a controlled single-input conditional, not a claim
that the original illumination account refutes all other light sources. The
expanded row tests the very same response equation and same receiver with an
additional independently assigned input. No source-relative redefinition of L
is used to force the cut.

Coverage is proved from the explicit response law. If L occurs, R is true and
at least one input is positive. That input constructs its admitted available
record. In solar-only scope the allowed-scenario restriction excludes the lamp
branch, so U supplies it. This proves coverage **within** the stipulated model;
actual optical input completeness remains an application premise. The records
are alternative sufficient sets for **positive illumination**, not complete
explanations of the exact total response magnitude.

The withdrawn scenario retains receptivity and the fixed air-region label but
sets emission to zero: response is zero. This models loss of illumination, not
loss of air. The expanded lamp-lit scenario has U absent, lamp input 5 and the
same L present. Both sources together give response 8, with respective inputs
3 and 5. Thus a positive contributor to the response need not be necessary for
**the occurrence of L**. This concrete source-alternative mechanism challenges
only an unqualified source-specific cut, and its expanded interpretation
formally defeats that cut. It does not deny the solar contribution or refute
conservation of esse. Calling U indispensable while silently switching between
these two rosters would be an error.

### Exercise correspondence and retained application gap

`model includeLamp actual performed` takes the actual scenario and the exercise
assignment independently. The checked coherence theorem consumes: the actual
scenario is allowed, and every performed record is admitted with its own
arriving input and R active. The response law then supplies L for that record.
The bright fixture declares the solar record performed and satisfies those
conditions; the joint fixture declares both records performed. They are
stipulated examples, not observations of a named actual episode.

Crucially the identical bright inputs and positive response also give a
coherent dictionary with **no exercised record**. This is a certified control,
not an objection to real solar activity: it shows that occurrence, coverage,
source cuts and the forward equations do not determine `performed`. To identify
a real exercise one needs evidence of the emitted/arriving activity on this
region and a warranted mechanism linking it to reception; the corpus's
historical conditional account is motivation, not that particular measurement.
There is no new predicate named “productive receipt” asserted to settle it.

**Proposed assessment.** The selected U/R/L account can now be represented by a
positive directed transmission-and-response mechanism with analyzable inputs,
a source/enabler distinction, exact record coverage and a tested alternative
source. This is useful conditional receipt content; it is stronger than a bare
source-cut calculation and weaker than an actual productive-exercise finding.
No substantive objection to these conditional model results is identified.
No conclusion about a universal conserver or every physical receiver is drawn.
The strongest historical-law rival to concurrent **esse** production remains
unchanged: this no-storage illumination model does not encode or exclude its
same-substantial-bearer persistence law. A retained-heat or stored-response
mechanism would have a different state variable and cannot be ruled out merely
by omitting that variable here; this is a stated model boundary, not evidence
that the selected received-light account fails.

**Consumer and root comparison.** New consumers are confined to the narrow
IlluminationReceipt batch, the two preservation definition notes and this
existing attempt/note. The previous exact consumer table is unchanged; no
existing sustaining/participation result consumes this component. Neither
PRESERVATION_1 nor PRESERVATION_2 receives a declaration; no original allowance
or lexical mapping changes. The root plan still targets
`732302a1-f7bf-594d-9a8a-cb4bd00687a7` through separately interpreted same-bearer
positive **esse** receipt, coverage, source distinctness and a local
receipt-to-CausesIn-at-esse bridge. This model concerns a determination of air;
it does not provide any of those existential applications by changing x to L.
The library remains unconnected to a root route and discharges no root premise.

**Next discriminating work and reassessment.** The assigned conditional U/R/L
interpretation, cut and coverage tests are now concrete and answered. An actual
receipt certificate next needs a named episode with independently established
emission, arriving input, receptivity and positive response, together with a
justified zero-alternative-input scope or a complete alternative roster. A
calibrated transport/receiver account must warrant the forward law and
exercise correspondence; another free exercise flag or equivalent table adds
no such evidence. The more consequential existential continuation requires a
positive account whose endpoint really is the same substantial bearer's esse,
then comparison with historical-law sufficiency. Illumination's successful
calibration cannot stand in for that account. These are substantive evidence
and interpretation requirements for coordinator reassessment, not requests for
source authentication or owner selection of a metaphysical winner.

**Self-sweep.** All three new theorem statements retain their exact model/domain
conditions. The source-cut and exercise conditions have different quantifier
roles and are not inferred from a numeric assignment. `performed` remains a
primitive exercise input. Every comparison fixes L as positive response and its
air bearer; magnitude changes are not treated as substantial replacement.
Existing sourced definitions, numbered senses, lexicon, old frozen Challenges,
q44/participation modules and coordinator-owned imports/status remain unchanged
apart from explanatory additions to the two owned preservation notes.
