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

### Independent illumination challenge (2026-11-17)

GPT-6.1 Sol reviewed ebb0b5517eab8506806ada021812a049ec365ca3 and its
complete 24-file outcome with no findings requiring repair. It confirmed the
separate emission/transmission/reception mechanism, contributor/enabler roles,
allowed-scenario coverage, same-L source alternative and independent performed
input. The model adds conditional mechanism content without establishing causal
direction from equations or actual productive exercise. Original preservation
bindings, empirical adequacy and same-bearer esse receipt remain unclaimed.
Supplied mechanical evidence was reused. The next assigned investigation concerns
positive existential receipt compared with historical-law sufficiency, not
further optical fixtures or an additional free flag.

## Root-reaching received-being test (2026-11-17)

**Complete proposed outcome for fresh semantic challenge.** This continuation
starts at `5441fa078fc990396998e8de5f06cc3bee92c367`, incorporating the
coordinator's `0c74fca5854c31a39673ba422417e9e37ace3c23` allocation repair.
The accepted #319 interface rationale is reused without a new review request.
The assigned destination is instead
`732302a1-f7bf-594d-9a8a-cb4bd00687a7`,
`Round2Grounding.ParticipatedEsseHasDistinctCause`. Its `related`, `dossier`,
`brief`, `novelty` and actual consumer context were inspected. This is an
existing root-reaching premise, not a newly connected result. Nothing here
repairs the disconnected #319 tuple `740a44f0` or supplies maximality or God
identification.

### Selected argument, actual consumer and same-bearer obligations

The actual consumer is argument `2162ca9d-cedf-581b-8ca6-16fcae8c45c1`,
result `b7fbe991-fdff-565b-b708-eae8c4c1c594`,
`Round2Grounding.contingentGroundedViaParticipation`. Its three inputs are:

- `ff8ff869-e90a-54f6-af8b-35060113568a`: each actual contingent concretum
  participates in esse;
- `732302a1-f7bf-594d-9a8a-cb4bd00687a7`:
  `∀ x, Participates x → ∃ c, c ≠ x ∧ CausesIn c x esse`;
- `cb1cdea9-eb6c-578c-8008-84e0d4107fd3`: each such distinct esse-cause of an
  actual concretum is an actual concrete ground at the selected w.

The conclusion `c71c068c-bbae-5ed5-a99d-70b155c8d239`,
`EveryContingentGroundedAt`, reaches the root according to its current context.
The proof keeps one arbitrary actual contingent concrete x and its selected
esse respect: participation gives c for **that x**, then the third input maps
**that c,x** to a ground. Neither the conclusion nor this work requires a
universal unique giver. Also, `732302a1` itself quantifies over every
participant, without an actual-world guard. Warrant for a selected actual x
would be a useful application, not proof of that entire universal premise.

The selected existing received-being argument is
`42908cf8-66e8-40d3-ab26-fc94d56e36f1`, result
`8477d8c7-db6c-48de-bf99-18eacf146886`,
`DeEnte.ExtrinsicSource.distinctEsseOtherCauseFromCaused`. It concludes
`457698e4-eb21-4561-ab32-eccbfb0a992e` on the existing q.3 a.4 profile:

```text
InAct x esse AND esseOf x != essenceOf x
  -> exists c, c != x AND InAct c esse AND CausesIn c x esse
```

Its complete premise bundle is some-cause coverage `d1f3ffcc`, no cause of
one's own esse `b62a64ab`, and causes-of-being-are-in-act `4ccb319f`.
The existing upstream arguments `05c81e70` / result `44eef980` and `16654a70`
/ result `42a89226` decompose coverage into the nature-or-extrinsic disjunction,
the efficient-nature sense bridge `600f91cb`, and the self-causation reading.
Their dossiers and exact theorem bodies were inspected; the findings of
[the De ente investigation](notes/de-ente-extrinsic-source-1629.md) and its
[efficiency repair](notes/esse-cause-efficiency-1633.md) are reused.

Applying this argument to the participation predicate needs the existing OPEN
`ParticipatedHasDistinctEsse`, statement
`cbb068e8-337d-5772-a3f9-10df457ba9fe`, on the same supplied profile and
participation predicate. It supplies actual distinct esse, not a production
episode. No new argument into `732302a1` is registered here: dropping the extra
`InAct c esse` conjunct would only transport an already assumed causal result,
without answering the assigned warrant question. The candidate's own context
already reports its conclusion root-reaching through other consumers; that
fact does not certify this particular application or close participation.

### Three discriminating warrant tests

**1. Does reception in a principle independently give a producer?**
The existing De ente reception reading
`ReceiverInPotencyToReceivedEsseReading` says
`EsseReceivedIn x r → ReceptivePotencyTo r (esseOf x)`.
Its subject is the act of being **of x**, so it avoids substituting illumination
for air's esse. But r and `esseOf x` inhabit `Principle`, whereas c in the root
premise inhabits `Being`. The formula supplies no c, action, or causal edge.
`EsseReceivedOnlyInOwnEssence` and receptive irreflexivity constrain the
receiver and represented act; they do not add a producing agent. This is
reception **in**, explicitly distinguished from origin **from another** in
the existing declaration and definition `4433942e`.

The positive hylomorphic rationale is that a recipient does not possess the
received act as its own unreceived actuality; it identifies an explanatory
asymmetry and motivates investigating derivative being. However, assigning
`EsseReceivedIn` or `Participates` to x is not evidence of productive receipt.
If “received” is already taken to mean effectively given by another, it supplies
part of the desired warrant as an interpretation commitment; it cannot also
serve as an independently established conclusion of the receiver/act formula.
No objection to treating derivative actuality as a candidate primitive is
inferred. The failed approach is specifically using the in-principle formula
as a derivation of an external producing bearer.

**2. Can specifying-versus-actualizing close De ente's coverage step?**
There is a positive reason to reject a bare specification as the complete
account of actual existence: describing what x would be does not assert that
there is such an x. Likewise, the agent's activity cannot be the sufficient
productive origin of that very agent's existence under the existing
bearer/product-priority account. These support explanatory inquiry and
non-self-production; neither asserts that every actuality is produced.

The proposed repair from the De ente note says that an accounting principle
must either be an agent or be identical with the act accounted for. With
nonidentity, this would eliminate the intrinsic non-agent option. But the
repair has not gained independent support merely from the specification test:
“does not account for actuality” and “is not an agent” are different exclusions.
The existing formal/constitutive account proposes that actual constitution,
rather than an agent's producing act, explains the bearer. It owes an adequate
account of its actual obtaining; it is not refuted by the absence of an agency
predicate. The existing `FormalNatureControl` establishes independence of the
two supplied nature-source predicates only. It does not positively establish
a complete non-agent explanation of this substantial x, and is not used here
as evidence that such an explanation succeeds.

Thus the tested principle still carries the very productive-exhaustiveness
commitment at issue. This is an exhausted repair **with the inspected evidence**,
not a claim that an independently defended agent-or-act account is impossible.
Q.44's received-being route supplies a substantive metaphysical account, but
its already recorded appeal to unique subsistent esse cannot independently
establish a pre-identification giver for this argument. The stronger actual
causal application remains conditional. `esseOf x` is x's represented act of
being, not the act by which c produces it; `InAct x esse` states x's actuality,
not c's activity. No new production flag or illumination model repairs this.

**3. What does historical-law persistence actually contest?**
Fix the same substantial x after its origin. The strongest recorded rival
accepts earlier actuality and proposes persistence under absence of destructive
causal change. It can accept a numerically distinct originating cause. On a
tenseless originating interpretation of `CausesIn`, it can therefore retain
`732302a1` while denying current existential giving. Its relevance is to the
consumer's passage to present support in `cb1cdea9`, not an automatic denial
of every distinct-cause premise. If `CausesIn` instead means sustaining
esse-contribution, the disagreement includes whether participation supplies
that kind of cause in the first place. The same symbol cannot be originating
in the existence argument and sustaining in the grounding application without
a defended bridge.

The existing `SustainingCausation.Control.inertia` keeps the same Bool bearer
false from time 1 onward. `trueCausesFalse` retains a distinct cause and
`inertiaGiving` gives only at time 1; at time 2 there is no giver. The first
conjunct of `ConcurrentActualization.Certificate` retains received esse and
rejects concurrent actualization. By inspection, on these assignments a
participation predicate selecting false satisfies the displayed distinct-cause
formula with witness true. This last observation is a substitution in an
existing structural interpretation, not a newly registered theorem or an
independently warranted attribution of participation. The fixture does not
encode the full historical-law explanation or prove its adequacy. Also,
`inertia.ontic.ExistsAt` is everywhere true while temporal presence differs;
this is not a countermodel to `cb1cdea9` until the world/situation dictionary
and selected support relation are specified. Times are not silently worlds.

The external-giver reply retains real force against sufficient efficient
self-origination. Its further premise that the bearer's present receipt needs
concurrent productive input is exactly what the historical-law account
contests. A persistence law does not explain initial actuality merely by
explaining later persistence. Conversely, an origin explanation does not
establish current giving. Neither gap proves the rival's positive account.

### Outcome, exhausted approaches and allocation

**Provisional outcome:** the selected De ente argument supplies a valid,
same-bearer conditional route to a numerically distinct esse-cause. Its
explanatory motivation and conditional no-self-production argument are retained
as positive reasons. This investigation supplies **no independently warranted
productive receipt of the selected substantial bearer's esse**, no completed
coverage argument against historical-law persistence, and no independently
established local receipt-to-`CausesIn` application. It does not establish or
refute `732302a1`, and does not withdraw its direct-assumption or conditional
support options. Distinctness follows once a genuine producing cause is given;
the absence of self-production does not generate that cause.

The approaches tried have specific endpoints: reception-in stops before a
producing bearer; real nonidentity plus no-self-production stops at some-cause
coverage; agent-or-act exhaustiveness does not acquire independent warrant
from the specification test; source-history plus persistence does not identify
a concurrent giver. The preservation/positive-receipt findings from #1701
already provide conditional mechanism and coverage analysis for a state of an
existing bearer. Their application to this bearer's esse is the unavailable
dependency. Repeating those controls or replacing a definition's name cannot
supply it. No further distinct test of this particular received-being argument
is available from the inspected evidence; this is a branch for coordinator
reassessment, not exhaustion of all philosophical approaches.

**Different root-node allocation recommended:**
`40a97664-e481-42d7-8458-78374a61aa26`,
`ConcurrentActualization.ConcurrentlyActualized`. Its current brief reports
root reachability. The actual consumer is `366a6ea3-604f-4485-9fdf-2f58a094df84`,
`sustainingOfConcurrentActualization`: received esse plus per-moment giving
plus concurrence yields the weak sustaining reading `ce55210c`. This is a
separate existing root destination, **not** a registered inference from the
#319 tuple or from this work. The weak premise needs some giver per moment,
not one fixed giver and not a distinct giver, so these stronger demands must
not obscure its actual warrant test.

The next assignment should test the strongest positive reason for treating
**remaining in received act** as actualization at each moment against the
historical-law account's causal requirement on cessation. It needs a reason
covering existence itself, beyond reception-in, no-self-production, no observed
destruction, or the already calibrated state examples. The relevant source
and rival arguments are already recorded under attempt `05bc2722`; no source
authentication campaign is needed. Without new support for that substantive
persistence/actualization distinction, redispatching the present receipt
argument would repeat the precise obstacle above. Source distinctness,
concurrence with the original cause, world-presence and grounding retain their
separate tests; no rival defeat or universal conservation is announced.

### Self-sweep and review boundary

Only this existing note and preservation/receipt attempt are extended. No
source attribution, definition, statement, argument, theorem, model, binding,
sense or shared generation changes. The actual root-consumer bundle, universal
versus selected-instance scope, same x/c/respect, Principle/Being distinction,
tenseless versus sustaining reading, and history/world mismatch are explicit.
Existing controls are structural interpretations, not possible-worldview or
real-bearer certificates. Source discussions reuse the cited repository
readings; external witnesses were not freshly acquired or read in this turn.
The new warrant assessment and reallocation are proposed for coordinator
challenge; the earlier accepted #319 finding needs no repeat review.

**Validation for this prose/attempt delta.** Shared conventions sourceRevision
remains `15f348b072188255da837578eaafc8a98f12fdf0`; the prepared setup is
unchanged and no preflight was repeated. Through `worker_env.py`, offline
`truth check` passes with the existing lexical/formal-status warnings, and
`attribution-check --base 5441fa078fc990396998e8de5f06cc3bee92c367` reports
no new or changed stating claim. `git diff --check` passes. Computed
`truth frontier-diff --base 5441fa078fc990396998e8de5f06cc3bee92c367`:
root-reaching open premises 494 → 494 (353 bare, 90 supported, 51 stated),
lowest expanded route cost 16 → 16, verified support alternatives 494 → 494,
added 0: **no change**. No Lean or binding inputs changed; unchanged proof
verification is reused, not represented as a new build/Comparator/NanoDa run.
Fresh challenge of this proposal and final integration CI remain with the
coordinator. No push, PR, watch or merge.

## Concurrent actualization: current case for God-existence research (2026-11-17)

**Complete proposed outcome for fresh challenge.** God’s existence is the
selected overall question; historical-evidence campaigns and Catholic-specific
bridges are deferred by owner direction. On the same continued-existence
phenomenon, conservation remains a substantive, defensible explanatory option:
if a bearer's actuality is a standing derivative actuality, its dependence is
not explained away by the mere passage of time. The historical-law account
nevertheless survives the strongest tested shared causal principle. The new
checked result shows why: requiring a cause of cessation is compatible with
both concurrent giving and its absence. It neither proves conservation nor
establishes existential inertia. The cumulative judgment is therefore positive
conditional support for conservation, without a warranted inference from
persistence alone to God. The two accounts’ remaining disagreement concerns
what sustains actuality, not whether the bearer persisted or whether every
change needs a cause.

This continues accepted `c43e57e8191e1f0840a35069d0830e6321bad5a8` at existing
`40a97664-e481-42d7-8458-78374a61aa26`,
`ConcurrentActualization.ConcurrentlyActualized`. Related/context/dossier/brief/
novelty and attempt `05bc2722` were inspected. Exact consumer `366a6ea3` keeps
reception, per-moment giving and original-cause concurrence separate. The new
comparison is statement `c7cff178-24d5-4383-b219-88586a3cb8fe`, argument
`4f11b24b-db72-459b-bf03-c5cfedf285ef`, result
`610e21dc-7679-4cfb-be45-b0534a7bae3b`. Its home is
[ConcurrentCessation](../TruthCore/Causality/ConcurrentCessation.lean), with
[the proof](../TruthCore/Results/Causality/ConcurrentCessation/Solution.lean).
It answers attempt `05bc2722`’s first pending test; it is not another
illumination calibration or a new definition of received being.

### Positive warrant and complete competing local explanations

Fix one numerical bearer x that is present before and after the selected
interval. The question is why **that bearer's continued existence** obtains.
A change of quality, a replacement bearer and a description of its nature
are not substitutions for this explanandum.

The strongest conservation case treats x's act as standingly derivative:
actuality belongs to the recipient without belonging to it as self-subsistent
actuality. Continuing in that same mode calls for actual efficacy, even where
there is no new motion or newly produced replacement at successive instants.
An earlier producing act explains an origin; the conservation account adds
that the present actuality still has this dependent mode. On that account,
productive support, ordinary secondary activity, the bearer's constitution and
the laws governing its behavior work together. The explanatory ambition is to
account for why the bearer is actual now, as well as why its states develop.
This is a reason to take concurrent actualization seriously as a metaphysical
primitive or conclusion, not an obligation to find an endlessly prior proof.
It is strongest when standing productive dependence is independently part of
the best account of the bearer, rather than inferred solely from the word
“received.” No substantive objection to a genuinely identified instance of
such continuing productive dependence was found here.

The rival is a complete **local persistence** account on its own commitments:
x was actual earlier, cessation requires an inducing factor, and none occurs
through the relevant interval; x therefore continues. Ordinary processes and
constitution explain its behavior, while this transition principle explains
why the same bearer is still there. It does not say that an abstract
specification efficiently produces x. Nor need it assign an intrinsic
self-giving power: the causal law and prior actuality do the explanatory work.
Its positive basis is the causal requirement on change that motivates the
no-change argument; its application to existential cessation remains a real
commitment. This is more than a bare possibility or a denial of all explanation.

These local accounts can both acknowledge x's originating cause. They can also
both leave the origin or total obtaining of the history to a further account.
A complete *ultimate* conservation case needs an adequate account of its
foundation; a fundamental physical or historical-law completion needs an
adequate account of its base and law. Calling either terminus necessary does
not by itself provide that account. Neither receives an exemption, and failure
to complete one does not establish the other. For the local phenomenon, the
rival does not fail a substantive test merely because it explains persistence
without productive giving. The conservation account has a distinctive proposed
ontic dependence explanation, but that extra content is an explanatory gain
only insofar as the standing-dependence account is warranted.

### What the new test changes

[The certificate](../TruthCore/Results/Causality/ConcurrentCessation/Solution.lean)
proves three discriminations using existing temporal and process dictionaries:

- Causal coverage of sampled cessation plus absence of every represented
  terminal process gives **double-negated** next presence of the same bearer.
  Positive presence additionally uses classical stability; giving is unused.
- A received, prior-present bearer cannot continue without *any* giver
  (`UngivenContinuationFails`) iff it has some giver whenever it continues
  (`ContinuedGiving`), classically. Recasting one as the other supplies no
  independent warrant, though either may be a substantive primitive. This is
  not an intervention or withdrawal of one original source.
- Adding that dependence to causal coverage requires a terminal-process
  witness on any resulting loss. Identifying withdrawal as such a process
  remains an application obligation, not a definition of negative causation.

The reused `inertia` history satisfies causal coverage and soundness of its
terminal losses: its dictionary has an actual loss of true at sample 2, while
recipient false persists from 1 to 2 without later giving. Thus coverage is
not tested only on a wholly changeless population. The reused `sustained`
history satisfies the same law and concurrent actualization. These are
structural assignments, not real-bearer or complete worldview certificates.
The code and definition `9bd9cc6b` retain the full process/target details.

`consumerRestriction` actually consumes `ConcurrentlyActualized`, preserving
the same bearer and next time through explicit selected-world process/presence
correspondence. Its giver may vary or be the recipient. The restriction covers
Nat-sampled continuation, not time zero, first appearances or dense-time limits;
no converse to the unrestricted target is claimed. World and time indices stay
distinct. Existing history proof evidence is imported unchanged.

The comparative consequence sharpens the earlier undercutting assessment.
The no-change deduction challenges “nothing else can explain persistence”;
it does not establish that giving is absent or superfluous in the actual
causal basis. Its no-inducer antecedent must cover all relevant factors,
including any warranted cessation of existential support, not just observed
damage. Conversely, asserting that lack of giving induces cessation imports
standing dependence. The common causal law alone favors neither account,
and does not refute the positive conservation primitive.

### A fixed-witness God-existence bundle, not an attribute detour

The concrete existence-stage destination is `8626f8a5-9531-5da7-9ebd-f901e74b1129`
(`GodExists`, G). Select the existing **twelve-input** conditional candidate
`DIRECT-ESSE-ROOT-GOD-EXISTENCE-ONLY`, argument `5e8e6054`, result
`973582b8-b190-5f29-ab82-2ae387cffc68`,
`DirectEsseRootGodExistence.ExistenceOnly.godExists`. Its context, all twelve
input dossiers, and exact `sameWitnessGod` proof were inspected. The complete
bundle is actual population `56f68b40`, whole-roster foundation `5c898d24`,
excluded middle `ee4ab504`, priority-to-ground `86efed1a`, genus-causality
`d9fad785`, existence-to-act `0436de86`, esse-cause-to-ground `cb1cdea9`,
grades-to-maximum `6c27657f`, actuality-in-being `7067553d`, universal-source
perfection transfer `b26c10a0`, no-component-first `09c6d5f0`, and full nominal
naming `1ec205ed`. All earlier direct-assumption options remain available.

This is one coherent typed **conditional support bundle**, selected for the
existence investigation; this continuation does not claim that its whole
metaphysical application is independently warranted. Fix one candidate domain,
selected situation, esse respect, actual existential-ground relation and
perfection interpretation throughout. In a proposed temporal application,
world-level existence must match presence at the selected situation; strict
`GivesAt` must really supply the same esse-causation used by the selected
`CausesIn`. Neither coupling is supplied by changing an index name. Current
conservation research bears on that *productive interpretation*; it does not
establish the generic bridge over every alleged cause.

The existing proof extracts **one n** from population and whole-roster
foundation, proves its firstness using the priority correspondence, obtains a
maximum through grades-to-maximum, and identifies every such maximum with
**that n** through actual esse-ground correspondence. Genus supplies its
universal esse-causal scope; transfer, firstness and component remoteness give
the remaining naming conditions. Only then does the explicit nominal premise
name that same n God. A giver g of the observed x is not silently identified
with n. Foundation is substantive: the existing whole-roster/root equivalence
shows that, with population and classical logic, nontrapping has the strength
of existence of a root in this very relation. Maximum, common causal scope and
perfection transfer likewise need their own warrant; no inference from “there
is a giver” supplies them.

The formal output is actual rootness, firstness and `IsGod n`, hence G. It does
**not** prove modal necessity of n, the nine classical predicates, intellect,
will, infinity, eternity, moral omniperfection or omniscience. Adding contingent
grounding gives the existing stronger necessary-witness route; it is not a
premise of this existence-only route. The nominal predicate does not confer
all later attributes by its name. No Catholic historical or authority bridge
is used here.

Current graph reachability of `40a97664` to G is real but is not an independent
existence argument: its path through `366a6ea3`, the sustaining/immensity bridge,
and the full attribute summary already obtains a named God before projecting
existence. For the existence-first priority, do not count that detour as added
existence warrant. Nor is `40a97664` a premise of the twelve-input proof. The
new cessation certificate is linked analytical evidence for its current
premise question, **not** a new arrow into G. The missing semantic application
from real giving to this bundle's selected esse-ground relation stays explicit.

### Cumulative judgment and next allocation

The strongest current case is a conservation account with actual population,
real standing dependence, and a substantive foundation and universal-source
completion. It has positive explanatory content, can be held provisionally
without demanding prior proof of every primitive, and is not refuted by the
historical-law cessation argument. Its competitor is the positive
historical-law account, potentially completed by fundamental impersonal
reality. Their shared observed persistence and shared causal requirement on
cessation do not discriminate them. The inspected evidence therefore does not
yet warrant selecting the entire God-existence bundle as established or the
natural completion as defeated. This is a comparative judgment on the whole
selected case, not a claim of equal credibility or a deduction from open-leaf
counts. Direct acceptance of the conservation premise remains a live support
option; its philosophical warrant is separate from formal closure.

The bounded test is now answered: the causal requirement on cessation neither
entails nor excludes present giving; the added no-giver dependency is the same
continuation commitment in classical form. Rejected as further advances are
renaming that dependency, treating no *observed* damage as exhaustive absence
of causal loss, requiring one/distinct giver, extending sampled proofs to all
histories, and using an attribute-to-existence projection as independent
support for God's existence. No repeated illumination, reception-in or
self-production test was used.

With existence first, the next consequential allocation is **`5c898d24` on
this exact twelve-input bundle**: assess why the actual existential-support
roster has a foundation against a positively articulated complete distributed
or fundamental-natural account of the same current actuality. Keep selected
support distinct from ordinary state-transition causation. This is a different
load-bearing existence node, not more work on immensity. An independently
justified standing productive-dependence account for the present bearer, or a
reason that the historical no-inducer law requires or excludes that support,
would reopen the current premise question. Further alleged arguments in the
unread ACPQ article remain source leads: the targeted publisher request returned
403; no conclusion about those arguments follows and no historical campaign
is started. The current source/rival assessment otherwise reuses attempt
`05bc2722`’s retained readings and precise locators.

### Verification and claim/type sweep

The generated statement/inference/argument/result, definition, frozen Challenge
and Solution were swept for quantifiers, prior/next presence, double negation,
some-versus-fixed giver, same process target, selected-world correspondence and
structural-model limits. The no-external-premise certificate establishes its
mathematical comparison, not concurrent actualization or God’s existence.
`DeiFiliusUnifiedRoute.deiFiliusRootUnified` obtains `hGod` before applying
`hImmenseSense`, confirming the existence-detour assessment. The twelve-input
proof and `sameWitnessGod` remain unchanged.

Through `worker_env.py` under the heavy lock: focused Solution and generated
Challenge builds pass; binding is **1 bound, 0 pinned, 0 mismatch**; Comparator
and independent NanoDa accept result `610e21dc-7679-4cfb-be45-b0534a7bae3b`.
Only the frozen Challenge has its expected `sorry`. The certificate and
`consequences` use `[propext, Classical.choice, Quot.sound]`, the permitted
profile; `consumerRestriction` has no axioms. Existing proofs are reused.

Offline corpus/attribution checks, scoped spec regeneration, bundle audit,
sense/definition/lexicon ratchets and whitespace check pass. Existing lexical
warnings remain; the new definition’s shared formal-status entry is not yet
generated. No shared imports, status, allowlist, old frozen contract or source
claim was edited. Convention sourceRevision remains
`15f348b072188255da837578eaafc8a98f12fdf0`; no preflight repeated.

Computed `truth frontier-diff --base c43e57e8191e1f0840a35069d0830e6321bad5a8
--frontier-root STMT-GOD-EXISTS`: **no change**; open premises 404 → 404
(283 bare, 76 supported, 45 stated), lowest route cost 6 → 6, verified support
alternatives 414 → 414, added 0. The new certificate dossier was inspected.
Fresh challenge of this full case assessment and final integration CI remain
coordinator-owned. No push, PR, watch or merge.

Foundation continuation: the complete proposed assessment of `5c898d24`, its
rootless versus fundamental-natural rivals, and the checked comparison with
maximal-target nonreciprocity is retained in
[the existing foundation note](notes/unique-feedback-explanation-311.md#current-foundation-judgment-on-the-existence-only-case-2026-11-17).

## Current cluster assessment under the substantive objection standard (2026-11-18)

**Scope and boundary.** Issue #1751, model-trial slice 2/3, drafted on main
`ebd3c2394a40eeae1bfc7fd9b0824d88e3bba887` (PRs #1754 and #1759 merged). On
that revision `truth currentness --frontier-root 8626f8a5` reports 57 current,
184 `legacy_only` and 182 `none` among 423 open premises. Nine `legacy_only`
premises are targets of attempts that cite this note by its literal path
(`05bc2722`, `76bad0cb`, `dee1c25e`). All nine counted at the slice baseline
are still `legacy_only`, so the scope is unchanged:

| Sub-route | Premises | Where their substantive evidence lives |
| --- | --- | --- |
| A. Sustaining and concurrent actualization | `23e04ae5`, `76d2cc96`, `d7f5a528`, `c4661518`, `140544c4` | This note; attempts `c94eed5b` and `05bc2722`; [modal-spine.md](notes/modal-spine.md), stage-two immensity paragraphs |
| B. Old Dei Filius bridges | `c7c32f20`, `fa3f08a8` | Attempts `b93ce632`, `76bad0cb`, `d9c2b200`, `0da0dd9e`; the same modal-spine paragraphs. They only link this note, for the Schmid reading. |
| C. Dependence premises of the necessary-being routes | `732302a1`, `96d25c42` | This note (received-being test); [underived-essence-identity.md](notes/underived-essence-identity.md); [power-existence-scope-boundary.md](power-existence-scope-boundary.md); [god-existence-support-formula.md](notes/god-existence-support-formula.md) |

Sub-route A cannot be assessed without its crux. The assessment therefore also
names two route nodes that are not open leaves in the currentness view: weak
concurrent actualization `40a97664` and the weak sustaining reading `ce55210c`.
Their recorded judgments are restated unchanged.

Other neighbours are discussed but not named as targets and not graded:
`da72ae93`, `8bf775e9`, `a3913182`, `9469ab62`, `0042dd05`, `18ca6f9d`,
`bbac932e`, `ff8ff869`, `cb1cdea9`, `dd41c165`, `2b25a78c`, `16828262` and
`1d4d9b13`. The eternity integration itself (same-source life, succession,
recognition, and the direct-conservation interpretation into `CausesIn`)
belongs to #1736 and is not done here.

For each target the dossier and brief were retrieved, the consuming and
producing arguments were computed from the corpus records, and every attempt
on it was read together with the note sections it cites. Earlier sections stay
unchanged under their own dates. This section changes no theorem, Challenge,
claim, definition, closure or formal status.

### (a) Fixed meanings

These are the meanings fixed by the existing definitions, disambiguations and
earlier sections. Nothing is redefined.

- **History, presence and time.** `History W B T` assigns `IsAt v x t`
  independently of `Ontic.ExistsAt` (definition `6e811e85`). Histories are
  indexed by worlds, moments by `T`; times are not worlds (disambiguation
  `92df85d7`). "Present at t" has the one inclusive reading adopted in
  `c94eed5b`: actual in the history and bearing on t, by location at t (a
  temporal thing) or by co-presence to t (a non-temporal agent). It asserts
  neither spatial location nor that the agent is in time.
- **Giving being at a moment.** `GivesAt v c x t` is an explicitly identified
  primitive (definition `158301bc`) with an effect-side time index. On this
  route it has the STRICT esse-giving reading. It is not counterfactual
  dependence, removal of a destroyer or `Ontic.Causes`, and no axiom
  constrains it.
- **Originating and sustaining (#1626).** `CausesIn c x esse` is tenseless and
  mode-unspecified (CAUSING_AN_EFFECT_3). CAUSE_OF_BEING_1, originating, gives
  being at a first moment of presence and requires such a moment.
  CAUSE_OF_BEING_2, sustaining, gives being at every moment of presence. It
  types the concurrence of the activity with the effect, not the dependence
  clause of per se conservation (definition `56989bd0`). The two overlap and
  are not exhaustive: preventing corruption and counterfactual dependence are
  further relations (disambiguation `88a8fba7`). Passage from `CausesIn` to
  either is an explicit open bridge.
- **Reception in versus origin from.** `EsseReceivedIn x r` is reception of
  x's act of being in a principle that stands to it as potency to act
  (definition `4433942e`). It is not origin from another being
  (disambiguation `5921354b`). The bridge `da72ae93` is the only statement
  joining them.
- **Participation.** ESSE_BY_PARTICIPATION_1 (definition `14d30c53`) is having
  being derivatively rather than being subsistent esse. `Participates` is a
  parameter with no body: assigning it to a thing does not establish that the
  description applies.
- **Necessity and support.** `NecessaryAt m w₀ x` is existence of one fixed
  individual at every world accessible from w₀, a de re surrogate (definition
  `38b92bb6`). `supportsEsse w c x` is a world-indexed direct
  existential-support parameter. `NoContingentGroundOfNecessary` quantifies
  over every world w, not only accessible ones, and over every existing
  supporter. It restricts neither generic efficient causes nor explanatory
  tokens (definition `659dbc9c`, disambiguation `6f1d1395`).
- **Creator and beginning (#1496).** `IsCreatorOfAll` is the weakest typed
  reading: g causes the being of every other thing that is in act as to being,
  tenselessly. Creation from nothing, freedom and a beginning are not encoded
  (definition `92c03350`). `BeginsAt` is presence at a moment with no earlier
  presence. Neither a temporal beginning nor its absence is creation ex
  nihilo, and no premise of this cluster passes from one to the other. The
  BEGINS senses of disambiguation `dc40914a` belong to the modal spine and are
  not used here.
- **Immense, incomprehensible, infinite.** IMMENSE_1 and INCOMPREHENSIBLE_1
  are primitives. IMMENSE_2 and INCOMPREHENSIBLE_2 are typed siblings that are
  not identified with them (disambiguations `3fc3ee02`, `d63d0696`).
  Incomprehensibility negates comprehension only; it is not unknowability.
  INFINITE_1 is unreceived subsistent being, not quantity (disambiguation
  `587c53cf`).
- **Eternity (#979).** None of the eleven named statements contains `Eternal`.
  Six notions stay distinct, and none is inferred from another here:
  1. proper eternity ETERNAL_1, without beginning, end or succession
     (definition `1291944d`, disambiguation `f561d4e4`), a primitive on the
     root route;
  2. the typed Boethian reading over a duration frame (definition `5e77da13`),
     which reaches the primitive only through an open recognition premise;
  3. participated or extended uses, such as never ceasing or long duration
     (sempiternity; definition `a26cce29`);
  4. aevum, internally all at once with adjunct change (q.10 a.5; definition
     `19e01de3`, disambiguation `6805c9bd`);
  5. temporal everlastingness within one world, `EverlastingAt` and ETERNAL_2,
     which allows succession and, for ETERNAL_2, a beginning;
  6. the timelessness of the conserving action, "without motion or time"
     (q.104 a.1 ad 4, claim `da9c82ed`), which is said of an action and is not
     a duration of its agent.

  "Gives being at every moment at which x is present" places the giver, by the
  contact premise, at those moments in the inclusive sense. That is none of
  the six. In particular a sustainer of everlasting things is not thereby
  eternal, and an eternal being is not thereby a sustainer. The root route's
  eternity node `0659227c` keeps the assessments that named it (`e64d5241`,
  `383d23ad`, `0ddaa334`) and is not regraded.

Under these meanings the registered structure is as follows.

- **Sub-route A.** Argument `366a6ea3` (result `5651df1e`, non-transcription)
  derives `ce55210c` from the reception bridge `da72ae93`, weak concurrent
  actualization `40a97664` and concurrence `d7f5a528`. With presence-in-act
  `140544c4` and contact `c4661518` it gives the presence step `9469ab62`
  (`2c3e7898`, result `0ed3a583`). The older arguments `ffef89fd` and
  `0681f64a` take the strong reading `23e04ae5` in place of `ce55210c`. The
  last step to `8bf775e9` through the narrowed bridge `a3913182` is a declared
  single-application transcription in both (`40826286`, `7ef41722`).
  Registered strength orders: `76d2cc96` strengthens `40a97664` (`9ef030cf`),
  and `23e04ae5` strengthens `ce55210c` (`8e76893e`); both are strict in one
  checked interpretation. `76d2cc96` is used by no derivation except that
  registration. `c4661518` also feeds both lasting-ground (A2ab) routes
  `db7bbdbd` and `3e0aa725`.
- **Sub-route B.** `c7c32f20` strengthens the sense bridge `8bf775e9`
  (`f80bbd9e`), and `fa3f08a8` strengthens `0042dd05` (`05eaa56a`); both are
  strict in one checked interpretation. Eight registered Dei Filius arguments
  consume both old bridges; they record `strong_version_needed` for them.
- **Sub-route C.** `732302a1` is consumed by `2162ca9d` (result `b7fbe991`,
  with `ff8ff869` and `cb1cdea9`) and by `5c5b794f` (result `764f43fe`).
  `96d25c42` is consumed by nine arguments of the necessarily-underived family
  and is an open leaf on none of the 28 recorded routes to the Catholicism
  root.

No argument concludes any of the nine targets. Each is therefore assessed on
its direct option and on the conditional material named below.

### (b) Strongest positive warrant, direct options and shared dependencies

"First grade" marks a grade given here for the first time. Every other
standing restates an earlier record.

| Premise | Strongest positive warrant | Direct option and dependencies | Provisional standing |
| --- | --- | --- | --- |
| Node `40a97664` weak concurrent actualization | The conservation account of the 2026-11-17 section: a bearer's act is standingly derivative, so continuing in that mode calls for actual efficacy now. An earlier producing act explains an origin only. The illumination and held-stone cases are analogies for the time profile; they presuppose the crux, since light is not esse. | A candidate primitive; direct acceptance is retained. It fuses the actualization principle with the contested thesis that continuing in received act is an actualization at each moment. Its rationale assumes what row 1 of (c) denies, so it does not discriminate against row 1. No case is on file of a received-esse thing given being at a later moment, and none of one persisting with no giver. | Unresolved (2026-11-12). Positively motivated and not refuted by the no-change deduction (2026-11-17 section, delivered in PR #1709, whose body records independent semantic review with no actionable findings; merged at `bbf1ce941`). Not graded; unchanged. |
| `76d2cc96` concurrent actualization by another | Entails `40a97664`. Its increment, that the giver is distinct, has one recorded argument: a persistence power depends ontologically on its substance, so the substance cannot depend on that power. `05bc2722` (b5) judges this independently justified against an intrinsic persistence power, as a provisional analyst judgment on the read Feser article. The statement records that it has the form of that reply and that no claim attributes the premise to Feser. | A candidate primitive. It presupposes everything `40a97664` asserts. A relay of givers satisfies it, so it yields no sustaining cause. No derivation uses it. | No standing above `40a97664`, which is unresolved. Given the weak version, the distinctness increment has the recorded circularity argument, a provisional analyst judgment. Not graded. |
| `d7f5a528` concurrence of causes of being | Its stated rationale only: a per se ordering of the givers of a thing's being, so that a cause of x's being is acting on x whenever any giver is. `05bc2722` records that **no warrant for it is on file**; the q.105 a.5 motivation (the first cause's concurrence in every action) is unread and not relied on. | A candidate primitive. It is the only premise linking tenseless `CausesIn` to `GivesAt`, so it carries the sense passage CAUSING_AN_EFFECT_3 → CAUSING_AN_EFFECT_5 on the route. It constrains only moments at which something gives, so the extrinsic inertia interpretation satisfies it. The immensity route needs it only for a cause of the being of everything else; that restriction is not formalized. | Open, with no recorded positive warrant beyond its rationale. Not graded. The recorded blocker is retained. |
| Node `ce55210c` weak sustaining reading | Derived by `366a6ea3` from `da72ae93`, `40a97664` and `d7f5a528`. The direct motivation is q.104 a.1 (below). | Shared dependencies: `40a97664` (unresolved), `d7f5a528` (no warrant on file) and `da72ae93`, which is **not assessed here**. `da72ae93` has its own recorded lead (no real essence–esse distinction). Its one registered derivation, `b25dbaad` through CREATURE_1, rests on the Fourth Way's universal causation of being. | Conditional on those three. Not graded. |
| `23e04ae5` sustaining reading | Motivation from q.104 a.1 co. and ad 4 (claims `40aefb2e`, `da9c82ed`, basis translation): causes of becoming differ from causes of being, and conservation continues the giving of esse. The article says this of the creature's dependence on God. That **every** cause of a thing's being gives it being at every moment of its presence is the analyst's generalization, and the statement drops the article's dependence clause. `c94eed5b` calls the comparison motivation, not a derivation. | A candidate primitive bridge. For causes of another's being its warrant reduces to `ce55210c`'s three inputs. Its increment over `ce55210c` is the case c = x; no warrant for that case is recorded, and its two consumers need the strong version by registration only (frozen Challenges). `cb1cdea9` carries the same reading at the selected world (support-formula note, 2026-11-14). | Contested and unresolved, as in `c94eed5b` and `05bc2722`. Not graded. The #1626 draft's "provisionally favorable to the scoped causal/essendi reading as a clearer formal target, but warrant underdetermined" is a judgment about the essendi reading of `DependsForBeing` and `Profile.grounds`, not a standing of `23e04ae5`; it is retained as such. |
| `c4661518` contact, time-indexed | Prima facie: exercising causation of x's being at t is a way of bearing on t, and the inclusive reading of presence asks no more of the giver than actuality in the history and bearing on t. A non-temporal agent satisfies it by co-presence. The source lead is q.8 a.1 (an agent is joined to that on which it acts), read in a public translation under `d9c2b200` with no pinned passage and no stating claim. | A candidate primitive. Its content is the exclusion of giving across a temporal gap: definition `158301bc` indexes the moment at which the activity bears on x and leaves the agent's standing at that moment to this premise. Shared by the immensity presence step and both A2ab routes; those uses are one commitment, not corroboration. | Moderate prima facie (first grade). Not strong, because its source is an unpinned lead and because gap-free esse-giving is exactly what it asserts. No substantive objection identified, as in `c94eed5b`. |
| `140544c4` presence-in-act | Prima facie, for one history taken as the actual one and its designated present moment `now`: under definition `ff1ba8f4`, `InAct x esse` is actually having being now, and on the inclusive reading whatever is present at that moment of that history is actual in it then. The extrinsic inertia interpretation satisfies the premise. | A candidate primitive calibration. Its Lean type is `∀ v x t, h.IsAt v x t → InAct x esse`: v ranges over every world's history, `IsAt` is independent of `ExistsAt` (definition `6e811e85`), and `InAct` has no world or history index. So presence in **any** history, including a non-actual one, yields unindexed actual being. The rationale gives only actuality relative to a history. The all-histories scope therefore needs a **reading choice** that no record fixes: either `InAct x esse` is world-insensitive (whatever is present in some history has being in act simply), or the premise is applied only at the selected history. A second reading choice concerns time. The premise also quantifies over every moment t, while `InAct` has no time index, and definition `ff1ba8f4` reads it as having the perfection **now** and excludes merely having had it or being going to have it. Even within the selected history, a bearer present earlier and absent now would on that definition have to possess being now. So the all-moments scope needs either a time-insensitive reading of `InAct x esse` (in act at some moment of the history), which no record fixes and which the definition's exclusions speak against, or application only at the designated `now`. No such reading is justified here. Reading the definition's "now" as `History.now` is an interpretive alignment, and "the selected history" is a choice of v; neither is fixed by a record. Result `0ed3a583` applies it at an arbitrary v and an arbitrary t and then uses the unindexed creator conjunct of IMMENSE_2, so the route consumes the full scope in both respects. Its world-level counterpart `0436de86` is a selected-world contract and so is narrower in this respect; neither is derived from the other, and neither lends the other warrant. | Strong prima facie only for the instance at the selected history and its designated present moment (first grade). The all-histories scope and the all-moments scope, both of which the route uses, rest on the two unrecorded reading choices above and are **unassessed**. No substantive objection is recorded (`c94eed5b`). |
| `c7c32f20` creator of all is IMMENSE_1 | Source lead q.8 a.1–2, read in a public translation under `d9c2b200`; no pinned passage and no stating claim. Its positive mechanism there is immediate ongoing causation of esse, which the tenseless `IsCreatorOfAll` does not encode. The typed route splits the bridge: presence from `ce55210c` or `23e04ae5` with `140544c4` and `c4661518`, then the narrowed bridge `a3913182`. | A candidate primitive bridge. It carries, untyped, sustaining as against originating causation, contact, immediacy, place, containment and measure, and presence by power and by knowledge. Its increment over `8bf775e9` is the case of a creator that is not INFINITE_1; on the routes infinity is available, so `76bad0cb` records the strong version as needed by registration only. In a one-being interpretation its antecedent holds vacuously. | Not graded. Its presence component stands exactly as sub-route A does. Its place, measure and other-modes component (`a3913182`) has no recorded warrant assessment and is **unassessed here**. |
| `fa3f08a8` INFINITE_1 is INCOMPREHENSIBLE_1 | Source lead q.12 a.7, read in a public translation under `0da0dd9e`; no pinned passage and no stating claim. Its reason there: knowability follows actuality, an infinite being is infinitely knowable, and a created intellect receives a finite degree of the light of glory. The typed route splits it into `18ca6f9d`, `bbac932e` and the near-analytic sense bridge `0042dd05`. Given infinity those three jointly entail `fa3f08a8` again, so the split is finer, not weaker in total. | A candidate primitive bridge. `fa3f08a8` entails `0042dd05`; the three finer premises entail `fa3f08a8` only together with infinity. `18ca6f9d` and `bbac932e` are **not assessed here** beyond the audits recorded in `76bad0cb`. The step from infinite esse to infinite knowability is recorded OPEN (`0da0dd9e`). `18ca6f9d` carries the scope condition of definition `80dea550`. | Positively motivated by the source lead; no substantive objection identified (`b93ce632`, `76bad0cb`). Not graded, because the finer premises and the knowability step are unassessed. |
| `732302a1` participated esse has a distinct cause | Supporting claim `11b0106d` (q.44 a.1 co. and ad 1, pinned Latin witness): being by participation entails being caused by another. The `supports` relation `6094905c` records the gap as the vocabulary choice of `CausesIn`, not the scope. | A candidate primitive under ESSE_BY_PARTICIPATION_1. If "participated" already means given by another, that meaning is an interpretation commitment and cannot also be an independently established conclusion (received-being test, 2026-11-17). The article's own argument runs through unique subsistent esse (`a576300f`, `75b5b027`; standings in `1db2004a` unchanged). Application to contingent concreta is `ff8ff869`, **not assessed here**; the reviewed 2026-11-11 judgment that contingency-to-reception is not independently warranted by the inspected argument is retained. The mode of causing is unspecified: an originating reading satisfies the premise, while its consumer `cb1cdea9` needs the sustaining reading. `2b25a78c` has the same body under a different linked sense; what is said here holds for that body, and its recorded sense-link defect is unchanged. | Strong as a source-internal reading of what q.44 a.1 says of participated being (first grade). Its application to any assigned `Participates` and to a present sustaining cause is not warranted by that reading. The 2026-11-17 outcome is retained: neither established nor refuted, with direct and conditional options open. |
| `96d25c42` no contingent supporter of a necessary bearer | The restricted argument of 2026-11-11: where a particular supporter is fixed and indispensable to the target's existence or identity, necessity of the target carries to it. The q.2 a.3 claim on causes of necessity presupposes inheritance rather than arguing it, and its types do not match this premise (source-interface section). | A candidate primitive, retained as an explicit OPEN commitment. It needs indispensability of **every** existing incoming supporter at **every** admitted world; no inspected warrant extends the restricted argument that far. The actual necessary-root route (#487) does not use it. `dd41c165` is the same predicate, instantiated on the concrete subtype; no strength relation between the two is registered. | Unchanged from the reviewed 2026-11-11 judgment, issued for the concrete instance `dd41c165` and applied here to the predicate it instantiates: the evidence favors keeping it an independently OPEN commitment and disfavors treating it as a consequence of de re necessity plus local foundation. That is an assessment of the inference, not a claim that the premise is false. Not graded further. |

Shared dependencies stay visible:

- `40a97664` is the single point at which sub-route A, the presence component
  of `c7c32f20`, and the sustaining reading that `cb1cdea9` carries all meet.
  Their agreement is one commitment seen from several consumers, not cumulative
  evidence.
- `c4661518` and `140544c4` enter every presence derivation together. They are
  calibrations of `GivesAt`, `IsAt` and `InAct`, and an inertia theorist
  accepts both. The presence step `9469ab62` (through `0ed3a583`) uses
  `140544c4` at arbitrary histories and arbitrary moments, and both scopes
  are unassessed.
- `da72ae93` joins origin from another to reception in a principle. It is
  unassessed here, and its one registered derivation (`b25dbaad`) depends on
  the Fourth Way.
- The support that the read Feser article gives `40a97664` was audited in
  `05bc2722` under the same standard as the objections. Its composition
  argument presupposes concurrent actualization against the extrinsic account.
  Its conditional that nothing extrinsic otherwise accounts for persistence is
  the premise the rival contests. Its telescope analogy presupposes the point.
  Its essence and circularity arguments are independently justified only
  against intrinsic and necessity versions of inertia. That audit is retained.
- Sub-route A reaches GOD_4 only through the immensity bridge and the full
  attribute summary, which obtain a named God before projecting existence.
  It adds no independent existence warrant (2026-11-17, retained). `40a97664`
  is not a premise of the twelve-input existence-only bundle.
- The sub-route C premises do lie on pre-naming existence routes. `732302a1`
  feeds `5c5b794f`, whose conclusion `09c6d5f0` is an input of the
  existence-only bundle `5e8e6054`, and it feeds `2162ca9d`, whose conclusion
  is `c71c068c`. This assessment adds no warrant on those routes: the grade
  of `732302a1` attaches to the source-internal reading and does not reach
  its application there, and `96d25c42` keeps an open standing.

### (c) Recorded objections and rivals, classified

| # | Record | Classification under the substantive standard |
| --- | --- | --- |
| 1 | Extrinsic existential inertia, the no-change account. Recorded against `23e04ae5` and `16828262` (`c94eed5b`), `40a97664` (`05bc2722`), the immensity bridges `8bf775e9` and `c7c32f20` on an originating reading (`76bad0cb`), and as a partial rival to contingent grounding (`b6384b6b`). | **Kept**, with one classification for every target: a substantive undercutting objection and a rival framework, not an established counterexample. *Primary target within this cluster:* `40a97664`; it reaches `ce55210c`, `23e04ae5` and the presence component of `c7c32f20` through it. *Mechanism:* S existed immediately before m, nothing induced its cessation, and a change occurs only if some factor induces it; so S exists at m with no concurrent giver. *Independent justification:* Schmid 2021 (pinned and read); the causal principle on change is one the conservation side also accepts, and the deduction is valid. *What it shows:* persistence is derivable from facts that include no concurrent giver, which undercuts the explanatory-need warrant. It does not show the premise false. The modal-spine summary's word "defeats" for that warrant is read as this "undercuts". Its own antecedent, that no factor induces cessation, must cover any warranted cessation of existential support, so it assumes the absence of standing dependence and does not discriminate against the conservation primitive either (2026-11-17). On `732302a1` it is conditional on the reading. With originating `CausesIn` it can accept the premise and contests `cb1cdea9` instead. With sustaining `CausesIn` it contests `732302a1` directly: the premise must then deliver a sustaining cause for the participated thing, which the inertia theorist denies (support-formula note, option (b); received-being test 3). `16828262`, on the sustaining A2ab route, is a separate direct target named by `c94eed5b`; it is not reached through the crux and is not a target of this assessment. |
| 2 | Persistence-power existential inertia: a thing gives itself being after its originating cause ceases. Recorded against `d7f5a528`, and against the strong version `76d2cc96`. | **Restated.** *Target and mechanism* are named, and control part 2 gives its typed shape. No independent justification for an intrinsic persistence power is recorded; the read material reports and criticizes the position. The recorded reply is the circularity argument, independently justified against exactly this version (provisional analyst judgment, `05bc2722`). It satisfies `40a97664`, so it is no objection to the crux. Not weighted as evidence against `d7f5a528`. That non-weighting is a classification made here for the first time; `05bc2722` named the rival and its provisional reply without classifying it. The earlier wording itself is unchanged. |
| 3 | Relay of givers: a room lit by a lamp, then by daylight. Recorded against `d7f5a528`. | **Restated as a lead with no evidential weight for esse**, as recorded. It is an established case for the time profile of illumination only. Whether causes of esse admit replacement is the open difference, and a restriction of concurrence to a universal cause would avoid it. |
| 4 | A gap-crossing, temporally distant cause of being, against `c4661518`. | **No substantive objection identified**, as in `c94eed5b`: a model possibility with no independent justification on file. |
| 5 | "Presence requires location, so an immaterial being is present nowhere", against the immensity bridges. | **No substantive objection identified.** It targets a spatial reading of presence that the bridge does not use, and no justification that all presence is spatial is on file (`76bad0cb`). |
| 6 | "Immaterial, therefore immense" is not Aquinas's argument; q.52 a.1–2 gives an angel a localized presence (`d9c2b200`). | **Boundary retained.** It is a substantive objection to a different inference, from immateriality to IMMENSE_1. It does not bear on `c7c32f20` or `8bf775e9`, which go through causing being. Its source is an unpinned lead. |
| 7 | A Spinozist God satisfies IMMENSE_2 and plausibly IMMENSE_1. | **Boundary retained.** It bears on the distinctness attribute, already recorded there, not on these bridges. |
| 8 | q.8 a.4 absolute ubiquity over hypothetical places. | **Boundary retained.** It is a stronger optional sibling reading, not a requirement of IMMENSE_1 and not an objection. |
| 9 | "Finite minds grasp infinite objects through finite principles", against `bbac932e` and so `fa3f08a8`. | **No substantive objection identified**, as in `76bad0cb`. Its justification concerns quantitative infinity; relevance to INFINITE_1 is not shown. |
| 10 | The q.7 a.2 caveat: a created intellect has an extensionally infinite reach over universals (`0da0dd9e`). | **Restated as an open reading check**, not an objection. A premise about finite intellectual power must be restricted to received intensity or adequacy. Whether `bbac932e`'s reading of a finite intellect, as one whose being is not INFINITE_1, is adequate to it is unchecked. |
| 11 | Apophatic tension with the knowability of God. | **No substantive objection identified.** Both senses negate comprehension only (`76bad0cb`). |
| 12 | The Nicene scope point against `18ca6f9d`. | **Boundary retained** as the recorded scope condition of definition `80dea550`. It is internal to the case and is not an objection to `fa3f08a8`. |
| 13 | The same necessary whole through replaceable realization, with the switching pattern, against `96d25c42` and `dd41c165`. | **Kept**, unchanged from 2026-11-11, as a targeted challenge to the universal scope. *Mechanism:* necessity of an effect does not make any particular sufficient or realizing supporter necessary; different contingent supporters can serve at different worlds. *Independent justification:* that direction-of-necessitation point is logical, and essential dependence is warranted only where an identity or origin criterion supports it. *Status:* not an established counterexample. The rival still owes numerical identity under substitution, real existential support and necessary coverage of realizations. |
| 14 | The formal or constitutive account of a bearer's actuality, against the De ente coverage step behind the conditional route to `732302a1`. | **Restated**, as in the received-being test. It targets some-cause coverage `d1f3ffcc`, not `732302a1` directly. It owes an account of its actual obtaining and is not refuted by lacking an agency predicate. |
| 15 | An esse-cause as mere enabling condition, moved upstream to `ca07cae9` and `732302a1` (support-formula note, 2026-11-14). | **Restated**, unchanged. *Target:* that a participated or composite thing has an effective cause of its being and not only enabling conditions. *Mechanism* and its general justification (enabling without production is familiar and is distinguished in q.104 a.1) are recorded. Its application to participated esse is not shown. It remains priced, not refuted. |
| 16 | The contingent-root and intrinsic-contingent accounts (2026-11-11). | **Boundary retained.** They target coverage and `ff8ff869`, not `732302a1`. Their recorded debts are unchanged. |
| 17 | De dicto necessity of some supporter, essential origin, and the q.2 a.3 cause-of-necessity premise, as defenses of `96d25c42`. | **Rejected support routes, retained as rejected** (source-interface section). They are not objections. Each either permits varying contingent supporters, runs in the wrong direction, or needs two unstated interface conversions. |
| 18 | The lead that there is no real essence–esse distinction (Suárez), against `da72ae93`. | **Restated as an unread lead** with no evidential weight. It would remove the antecedent of `40a97664` for creatures, a different exit from inertia. |

Countermodels and controls are facts about one stated formal interpretation
each. They show where a premise is needed there, never that it is false or
doubtful:

- `ConcurrentActualization.controls` (`955ef523`). In part 1 an inertia
  interpretation satisfies the reception bridge, concurrence, presence-in-act
  and contact and falsifies `40a97664` and the conclusion. In part 2 a
  persistence-power interpretation satisfies `40a97664` and falsifies
  `76d2cc96` and `d7f5a528`. In part 3 a relay satisfies `76d2cc96` and
  falsifies `d7f5a528`. In part 5 a self-cause that gives nothing separates
  `23e04ae5` from `ce55210c`. In part 7 all premises hold together
  nonvacuously.
- `SustainingCausation.controls` (`b12b253b`). An originating interpretation
  satisfies contact and presence-in-act while an IMMENSE_2 being is not
  present to all. Each premise of the presence route is needed in one
  interpretation.
- `ConcurrentCessation.certificate` (`610e21dc`). The reused inertial and
  sustained histories both satisfy causal coverage of cessation. The
  no-giver/no-continuation condition is classically equivalent to continued
  giving on the same received, prior-present bearer. The result covers
  Nat-sampled continuation only.
- `DeiFiliusImmenseIncomprehensible.controls` (`ccba9330`). A cause of the
  being of all that is not infinite satisfies `8bf775e9` and falsifies
  `c7c32f20`. An infinite being comprehended by a caused intellect satisfies
  `0042dd05` and falsifies `fa3f08a8`.
- `NecessaryWholeReplacement.checks` (`be32d3af`). One interpretation has a
  fixed target with contingent support at both worlds, all-world local
  grounding and cross-world direct-edge asymmetry. Its fixed label is not a
  genuine whole.
- The `Round2Grounding` omission controls. With an empty participation
  predicate the other two inputs of `2162ca9d` hold vacuously.
- The source-cut, illumination and omission-case material of the earlier
  sections concerns states of an existing bearer or stipulated records. The
  parent/child valuation of the #1626 draft was checked by a local truth table,
  not by Lean. None of it is a model of esse-giving or of a complete inertial
  worldview.

Tally: **kept** 2 (rows 1 and 13); **restated** 6 (rows 2, 3, 10, 14, 15 and
18); **boundary retained** 5 (rows 6, 7, 8, 12 and 16); **no substantive
objection identified** 4 (rows 4, 5, 9 and 11); **rejected support routes
retained** 1 (row 17). Nothing is dropped as evidence and no earlier weighting
is changed. For `140544c4` no objection is recorded and none is identified;
the thin-existence alternative is recorded as a formal alternative only for
the bundle containing the world-level contract `0436de86` (`b6384b6b`). That
classification is not transferred here, because `140544c4` quantifies over all
histories and all moments and `0436de86` over one selected world.

### (d) Overall provisional judgment, revision conditions and next test

**Judgment.** On the meanings in (a), the conservation reading behind
sub-route A is a coherent, positively motivated conditional account. Its crux,
weak concurrent actualization `40a97664`, is unresolved against extrinsic
existential inertia: each side's recorded rationale assumes what the other
denies, and the causal requirement on cessation that both accept favors
neither. The rest of the route is no better supported than that crux together
with concurrence `d7f5a528`, for which no warrant is on file, the
unassessed reception bridge `da72ae93` and, for the presence step, the
unassessed all-histories and all-moments scopes of `140544c4`. This covers
`ce55210c`, `23e04ae5`, `76d2cc96` and the presence component of `c7c32f20`.
The two calibration
premises carry no recorded substantive objection: `c4661518` is moderate prima
facie, and `140544c4` is strong prima facie only for its instance at the
selected history and present moment, with its all-histories and all-moments
scopes unassessed.

In sub-route B, `c7c32f20` and `fa3f08a8` are positively motivated by source
leads that are read but unpinned. Both are ungraded, because the finer premises
that carry their warrant are unassessed.

In sub-route C, `732302a1` is strong as a source-internal reading of q.44 a.1.
That reading warrants neither its application to contingent concreta nor a
present sustaining cause. `96d25c42` keeps its reviewed 2026-11-11 standing as
an independently open commitment, with a kept rival.

The cluster supplies no eternity conclusion and no independent warrant for
God's existence. Sub-route A reaches GOD_4 only after naming. The sub-route C
premises lie on pre-naming existence routes (`732302a1` through `5c5b794f` to
`09c6d5f0` in bundle `5e8e6054`, and through `2162ca9d` to `c71c068c`), but
add no warrant there, because their grade does not reach their application.
Nothing is established or defeated.

**Comparison with earlier judgments.** Each earlier recorded judgment on these
statements is kept unchanged, and **no revision is declared**:

- `c94eed5b` and `05bc2722` (2026-11-12): inertia is substantive against the
  sustaining reading; the dispute with the extrinsic version rests at
  `40a97664`, and with the persistence-power version at `d7f5a528`; overall
  unresolved.
- The 2026-11-17 sections of this note: the received-being test's outcome for
  `732302a1`, and the concurrent-actualization case assessment. Both were
  delivered in PR #1709 (commits `65b0fc8c6` and `6aadc6bdb`). Its body records
  that both complete proposals received independent semantic review with no
  actionable findings, and it merged at `bbf1ce941`. Their in-note handoff
  wording ("for fresh semantic challenge", "for fresh challenge", "proposed
  for coordinator challenge", "No push, PR, watch or merge") is therefore
  superseded as a statement of current work; their substantive outcomes are
  kept, and this section adopts no wording stronger than theirs.
- `76bad0cb`, `b93ce632`, `d9c2b200` and `0da0dd9e` (2026-11-12): the
  classifications of the Dei Filius leads.
- The reviewed 2026-11-11 judgments in the underived-essence note:
  contingency-to-reception, and replaceable support.
- The support-formula note (2026-11-14) and its #1626 research draft.
- The current assessments `5c7bc356`, `1db2004a`, `e64d5241`, `383d23ad` and
  `0ddaa334` for the neighbours they name.

The three first grades (`140544c4` at the selected history and present
moment, `c4661518`, and
`732302a1` as a source-internal reading) fill places where no grade existed.
They contradict no earlier statement: `c94eed5b` identified no substantive
objection to the first two, and the grade of `732302a1` attaches to the reading, which the
2026-11-17 outcome did not assess.

**Blockers and boundaries retained.**

- No warrant for concurrence `d7f5a528` is on file; q.105 a.5 is unread.
- The independent evidence dependency of `05bc2722`: a real
  standing-dependence application against the historical-law account.
- `96d6d1cd`: independent justification that every selected incoming
  existential support is indispensable across the relevant alternatives is
  missing; the world-quantifier scope boundary stands.
- `cbfd544b` and `dee1c25e`: independent warrant for contingency-to-productive
  receipt is absent; a positive same-bearer esse receipt, its coverage, source
  distinctness and a local receipt-to-`CausesIn` bridge remain separate
  obligations. Illumination and source-cut results concern a state of an
  existing bearer.
- `0da0dd9e` and `d9c2b200`: q.12 a.7, q.7 a.2 and q.8 must be pinned and read
  before any stating claim; the step from infinite esse to infinite
  knowability is open; place, immediate causation and containment need their
  own vocabulary. Vacuity in a model with no created intellects must not be
  counted as warrant for `fa3f08a8` or its finer premises (`0da0dd9e`).
- The pending next tests of `c94eed5b` (2 to 4) and `76bad0cb` (1 to 5) stay
  recorded leads. The ACPQ article is unread, and no conclusion about its
  arguments follows.
- Pointwise giving is not one fixed giver, a giver is not the root witness,
  times are not worlds, and q.104's timeless action is not a temporal
  sequence.

**Revision conditions.**

- An independently justified standing productive-dependence account for a
  present bearer, or a reason why the no-inducer law requires or excludes
  existential support, would move `40a97664` and everything that rests on it.
  A case of received esse persisting with no giver, independently supported,
  would weaken it.
- A read and assessed warrant for concurrence, or a positively supported case
  of replaceable or redundant givers of esse, would grade `d7f5a528`.
- An assessment of `da72ae93`, `18ca6f9d`, `bbac932e` and `a3913182` would
  allow `ce55210c`, `fa3f08a8` and the non-presence component of `c7c32f20` to
  be graded.
- An assessment of `ff8ff869`, or a disambiguation fixing whether
  participated esse means given by another, would settle how far the
  source-internal grade of `732302a1` reaches.
- The 2026-11-11 conditions recorded for the concrete instance `dd41c165`
  stand for `96d25c42`, the predicate it instantiates: an identity or existence
  criterion making each supporter indispensable would strengthen it; a
  non-question-begging identity and complete-ground account of replaceable
  realization would strengthen the rival.
- A gap-crossing cause of being with independent justification would weaken
  `c4661518`.

**Next discriminating test.** Formalize the restriction that `05bc2722`
recorded and did not formalize: concurrence only for a cause of the being of
everything else. Then test whether the presence step `9469ab62` still follows
from it with `da72ae93`, `40a97664`, `140544c4` and `c4661518`, or find the
exact obstacle. Under the strength rule (#1017) the route should consume the
weakest version that suffices. A success would register the restricted
premise as weaker than `d7f5a528` and remove the relay lead (row 3) from the
route, leaving the persistence-power rival and the unread q.105 a.5 as the
remaining questions for a much narrower premise. A failure would show that the
route needs concurrence for arbitrary causes of being. Either outcome reuses
existing vocabulary and controls. It does not touch the crux: `40a97664` moves
only on the evidence named in the first revision condition, and under the
existence-first direction of 2026-11-17 that work stays behind the foundation
question already continued in
[the foundation note](notes/unique-feedback-explanation-311.md#current-foundation-judgment-on-the-existence-only-case-2026-11-17).
For sub-route C, `96d25c42`'s own recorded next step is retained unchanged
(source-interface section): "Stop this line until independent evidence
discriminates universal essential dependence from switching support, or
justifies the two source interfaces and their world scope." The 2026-11-11
next step recorded for its concrete instance `dd41c165` is likewise retained.


## ¬C3: from finite survival to survival at a limit (2026-11-23)

**Target and nonoverlap.** Issue #1801 asks what a law contributes to the
continued existence of the *same already actual received-esse bearer* under
¬C3 (`40a97664`). This is a temporal-scope test of that law, distinct from
#1891's complete #1614 source/priority model, #1895's finite-step source
withdrawal, and #1898's inertial-foundation subset. It adds no new causal
ontology, source claim, God-route premise, or proof of a metaphysically
possible world. The relevant existing relations are
`TimeSymmetricGiving.CessationNeedsInducer` (all time pairs),
`ConcurrentActualization.ConcurrentlyActualized`,
`SustainingCausation.BeingGiving`, and `TemporalHistory.History`.

### Same bearer, two laws and the limit

The new `LawActuality.LimitPersistence` control uses `WithTop Nat`, an
abstract time order with natural-number stages and an additional limit
`⊤` (ω+1). The source is present at every stage in both versions; the
received-esse recipient is present at *every finite* stage and is given
being at stage zero only. All finite stages and the source's identity are
the same in the two versions. At `⊤`, one history keeps the recipient
and the other loses it. Both agree with the world-level existence
interpretation at the designated present `now = 0`.

- **Finite-step persistence** `E(n) → E(n+1)` is true in **both**
  versions. It is silent on whether the receiver exists at `⊤`.
  Therefore it cannot, by itself, carry a proof of existence through a
  limit, regardless of the number of finite stages inspected.
- **Global interval no-positive-loss** (the already defined
  `CessationNeedsInducer`) says that if the *same* bearer is present
  at s and missing at any later t, some positive cessation-inducer
  occurs in (s,t]. With no inducer, it holds of the limit-surviving
  history and fails for the disappearing one. This is a genuinely
  stronger existential-law scope, not a theorem extracted from the
  finite-step rule.
- **Positive loss at the limit**: a third profile retains the
  disappearing history but explicitly declares an inducer at `⊤`
  for that very receiver, which makes the interval law true. That
  interpretation adds an ontic event; it is not licensed by
  describing a missing recipient or source withdrawal as an event.
  The conserver may reject the no-inducer premise for precisely
  this reason, while the inertialist must argue that the event
  really is a positive loss, rather than pure failure of production.
- **¬C3 survives the stronger law.** The limit-surviving receiver
  obeys the interval-wide no-positive-loss law while the originator
  does not give its being at later stages or the limit. Thus even
  a strengthened global conservation-of-presence law is compatible
  with rejection of weak concurrent `GivesAt` in the *same model*.
  This compatibility is not an explanatory proof of that law or
  of genuine existential derivativeness.

`TruthCore.Results.Explanation.LawActuality.limitPersistenceControls`
is the unregistered proof of the above exact 14-conjunct
`LimitCertificate` (check the delivered CI head before calling it
Lean-verified). It reuses `WithTop Nat` from Mathlib and leaves
the previously registered #743 law-identification results untouched.

### Strongest ¬C3 response and the exact question

The most robust inertialist does **not** restrict the causal principle
to discrete successor steps: Schmid's own no-cessation account is stated
for arbitrary earlier/later instants (the existing
`TimeSymmetricGiving.CessationNeedsInducer` encoding already reflects
this), and therefore reaches a designated endpoint without a separate
successor there. If the global law is genuinely metaphysically governing,
prior actuality plus no positive loss explains the later bearer,
including at a limit, without strict concurrent production.
This model adds **no independent objection** to that broad form of
existential inertia. It shows why the weaker local/step version of
the rival is not enough.

The conservation advocate can deny the **existential** reach of
that global law for still-received esse, or argue that loss of a
concurrent actualizer is itself a relevant absence whose effects
need no positive destructor; neither is a consequence of the
purely formal model. The inertialist can reply that cessation is
a change requiring an inducer but must clarify whether this covers
a bearer without an underlying persistent subject at the endpoint.
Both sides must preserve the distinction between an ontic
destructive event and an absent productive contribution.

At **local explanatory scope**, the broad interval law plus the
earlier positive existence fact is a genuine conditional persistence
account. At **ultimate scope**, that law still uses the prior actuality
as a positive explanans. A global law can be independently primitive,
but neither its quantifier over arbitrary intervals nor its satisfaction
by the complete history establishes the actual *instantiation*
`∃t, E(t)` without a further foundation/ontology commitment.
This is the previously recorded #1801 §7 positive-actuality question,
not a second "law fails to select a history" theorem or an independent
new cost. The sustaining side is subject to the same test for its
source's actuality and the bridge from ground to productive giving.

**Cumulative judgment (provisional):** the stronger interval-wide
no-destruction law avoids the limit objection and remains a coherent
structural ¬C3 rival. Compared with mere successor-step persistence,
it pays for **explicit limit-inclusive existential coverage**, not
a demonstrated logical contradiction. Its metaphysical warrant and
the treatment of an apparent nonproductive cessation remain open.
Neither C1/C2 nor a same-witness GOD_4 route is disproved by it; in
particular a necessary origin can coexist with inertial persistence.
C3 and its negation still separate at the meaning and positive warrant
of *presently productive existential derivation*, not the arithmetic
of successor steps.

**Next discriminating test:** seek a source/causal or metaphysical
principle for **limit-inclusive absence of real destruction** that
(i) is not simply `CessationNeedsInducer` asserted again, (ii)
does not confuse absence of a bearer with an act of destroying it,
(iii) applies to this very bearer with received esse, and (iv)
can be evaluated against a timeless/concurrent sustainer under
matched explanatory completeness standards. No claimed frontier
change; no fresh premise, theorem registration, source attribution
or warrant promotion.
