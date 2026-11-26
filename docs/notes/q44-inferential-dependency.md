# Q44: the selected inferential presentation and the missing source-selection bridge

Proposed outcome for independent semantic challenge, 2026-11-17. Baseline
`d69634db451aabb99ba0be7f2c231747169a478f`; target definition
`f114f527-20e2-5997-8219-df7f0457cf63`. Analyst dependency reconstruction;
existing source readings reused, attribution deferred. This note does not
certify a historical derivation or introduce a theological premise. [Original PR #1701](https://github.com/moritzbrantner/formal-logos/pull/1701)

## Parent and root connection

The exact existing participation parent is statement
`11e24b50-06bc-5e2e-b9b6-a4e4dc421237`,
`Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse`:
`∀ x, x ≠ p → Participated x`. It is an open supported reading for a
selected primary `p`, not a theorem selecting that primary. Argument
`38bef29c-ff2d-5f34-96f9-f6a35fb2293d` consumes it to conclude
`612078bf-5a68-5542-8b7b-f862f816ece0` (others are CREATURE_1).
There is an existing graph connection from that conclusion through argument
`18fe3293-895f-5fe1-b142-14d33b6c1ae9` to
`da09703b-0b1e-5dca-9dd7-6c0c8d1610d7` (genus causality at being), then
argument `1deb1d29-d514-591d-9b2d-26eb4401d371` to root
`53964cbe-5831-5812-af33-4d87896d47a7`. Each downstream argument retains
all its other premises. This is graph reachability, not a claim that this
support bundle occurs on a currently selected cheapest frontier route.

The separate universal divine-cause candidate is
`86d02b69-87eb-5594-9958-ccaa5fe6b685`,
`GodMaximalCausal.GodCausesBeingOfAllOthers`. It quantifies over GOD_4;
the participation parent names `p` without `IsGod p`. No identity between
these targets is inferred. The corpus has no argument concluding either
11e24b50 or 86d02b69 at the baseline. The latter's own recorded support is
the q.2 a.3 naming converse, not a registered q44 proof.

## Concrete application of immediate dependency

Use the existing definition `3492ef00-6d09-4008-8ab2-25e2aa03e725`,
`RegressDomains.Justification.inferential`. Select a presentation whose claims
are corpus statement identities, whose rules are exactly the argument IDs in
the table, whose premise sets are the complete listed sets, and whose
conclusions are the listed statement IDs. This specifies the data to which
immediate membership is applied; it does not assert `justified` or declare
noninferential foundations. Every ID in one premise cell is conjunctively
required by that selected rule. Other corpus support options remain available.

| Selected rule (argument UUID) | Complete immediate premise set | Conclusion |
| --- | --- | --- |
| `38bef29c-ff2d-5f34-96f9-f6a35fb2293d` | `11e24b50-06bc-5e2e-b9b6-a4e4dc421237`, `2b25a78c-abad-50d9-abb9-31a753409192`, `b7d4eede-ab50-5522-8902-f33238fa234d` | `612078bf-5a68-5542-8b7b-f862f816ece0` |
| `d3c6a6f7-b653-578c-a3d5-dc94480401ba` | `7561e216-900f-53f1-9e22-d74427758cd6` | `2b25a78c-abad-50d9-abb9-31a753409192` |
| `4876dc46-bbcb-5daa-a669-1abfce58b2ef` | `cbb068e8-337d-5772-a3f9-10df457ba9fe`, `33ad148b-ceab-5856-a4f8-c999a1dba644` | `7561e216-900f-53f1-9e22-d74427758cd6` |
| `efb88bdf-6f08-42a1-925e-90e591f3100d` | `5969873b-a619-4880-a92d-77e1f2752513` | `b7d4eede-ab50-5522-8902-f33238fa234d` |
| `a9cd32b6-c7fa-4b4b-94dd-108ff52bcb60` | `0e242e29-7670-55f8-bf8e-f5800b9890c7`, `2f2f5bd2-9b6a-4251-8b93-885996ae08e2` | `5969873b-a619-4880-a92d-77e1f2752513` |
| `87dd8489-f336-52f7-904f-96cc97d60c86` | `a9622441-2db2-5d32-9b02-a9d283bd2949`, `6c27657f-a2bf-5c1d-963c-c154b66bfa85`, `101bdd62-7cd0-5923-8f03-d9d443f4ba51`, `d9fad785-40ab-555a-a1c1-5e39c9d50497`, `d5a94eb1-72d2-53e0-9a52-9787b5b61a8d` | `0e242e29-7670-55f8-bf8e-f5800b9890c7` |

Thus 11e24b50, 2b25a78c and b7d4eede each immediately depend **into**
612078bf in the premise-to-conclusion orientation of `inferential p c`.
Neither 0e242e29 nor cbb068e8 is an immediate premise of that rule.
The selected presentation instead gives these explicit transitive paths:

- `cbb068e8 → 7561e216 → 2b25a78c → 612078bf`;
- `0e242e29 → 5969873b → b7d4eede → 612078bf`.

These abbreviations denote the unique full IDs in the table. Each step retains
the other premises of its rule: a path is not a sufficient argument bundle.
For example, expanding both middle premises of 38bef29c by the selected rules
leaves the joint bundle **11e24b50, cbb068e8, 33ad148b, 0e242e29,
2f2f5bd2**. Alternatively retain the three direct premises; alternatively
expand only one. No direct-assumption option is removed. Further expanding
0e242e29 requires all five inputs in the last table row; in particular
`d9fad785-40ab-555a-a1c1-5e39c9d50497` already supplies the universal
maximum-to-cause principle. Expanding that input via the attribution route
is a different selected proof choice and must not be silently used as an
independent warrant for the same principle.

Exact theorem reuse, with namespace prefix `TruthCore.Results.`:

- `Causality.Round2PerfectionPrimacy.othersAreCreatures` uses hOthers,
  hCaused and hCreature, obtaining a distinct cause from hCaused and applying
  hCreature. It invokes no subsistence or uniqueness theorem in its proof.
- `Causality.TermSenseForks2.participatedExternalEsseCause` uses both the
  participation-to-distinct-esse bridge cbb068e8 and q3 reading 33ad148b;
  `participatedHasOtherCauseFromExternal` forgets the extra existence data.
  The external cause remains mode unspecified, not automatically efficient
  or conserving. The 33ad148b node itself retains distinct support options:
  argument af503cd7 has premises be639b3f and 61bd42e5; a398cc69 has sole
  premise 1ff08418 (full IDs are in their existing records). These are not
  proofs from the bare word "participation".
- `Causality.CreatureSenses.causedInBeingByAnotherIsCreature1` uses
  `MaximalCauseWithNoDistinctEsseCause` and `CausedEsseIsHad`, selecting the
  maximum as each caused thing's universal cause; its instantiation theorem
  supplies the legacy b7d4eede. CREATURE_1 contains a universal cause;
  CREATURE_2 contains only some distinct cause. Their bridge is substantive.

## What the subsistence/unity report does and does not supply

The earlier reading in [causal-perfection-transfer.md](causal-perfection-transfer.md#source-defense-audit-why-would-an-esse-maximum-cause-other-beings-2026-10-31)
reports q44's appeal to prior subsistent esse and numerical uniqueness.
That is retained as a source-reading report. It supplies no identified
corpus rule binding particular earlier results as premises of 11e24b50 or
86d02b69. A shared imported Solution, definition or word supplies no edge.
In particular the existing Q11 theorem
`TruthCore.Results.Case.Catholicism.Q11NatureUniqueness.godIsOneFromNature`
requires incommunicable individuation, divine suppositum/nature identity and
common divine nature. Its conclusion `GodIsOne IsGod` concerns the IsGod
extension. It does not say that every essentially-esse source belongs to that
extension. Substituting it for source uniqueness needs that bridge, not just
its theorem name. The formal esse=essence equation likewise does not alone
identify the primitive `Participated` predicate (definition 14d30c53 explicitly
rejects that identification).

The precise missing analyst application is therefore: establish participation
coverage for the same selected `p`; connect participating possession to a cause
having esse essentially; identify every relevant essentially-esse cause with
that `p`; and, for 86d02b69, connect each GOD_4 witness to the selected source.
These are open semantic/inference bridges, not new registered propositions or
hidden definitions. The local external-cause theorem only yields an existential
cause for each participant. It does not select one common cause. The existing
CREATURE route supplies a common universal cause through the Fourth Way instead;
that is a defensible conditional alternative, not a defeat of the q44 proposal
and not an independent q44 discharge of universal causality. No substantive
objection to the truth of subsistence, unity or participation is established by
this dependency audit.

## Four dependence roles and proposed judgment

Immediate inferential dependence is membership in one selected rule's premise
set; transitive dependence is a nonempty chain of those memberships, still with
all companion premises retained. Ontic requirement instead uses
`FirstPrincipleRoles.OnticRequirements.requires w dependent prerequisite` on
interpreted obtaining conditions. Causal dependence instead concerns the
interpreted causes/effects and the source/effect existence interface of q44's
replies. Statement tokens in the table are neither those conditions nor their
causes. No transitivity, asymmetry, well-foundedness or causal applicability is
transferred from the selected proof graph to either metaphysical relation.
The already linked ad2 claim bd3767d3 explicitly says its necessary-principles /
necessary-conclusions illustration is not itself an efficient-cause ontology.

Proposed provisional judgment: the immediate dependency application is resolved
for the selected registered presentation, including its complete companion
premises and two substantive expansion choices. The stronger report that this
is a formally integrated historical q44 subsistence/unity chain is unsupported
by the inspected bindings. This is a precise semantic gap, not uncertainty
manufactured about the premises' truth. Independent source and philosophical
warrant remain as previously recorded. No new theorem is needed to repeat
membership data, and nominal subsistence/unity wrappers would not repair the
missing meanings or bridges.

Reopen the historical question with an exact earlier result/statement mapping
and the corresponding q44 inferential reading. Reopen the analyst formalization
when a source-indexed essential-possession interpretation and its same-source
selection bridge are supplied or selected for investigation. Then test the
complete bundle against the existing external-cause and CREATURE alternatives;
do not infer it merely from q3 identity or Q11 uniqueness. That vocabulary and
warrant investigation is a distinct consequential scope decision for the
coordinator, rather than an unreported extension of this dependency audit.

## Claim/type self-sweep and evidence boundary

No claim, statement, argument, result, Lean type, sense binding, frozen Challenge,
source record or certificate changes. Existing theorem source signatures and
proof bodies support exactly the uses above; context's import neighbours are
not proof uses. Existing CreatureSenses controls witness finite interpretations
separating some external cause from a universal cause, an omitted actuality
premise, and a positive caused-being bundle. They prove facts about those
interpretations, not falsity of either metaphysical premise or a complete rival
worldview. No new model claim is made. Premise effect: **none**.

Readiness: this runtime checkout has no .lake or local CLI. Used the warm parent
CLI read-only with `--root` this checkout through `worker_env.py --`; no cold
build, checkout preparation or preview. Ran related, dossier (each immediate
participation premise and the distinct divine-cause target), brief, novelty,
and context for the five substantive/bridge rules above. No issue snapshot was
supplied; missing issue hits imply nothing. Shared convention sourceRevision
`15f348b072188255da837578eaafc8a98f12fdf0`. Unchanged proof evidence is reused;
this semantic proposal awaits independent challenge and required final CI.

Focused validation of this delta: `truth check` passed (existing corpus/lexicon
warnings remain; no allowlist or status-cache edits); offline
`attribution-check --base d69634db451aabb99ba0be7f2c231747169a478f` reports no
new or changed stating claims. Computed `frontier-diff` against that baseline:
490 root-reaching open premises (349 bare, 90 supported, 51 stated) unchanged;
489 distinct verified support alternatives unchanged; zero added alternatives;
"no change". `git diff --check` passed. These checks validate records and the
reported premise delta; they do not independently certify semantic fidelity.

## Independent challenge (2026-11-17)

GPT-6.1 Sol independently reviewed dab87151d054e6b1caff719dc0330c81e5c39033
against d69634db451aabb99ba0be7f2c231747169a478f and found no substantive
findings. The premise table, complete companion bundles, theorem descriptions
and downstream graph match the records. Q11 uniqueness remains restricted to
IsGod; the Fourth-Way alternative is not represented as independent q44 support.
This resolves the scoped dependency audit, not premise truth or formal closure.
Next research interprets essential possession of esse and tests selection of the
same source p, with GOD_4 identification separately explicit. Existing mechanical
evidence was reused; no new historical authentication was claimed.
## Essential-source application

Expanded assignment after independent review of `dab87151d` found no substantive
findings. This section is the complete proposed outcome for a new independent
challenge. Formal home: `TruthCore/Causality/Q44EssentialSource.lean`, sibling
results `TruthCore/Results/Causality/Q44EssentialSource/`, and
`specs/q44-essential-source.toml`. Earlier historical gaps above remain; this
is an explicit analyst application, not a recovered historical proof chain.

### Meaning before the bridge

**Having esse essentially** is read here using the existing `OwnBeing`
primitive of definition `5dc08b95-ca15-52ab-b8cd-2b558e9a13f7`: the bearer is
its own subsistent act of being, rather than a subject that has an act of being
received in a principle. This is stronger in meaning than "happens to exist",
"exists necessarily", "has no recorded cause", or "two arbitrarily chosen
profile-map values are equal". It is not being efficiently self-caused:
"own" identifies what the bearer is, not an exercise producing itself.
An abstract term or predication of being is not itself a subsistent causal
bearer. A subsistent created form is not, merely by subsisting, its own esse;
the existing q7 reading distinguishes its received esse. These exclusions reuse
the recorded q3/q7/SCG readings, without new source claims.

The intended subsistent-esse case is the theological source described in those
readings. It is an interpreted candidate, not a newly demonstrated concrete
example. No independently observed case of an essentially-existing causal
bearer is supplied by this investigation. The existing heated-iron/fire example
is an analogy for received possession versus source possession; it supplies no
universal inference from familiar heat to the production of esse. No such
abstraction bridge is asserted here.

`OwnBeing` and `Participated` remain interpreted primitive parameters. The new
predicates are transparent quantified compounds over them and the SAME q3
`Profile.InAct`, `CausesIn`, `essenceOf`, `esseOf` and `esse`. Their Lean bodies
define their scopes and logical contents; they do not complete the primitive
formal meanings. In particular neither OwnBeing nor participation is defined
as the negation of the other, or as a represented identity/inequality. No
exhaustive dichotomy between the two is assumed. No new sense of modal essence,
efficiency, conservation or ontic grounding is mixed in.

The new source-supply premise de05072a says: each participant x has a distinct,
actual OwnBeing c that causes x's esse. It requires an explicit `CausesIn c x
esse` edge. This is stronger than finding an arbitrary local cause or merely
an ancestor in a chain. An encoded edge is not a claim that there are no
intermediate/secondary causes; `CausesIn` already admits causal responsibility
without defining immediate adjacency. A secondary cause need not itself be
OwnBeing. Selection quantifies only over distinct actual OwnBeing causes of participants,
not over every cause or every hypothetical own-being bearer.

### The tested identity bridge and the root consumer

| Statement | Exact content and role |
| --- | --- |
| `de05072a-5db0-4a31-8e24-b18fedf01401` | Each participant has a distinct actual OwnBeing cause of esse. Open analyst source-supply premise. |
| `6acd44eb-4b3e-480c-a479-6b4ac7a2522e` | Every relevant distinct actual OwnBeing cause has `esseOf c = essenceOf c` in this same profile. Open, restricted semantic dictionary. |
| `e2bfd1b1-7d5e-4be3-b5d4-f9db988c5745` | The selected p is actual and has that represented identity. Open witness premise; it does not assert `OwnBeing p`. |
| `a576300f-4b01-45ae-902c-cfe3d0fbf2de` | Existing `DeEnte.AtMostOneEsseIsEssence`: any two actual identity bearers are identical. Retained with its existing support options. |
| `dcf4bcdd-4feb-4d97-a7e2-f6a08cdf4702` | Every relevant distinct actual OwnBeing cause c is numerically p. Derived selection, not an assumed definition of essential source. |

Result `015caba2-d6c1-46a1-abbc-ba3e836ebab6`, theorem
`TruthCore.Results.Causality.Q44EssentialSource.sourcesSelected`, derives the
last row jointly from **6acd44eb, a576300f and e2bfd1b1**. The source c is distinct from its participant and actual;
the dictionary puts it under the existing uniqueness predicate; the selected
witness is actual with the same identity property; at-most-one yields c=p.
The corpus detector classifies this selector as a transcription (an application
of the at-most-one input). Its conclusion therefore stays open under the
existing closure rules; no classification override is requested.
This does not confuse "each has esse as its own essence" with "their essences
are numerically the same": numerical identity comes from a576300f, with its
substantive shared-nature burden, not from equality inside each individual.

Result `3beb5720-7210-4772-9bb2-ced7756557eb`, theorem
`TruthCore.Results.Causality.Q44EssentialSource.othersAreCreatures`, derives the
EXISTING `612078bf-5a68-5542-8b7b-f862f816ece0` from **11e24b50, de05072a
and dcf4bcdd**. For each x≠p, coverage makes it a participant; its essential
source is p; so p causes x's esse. Therefore p is a universal cause of every
other actual being, and x is CREATURE_1 with p as that universal cause.
The conclusion instantiates `OthersAreCreaturesReading` at the existing
`CreatureSenses.IsCreatureOfUniversalCause`, not at CREATURE_2.
The expanded joint bundle is **11e24b50, de05072a, 6acd44eb, a576300f,
e2bfd1b1**. Existing direct-premise and Fourth-Way support options remain.

No selected OwnBeing premise was hidden: if at least one participant is
supplied, de05072a gives an OwnBeing source and selection identifies it with p,
so OwnBeing p follows. Without that population, selection and the consumer can
be vacuous, and no existence of another being is inferred. The proof does not
require every domain member to be independently stipulated actual. Its strong
coverage premise is exactly the existing 11e24b50, and source supply then gives
causal edges for each other domain member. The universal-cause component of
CREATURE_1 itself quantifies only over actual others.

### What the three omissions discriminate

Result `7cdc011d-037c-4a23-b748-f4311ebc5cd3`, theorem `controls`, checks
`3b601644-d9c2-43a5-8bb1-d16ddfba0a87`. All models use three actual beings
(primary, source, effect). In the first three the effect participates, the
source is OwnBeing, and the source causes that distinct effect. Selection
fails because source≠primary:

1. **Dictionary omitted:** only primary has represented essence/esse identity.
   At-most-one and the selected identity witness hold. This interpretation
   deliberately fails to represent the intended own-being identity; it shows
   why arbitrary profile maps do not interpret the primitive automatically.
   It is not evidence that real own-being could lack its intended identity.
2. **At-most-one omitted:** both primary and source have represented identity.
   Dictionary and selected witness hold. Thus even faithful local identity
   representation does not by itself identify two bearers. The model supplies
   no philosophical warrant for multiple real subsistent esse bearers.
3. **Selected witness omitted:** only source has represented identity. Dictionary
   and at-most-one hold. A unique relevant bearer need not be a previously
   designated p that lacks its qualifications.
4. **Positive full route:** only primary has represented identity and OwnBeing;
   both other beings participate; primary causes both. All selection inputs,
   source supply and coverage hold, and each other being is CREATURE_1.

These are exact formal non-implications and joint satisfiability checks. They
do not constitute objections to the metaphysical premises. No acyclicity,
transitivity, well-foundedness or modal necessity is assumed or inferred by
the new selection proof; equality substitution needs none of them.

### Comparison of the strongest existing support bundles

**De ente numerical unity.** a576300f is not an unexplained new "essential
sources are unique" flag. Existing argument
`07b1fac4-4769-4377-9d07-91ca8e0e2424`, theorem
`TruthCore.Results.Aquinas.DeEnte.EsseSource.atMostOneEsseIsEssenceFromPlurification`,
derives it from all seven premises: multiplication inventory
`2495a71d-81b6-47b7-8394-b37d3308fcda`, shared nature
`75b5b027-21f1-400a-8b21-775bb6d47983`, no added difference
`f13d1cdd-6b9f-4d05-9919-312587ad835a`, no matter
`38ed105c-6103-4969-8246-a6a071cdbb18`, reception only in own essence
`6dfe01ab-e3f2-5a4c-b102-701c161f2cf7`, receiver-to-act potency
`7fcfcee8-86ab-5a16-84ad-124cf5e8f9b2`, and no self-receptive potency
`14325c83-1c3f-5afb-b63f-52b0c2b2a326`. It uses shared nature to apply the
inventory, excludes reception with the potency premises, and excludes the
other two modes with the remaining inputs. Shared nature is not derived from
each bearer having its own identity. The existing two-source control isolates
that dependency; it is not independent evidence against shared nature.
Keeping a576300f as a direct prima facie commitment is also available.

**Q3/local participation.** The exact 4876dc46 + d3c6a6f7 chain above supplies
an actual external cause from cbb068e8 and 33ad148b, preserving the alternative
supports of the latter. It supplies neither OwnBeing at that cause nor a
common numerical source. Existing De ente stage (c),
`distinctEsseHasEsseIsEssenceSource`, instead uses the other-actual-cause
principle, no infinite actual esse-cause regress, and excluded middle to
reach an identity-bearing ancestor. Its `commonEsseIsEssenceSource` theorem
adds at-most-one, two actual beings, the other-cause principle and no-regress
to obtain one common uncaused identity source and finite causal chains to
all other actual beings. This is a genuine alternative support bundle,
not a failed q44 proof. It does not yet replace de05072a: ancestry does not
by itself supply the requested `CausesIn` edge or primitive OwnBeing. A
transitivity/application bridge and an own-being interpretation would be
needed for that use. We import neither silently, nor require a regress
argument merely to investigate the q44 principle directly.

**Fourth Way.** The exact 87dd8489 + a9cd32b6 + efb88bdf chain above already
produces the CREATURE bridge from a universal cause without the new own-being
dictionary. The universal-cause premise is secured there through all five
Fourth-Way inputs, including d9fad785. That conditional option is retained
with its warrant burden. It can explain why things caused by secondary causes
are also caused by a universal cause. It cannot be recounted as an independent
q44 argument establishing the universal causal principle that it already uses.
Conversely the new q44 bundle needs essential-source supply and numerical
unity but does not use grades or the genus principle. Neither bundle is
preferred merely because it has fewer open premises or a shorter route.

**IsGod uniqueness.** Q11's `godIsOneFromNature` still concerns `IsGod`.
No new result uses it, identifies GOD_4 with OwnBeing, or concludes 86d02b69.
The numerical unity route selected here is a576300f over actual identity
bearers, not an IsGod-to-essential-source substitution. Any later named
universal-cause conclusion must separately bind its GOD_4 witnesses to p.

### Warrant assessment, self-sweep and next tests

The own-being meaning gives conceptual motivation for the restricted identity
dictionary: if a source is its own subsistent act, the intended essence/esse
maps should represent that identity. Its open task is to justify that these
particular representations preserve real identity; it is not a demand for
an endlessly prior argument about the mere word "own". The finite mismatch
control cannot count against that motivation. A576300f has both its prima
facie reading and the seven-premise conditional support above. The unclosed
shared-nature application remains visible; no new substantive objection to
it is established here.

The strongest new substantive causal input is de05072a. The recorded q44
participation rationale motivates deriving received actuality from what has
it essentially. The q3 local conditional establishes only external causation
under its premises, so it cannot independently warrant that stronger source
character. Deriving an essentially-esse source by a no-regress route is one
available support option, whose property and abstraction premises remain
explicit. The present result therefore earns a new conditional common-source
application, not the truth of universal source supply, a historical dependency
certification, or defeat of the alternative frameworks.

Claim/type self-sweep: five new statements bind exactly the five new compound
predicates; three result types bind the exact listed bundles. Source supply
contains actual sourcehood, numerical nonidentity, primitive own-being and a
causal edge. The dictionary contains neither source existence nor uniqueness.
The selected witness contains neither own-being nor universal causation.
The selection conclusion is restricted to distinct actual own-being causes of
participants. The consumer is CREATURE_1 and retains participation coverage.
No premise, source assertion, modal conclusion or ontic requirement is hidden
in a definition. Existing frozen Challenges, sense aliases, status caches,
allowlists and shared imports remain untouched. No new source/claim/passage
records or source retrieval. This section and the existing attempt preserve
the full proposed outcome before challenge.

The scoped numerical-selection question is resolved conditionally. Next
materially different tests concern the substantive source-supply input:
(a) connect the existing common-ancestor result to the causal-responsibility
edge at esse under a defended composition principle, retaining its no-regress
burden, or (b) investigate the q44 participation-to-essential-source rationale
directly without importing Fourth-Way causation. Both require semantic work
on that particular causal input; repeating q3 external-cause search or IsGod
uniqueness cannot supply it. GOD_4 naming remains a separate downstream task.

### Validation and computed premise effects for the extension

The coordinator supplied independent copies of pinned packages and the warm
build into this existing checkout; toolchain/manifest/lakefile matched. New
module builds then ran through `worker_env.py --` under
`/tmp/moenarch/truth-core-heavy.lock`. This supersedes the earlier no-.lake
readiness report for the extension only. No checkout, service, cold build or
shared writable build links were created.

Focused Solution/Challenge builds pass. Comparator plus NanoDa accepted each of
015caba2, 3beb5720 and 7cdc011d with `permitted_axioms: []`. The controls use
constructive enumeration of three constructors, avoiding an incidental
propositional-extensionality dependency in the first development proof.
The final narrowed dictionary and selector cover distinct sources only, exactly
the source-supply instances used by the consumer. All three affected results
were verified on these final inputs. Scoped binding on the final module
reports **3 bound, 0 pinned, 0 mismatch**; its nonzero exit is the baseline
IsMaximalIn/IsMaximumIn sense alias, which the coordinator already retains and
will reconcile during integration. No alias allowlist was edited. Shared root
imports/status-cache refresh and delivered-head CI remain coordinator-owned.

`argument_batch.py records --check specs/q44-essential-source.toml` regenerates
unchanged. Offline `truth check` passes with existing warnings.
`attribution-check --base dab87151d054e6b1caff719dc0330c81e5c39033` reports no
new or changed stating claims. `git diff --check` passes. No historical witness
was fetched. Shared convention sourceRevision remains
`15f348b072188255da837578eaafc8a98f12fdf0`.

The actual computed `frontier-diff --base dab87151d054e6b1caff719dc0330c81e5c39033`
output, rather than a hand-reconstructed premise comparison:

```text
premise delta for Catholicism is true: the Catholic Church is a teaching authority founded by GOD_4, and every… [53964cbe]: dab87151d054e6b1caff719dc0330c81e5c39033 -> working tree
open premises reaching the root: 490 (349 bare, 90 supported, 51 stated) -> 494 (353 bare, 90 supported, 51 stated)
expanded-route diagnostic (lowest cost): Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16) -> Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16)
distinct verified support alternatives: 489 -> 490
verified support alternatives added: 1
  Everything other than the primary is CREATURE_1 [612078bf] <- Everything other than p has its being by participation [11e24b50], All relevant actual own-being causes are the selected p [dcf4bcdd], Each participant has a distinct actual own-being cause of esse [de05072a]
bare premises added: 4 (listed for visibility; not a regression, owner decision 2026-11-07)
  Relevant own-being sources respect the essence-esse identity dictionary [6acd44eb]
  All relevant actual own-being causes are the selected p [dcf4bcdd]
  Each participant has a distinct actual own-being cause of esse [de05072a]
  Selected p is actual with its represented esse identical to its essence [e2bfd1b1]
added (bare): 4
  Relevant own-being sources respect the essence-esse identity dictionary [6acd44eb]
  All relevant actual own-being causes are the selected p [dcf4bcdd]
  Each participant has a distinct actual own-being cause of esse [de05072a]
  Selected p is actual with its represented esse identical to its essence [e2bfd1b1]
```

The four listed items include the detector-classified selector conclusion;
its checked instantiation is not counted as a non-transcription discharge.
The one new support alternative is the substantive CREATURE_1 consumer.
Neither the additional open inputs nor the unchanged lowest-cost diagnostic
measures the philosophical value of that alternative. No source-supply,
identity-dictionary, unity or GOD_4 premise is declared established. Independent
semantic challenge of this expanded proposed outcome is still required.

### Independent essential-source challenge (2026-11-17)

GPT-6.1 Sol reviewed 6d33a24a2cbf7ec21de987b7efb825ca162d8049 against
dab87151d054e6b1caff719dc0330c81e5c39033 and found no substantive findings
in the complete 29-file outcome. It confirmed the restricted identity dictionary,
actuality and same-profile selection, exact CREATURE_1 consumer and finite controls.
The consumer supplies substantive conditional support without concealing universal
causation in the selector. GOD_4, own-being applicability and source supply remain
separate. Supplied binding and Comparator/NanoDa evidence was reused. Next work
tests common-ancestor/composition, including participant actuality, represented
identity-to-OwnBeing and alignment with p; transitivity alone is insufficient.
## Ancestor-to-source supply

Complete proposed outcome for independent challenge of the source-supply
assignment following acceptance of `6d33a24a2cbf7ec21de987b7efb825ca162d8049`.
Target remains `de05072a-5db0-4a31-8e24-b18fedf01401`, feeding the existing
CREATURE_1 parent `612078bf-5a68-5542-8b7b-f862f816ece0` and the root connection
already specified above. Formal home: `TruthCore/Causality/Q44SourceSupply.lean`,
`TruthCore/Results/Causality/Q44SourceSupply/`,
`specs/q44-source-supply.toml`. Analyst reconstruction; no new source attribution.

The selected ancestor route now supplies de05072a under seven explicit inputs.
It does **not** follow from transitivity alone. It also yields a selected-source
consumer that need not identify every possible own-being cause with p. The
direct participation rationale and the earlier stronger selection route remain
support options.

### Exactly what is reused

- `cbb068e8-337d-5772-a3f9-10df457ba9fe`,
  `TermSenseForks.ParticipatedHasDistinctEsse F`, supplies both participant
  actuality and represented esse/essence distinction in F.profile.
- `3d01134d-0b03-4469-a81a-a18d6e179fa0`,
  `DeEnte.EveryDistinctEsseHasEsseIsEssenceSource`, supplies each such actual
  distinct-esse bearer with an actual identity-bearing ancestor and a nonempty
  `Relation.TransGen (ActualEsseCause F.profile)` chain. The ancestor can vary
  with the participant. This is weaker than assuming a global common source.
- The existing common-source alternative is
  `c35b1a5c-6405-449b-993b-8196b2457e08`,
  `DeEnte.CommonEsseIsEssenceSource`: one actual identity bearer, no incoming
  actual esse cause, chains to every other actual bearer. Only its actuality,
  identity and paths are needed for source supply; its uncausedness is retained
  in the premise rather than advertised as newly derived.
- Four **separate existing premises** carry identity to OwnBeing:
  `6dfe01ab-e3f2-5a4c-b102-701c161f2cf7` (reception only in own essence),
  `7fcfcee8-86ab-5a16-84ad-124cf5e8f9b2` (a receiver is in receptive potency
  to the received esse), `14325c83-1c3f-5afb-b63f-52b0c2b2a326` (no principle
  is receptively potent to itself), and
  `bc1810e5-1070-5585-9b0f-e17ca3547ac7` (unreceived esse implies OwnBeing).
  Their exact definitions are `EsseReceivedOnlyInOwnEssence`,
  `ReceiverInPotencyToReceivedEsseReading`,
  `NothingInReceptivePotencyToItself` and `UnreceivedEsseIsOwnBeing`.
  This reuses the reception argument in `ReceptionLimitation.unlimitedIsOwnBeing`
  without importing unnecessary composition/priority predicates from its target.

All these fields come from the same profile/reception dictionaries. The frame's
`CausesOrigin` field is unused; no cause of coming-to-be is converted to a cause
of esse. `OwnBeing` remains the interpreted primitive discussed above. It is
not replaced by the equality of two maps.

### One new composition premise, not a replacement for the other inputs

New statement `b4987085-f7b0-4031-a795-364873d3c216`,
`ActualEsseCauseComposes f`, means:

```text
For any a,b,c: a is actual as to esse;
a is causally responsible for b's esse;
b is an actual distinct cause of the actual c's esse;
therefore a is causally responsible for c's esse.
```

Its last hypothesis is exactly `ActualEsseCause f b c`, retaining b≠c,
actuality of b and c, and the causal edge at this same `esse`. It propagates a
responsibility edge along an actual esse-cause link. It asserts no temporal
order, modal dependency, source existence, receptive identity, participant
classification, or source selection. In particular it is not a definition of
`CausesIn` as transitive closure. No theorem that some graph is well-founded,
or that an agent causes "as caused", supplies this property automatically.

The `causeOfChain` lemma proves the exact chain-to-edge passage by induction:
a one-link chain already contains the required edge; append one actual
esse-cause link and use composition with the actual initial ancestor. All
actuality and edge information remains explicit. An edge here is causal
responsibility, not a claim that secondary/intermediate causes are absent.
No acyclicity, well-foundedness or asymmetry is used in this induction.

### The identity-to-own-being argument

The separate `ownBeingOfIdentity` lemma does the following. If ancestor n's
esse were received in r, the reception/own-essence premise gives
r=essenceOf n. The potency premise gives Potency r (esseOf n). Since
esseOf n=essenceOf n, that would put one principle in receptive potency to
itself, contradicting the irreflexive-potency premise. Thus its esse is
received in no principle. The existing unreceived-to-own-being premise then
gives OwnBeing n.

This is a substantive explicit conditional argument, not an inverse of the
previous OwnBeing-to-profile dictionary 6acd44eb. It needs neither that
previous dictionary nor a stipulation that identity just means OwnBeing.
The four premises keep their existing scope and warrant burdens, including
the generalization of reception in one's own essence and the completeness
of the interpreted reception relation. No conjunction of these premises is
introduced as an opaque argument input. `Control.ReceptionInputs` only groups
those same four laws in closed finite test data; no registered argument uses
it as a premise.

### Complete new inference bundles

Here abbreviations denote the full IDs just listed and the existing
`a576300f-4b01-45ae-902c-cfe3d0fbf2de` (at most one actual identity bearer),
`e2bfd1b1-7d5e-4be3-b5d4-f9db988c5745` (selected actual identity witness),
and `11e24b50-06bc-5e2e-b9b6-a4e4dc421237` (all others participate).
The namespace prefix for the theorems is
`TruthCore.Results.Causality.Q44SourceSupply.`.

| Result / theorem | Complete joint premise set | Conclusion |
| --- | --- | --- |
| `9bbfe378-02bc-48cc-bc12-c90118707f52` / `sourceSupply` | cbb068e8, 3d01134d, b4987085, 6dfe01ab, 7fcfcee8, 14325c83, bc1810e5 | Existing de05072a |
| `d31e0887-decb-4c53-82ea-cf88bf2881b3` / `sourceSupplyFromCommon` | cbb068e8, c35b1a5c, b4987085, 6dfe01ab, 7fcfcee8, 14325c83, bc1810e5 | Existing de05072a |
| `b171d107-6ace-4547-b0b3-0b783d2f96c4` / `selectedSourceSupply` | cbb068e8, 3d01134d, b4987085, 6dfe01ab, 7fcfcee8, 14325c83, bc1810e5, a576300f, e2bfd1b1 | New `8b8bb6df-7b8a-4f08-bfe2-21d52fe9f217` |
| `ac416809-f937-4d0d-9546-1ceefb3c3009` / `othersAreCreatures` | 11e24b50, 8b8bb6df | Existing 612078bf at CREATURE_1 |
| `406fbe1a-1613-4af9-afcf-33cea6682eb2` / `controls` | none | Finite certificate `b4ae3ffa-2c19-41a1-bc29-35a768af174e` |

For de05072a, take a participant x. cbb068e8 supplies its actuality and
distinction; 3d01134d supplies an actual identity ancestor n and a chain.
The represented distinction excludes n=x. Composition gives CausesIn n x esse;
the reception argument gives OwnBeing n. Those are **all four** required
source-supply conjuncts: n≠x, source actuality, OwnBeing, and causing x's esse.
No globally selected source or uniqueness is needed for that existential
conclusion. The common-source sibling first obtains this weaker ancestry
interface from the existing common source and the participant's distinction.

To align with p, the selected actual identity witness and at-most-one give
n=p for each supplied ancestor. This does not identify n with p merely because
n exists, because both have a word in common, or because God is unique. New
8b8bb6df spells out that the **same p** is distinct, actual, OwnBeing and
causally responsible for each participant. The two-premise consumer then uses
coverage to make p a cause of every other actual being and each other thing
CREATURE_1. It does not require `RelevantEssentialSourcesSelected` dcf4bcdd,
which quantifies over every relevant own-being cause. Selecting one sufficient
witness per participant suffices. Both support options remain available.

If there are no participants, the source-supply conclusions are vacuous;
the per-participant ancestry route does not discover a source from an empty
participant class. The common-source premise itself already asserts one actual
source, and the selected-witness premise already qualifies p; those contents
are not exported as new existence discoveries. No GOD_4 binding, efficiency,
conservation or world-indexed ontic grounding is added.

### Seven discriminating controls

All controls use three named beings (primary, source, effect), an explicit
profile, received-esse and receptive-potency tables. Their common-ancestor
properties are proved with explicit one- or two-link `TransGen` witnesses,
not by equating ancestry with causal responsibility.

1. **Actuality omitted:** effect is classified as participating and has
   represented-distinct esse, but is not actual. Only primary and source are
   actual, with primary causing source. The common source covers every actual
   other being; composition and all four reception inputs hold, but no own-being
   cause supplies effect. This tests the missing actuality dictionary; it is
   not evidence that a genuine existent participant could be nonactual.
2. **Distinction omitted:** primary itself participates in the table and is
   actual, with identity-bearing esse and no incoming cause. Common ancestry,
   composition and the four reception inputs hold, but no distinct source
   causes primary. Thus participant actuality alone is insufficient. This is
   not a philosophical example of OwnBeing genuinely having participated esse.
3. **Composition omitted:** primary causes source, and source causes effect;
   primary does not cause effect in the table. All are actual, only primary
   has identity/OwnBeing, effect participates, and the common-source and all
   reception premises hold. The two-link chain exists, but de05072a fails.
4. **Own-being interpretation omitted:** use the star causal table, with the
   common ancestor and composition present, but assign OwnBeing to nothing.
   The first three reception laws hold and unreceived-to-OwnBeing fails.
   Source supply fails despite actual identity and the relevant causal edge.
   This diagnoses an interpretation bridge, not an objection to its truth.
5. **Selected qualification omitted:** with a unique actual identity source,
   designate the different source-labelled being as p. Every supply premise
   and at-most-one holds, but the selected identity witness and selected supply
   fail. The existential ancestor is not an arbitrary designated individual.
6. **Uniqueness omitted:** primary and source both have represented identity;
   primary is the common ancestor and causes effect, while source does not
   cause effect. Designate source as p. The selected witness and supply inputs
   hold, but at-most-one and selected supply fail. Identity qualification alone
   does not select the common causal ancestor. The assignments are not asserted
   to instantiate metaphysically possible multiple subsistent esse bearers.
7. **Positive composition:** primary→source→effect and primary→effect all hold.
   Only primary has identity/OwnBeing, both others participate, all reception
   and selection inputs hold, and each other being is CREATURE_1. Composition
   is exercised on an actual two-link chain; it is not merely vacuous.

The negative tables are formal non-implications under these exact predicates,
not independently justified objections to the metaphysical premises. No new
substantive objection to the interpreted composition or reception principles
has been established here. In the controls, assigning OwnBeing to identity
bearers is one chosen finite extension, never the general definition of
OwnBeing in either the theorems or the corpus.

### Support comparison and provisional warrant

The ancestry input is not an unexplained source-existence flag. Existing
argument `6503fc58-1be8-4596-9ccc-98e22a513e88`, theorem
`TruthCore.Results.Aquinas.DeEnte.EsseSource.distinctEsseHasEsseIsEssenceSource`,
derives 3d01134d from the joint bundle
`457698e4-eb21-4561-ab32-eccbfb0a992e` (each actual distinct esse has another
actual cause), `fd12ad3d-6729-4fa0-bb87-0121260df684` (no infinite actual
esse-cause regress), and `ee4ab504-c8fe-59bc-bc96-7cbeefed6410` (excluded
middle). The no-regress property's existing per-se alternative requires its
own per-se bridge; actual existence does not mean causing "as caused".
The shared/numerical source is not imported from local causes alone.

The stronger common-source input retains its five-premise bundle in argument
`5ab6cc2b-3997-4206-ab77-3b70e90f7867`: 3d01134d, a576300f, population
`33f3c4c5-ccd6-4e8e-9cfb-0b231bb0e38f`, fd12ad3d and ee4ab504. That
provides one common uncaused source, but its extra global content is unnecessary
for de05072a. The weaker per-participant source-supply result therefore keeps
that distinction visible without discarding the common-source option. Alignment
of the resulting ancestors with a selected p is the separate at-most-one step;
the existing seven-premise numerical-unity support bundle remains as recorded
in the preceding investigation, including its shared-nature input.

The participation-to-distinct-esse bridge has its ordinary conceptual motivation:
a participant has being, so is actual, and has it derivatively rather than
being its own act. Its application to these profile maps is still an explicit
bridge, not a consequence of an uninterpreted predicate's spelling. The
reception argument now exhibits exactly what a represented identity needs to
give OwnBeing. It does not require another argument for each primitive merely
because it is primitive; it preserves the existing meanings, prima facie
commitments, conditional support and revision conditions of those premises.

The new composition input is the remaining new causal commitment. Interpreting
`CausesIn` as mediated causal responsibility for esse gives a reason to consider
propagation through an actual cause of esse, especially on a derivative-agent
account. But the fact that a source supplies an agent's being does not by
itself define its responsibility for every causal exercise. This law explicitly
requires that propagation at esse; it is neither a proof from mere actuality
nor a transfer from counterfactual/intervention dependence. The earlier generic
causal-transitivity discussion and intervention controls concern their own
relations and are not evidence against this narrower application. No new
source passage states or independently establishes the law here. Accepting it
as a primitive or defeasible causal commitment is an available support option;
the finite chain omission is not a reason to reject it.

The direct q44 participation-to-essential-source rationale is retained alongside
this ancestry/composition/reception route. It can be investigated on its prima
facie explanatory merits; it need not be forced through a regress derivation.
Conversely the ancestor route adds a concrete conditional support option with
its exact separate obligations. Neither route borrows Fourth-Way universal
causation as independent support, nor is either judged by leaf-count economy.
The scoped source-supply application and its selection conditions are resolved
under the listed inputs. Warrant for composition, the reception application,
ancestry/no-regress, numerical unity and the selected witness remains revisable;
no premise is thereby independently established and no rival worldview defeated.

### Claim/type self-sweep

The theorem signatures list participant actuality/distinction, ancestor
existence, composition, all four reception premises and any selected-witness /
uniqueness inputs separately. No whole-premise wrapper hides one of them.
The new composition statement is one explicit conditional propagation law;
the new selected-source statement is an output with all four supply conjuncts.
The source-supply conclusion is the exact existing de05072a. The consumer
concludes existing 612078bf at CREATURE_1, not CREATURE_2. The controls prove
only their specified finite data properties. No original frozen Challenge,
other-family file, claim, source witness, allowlist, shared import or generated
status record is edited. No source retrieval, causal-mode conversion, necessary
existence, GOD_4 naming or completed primitive formal meaning is claimed.

Reopening tests are specific: investigate whether causal responsibility for
esse really propagates across the actual cause links used here; compare a
per-se-restricted propagation rule only with its explicit as-caused bridge;
or test the reception interpretation on a genuinely different account of esse.
Those are warrant/interpretation questions left after this completed conditional
application, not another search for the same missing local cause. Any challenge
to a premise must offer a supported failure mechanism rather than citing these
formal omission tables as evidence against its truth.

### Source-supply verification and computed premise comparison

All five new results pass focused Solution/Challenge builds, Comparator and
NanoDa with `permitted_axioms: []`; no classical or project axiom is introduced.
The scoped binding check reports **5 bound, 0 pinned, 0 mismatch**; its nonzero
exit is the already known IsMaximalIn/IsMaximumIn baseline sense alias. That
alias, shared imports, status caches and final integrated-head CI remain with
the coordinator. No original frozen Challenge is changed. The prepared worker
artifacts were used through `worker_env.py --` and the shared heavy-job lock;
no preflight repeat, cold build, checkout preparation or source download.

`argument_batch.py records --check specs/q44-source-supply.toml` regenerates
unchanged. Offline `truth check` passes with existing warnings;
`attribution-check --base 6d33a24a2cbf7ec21de987b7efb825ca162d8049` reports no
new or changed stating claim. The shared convention sourceRevision remains
`15f348b072188255da837578eaafc8a98f12fdf0`. Independent semantic challenge of
this full proposed outcome and final delivered-head CI remain pending.

Actual `frontier-diff --base 6d33a24a2cbf7ec21de987b7efb825ca162d8049` output:

```text
premise delta for Catholicism is true: the Catholic Church is a teaching authority founded by GOD_4, and every… [53964cbe]: 6d33a24a2cbf7ec21de987b7efb825ca162d8049 -> working tree
open premises reaching the root: 494 (353 bare, 90 supported, 51 stated) -> 494 (353 bare, 90 supported, 51 stated)
expanded-route diagnostic (lowest cost): Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16) -> Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16)
distinct verified support alternatives: 490 -> 494
verified support alternatives added: 4
  Everything other than the primary is CREATURE_1 [612078bf] <- Everything other than p has its being by participation [11e24b50], The selected p supplies a distinct actual own-being cause for every participant [8b8bb6df]
  The selected p supplies a distinct actual own-being cause for every participant [8b8bb6df] <- No principle stands in RECEPTIVE_POTENCY_1 to itself as to its own act [14325c83], Every actual distinct esse descends via actual causes of being from one whose esse is its essence [3d01134d], For every being x and principle r, if the esse of x is received in r, then r is the essence of x [6dfe01ab], For every being x and principle r: if the esse of x is received in r, then r stands in receptive… [7fcfcee8], At most one actual being has its esse identical with its essence [a576300f], Actual esse-cause responsibility composes along actual cause links [b4987085], For every being x, if the esse of x is received in no principle, then x is its own subsistent being [bc1810e5], Whatever has being by participation actually exists with esse distinct from its essence [cbb068e8], Selected p is actual with its represented esse identical to its essence [e2bfd1b1]
  Each participant has a distinct actual own-being cause of esse [de05072a] <- No principle stands in RECEPTIVE_POTENCY_1 to itself as to its own act [14325c83], Every actual distinct esse descends via actual causes of being from one whose esse is its essence [3d01134d], For every being x and principle r, if the esse of x is received in r, then r is the essence of x [6dfe01ab], For every being x and principle r: if the esse of x is received in r, then r stands in receptive… [7fcfcee8], Actual esse-cause responsibility composes along actual cause links [b4987085], For every being x, if the esse of x is received in no principle, then x is its own subsistent being [bc1810e5], Whatever has being by participation actually exists with esse distinct from its essence [cbb068e8]
  Each participant has a distinct actual own-being cause of esse [de05072a] <- No principle stands in RECEPTIVE_POTENCY_1 to itself as to its own act [14325c83], For every being x and principle r, if the esse of x is received in r, then r is the essence of x [6dfe01ab], For every being x and principle r: if the esse of x is received in r, then r stands in receptive… [7fcfcee8], Actual esse-cause responsibility composes along actual cause links [b4987085], For every being x, if the esse of x is received in no principle, then x is its own subsistent being [bc1810e5], One being whose esse is its essence is a first cause of being of every other actual being [c35b1a5c], Whatever has being by participation actually exists with esse distinct from its essence [cbb068e8]
bare premises added: 1 (listed for visibility; not a regression, owner decision 2026-11-07)
  Actual esse-cause responsibility composes along actual cause links [b4987085]
added (bare): 1
  Actual esse-cause responsibility composes along actual cause links [b4987085]
moved (bare -> closed): 1
  Each participant has a distinct actual own-being cause of esse [de05072a]
```

The computed move of de05072a from bare to closed/proved records conditional
formal support; it is **not establishment** of the stronger source-supply
principle or of the root. The four added alternatives are positive support
options with all their obligations visible. The new propagation law is an
open bare premise, retained alongside the direct participation rationale.
The unchanged root-reaching total and lowest-cost diagnostic do not measure
that philosophical progress. No semantic conclusion or premise count has
been substituted for this computed comparison.

Reproduce each result check with `python3 scripts/worker_env.py -- flock
/tmp/moenarch/truth-core-heavy.lock scripts/verify-result.sh <result-UUID>` for
the five result UUIDs in the table. `git diff --check` passes for this delta;
record generation, offline source/attribution validation and exact premise
comparison are as reported above. The current outcome is ready for independent
challenge; no push or publication action was taken by this worker.

### Independent source-supply challenge (2026-11-17)

GPT-6.1 Sol reviewed8593a7db85a73a43c8395a8687020b281e509b50 and the
complete32-file outcome with no findings. The same-profile actual cause links,
reception premises, actuality/nonidentity and selected-witness alignment remain
explicit. All seven controls match their stated bundles; no metaphysical defeat
is inferred. Four conditional support alternatives preserve direct participation
and primitive support options. The bounded connection is resolved under its
inputs, not established as true. Composition's general versus per-se scope is
the next semantic question. Further research was superseded by the owner's
retrieval-reliability assignment; committed evidence remains available.

## Current cluster assessment under the substantive objection standard (2026-11-18)

**Scope and boundary.** Issue #1751, slice 3, drafted on main
`95ed6125265252988b7a88ad14e42fed79e9d8ec` (PR #1754 merged). The coordinator
counted 11 `legacy_only` GOD_4-route premises whose attempts cite this note: the
open targets of legacy attempt [`74008d2a`](../../corpus/attempts/causal-perfection-transfer.json), which cites this note and
[causal-perfection-transfer.md](causal-perfection-transfer.md). At this baseline
all 11 are already `current` through slice 2's [`5c7bc356`](../../corpus/attempts/5c7bc356-a1dc-4781-8548-24ad1ce06f79.json). Slice 2 left two
things open. It deferred the source-selection detail of six of them
(`11e24b50`, `cbb068e8`, `b4987085`, `6acd44eb`, `e2bfd1b1`, `dcf4bcdd`) to this
note. It also stated that it supplies "no numerical unity (`a576300f`,
`75b5b027`)". This note's
[comparison section](#comparison-of-the-strongest-existing-support-bundles) names
four further open GOD_4-route inputs of that numerical unity and of the common
source. Their currentness state is `none`: the multiplication inventory
`2495a71d`, no added difference `f13d1cdd`, no matter `38ed105c` and the
population `33f3c4c5`. [Assessment record](../../corpus/attempts/1db2004a-5956-4c7e-994a-fd74c3b584a6.json)

The cluster is therefore the q44 participation route as this note fixes it:

- the selected inferential presentation;
- essential-source selection (`015caba2`, `3beb5720`);
- ancestor-to-source supply (`9bbfe378`, `d31e0887`, `b171d107`, `ac416809`);
- the numerical-unity and population inputs that selection and the common source
  consume.

The scoped assessment names the six deferred premises, the four new ones and the
route nodes `a576300f`, `de05072a` and `8b8bb6df`, which are not open leaves. The
other open inputs keep the assessments that actually assessed them, reused
unchanged: `75b5b027` under [`9f771edb`](../../corpus/attempts/9f771edb-fb20-4426-9ae2-82de322bbe5f.json) and the
[de ente source-selection judgment](de-ente-esse-source-1628.md#current-source-selection-judgment-identity-and-the-nature-being-multiplied-2026-11-17),
and `6dfe01ab`, `7fcfcee8`, `14325c83`, `bc1810e5` and `86d02b69` under
`5c7bc356`.

Earlier sections stay unchanged under their own dates. This section changes no
theorem, Challenge, claim, definition, closure or formal status.

### (a) Fixed meanings

These are the meanings fixed in the earlier sections of this note and in the
De ente note:

- **Profile.** There is one q.3 a.4 profile: `InAct`, `CausesIn` at `esse`,
  `essenceOf` and `esseOf` in one `Principle` sort. "Esse is its essence" is the
  represented identity `esseOf x = essenceOf x`. Reading it as real identity
  requires faithful maps. The restricted dictionary `6acd44eb` supplies only the
  forward direction, from `OwnBeing` to represented identity, at relevant
  sources; no converse is encoded. The converse reading, on which represented
  identity is "esse tantum" in the addition-excluding sense, exists only as reading
  choices inside claims `8bca93ec` and `e2319cd1`. No definition or
  disambiguation record fixes it (none exists; the definition `b7c083b2`, "merely
  existing", is unrelated), and it has no assessment.
- **Causing being.** `CausesIn c x esse` is causal responsibility for x's being.
  It is mode-unspecified and tenseless, and it is not a claim that no secondary
  causes intervene.
- **Own being and participation.** `OwnBeing` (definition `5dc08b95`) and
  `Participated` (PARTICIPATION_4, q.44's derivative esse) are interpreted
  primitives. Neither is defined as the negation of the other, and neither is a
  map equality.
- **Shared nature and the three modes.** `SharesNature` (definition `2a19c5e4`)
  is the primitive "one nature, so their being two would be a multiplication of
  it". It is not essence-value equality, common predication or x=y. The three
  modes of multiplication are `AddsDifference`, `InMatter` and the reception of
  esse. At identity bearers, where the nature is esse, "one absolute and another
  received" is the reception of esse.
- **Inferential dependence.** It is membership in one selected rule's complete
  premise set. It transfers no ontic, causal or well-foundedness property (see
  "Four dependence roles").
- **Selection.** `p` is a designated individual. `e2bfd1b1` qualifies it as
  actual with represented identity and does not assert `OwnBeing p`. GOD_4 is
  never identified with `p` or with an own-being source anywhere in this route.

Under these meanings the cluster has three conditional support bundles for the
CREATURE_1 parent `612078bf`. None of them is preferred by leaf count.

| Bundle | Complete inputs (expanded) | Status |
| --- | --- | --- |
| Legacy parent `38bef29c` | `11e24b50` with either the two direct middle premises `2b25a78c` and `b7d4eede`, or their expansions (`cbb068e8`, `33ad148b`, and the Fourth-Way chain `87dd8489`/`a9cd32b6`/`efb88bdf` with `d9fad785`) | The Fourth-Way branch is not q44 support and not independent warrant for the universal-cause principle it already uses. |
| Essential-source selection `3beb5720` | `11e24b50`, `de05072a`, and `dcf4bcdd` ← (`6acd44eb`, `a576300f`, `e2bfd1b1`) | The selector `015caba2` is a detector-classified transcription. |
| Ancestor and source supply `ac416809` | `11e24b50`, and `8b8bb6df` ← (`cbb068e8`, `3d01134d`, `b4987085`, reception four, `a576300f`, `e2bfd1b1`) | Selects one sufficient witness per participant and avoids `dcf4bcdd`. |

Numerical unity `a576300f` enters both of the last two bundles. It is closed
(proved) by the non-transcription result `860eae63` (argument `07b1fac4`). Its
seven jointly required inputs are:

- the inventory `2495a71d`;
- shared nature `75b5b027`;
- no added difference `f13d1cdd`;
- no matter `38ed105c`;
- the reception premises `6dfe01ab`, `7fcfcee8` and `14325c83`.

The existence of a selected witness enters through the common source `c35b1a5c`.
Its argument `5ab6cc2b` takes `3d01134d`, `a576300f`, the population `33f3c4c5`,
`fd12ad3d` and excluded middle `ee4ab504`. The CCR argument `3de4bd49` takes the
weaker population `78cffb8e` instead.

### (b) Strongest positive warrant, direct options and shared dependencies

| Premise | Strongest positive warrant | Direct option and dependencies | Provisional standing |
| --- | --- | --- | --- |
| `2495a71d` multiplication inventory | Stated claim `872032e9`, De ente c.3 [69874] (Baur/Koch; Leonine c.4). The passage says a thing is multiplied only by an added difference, by a form received in different matters, or by one instance being absolute and another received. Analyst's prima facie rationale: two instances of one nature must differ by something, either in the content (a differentia) or in what has the nature (matter, or a recipient). This rationale assumes what row 1 denies, so it does not discriminate against row 1. The encoding is restricted to pairs of identity bearers, as the passage applies it. | A candidate primitive of the multiplication account. The inventory's **exhaustiveness** is the passage's assertion and is not derived ([individuation audit](necessary-simple-plurality.md#what-the-primary-arguments-actually-supply)). No identity with the narrower bridge `PurelyDeterminedIndiscerniblesIdentical` is inferred. | Moderate as a sourced principle. Its exhaustiveness is contested (row 1 below), unchanged from the 2026-11-14 De ente judgment. |
| `f13d1cdd` no added difference | Stated claim `8bca93ec`, same anchor: esse alone that subsists does not receive an added difference, "since then it would not be esse alone but esse and some form besides". | Close to analytic once "esse tantum" is read as a quiddity that is wholly its esse. The claim records two reading choices. Applied at represented identity bearers, it depends on the converse reading that represented identity is esse tantum in the addition-excluding sense. That reading lives only in the reading choices of `8bca93ec` and `e2319cd1`. `6acd44eb` supplies only the forward direction and is not a dependency here. It does not exclude whole-nature differences that are not added constituents (De ente note, 2026-11-17). | Strong as a source-internal reading. Its application to these profile maps is an unassessed interpretive bridge, shared with `e2bfd1b1`'s significance. It carries no uniqueness load by itself. |
| `38ed105c` no matter | Stated claim `e2319cd1`, same anchor: "much less" matter, "since then it would be not subsistent but material esse". | Close to analytic under the same reading. Its subsistence clause is read as a consequence of identity (a reading choice recorded in the claim), which ties it to the reception package (`bc1810e5`, `5c7bc356`). Its application at represented identity bearers rests on the same converse reading choice, not on `6acd44eb`. | Strong as a source-internal reading. Its application to these profile maps is an unassessed interpretive bridge, shared with `e2bfd1b1`'s significance. |
| `33f3c4c5` at least two actual beings | Ordinary experience: perception of distinct things, and the inquirer together with what the inquirer considers. A commonsense datum. | A candidate primitive. Applying `InAct x esse` to ordinary existents is the profile's interpretation of actual existence. It strengthens `78cffb8e`, and the CCR route uses only that weaker version. | Strong prima facie. |
| `11e24b50` others participate | Unchanged from `5c7bc356`. Supporting claim `11b0106d` gives q.44 a.1 co. and ad 1. Identifying `p` with the essential-esse primary is the analyst's step. | Depends on unique unreceived esse (`a576300f`, `75b5b027`). | Moderate, conditional on that uniqueness. Unchanged. |
| `cbb068e8` participant has distinct esse | Unchanged: a participant has being derivatively, so it is actual and is not its own act. | Its application to the profile maps is an explicit bridge. | Strong prima facie under PARTICIPATION_4. Unchanged. |
| `b4987085` actual esse-cause composition | Unchanged: mediated responsibility for esse passes along actual esse-cause links, as in essentially ordered series. | A primitive or defeasible causal commitment; no source states it. Its general-versus-per-se scope is an open meaning question (next test). | Moderate. Unchanged. |
| `6acd44eb` identity dictionary | Unchanged: the meaning of own being motivates representing identity for the relevant sources. | A restricted application dictionary, forward direction only (`OwnBeing` to represented identity). It is not the converse reading that `f13d1cdd` and `38ed105c` need. | Moderate. Unchanged. |
| `e2bfd1b1` selected identity witness | Some such witness exists if the common source `c35b1a5c` does. The existential claim is derived by `5c904cf6` from `3d01134d` (← `457698e4`, `fd12ad3d`, `ee4ab504`), `a576300f`, `33f3c4c5`, `fd12ad3d` and `ee4ab504`; `e2bfd1b1` designates `p` as that being. | Shared dependencies: the numerical-unity inputs assessed here, plus `457698e4` and `fd12ad3d`, which are **not assessed here**. The De ente judgments of 2026-11-14 treat both as contested (causal coverage and the regress premise); the brute-esse and global-order rivals are unpaid, not refuted. The per accidens objection is a scope objection, which #1635 moved to the open bridge `e74de400`. | Conditional on that bundle. Not graded, because two of its inputs are unassessed here. This matches `5c7bc356`'s "not independently assessed". |
| `dcf4bcdd` selection of all relevant sources | Derived by the transcription-classified selector. | Not needed: `ac416809` via `8b8bb6df` suffices. | Formal residue only. Unchanged. |
| Neighbour `a576300f` at most one identity bearer | Derived from the seven inputs above. It is also stated in the source. A direct prima facie option is retained. | Its uniqueness load rests on the application of `75b5b027` and on the exhaustiveness of `2495a71d`. Both are live (rows 1 and 2). | Provisionally supported to the degree that those two are, which is the 2026-11-14 De ente wording. Not regraded. |
| Neighbour `de05072a` | Conditional results `9bbfe378` (argument `d8509a73`) and `d31e0887`. The direct q44 participation-to-essential-source rationale is retained. | Via `9bbfe378`: `cbb068e8`, `3d01134d`, `b4987085` and the reception four; it uses neither `a576300f` nor `e2bfd1b1`. Via `d31e0887`: `c35b1a5c` in place of `3d01134d`, so it uses `a576300f` only through `c35b1a5c`, and not `e2bfd1b1`. | Conditional. Not regraded. |
| Neighbour `8b8bb6df` | Conditional result `b171d107` (argument `12bc6bf0`). | The `9bbfe378` inputs plus `a576300f` and `e2bfd1b1`. Only this node consumes `e2bfd1b1`. | Conditional. Not regraded. |

Shared dependencies stay visible:

- The reception premises `6dfe01ab`, `7fcfcee8` and `14325c83` are shared by
  numerical unity, source supply, infinity and ascent. They are not independent
  corroboration of one another.
- The application of `f13d1cdd` and `38ed105c` at represented identity bearers
  depends on the converse reading choice of claims `8bca93ec` and `e2319cd1`:
  represented identity is esse tantum in the addition-excluding sense. This
  interpretive bridge is unassessed and also fixes what `e2bfd1b1`'s represented
  identity signifies. `6acd44eb` supplies only the forward direction and is not
  part of this dependency.
- `a576300f` is consumed by selection (`b8b21fb3`), selected supply (`12bc6bf0`),
  the common source (`5ab6cc2b`, `3de4bd49`) and the root-uniqueness routes. A
  defeat of it would reach all of them.
- `fd12ad3d` enters twice in `5ab6cc2b`: directly, and through `3d01134d`. It
  counts once.

### (c) Recorded objections and rivals, classified

| # | Record | Classification under the substantive standard |
| --- | --- | --- |
| 1 | Bare numerical difference with common nature: two identity bearers that share one nature and differ by no difference, matter or reception, only by primitive thisness. Source: the De ente note, 2026-11-17 ("challenges inventory `2495a71d`"), and the #320 pure-act thisness and narrower-bridge sections of [necessary-simple-plurality.md](necessary-simple-plurality.md#narrower-bridge-bare-difference-needs-a-non-pure-principle-2026-11-07). | **Kept** as a targeted, unresolved challenge to the exhaustiveness of `2495a71d` at identity-bearer pairs. *Mechanism:* numerical difference without any real differentiator. *Independent justification:* primitive numerical distinctness, motivated by the Adams/Black cases recorded in that note. *Relevant difference:* every such case comes with a non-pure frame (place, matter, a subject), and unreceived esse has none. Whether a frame is required for bare difference or merely present is a general question about numerical difference. The only test cases where the two answers diverge are the pure acts themselves, so no independent case settles it. This is not an established counterexample, and no independently supported bare-thisness case at addition-excluding unreceived esse is recorded. The earlier status, "exhaustiveness contested", is kept unchanged. |
| 2 | Distinct whole natures, and two first sources (#697), against `75b5b027` | **Restated**, unchanged from the De ente judgment of 2026-11-17. It is a targeted challenge to the step from qualitative determination to an added constituent or receiver, and an unfinished alternative ontology. Its proponent owes an intrinsic-determination account compatible with esse tantum; the defender owes a reason to exclude it. It does not target `f13d1cdd` or `38ed105c`: `f13d1cdd` excludes only an added differentia. It bears on this cluster only through `a576300f`. |
| 3 | Conceptual-to-real distinction challenge (Wippel lead, unread) | **Restated** as in the De ente note. It is accepted and avoided: the route draws the real distinction from stage (b), not from the intellectus-essentiae argument. That moves the burden to `75b5b027` and targets no premise of this cluster. |
| 4 | Omission controls: TwoSourcesControl `04212a3f`, the three essential-source omissions `7cdc011d` (`3b601644`) and the seven source-supply controls `406fbe1a` (`b4ae3ffa`) | **Restated.** Each shows that a premise is needed under one stated finite interpretation. None is evidence that two subsistent esse bearers, a nonactual participant or a failure of composition is possible. |
| 5 | Report of a historical q44 subsistence/unity chain | **Restated** as a semantic gap (2026-11-17 dependency audit, unchanged). The inspected bindings do not support the stronger historical-integration report. This is not an objection to any premise. |
| 6 | Substituting Q11 `godIsOneFromNature` (`841e7c81`) for numerical unity | **Boundary retained.** It is not an objection. Q11 uniqueness is God-indexed (`IsGod`). Using it here needs the pre-naming identification of the identity candidates with proper God instances, alignment of their essence representations, and a bridge from nature-value equality to `SharesNature`. The De ente Q11 reconciliation calls this overlapping warrant for different propositions, not independent corroboration. |
| 7 | Fourth-Way universal cause (`d9fad785` chain) | **Restated** as an alternative support bundle at matching scope for `612078bf`. It does not defeat the q44 bundles. It is not independent warrant for the universal-cause principle it already uses. |
| 8 | Generic causal-transitivity and intervention worries against `b4987085` | **No substantive objection identified**, as in `5c7bc356` row 10. Those controls concern other relations. Whether composition holds generally or only along per se links is a meaning question (next test). |

No objection is recorded, and **no substantive objection is identified**, for
`f13d1cdd`, `38ed105c`, `33f3c4c5`, `cbb068e8`, `6acd44eb`, `e2bfd1b1` and
`dcf4bcdd`. A denial of plurality such as existence monism is not recorded in the
corpus and is not introduced here. For `11e24b50`, rows 1 and 2 reach it only
through `a576300f` and `75b5b027`, as `5c7bc356` recorded ("a plural-source
objection targets `a576300f` and `75b5b027`"); no other objection to it is
identified. A remark that a supported reading generalizes
something a passage says only of God is an attribution boundary, not an
objection.

Tally:

- **kept**: 1 (row 1);
- **restated**: 5 (rows 2, 3, 4, 5 and 7);
- **boundary retained**: 1 (row 6);
- **no substantive objection identified**: row 8, plus the seven premises listed
  above;
- **dropped as evidence**: none, and no earlier weighting is changed.

### (d) Overall provisional judgment, revision conditions and next test

**Judgment.** On the meanings in (a), the q44 participation route is a coherent,
positively motivated conditional account. On it, everything other than a
selected `p` is CREATURE_1 with `p` as universal cause of being. The
source-supply bundle `ac416809` avoids the transcription selector. The route's
warrant concentrates in four places:

- participation coverage `11e24b50` (moderate);
- composition `b4987085` (moderate, with its scope open);
- the ancestry inputs of `3d01134d`, namely `457698e4` and `fd12ad3d` (not
  assessed here);
- numerical unity `a576300f`.

The newly assessed inputs of numerical unity split. The sourced exclusions
`f13d1cdd` and `38ed105c` are strong as source-internal readings. Their
application to these profile maps rests on an unassessed interpretive bridge,
the converse esse-tantum reading choice of claims `8bca93ec` and `e2319cd1`,
which also fixes what `e2bfd1b1` signifies. The
population `33f3c4c5` is strong prima facie. The uniqueness load rests on two
live points: the exhaustiveness of the inventory `2495a71d` (moderate, with the
kept bare-difference challenge) and the application of shared nature `75b5b027`
(a positively motivated primitive, unchanged).

The route names no GOD_4, supplies no efficiency, conservation or necessity, and
uses no God-indexed uniqueness. Nothing is established or defeated.

**Revision conditions.** Each of the following would revise this judgment:

- A general account of numerical difference showing that bare difference needs a
  non-pure frame would remove the row 1 challenge and strengthen `2495a71d`.
  Conversely, an independently supported case of frameless bare difference would
  weaken it.
- A positively warranted, intrinsically differentiated account of unreceived act
  would weaken `75b5b027`, and through it `a576300f`, `11e24b50` and selection.
- An assessment of `457698e4` and `fd12ad3d`, or of their per se replacements
  `ea251340` and `e74de400`, would allow `e2bfd1b1` and the common source to be
  graded.
- An assessment of the converse esse-tantum reading (represented identity is
  addition-excluding esse tantum), or a disambiguation record fixing it, would
  allow the application of `f13d1cdd` and `38ed105c` to be graded. A reading on
  which represented identity does not exclude added form would weaken that
  application.

**Next discriminating test.** Test the scope of composition `b4987085` against
the per se split that the De ente note already registered. The supply chains come
from `3d01134d`. Under the open bridge `e74de400` ("a caused actual cause of
being causes being as caused"), every link after the first starts from a caused
cause, so every such link is per se. The test: derive `b4987085` from a per
se-restricted composition law together with `e74de400`, or find the exact
obstacle. A success would rest composition on the essentially ordered paradigm.
Its warrant would then share `e74de400` with the regress route, a shared
dependency that is not independent evidence. A failure would locate the
general-scope commitment exactly. This is the question that the source-supply
challenge (2026-11-17) left next. It reuses existing vocabulary and is distinct
from the individuation question in row 1, which needs a general account of
numerical difference rather than another finite model.

**Formal residue, not new campaigns.**

- `dcf4bcdd` has only transcription support. The selected route avoids it.
- `5ab6cc2b` consumes the strong population `33f3c4c5` and records no
  `strong_version_needed`. The CCR route `3de4bd49` uses the weaker `78cffb8e`.
  Whether the weaker version suffices for `5ab6cc2b` is a strength-consumer
  question (#1598).
- The broad `6dfe01ab` is consumed by `07b1fac4` and the q44 supply lemma, as
  slice 2 already recorded (#1598).

**Declared revisions: none.** Each earlier judgment that this section touches is
compared below and kept:

- The dependency-audit judgment (2026-11-17), the essential-source judgment that
  `de05072a` is the strongest substantive causal input, and the source-supply
  judgment that composition is a revisable primitive option are unchanged.
- Slice 2's standings for the six deferred premises are unchanged. `e2bfd1b1`
  stays ungraded, as slice 2 left it, now with its dependencies listed.
- The De ente 2026-11-14 wording "exhaustiveness contested" and "provisionally
  supported to the degree that they are" for `a576300f`, and the 2026-11-17
  shared-nature judgment, are unchanged.
- The God-indexed Q11 boundary and the GOD_4 separation are retained.
- `2495a71d`, `f13d1cdd`, `38ed105c` and `33f3c4c5` had no earlier
  `current_assessment`. Their first grades are new judgments and revise nothing;
  the 2026-11-14 qualifier "exhaustiveness contested" is retained for
  `2495a71d`.

## When does the giver act through the agent?

The [production investigation, §10](actuality-esse-research.md#10-can-a-producer-withhold-being-from-the-very-actuality-it-produces) distinguished the producer's contribution to a particular effect's onset from giving esse as such. Suppose now that the disputed last edge *has* been supplied: b is an actual distinct cause of x's esse. Does the agent a which causes b's esse thereby act through b in giving x esse?

### A conditional answer to the binary composition test

Take one q3 profile and the existing binary `AsCaused b x`. Restrict composition to last links which satisfy both `ActualEsseCause b x` and `AsCaused b x`. The proposed binary law requires an actual distinct first link from a to b. It quantifies over **every** such giver. Alongside `e74de400` and the case distinction supplied by excluded middle, this recovers `b4987085`. If a is b, the final causal edge is already among the hypotheses. Otherwise a and b are distinct; a is actual by hypothesis and b is actual by the last link. Therefore a itself witnesses the existential input of `e74de400`. This gives `AsCaused b x`, which licenses the restricted rule.

Notice where the explanatory burden has moved. The two-place predicate tells us *that b causes x as caused*. It has no place to identify the agent in virtue of which b does so. The antecedent of `e74de400` can be witnessed by a; its consequent cannot be specialized to “through a.” Even interpreting it as “through some actual cause of b” leaves the question which one. The binary restricted law assigns responsibility to the very a in the first link whenever the last link is per se. It therefore retains a substantive every-giver commitment in cases with several givers. Its derivation isolates a support option sharing `e74de400` with the regress route. The argument does not reclassify an originating cause as an esse cause. [Actual cause and per se definitions](../../TruthCore/Latin/Aquinas/DeEnte/RootInterface.lean) · [Composition target](../../TruthCore/Causality/Q44SourceSupply.lean)

### Positive warrant for identifying the applier

In a working press, distinguish the supply keeping the apparatus available from the drive engaged with the loaded shaft. Trace what each actually does during the stroke. Torque transmitted across the clutch under load and into the moving ram bears on which drive is now acting through the press. Compare a second run after disengaging the charging motor: a charged store can still drive the ram. Its original charger explains the stored capacity without thereby supplying a present working input. A backup drive exposes a different error: cutting the active drive may leave a stroke available although that drive supplied work on the observed run. And cutting power to a shared interlock may stop the entire apparatus without making that power supply the source of torque. These are comparisons of intelligible mechanisms, not reports of a measured experiment. The evidential point is the combination of source, actual coupling, exercise under load and effect. Mere presence, the ability to intervene, and indispensability considered singly do not establish that attribution.

Energy transfer is only one way in which a named agent can contribute to execution. A live control signal that modulates a valve as flow occurs can be productive of the particular flow profile while supplying negligible motive power. The account should show how its actual signal enters the working loop. A controller that only preset a valve position can have a real historical role with no such current signal. The distinction concerns *which effect and which role* are claimed, not a requirement that every cause act contemporaneously. The existing `Lender` vocabulary allows an exercised group to be examined and the bearer of an actual contributor to be identified in the exercise frame. Bare borrowing quantifies over available lenders; a classification alone does not perform that identification. [Exercise model](../../TruthCore/Explanation/BorrowedExercise.lean)

Two replies to the every-giver problem deserve different answers. First, if an applier is known to be an actual esse giver of b and b has exactly one such giver, its identity with a follows locally. An applier might instead be a craftsman who did not give his instrument its existence. Uniqueness alone cannot supply the missing classification. Moreover, a can act **through** a distinct applier; numerical identity is sufficient in the former argument and unnecessary in the latter. Second, a primary agent might give and apply through one indivisible act. An inability to detach its preserving action from its applying action would be expected on that account. A literal switch test is consequently inappropriate. The positive burden is to explain why this source's action includes the *actual efficacy* of b in this realization. The ordered-agent account of q.105 a.5 meets that description within its theology. Simply designating a as universally responsible for bearers' existence does not establish that order.

**Does identity of the exercise with the patient's change help?** Consider the existing teaching/learning statement `bb123b16` as a test of this proposal. Its encoded content is shared underlying motion together with difference in account. There is a genuine saving if the producer's exercise and the patient's acquisition are two accounts of one concrete change: no second transition is required to transmit actuality from the first event to a separate event. But even if a giver accounts for the existence of that numerically one event, it takes a further step to say the giver acts *through the teacher as teaching*. The same reasoning must also respect the pupil's real contribution. Numerical identity permits substituting names of the event in an extensional statement about that event. It supplies neither an independently identified upstream agent nor a rule converting an event's existence into responsibility under an agent/patient description. The Lean reading takes two propositions as parameters; it does not construct or identify particular events, teachers, pupils, or causes. This is a limited structural comparison, with historical attribution confined to the existing record. [Teaching/learning statement](../../corpus/statements/teaching-learning-same-motion-different-account.json) · [Formal reading](../../TruthCore/Greek/Aristotle/Physics.lean)

**Provisional assessment.** Credit to a named upstream agent has positive warrant where its contribution to the particular operation can be traced through the secondary agent. This is compatible with real secondary efficacy, retained powers and more than one contributor. A binary per se classification alone leaves the named-source question undecided. The press supplies warrant within a productive efficient interpretation. The q3 profile itself leaves the mode of esse causation open, including the question of efficiency. Applying the instrumental reading to all its links requires further warrant. The example supplies no witness of two real metaphysical donors of esse and no refutation of `b4987085`. For `b26c10a0` there is an additional change of respect: even a correctly identified chain at esse needs a warrant for the giver's action in the effect's particular determination. Reopen the metaphysical inference on an account of the giver's role in **this** efficacy independent of classifying the bearer as received, or on an independently warranted restriction that identifies the actual applier with that giver in the target domain.

**Formal comparison.** `AppliedGiverComposes` attributes the final esse edge to a specified giver a when both actual links hold and `Through a b x` holds. The further premise `EachGiverApplies` assigns that ternary relation to every preceding actual giver of a binary per se link. Together they imply the binary composition law. This decomposition identifies a sufficient alignment commitment for explaining the final edge by a acting **through b**. A different contribution by a to x could also warrant a downstream edge. Neither binary nor unrestricted composition requires the indexed alignment as a necessary condition. The ternary predicate has person or bearer indices only. Applying it to repeated exercises by the same agents requires fixing the relevant episode in the interpretation, or enriching the interface to distinguish episodes. The theory neither quantifies over times nor identifies all actions of b toward x. Conversely, unrestricted composition already covers any actual distinct first link and any per se actual last link, by forgetting the extra conditions. This one-premise restriction records the strength order. Cycling through it back to unrestricted composition supplies no additional warrant. The direct composition premise remains available.

In the four-role control all four individuals are actual at the one respect, esse. The source and the supporter both cause the producer's esse, the producer causes the recipient's esse, and the supporter also causes the recipient's esse. Only the producer–recipient link is marked per se. In both rows the binary marker is **exactly** the projection of application by some actual incoming giver. When only the supporter applies the producer, indexed causal credit and `e74de400` both hold, but binary composition fails for the source. In the restoration row the source also applies the producer, **and** the model supplies the matching source–recipient edge. Both versions of composition then hold. A third comparison keeps the restored causal table and returns to the first application table. The binary and unrestricted laws still hold, indexed credit holds, and the every-giver application premise fails. A separate route for the source is one possible interpretation of its extra edge; the table stipulates the edge and does not identify such a route. The two-row restoration changes both facts together; it does not prove that changing one forces a metaphysical change in the other. Unit-valued essence and esse slots play no explanatory role. Source and supporter are role names. Neither the real existence of two such metaphysical givers nor an application at every perfection is certified. [Formal vocabulary and control](../../TruthCore/Causality/GiverIndexedApplication.lean) · [Composition proofs](../../TruthCore/Results/Causality/GiverIndexedApplication/Solution.lean)

The existing `sourceSupplyFromCommon` consumer can use the resulting `b4987085` on exactly the same profile with its other premises (see the bundle table above). This is an alternative derivation of an open input to that consumer. It leaves source selection, population, and transfer across respects as separate obligations.

**Independent challenge.** Review of `5b864f4dc5d0969592973b3e978d969e8dd40292` identified the distinct-route case and the difference between efficient application and the mode-unspecified q3 relation. Re-review accepted `020f500b690824419b56e38f98e6b598b2b8dfb0` with the third assignment and the constructive restriction projection. The computed comparison to `dee9abb04` adds one verified conditional support alternative for `b4987085`. Its dossier reports “proved; established: false”. The new inputs and the philosophical alignment question remain open. [Attempt and result references](../../corpus/attempts/4adbd36c-854c-408f-b72f-857f9922668a.json)

The [comparison of application, immediate concurrence and conservation](actuality-esse-research.md#11-does-the-giver-act-through-the-secondary-agent-in-this-effect) examines whether contributing to the same effect can justify credit even when the named source does not bring the secondary power into exercise.

### Can the effect alone locate the giver's contribution?

Fix the named giver, secondary producer and patient in one actual occasion. Two questions are at issue. Does the giver contribute to the patient's result? Does its contribution to that result enter **through this producer's exercise**? The second question matters to `d851dbc6`, which extends the attribution to *every* qualifying upstream giver. Its q3 type has no occasion parameter. Applying it to a particular exercise requires a reading under which the selected relation concerns that exercise; agreement about the bearers alone cannot pick a repeated occurrence.

**Test with the actual corpus meanings.** Give the proponent even unrestricted composition of actual esse causes (`b4987085`), the binary caused-cause bridge (`e74de400`), and credit whenever a named giver applies the intermediate (`6dd808ed`). These statements pass the sense preflight together. All three are true in the **same** four-role interpretation of [the control certificate](../../TruthCore/Results/Causality/GiverIndexedApplication/Solution.lean#L53). The source gives esse to the producer and the recipient. The supporter applies the producer in its per se production of the recipient. The source does not. The distinction survives even when the binary marker is exactly the projection of application by some actual upstream giver. It identifies an invalid inference at the declared meanings; which interpretation applies to a real existential giver remains open. The assignment uses `profile true` and `through false`.

On revision `ba741f5cd`, Duper ran with 10,000 heartbeats, one job and a batch size of one. Ranked discovery (`--premise-pool all --candidates 8`) retrieved all three exact-bundle members among its eight candidates. The exact run explicitly supplied `e74de400`, `6dd808ed`, `b4987085` in that order. Both ran one goal, returned unresolved and reported no setup errors. Both reports include name-based binder identifications. The independent Lean projection fixes the profile and relations explicitly and establishes non-entailment for the exact three premises. The search outcomes alone do not establish non-entailment for the ranked eight or for other candidate bundles.

**A test that grants selective input dependence.** In an instrumented press, distinguish the giver's working input `g` from the upkeep that keeps the press in existence. Let `p` represent the producer's local readiness, `s` its effective stroke and `y` the patient's mark. Two rival mechanisms give the mark exactly the same response to **every** combination of the two inputs. In one the selected input transmits force to the ram. In the other the ram strokes independently while a second contribution is needed at the patient, for example an independently powered backing plate required to receive the imprint. Keep the actual input, stroke and mark present in both. These are deliberately simplified productive mechanisms. The second represents independent execution at the producer with joint production at the patient; a source doing mere upkeep would have a different role again.

| Mechanism | Stroke | Patient's mark | Withhold working input, keep readiness | Hold stroke present while withholding working input |
| --- | --- | --- | --- | --- |
| Through the producer | `s = g ∧ p` | `y = s` | Stroke and mark cease | Mark occurs |
| At the patient alongside the producer | `s = p` | `y = g ∧ s` | Stroke persists, mark ceases | Mark ceases |

Thus, even selective loss of the mark and an actual observed stroke give the same answers before locating the path. Observing what happens **at the stroke** under selective withdrawal already distinguishes these mechanisms. If the stroke can instead be driven independently, the last column tests whether the mark still needs the giver's input when the stroke is supplied. Both tests assume the other working conditions and patient response can be held fixed. This reuses the [controlled direct effect distinction](causal-transitivity-1399.md) for the named-source question. It complements the [previous press cases](actuality-esse-research.md#11-does-the-giver-act-through-the-secondary-agent-in-this-effect) by giving the rivals the same entire endpoint response table. The finite equations are checked without axioms.

[Compiled endpoint, stroke and withdrawal comparisons](../../TruthCore/Causality/ExerciseEndpointControls.lean#L22).

**Provisional assessment.** Actual transmission traced from this giver into this producer's exercise is positive evidence of named application, even where other agents share the work. Credit at the endpoint and knowledge that the giver sustains both bearers leave its role in the producer unresolved. The controlled comparison establishes the limits of that evidence even after granting functional dependence of the endpoint on a selective working input. It gives no reason to posit a second action where the agent's operation and the patient's change are numerically one. In that reading the stroke/mark manipulation may be unavailable. The remaining test is to identify a source-specific contribution to the producer *as exercising its power*, for example a measured transmission at its working interface, or an independently warranted account of why receiving this power entails receiving its actual employment in this occasion from the same giver. Showing only that the producer received its nature or that the patient received the result would repeat the existing evidence. The restricted composition assembly `9f2abd14` retains its two explicit inputs. Extension to every respect under `b26c10a0` still requires coverage and an interpretation of each productive contribution in the target profile.

### Does the giver of the producer's native power supply its exercise on this occasion?

Grant the stronger starting point. The same giver *a* now sustains the producer *b* **with the very power it actually uses** on patient *x*. Keep fixed this occasion and the respect in which the power operates. This goes beyond sustaining a bearer that happens to possess a power. The earlier [power and existence control](../../TruthCore/Causality/PowerExistenceBoundary.lean) allows an externally conserved bearer to have unborrowed power. It does not give the conserver the active power itself as its productive terminus. The [conservationist argument](actuality-esse-research.md#does-a-complete-local-explanation-exclude-the-giver) already grants a positive form of mediated authorship of the very action to the giver of its operative power.

**The positive inference.** Specify what passes from giver to producer. When the giver's current activity produces or maintains the operative feature, and that feature's actual operation productively shapes this stroke, the giver can act through the producer in that respect. Another agent may supply the occasion, release or patient. The giver need not turn on and off, select the time or do all the work. This is especially strong when a change of the feature during operation changes the stroke in the predicted way and the transmission of that influence can be traced. Conversely the mere truth of “the power was present and was exercised” does not yet identify the giver's continuing activity as a constituent of its execution. A standing power denotes an ability even while idle; an actual process bearing or transmitting its influence can serve as a contributor in an exercised record. Introducing an event named *power* cannot supply this interpretation.

There is an exact conditional reading of this inference using the existing [productive-path interface](../../TruthCore/Causality/ExerciseContribution.lean). Take an occurring giver event, an occurring realization of the operative power, the producer's stroke and its particular result. Given exercised contributor steps linking them in that order, the actual named giver satisfies `ThroughAt`. The result allows mediated influence. It neither requires another feed into the stroke nor identifies a new activating event. The path proof requires an additional condition. The step from operative realization to stroke is a **productive contributor** premise, stronger than membership among the stroke's enabling conditions. Temporal coincidence with a present gift must be supplied in the interpretation. Applying the conclusion as the q3 `Through` further needs the episode and esse links used in `d851dbc6`.

**What if an operative power manifests whenever the trigger arrives?** Consider a producer with a variable response gain: how far its output moves for a standard release. In both mechanisms a named station maintains that very gain, including under load. A variable-ratio transmission whose linkage the station holds in position illustrates the maintained characteristic. Release is controlled elsewhere. In one arrangement the local system supplies the running work. In the other the same station also supplies the running work. A common station shutdown removes its gain-setting action and any running supply from it. These are mechanical analogues of distinct contributions to an operation. They do not identify a basic natural power with an acquired adjustable setting or equate productive agency with energy transfer.

In the compiled equations the gain is a nonnegative integer, `trigger` is the release, and `feed` means running work is available. The output is a normalized stroke magnitude; take an otherwise fixed patient that records it. With an intact local running supply, `feed = true`. With a running supply coupled to the station, `feed = giver`. For **every** giver state, trigger setting and gain, both arrangements have the same actual gain and stroke magnitude. Even measuring the producer as well as the patient while varying these inputs leaves that additional role undecided. Now keep the gain-setting action on, release the producer, and selectively isolate the station's running line. In the first arrangement the local supply remains; in the second there is no running supply. At positive gain the strokes diverge. The comparison requires independent access to the running line and continued operation of the gain setter under load. It identifies an additional motive contribution where those conditions hold. The station can already deserve productive credit for the profile in **both** arrangements. These equations are therefore not an omission model of `ThroughAt` or a counterexample to `EachGiverApplies`.

[Compiled coupled-feed and isolation tests, including the three-step productive path](../../TruthCore/Causality/ExerciseEndpointControls.lean#L40).

These three local checks use no axioms. The two equations give no independent evidence that a psychological or metaphysical power has distinct supply lines. They sharpen the appeal to a sufficient local nature. If the law “this power in these circumstances manifests” ranges only over ordinarily sustained operation, both arrangements satisfy it. If it ranges over an independently justified variation with the further working input withdrawn and the power and triggering conditions intact, a case that still manifests excludes **indispensability** of that input to that manifestation under the test. A second contribution could be redundant, or inseparable from the act of giving the operative principle. Neither the mere absence of a second switch nor identity of the giver's conserving act across its roles tells us which termini it has. An indivisible-act account can earn affirmative warrant by showing why the giver's activity realizes the very operation of this producer as well as its ability, under an independently supported account of that activity.

The act–potency argument supplies a further test on the producer itself. A power at rest does not account, by its mere possession, for its own transition to use. Grant that what makes the difference must already be actual in the relevant respect. This favors looking beyond the idle power. It does not yet identify the conserver: an actually approaching patient, contact, or the exercise of another local power can supply what was previously absent. The rival's explanation invokes the operative power *in that actual interaction*. The affirmative reply has force if the local factors explain only which response would be appropriate and the exercise of their efficacy itself has an identified dependence on this giver. It loses force if “only appropriate” assumes from the outset that no intrinsic power ever actually produces its manifestation. The proposal that some actualizer is needed and the claim that every antecedent giver is this actualizer have different witnesses. Actual contact need not be the sole sufficient cause, and in an atemporal order one cannot argue from a first instant of contact without a further interpretation.

**Two corpus connections test the witness.** Statement `495a40ad` says that giving being exercises a power of the *giver*. Even a successful identification of that giving leaves open which operation of the *recipient* proceeds from it. An exact 10,000-heartbeat Duper run from that statement to `d851dbc6` at `2ce9c294a` was unresolved. The reason for separating the claims is the difference in their subjects and termini, independently of proof search. In the q.105 a.5 [created-agent reading](../../TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/Question105/Article5.lean), `777646a5` says that a created agent that moves something is itself moved in some respect. Its conclusion `∃ r', MovedIn y r'` supplies neither a named mover nor the respect of this exercise. Moreover, sense preflight for these two premises together flags unbridged CAUSE_1/CAUSE_2. The conjunction is not a registered route.

**Provisional assessment.** Where a named giver actually supplies the exercised productive principle, the positive case favors mediated credit for this token in the respect that principle determines. Where the gift itself reaches the producer's exercise along an actual contributor path, it also meets the existing path reading of named application for that episode. No further motive feed is generally required for that conclusion. A stronger proposal attributes to the giver the very bringing-into-exercise of each power. The strongest local rival grants the power's present dependence and its role in the stroke, and explains its exercise by the intrinsically active producer engaging the patient in the appropriate conditions. The selective running-line comparison shows what additional fact can distinguish two accounts even after their accounts of the producer's measured response agree. Independent timing alone settles neither application nor its absence. For a basic natural power the outstanding test is whether a specific argument for its *present dependence* identifies the production of its employment, or only the basis for its characteristic response. Evidence for the former would strengthen strict application. A complete local realization under a demonstrated withdrawal of the proposed additional working contribution would weaken a claim that this contribution is indispensable. Neither conclusion propagates to every upstream esse giver (`d851dbc6`), nor does a native-power example cover every actual respect (`b26c10a0`).

## Can effective local supply continue throughout a borrower-only order?

The q44 claim `de05072a-5db0-4a31-8e24-b18fedf01401` asks for an actual cause of **each participant's own esse** which is distinct from the participant and has being of itself (`OwnBeing`). A concrete rival grants effective giving at every local link and takes the populated order as primitive. Granting the observed datum that at least one bearer exists is legitimate when asking how the other members are determined. When asking why any such order obtains, that same datum is part of the explanandum. “Generation” below means accounting for the obtaining of the activity in this respect, at the occasion in question. It presupposes no first moment or passage from a previously empty world.

### A stronger source-free rival under interventions

The earlier acyclic control lets every suffix of the natural numbers satisfy its state-indexed equation. Its reverse implication uses the recipient's actuality guard. An active supplier can therefore sit immediately above an inactive recipient even with the connection intact. A stronger rival posits an effective local disposition. With the requisite working conditions fixed, an intact connection delivers whenever its upstream supplier is active, and no other input activates the recipient. An ideal signal line provides a limited rationale for testing this hypothesis: opening a working contact can extinguish the downstream signal while leaving the sending side live. The signal, conductors and their power already exist in that analogy. It warrants the distinction between an operative transmission and a passive correlation. Extending the interpretation to the exercise that gives a bearer its esse remains a further claim. [State-indexed tail control](unique-feedback-explanation-311.md#state-indexed-actual-holism-what-global-selection-buys-1724-1616-2026-11-23) · [Existing power-transmission rule](../../TruthCore/Causality/EssentialPower.lean)

Index the receivers by natural numbers, with `x+1` the sole possible upstream supplier of `x`. An intervention chooses which connections remain intact. The law says that `x` is active exactly when its link is intact and `x+1` is active. The old power certificate already gives an all-on and an all-off solution and a possible response to any one cut. The further result classifies **all populated solutions for any choice of cuts**. A populated solution exists exactly when there is an index beyond which every link is intact. In that solution, `x` is active exactly when **every** link at or above `x` is intact. To see why, one active receiver forces active suppliers however far one goes upstream. Conversely, if all links above a proposed receiver are intact, follow that known active chain to a point above both receivers, then transmit back down the intact segment. This gives pointwise uniqueness given population without selecting a named stage, assuming maximality or adding a bearer at infinity. [Checked characterization, `classify` and `populationCriterion`](../../Scratch/q44-borrowed-supply/InterruptedTransmission.lean) · [Prior single-cut certificate](../../corpus/results/ESSENTIAL-POWER-UNDERDETERMINED.json)

| Intervention on the same rule | Predicted response | What it distinguishes |
| --- | --- | --- |
| Leave every connection intact and grant population. | Every stage is active, and each has a distinct active supplier. | Acyclicity does not itself force a stronger admission than population. Here effective delivery strengthens the **local law** used in the earlier guarded control. |
| Interrupt only the link into stage `k` and grant continued population. | Stages through `k` go inactive, and every stage above it stays active. | Every working link can make a difference to its own recipient. This response gives a source-free rival genuine local explanatory content under the stipulated intervention semantics. |
| Interrupt links arbitrarily far upstream of every stage. | Only the empty solution survives, even if the segment immediately above a chosen receiver is intact. | In this law an intact short segment has no supply of its own. In particular, with links into `k` and higher disabled, an independently active input at `k` would instead sustain `k` and every intact stage below it. |

The last comparison holds the lower links fixed and changes the explicit input term in the second rule. It does not discover such an input. All the cuts here are alternatives to a fixed arrangement, not interventions performed in temporal succession. Sufficiently distant individual cuts leave a populated upstream order but can extinguish any one fixed receiver. An unbounded set of cuts destroys the possibility of population in this chain. The rival therefore earns a specific prediction by supplying more than a compatible diagram. At every setting the empty state still obeys the purely transmitting law. A positive boundary “at infinity” can encode the populated solution, but no index denotes such a boundary bearer. If the rival treats the populated boundary as necessarily governing, it owes the necessity and concrete actuality of that condition. If it takes the actual pattern as primitive, its explanatory stopping point is explicit.

### What this buys for the existential source

For **local delivery**, the positive rival survives a stronger test than fitting observed endpoints. In an independently warranted application, interruption of this link with the upstream and working conditions maintained would distinguish its real work from a coincident pattern. The Lean helper `localGiver` supplies both actual-bearer guards on the existing `tailAtState` interpretation of `ActualEsseCause`. On the populated interpretation one can assign participation to the active nodes and `OwnBeing` to none. The q44 conclusion then fails (`noOwnAssignment`). The rejection follows from that explicit interpretation of `OwnBeing`. The calculation establishes the independence of that predicate from a transmission law and its local responses. It supplies neither a case of real source-free existential production nor evidence that a receiver's having esse in fact obeys the relay law.

For **why that delivery obtains**, the affirmative account has a positive asymmetry on the received-as-produced reading. A giver whose actuality in this respect is intrinsic can exercise its giving without borrowing that very actuality from an already active neighbour. Every relay contribution is conditional on an already active neighbour. Thus, if what is to be supplied includes the actuality in virtue of which any relay is giving, the source offers a candidate answer that the transfer law alone cannot supply. Its own burdens are to warrant this intrinsic mode of having being, actual exercise towards this recipient, and the connection to every relevant supplier cone. A primitive obtaining of the concrete order can also stop the explanation, and each operating member can explain its neighbour within that order. No failure of the rival's local predictions or contradiction in its primitive has been found. The cut comparison detects independence from the interrupted channel. Its surviving input could borrow all its actuality elsewhere. The **conditional preference** for a nonborrowed giver comes from the received-as-produced reading: if the order's productive exercise itself calls for a giver, intrinsic actuality actually exercised toward these recipients would answer that demand. The unrestricted existential preference still turns on whether receiving as such needs a giving origin in each complete cone. Making the local sufficiency rule stronger has reduced the rival's selection burden without answering that collective question. [Earlier comparison of sources, primitive wholes and groundedness](unique-feedback-explanation-311.md#c1-can-an-entirely-derivative-reality-account-for-its-own-actuality-1724-1616-2026-11-23)

The direct q44 premise remains an available commitment. The checked alternative first obtains an identity-bearing ancestor for each actual participant with esse distinct from essence. On the CCR route, `109e22e1` needs closed-supplier-cone rootedness `20babef7`, causal coverage of distinct esse `457698e4` and excluded middle `ee4ab504`. Then `9bbfe378` uses participant actuality and distinction `cbb068e8`, that ancestry `3d01134d`, composition of actual esse-cause responsibility `b4987085` and the four reception premises `6dfe01ab`, `7fcfcee8`, `14325c83`, `bc1810e5`. Those steps locate a distinct actual cause and justify `OwnBeing` for that same cause. A relay-independent input is only independent of the tested channel. Even an actual underived bearer elsewhere need not supply this recipient. Common source selection `dcf4bcdd` and participant population `f3e1d294` are additional inputs for the sole essential giver `eeb89ffe`. [Full ancestor bundle](#ancestor-to-source-supply) · [Principal-giver argument](../../corpus/arguments/1a4f8730-c6d9-4be8-9b4e-dcd5bd320433.json)

**Revision test.** For a particular esse recipient, identify the allegedly exhaustive supplying respect and independently justify either an intrinsic act giving in that respect, or a concrete law or whole whose obtaining suffices for these members to be actual. A source that continues to supply with the proposed borrowed input independently excluded would bear on that cone. A constitutive rival that accounts for the actual exercise as well as its propagation would reduce the source's explanatory advantage. Check whether its whole is itself an underived actual giver in the selected relation: in that case the remaining disagreement concerns its identity and scope. Further finite surveys of working links cannot turn either candidate into general supplier completeness.

The [Lean control](../../Scratch/q44-borrowed-supply/InterruptedTransmission.lean) reuses `PowerTransmissionRule`, `ActualEsseCause` and `ParticipatedHasEssentialSource`. It elaborates locally with `python3 scripts/worker_env.py -- lake env lean Scratch/q44-borrowed-supply/InterruptedTransmission.lean`. It is unregistered. This section contributes a scoped interpretation test and a proposed warrant assessment, with no formal premise change or new historical attribution.

## Can the organization of a whole explain why any supplier is active?

There is a stronger holistic answer than assuming a populated chain. A whole can impose relations among its parts that force *some* activity while leaving open which part is active. The question for `de05072a` is whether that sort of explanation reaches a participant's own being, and whether the whole then counts as its distinct actual giver.

### An organization that selects population

Consider a possible mechanism with three latches. Each is held at either of two stops, at signed displacements −1 and +1. At each of the three pairs, a linkage adds the two displacements and applies the sum to a spring about its neutral position. A spring with positive stiffness then exerts a restoring force whenever its ends' settings agree. These mechanical details give the word “loaded” an independent test. Disconnect the spring and the latches can retain their settings while the restoring force disappears. This is a design calculation for ideal bidirectional springs, with no claim of an experiment.

If all three springs were relaxed, each latch would have to be opposite to each of its neighbours. Following the three reversals around the triangle would bring the first latch back to its opposite setting. In fact exactly one or all three springs carry load. Any one can carry the sole load. Two loaded springs would already satisfy a mere population requirement, yet this arrangement excludes that outcome. Reverse one linkage to take the *difference* of its two settings and all three springs can be relaxed together. Thus the joint organization explains a contrast independently of naming an active spring. The formal calculation uses signed displacement alone. Its force interpretation requires actual intact springs of positive stiffness. [Checked parity and reversal](../../Scratch/q44-borrowed-supply/ConstrainedPopulation.lean)

To compare with the borrower-only rival, put one intact-or-interrupted chain under each contact, keep the effective transmission rule above, and require that the bottom stage be active exactly when its contact carries load. This last requirement is a separate interface assumption. It says how the two descriptions constrain the same state and gives the springs no role as extra inputs to the relay equation. With free latch settings, a joint assignment exists exactly when at least one chain has **every** link intact. A loaded contact requires activity at its bottom, which requires an intact link and an active supplier at every higher stage. Conversely, put the sole load over any fully intact chain, turn on all its stages and leave the other chains off. Cutting a link somewhere in each chain rules out the joint arrangement altogether. Holding all other conditions fixed after those cuts, sustained bottom activity would require a different supply rule, such as a working feed at that bottom. The cuts would locate an additional contribution relative to the interrupted channels. They could not tell whether the feed itself received its being. [Assembly criterion and actual-supplier interpretation](../../Scratch/q44-borrowed-supply/ConstrainedPopulation.lean)

### Where the explanation reaches esse

For the mechanical case a holist can explain both *that* some spring is loaded and *which* spring is loaded given the actual latch settings. The restoring force is the spring's own exercise under deformation. Its being an exercise of a part of this very assembly requires no additional producer external to the device. The structure constrains activity even when no individual latch fixes where the load falls. The device still presupposes the concrete springs, latches and linkages whose activity is explained. Those parts persist when unloaded. Reading the computed load as the *esse of a participant* therefore requires an argument that the given whole constitutes the bearer itself, in addition to determining one of its states. The Lean comparison lets the active stages of a loaded chain be participants and gives each an actual distinct neighbour in the existing q3 profile. Assigning `OwnBeing` to none of those stages is consistent with this rule. The carrier of that profile consists of stages only. It leaves open whether a whole outside that carrier supplies their being.

There is also a constitutive case in which a *concrete member itself* can be identified. Consider a metal casting with two lobes joined only by one narrow web. Count a piece as a maximal physically continuous portion of this metal. A groove that stops short of cutting the web leaves one piece. Cutting the last connection leaves two, with each piece identifiable by tracing continuous metal through its lobe. The difference makes each lobe a separate piece without adding metal to it. The cut has an efficient cause, and the casting has a material history. What the constitution explains is why *this separate piece* exists given the actual material and the separation. The explanation earns its existential wording from an independently applicable criterion of individuation. A further identification is needed to infer that the piece's entire act of being, as opposed to its being separately countable, is received from the organized whole. This gives a concrete test of that identification for proposed whole-to-bearer explanations.

Consider two ways the holist might identify a concrete whole. If “the whole” just names the roster of already existing members, the roster's existence presupposes theirs. Relational organization can still explain their pattern. If the whole instead has its own actuality and the members are differentiations of it, explaining how its determinate modes constitute *these bearers* can explain their existence without a second bearer producing them from outside the whole. Inclusion alone supplies no such account. For the mechanical example, independently setting the stops and measuring the predicted pattern and its reversal could warrant the device's actual operation. At existential scope an occurring act likewise gives a reason to affirm some concrete actuality. To identify that actuality as a mode of one comprehensive whole would take evidence that the conditions individuating this bearer require that whole. A law obeyed by every instance allows the question whether it has an instance. Even a reason why *some* concrete reality must obtain leaves open which reality must obtain. The holist can instead take this determinate whole's actuality as primitive and offer its internal explanation without further modal commitment. [Existing comparison of primitive and necessary concrete wholes](unique-feedback-explanation-311.md#state-indexed-actual-holism-what-global-selection-buys-1724-1616-2026-11-23)

For the same explanandum, the positive source argument starts from the distinction between having a received power and exercising it. If each stage's *own actuality to give* is received through the complete order, an intrinsically actual giver already exercising towards this participant supplies what receipt presupposes. Its positive advantage depends on warrant for that productive reading throughout the cone. Inferring the source solely from the need for some activity would lose that advantage, since the triangle can already select activity. Conversely the source premise alone predicts neither which recipient is actual nor the parity pattern. The concrete source account owes the particular direction of its exercise, just as the constitutive account owes the particular articulation of its whole.

**Overall provisional judgment.** Constitutive organization has positive explanatory warrant for population *within* an instantiated system. The direct source premise remains positively motivated where the participant's existence is itself received as a product. The contest over the existence of the whole order remains open on the mode-unspecified q3 meaning. The q44 target requires a cause numerically distinct from its recipient, with its own subsistent esse. A whole may include its recipient as a proper part and still be distinct. If the whole has its own subsistent esse and its constituting the member qualifies as causing that member's esse in the selected sense, the whole qualifies for this participant. The productive reading additionally requires actual giving in that respect. Grounding priority, basicness and holism alone supply neither classification. For the universal premise the account must reach each participant. The existing common-source conclusion also needs population and the same-giver selection premise. [Q44 target](../../TruthCore/Causality/Q44EssentialSource.lean) · [Principal giver argument](../../corpus/arguments/1a4f8730-c6d9-4be8-9b4e-dcd5bd320433.json)

**Reopening condition.** Hold fixed a particular participant whose actuality is independently warranted. Show either how an independently identified whole individuates and constitutes that bearer, or how a named giver contributes to that bearer's very existence with the secondary conditions specified. An independently justified reason that this very whole must be instantiated would strengthen the first explanation at total-order scope. Evidence for a productive gift applying across the complete cone would strengthen the second. Further constraints on the distribution of activities of already existing parts leave that question unchanged.

The unregistered Lean diagnostic elaborates with `python3 scripts/worker_env.py -- lake env lean Scratch/q44-borrowed-supply/ConstrainedPopulation.lean`. It adds no formal premise change or historical attribution.

## Research attempts citing this note

- [Constitutive population from a concrete organization and the q44 own-being giver](../../corpus/attempts/e37eaee1-2907-4523-9164-b1b21f67dd41.json)
- [Effective delivery through an interrupted borrower-only order and q44 source supply](../../corpus/attempts/0719304b-11a2-4b0b-851c-3b8d3371b5b6.json)
