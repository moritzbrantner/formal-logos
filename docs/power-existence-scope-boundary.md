# Power and existence: two omitted bridges (#319)

`POWER-EXISTENCE-SIMPLICITY-SCOPE-BOUNDARY` is an original, finite
countermodel result, not an interpretation of Aquinas, a positive argument for
God, or a proof of metaphysical possibility. Its role is to identify exactly
what the current finite power-grounding result does **not** prove.

## Two models

Both models have three distinct beings—source, instrumental effect, and a
conserver/component—and two universally accessible worlds. Every recorded
relation connects beings that exist in the relevant world. At the actual
world, an instrument receives causal power from an intrinsic source through
a finite `FinitelyGroundedPower` derivation. The theorem now requires the
actual `source → effect` transmission edge and asserts that the effect has
no independent intrinsic power in the model; the inductive constructor alone
would not have guaranteed either fact. The source receives no power from
another through the *same* transmission relation.

| Question | Model 1: contingent conserved source | Model 2: necessary composite source |
| --- | --- | --- |
| Finite instrumental power derivation | Yes | Yes |
| Original power at source in the selected respect | Yes | Yes |
| Source exists at every accessible world | **No** | Yes |
| Another existent directly supports source's esse | **Yes** | No relation recorded |
| Source has a numerically distinct proper component | No relation recorded | **Yes** |

The first model separates **original power** from **original existence**.
The second separates both modal necessity and the absence of an external
existence supporter from **simplicity**. Neither absence of a recorded support
relation nor de re necessity asserts the stronger Thomistic identity of
essence and esse. A `properPartOf` witness is only one kind of composition.

## Interpretive audit: what do *existence* and *power* mean?

These are distinguishable readings, **not equivalent definitions**. The
source-based Thomistic notions have their own corpus records; the model's
relations are analyst-defined proxies, not interpretations attributed to a
source without evidence.

| Phrase | Current model / scope | Distinct reading still to test |
| --- | --- | --- |
| "x exists" | `ontic.ExistsAt w x`: the candidate x actually occurs at w | Quantifier-based existence/instantiation; the metaphysical act of being (`DEF-ESSE`) |
| "x exists necessarily" | `NecessaryAt`: x exists at each accessible world, even though no reason is specified | Necessary **per se**, intrinsic intelligibility of its existence, or identity of essence and esse |
| "x has power" | `intrinsicPower w x`: a source-status predicate in a chosen power channel | A capacity or disposition that need not be exercised; an ability sustained by something else |
| "x exercises power" | `transmitsPower w x y`: an actual modeled link to y, with `Coherent` requiring that x causes y | Temporal production, continuous simultaneous instrumental efficacy, and act/potency as a metaphysical theory |
| "x's power is underived" | `UnborrowedPowerAt`: no incoming **same-channel** transmission to x | No enabling causes whatsoever; underived actuality of every power; underived being of x itself |
| "x receives existence" | `supportsEsse w y x`: one existing being supports another, as an uninterpreted model edge | Conservation of esse in ST I q.104; derivation of an existence-fact's sufficient reason; participation in esse |
| "x is simple" | `Composite`: x has a distinct proper part | Composition of matter/form, essence/esse, act/potency, substance/accident, or other constitutive principles |

### Important negative results of this audit

1. **Capacity is not exercise.** A being may have a disposition even when
   nothing is happening. The model now includes an actual transmission, but
   still says nothing about the capacity of a dormant being. Its selected
   respect is supplied by the relation itself; no universal quantification
   across respects occurs.
2. **Exercise is not existential independence.** An agent can be actively
   causing one effect while depending on another being for its own existence.
   The first model represents precisely that logical possibility; whether
   such a case is *metaphysically* possible depends on further principles.
3. **World-invariance is not intrinsic explanation.** Necessity as truth
   across possible worlds is distinct from why an existent is necessary.
   A PSR demanding explanatory adequacy must say what qualifies as an
   informative **intrinsic** reason rather than merely labeling existence
   "necessary" or constructing a circular explanation.
4. **No incoming supporter is not a proof of self-subsisting esse.** An
   absent model edge says less than an argued positive account of what
   makes the being exist. Likewise, lack of proper parts would not by itself
   eliminate all the broader kinds of composition.

The choice of metaphysics matters. A Thomistic account asks about the
actualization of potency and the distinction between essence and esse; a
dispositional-powers account can give causal capacity a primitive role; a
Humean account may decline to postulate necessary power-transmission at all;
an explanatory-PSR account can ask for a sufficient reason for a fact even
when no efficient cause of that fact is proposed. None is established or
refuted by these finite fixtures, and each needs its own non-circular
semantics and source-grounded argument.

For a next proof-bearing test, compare the *same actual exercise* under
these rival accounts while holding its bearer contingent and externally
supported. Identify the weakest metaphysical proposition that rules out
that interpretation; only then try to compose it with the established
necessary-per-se, simplicity, and uniqueness results. In particular, do
not insert the conclusion "the source's esse is underived" into the
definition of its causal power.

## What actually remains to be defended

1. **BR-POWER-TO-BEING:** Provide a justified metaphysical principle that
   excludes the first model. A candidate is that direct conservation of the
   bearer's being must transmit its very exercise of causal power *in the
   same relevant respect*. This principle is not already in the finite power
   model and could be rejected by rival accounts of causation. It must be
   sourced and tested without defining `supportsEsse = transmitsPower`.
   `originalPowerBlocksEsseSupportIfItTransmits` verifies the **conditional**
   consequence of that open bridge, with no purported proof of the bridge.
2. **BR-SIMPLICITY:** Even if a bearer exists necessarily and has no external
   conserver, establish why any internal composition requires an actuality
   or support external to it that contradicts ultimate independence. This
   is distinct from the assertion that the bearer has no proper parts.
3. **BR-NECESSITY:** A de re `NecessaryAt` predicate ranges over accessible
   worlds; it is not already "necessary per se", a self-explaining being, or
   an identity of essence and esse.

These are candidate premise investigations, not new theorems. Reuse
`TruthCore.Causality.FinitelyGroundedPower`,
`TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource`,
and the existing ST I q.3 and q.11 results. The present result does **not**
close #319 or the Catholicism frontier.

**Premise comparison:** no old premises discharged; zero new philosophical
premises admitted; one independently checked logical-independence statement
added. The metaphysical bridges remain open for source investigation.


## Integration reuse audit (2026-10-28)

The #319 integration inventory reuses the existing results rather than
recreating their omission models. This is an audit of encoded propositions,
not a new source reading or a new proof of any metaphysical premise.

| Existing result | Exact reusable consequence | Boundary for the integration |
| --- | --- | --- |
| `TruthCore.Results.Causality.PowerExistenceBoundary.originalPowerBlocksEsseSupportIfItTransmits` | Same-channel unborrowed power excludes external esse support if every support edge transmits that power | The support-to-transmission premise is still open; the existing `powerExistenceBoundary` already contains both requested omission models |
| `TruthCore.Results.Alternatives.RespectSwitch.consecutiveRespects` (#591) | Consecutive motion edges have distinct respects under its four local act/potency premises | It supplies neither a map from power to esse support nor existential independence in every respect |
| `TruthCore.Causality.NecessarilyUnderived.underived_of_lifting_and_excludedMiddle` (#495) | Given necessary existence, actual support well-foundedness, predecessor lifting and explicit excluded middle, some actual necessary individual has no incoming support from an existent at any admitted world | This conclusion says nothing about power origination, composition, explanation tokens, or identity with a different existential witness |
| `TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple.firstMoverSimple` | A first unmoved mover is simple under its first-being, component-priority, proper-component and composition-kind premises (and the no-body premise for its bodily conclusion) | It already derives simplicity; an integration must supply the first-being relation for this same mover rather than repeat the theorem |
| `TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple` | Maximality in being, a distinct uniting cause of every composite, and causal comparison exclude composition for a God witness | Neither #495 nor existence-PSR supplies maximality or the God identification |
| `TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSeIsMaximeEns.necessaryPerSeIsMaximeEns` | A necessary-per-se individual equals **each given** maximum in being under the genus-causality, has-being, cause-of-necessity and excluded-middle premises | Its conclusion is universal over a maximum; it does not produce one. `NecessaryAt` and the temporal `IsNecessaryPerSe` remain different predicates |

A precise candidate interface for the remaining **simplicity** connection is
visible without introducing a simplicity flag. Keep the existing
`CompositeHasAUnitingCauseReading Composite CausesIn esse` and the same
individual `x` furnished by `NecessarilyUnderived`. One would need to justify,
for that individual, that a distinct cause `c` of its being corresponds to a
`supportsEsse w c x` edge at some admitted world where `c` exists. The uniting
cause then contradicts the no-incoming-support conjunct. This is a proposed
relation between existing typed vocabularies, **not** a theorem or an admitted
premise in this audit. In particular, the uniting-cause reading alone does not
supply world-indexed presence of its witness. The generic `Ontic` type also
does not impose endpoint soundness on causal edges.

This interface differs from the existing maximum-based simplicity proof,
but it cannot honestly be treated as a discharge until that correspondence is
independently defended. Merely assigning `supportsEsse := CausesIn … esse`
would select a semantic profile, not prove metaphysical applicability.
`PowerExistenceBoundary.Composite` means a proper-part witness; the broader
`Composite` parameter of the q.3 reading is not identified with it here.

The **common-witness** gap also remains: the power theorem and the #495
theorem supply separate existential witnesses. Their sharing a `Being` type
would not establish equality. The PSR vocabulary relates `Reason` tokens to
`ExistenceFact`s and supplies no denotation map making a reason token an esse
supporter. A uniqueness theorem can transport properties only after both
witnesses satisfy the same independently specified domain and relations.

The strongest surviving rivals are the existing contingent conserved power
source, the necessary composite power source, and accounts in which a reason
for existence is not an external cause. They are not ruled out by a change of
labels. No new model or source claim was needed to retain these boundaries.

**Actual premise comparison:** zero statements, arguments, inferences or
results added; zero metaphysical premises added or discharged. Every root
open-premise set is unchanged. At the audited revision, the eight route costs
are 31, 32, 36, 38, 39, 39, 40 and 41 (the designated efficient-regress route is
40). #495 and the necessary-per-se convergence statement are not themselves
open leaves on these routes. The audit therefore supplies a reusable
interface and rejects duplicate work; it makes no root-closure claim.


## Same-support-source composition after #633

`TruthCore.Results.Causality.UnderivedCommonSource.named_support` now
connects `NamedNecessarilyUnderived m R w n` (#608) to source uniqueness
without identifying support with ordinary causation. The task module's
`actualSupportGraph m R w` reuses `Actual m w` and the existing `Graph`,
with edge `R w source target`. Named underivedness makes **this same n** an
actual source. The proof imports and applies
`TruthCore.Results.Causality.SourceForest.atMostOne_of_confluent` (#633).
It concludes that n is a source and every actual R-source at w equals n.
`exists_support` unpacks exactly `NecessarilyUnderived m R w` (#495),
retaining that witness's named necessity and no-support properties alongside
its unique selected-world R-source property.

The primary direct premise vector is:

- `STMT-NAMED-NECESSARILY-UNDERIVED` (or, for `exists_support`,
  `STMT-NECESSARILY-UNDERIVED`);
- `STMT-SOURCE-FOREST-WEAKLY-CONNECTED`, instantiated on
  `actualSupportGraph m R w`;
- `STMT-SOURCE-FOREST-UPSTREAM-CONFLUENT`, instantiated on that same graph.

This is useful proof assembly, not independent defense of any premise.
Named actual presence supplies population; it is not inferred from necessity
on a non-reflexive frame. There is no ordinary-world well-foundedness,
maximality, reciprocal potential causation or accessibility assumption.
Uniqueness is at this **one selected world** and on its actual-node support
carrier. No source at an inaccessible or different world is identified, and
no finite upstream path from every actual node to n is asserted.

The optional ordinary-causal corollaries `named` and `exists_common` instead
use `actualGraph m w`. Their direct vector has the same named/existential
underived premise, causal-graph connectivity and confluence, **plus**
`STMT-ACTUAL-CAUSE-SUPPORTS-ESSE`. That last interface is explicitly OPEN:
every ordinary causal edge whose source and target both exist at w gives an
R-support edge there. It is one-way, limited to actual endpoints at w, and
neither source-attributed nor a definition identifying R with Causes. It
converts the named underived witness into an ordinary-causal source before
the same imported uniqueness theorem applies. Nothing identifies either
source with the original instrumental-power source unless that witness is
separately proved to have the corresponding graph-source property.

The existing V-shaped `SourceForest.fork` remains the decisive rival to
connectivity alone: its two distinct roots share a dependent target, so it
is weakly connected and even well-founded while both roots are sources.
The imported confluence uniqueness theorem excludes that two-root profile
when confluence is added. This is a conditional graph constraint, not a
claim that the metaphysical support relation is confluent. The existing
source-free integer chain explains why graph uniqueness alone supplies no
source; here the underived witness, not a hidden WF premise, supplies one.

**Premise comparison:** the support route retains the existing named or
existential underived premise and adds the two explicit structural premises
to that conditional argument; the ordinary-causal alternative additionally
requires the open causal-to-support interface on its distinct graph. Zero
metaphysical premises are independently established or discharged. These
assembly results create no connection to God, simplicity or personhood, and
make no root-frontier change. Two end-to-end certificate records distinguish support from ordinary-causal
semantics; the named and existential-fiber lemmas are implementation helpers,
not additional corpus arguments or independent philosophical discoveries.


The advertised end-to-end results are `from_union` and `causal_from_union`.
Both **import and apply** the existing
`TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks`,
rather than adding its proved conclusion as a fresh ordinary premise. Their
exact retained five-premise vector is
`STMT-KANT-CONVERSION-NECESSARY-WITNESS`,
`STMT-ACTUAL-MODAL-REFLEXIVITY`,
`STMT-NO-CONTINGENT-GROUND-OF-NECESSARY`,
`STMT-WELL-FOUNDED-UNION-NECESSARY-SUPPORT`, and
`STMT-EXCLUDED-MIDDLE`. The primary support-graph route adds connectivity and
confluence (seven direct premises); the ordinary-causal route adds its
corresponding graph constraints and the open map (eight direct premises).
The necessary-support **union WF is retained**. Only ordinary-world causal WF
is absent. Neither configuration establishes its five original metaphysical
inputs or the structural extensions; root open premises remain unchanged.

## Shared interfaces for the four-area foundation investigation

The inventory below fixes the reuse boundaries for the owner's dependence,
composition, individuation and necessity investigation. It inspects existing
declarations and dossiers, not new primary-source evidence. It does not identify
an arbitrary mathematical interpretation with a metaphysically adequate account.

| Arena | Reuse | Interface still requiring justification |
| --- | --- | --- |
| World-relative existence and causation | `German.Kant.CosmologicalInference.Ontic` has independent `frame`, `ExistsAt` and world-local `Causes` fields. `NecessaryAt` quantifies over accessible worlds; `NecessaryBeing` additionally supplies an actual existent. | Actual presence does not follow from a non-reflexive box, and `ExistsAt` does not analyze Thomistic esse. There is no separate `Modal.Ontic` declaration. |
| Power and existential support | `PowerExistenceBoundary.Profile` separates `transmitsPower`, `supportsEsse`, `intrinsicPower` and `properPartOf`. Its `Coherent` conditions give endpoint presence and transmission/support-to-ordinary-cause inclusions. | Underived exercised power in the selected respect is not independence of the whole being. The inclusions have no converse. |
| Named underivedness | `NamedPotentialCauser.NamedNecessarilyUnderived m R w n` retains the same actual necessary n and excludes incoming R edges from existing sources at every admitted world. | The no-support quantifier is broader than root accessibility. It is not uniqueness, an intrinsic reason, or absence of a different causal relation. |
| Explanation | `ExistencePSR.Model` relates `Reason` tokens to `ExistenceFact`s while preserving the underlying `Ontic`. `Sound` supplies existence-factivity; `WorldwiseExplanation.StableExplanation` and `ReasonInvariant` are guarded by existence at the target world. | An `intrinsic` tag is not essence–esse identity or adequate intrinsic explanation. Stable explanatory assignment is not `BruteFoundationExplanations.NecessitatesExistenceAt`. Reason tokens are not automatically concrete causes. |
| Conservation | `DEF-PER-SE-ESSE-CONSERVATION` and `STMT-DIVINE-ESSE-CONSERVATION-CONTINUES-GIVING-ESSE` record the q.104 a.1 account; `DEF-CAUSE-OF-BECOMING` and `DEF-CAUSE-OF-ORIGIN` retain different roles. | This conservation record supplies no Lean conservation relation or theorem equating it with `supportsEsse`, `CausesIn`, production at successive instants, or a nonexistence counterfactual. |
| Composition and priority | `Article7.MatterFormAndEsseEssenceAreCompositionsReading`, `CompositePosteriorToComponentsReading` and `CompositeHasComponentOtherThanItselfReading` feed `FirstMoverSimple.firstMoverSimple`. | The implemented kind inclusions cover matter/form and distinct essence/esse. The primitive q.3 `Composite` remains broader than proper material parthood. Quantitative and genus–difference realization are not supplied by these inclusions. |
| Genus and difference | `MetaphysicsIII3` supplies strict `IsGenus`, `DifferentiaOf` and `SaidOf` readings; q.3 a.5 adds `InGenus : Being → Term → Prop`. | Conceptual predication does not itself give a real component, a potency/act principle, or an efficient cause. No generic classified-bearer structure is needed merely to put these parameters beside the q.3 a.4 profile. |
| Essence and efficient esse-causation | q.3 a.4 `Profile` represents `essenceOf` and `esseOf` in a common `Principle` sort. `distinctEsseExternalFromExhaustion` reuses two separately open causal premises. | This result is explicitly a transcription of the exhaustive dichotomy and its exclusion. Its efficient self-cause exclusion does not refute all intrinsic or noncausal reasons. The profile is not modal. |
| Individuation | `Q11NatureUniqueness.godIsOneFromNature` uses injectivity of `suppositumOf`, suppositum/nature identity, and one common nature; its three Bool omission controls remain the exact reusable controls. | Mere necessity, absence of represented components and equality of an individual's own essence and esse do not supply a common nature or injective individuation. The three separate controls do not already certify a joint two-necessary-simple-being model. |

Two minimal shared declarations make the direct connection explicit.
`TruthCore.Causality.ExistenceActuality.ExistingInActAt` retains its one-way
actuality role. Its exact type is
`∀ x, m.ExistsAt w x → InAct x esse`, with `m`, `InAct`, `esse` and `w`
supplied. This is the open `STMT-EXISTING-IN-ACT-AT` interface, not an axiom or
an asserted equivalence. It supplies target actuality for a q.3 a.4 application;
it does not supply the actual presence of a proposed cause, causal-to-support
correspondence, all-perfection actuality, necessary existence, or essence–esse
identity. `EXISTENCE-TO-ACT-IN-ESSE-INTERFACE` records the independent
interpretive obligation. Shared authorship is integrated with the consuming
necessity/actuality result rather than creating a second theory profile.


`ExistenceActuality.ActualEsseCausesSupportAt m R CausesIn esse w` is the
separate direct interface: from `m.ExistsAt w c`, `m.ExistsAt w x`, `c ≠ x`
and `CausesIn c x esse`, it gives `R w c x`. This is the open
`STMT-ACTUAL-ESSE-CAUSES-SUPPORT-AT`, not an identification of causes and support.
It does not mention `m.Causes`. In particular, ordinary event-causal edges need
not all be existence-support edges. Both endpoints' presence is an antecedent,
not a conclusion, and the act-in-esse interface remains independent.

The stronger pair of cause-in-esse-to-ordinary-cause correspondence and
`ActualCauseSupportsEsse` can supply this direct map by composition. The
ordinary route retains its original eleven-premise Challenge; a separately
frozen direct Challenge replaces that pair by the qualified direct interface.
No existing Challenge is weakened. The consuming investigation must demonstrate
its claimed strictness with an actual model and preserve the independent
cause-presence premise. A possible ordinary event cause that is not a cause of
esse is not ruled out merely by calling the bearer underived with respect to R.

The direct q.3 a.4 route can therefore be compared with the q.3 a.7 route
without silently identifying their premises. A named underived actual bearer,
target actuality, the source's distinct-esse external-cause conclusion, and
explicit cause-presence/correspondence interfaces can exclude distinct esse.
Constructively that yields a double negation of essence–esse equality;
positive equality requires an appropriate further logical principle. This
paragraph identifies the proposed consuming argument, not a newly certified
theorem in this inventory. The actual result must import the existing q.3 a.4
theorem and retain its open causal premises.

The live joint rival model uses two actual necessary roots with a common actual
dependent effect. Deriving represented simplicity through the existing
`firstMoverSimple` theorem is stronger than assigning a free `Simple` flag,
but a proper-component interpretation still does not cover all q.3 composition
kinds. A fork's common dependent target does not supply upstream confluence.
Equal represented perfections also do not establish numerical identity: the
Q11 common-nature/individuation or differentiation-in-act premises must be
stated and defended separately. This inventory approves no new metaphysical
possibility claim and does not certify the worker's forthcoming joint model.

**Premise comparison:** two analyst-defined interfaces are added as explicitly
unproved vocabulary items. No philosophical premise is endorsed, removed or
discharged; no new root route, source claim or consequence result is added by
this inventory. The existing root-path commitments remain open. In particular,
q.104 conservation's formal relation, genus–difference realization, the actual
cause mappings and the common-nature/individuation bridges remain live gaps.
## Same-witness noncomposition after #636

`NECESSARY-UNION-COMMON-NONCOMPOSITE` imports and applies the exact
`TruthCore.Results.Causality.UnderivedCommonSource.causal_from_union`
theorem. It retains that theorem's eight premises and its **same named
individual**, including necessary existence, absence of R-support and
unique actual causal sourcehood. Its additional conclusion is
`¬ Composite n` for the supplied q.3 predicate. It neither supplies a God
identification nor asserts the other classical attributes.

Three further direct premises do the work:

1. The existing `CompositeHasAUnitingCauseReading` gives a distinct
   `CausesIn c n esse` witness for a composite n.
2. `UnitingCausesPresent` says such a cause of an actually existing target
   itself exists at the selected world.
3. `UnitingCausesAreActual` says such a cause with actual endpoints gives
   an ordinary `m.Causes w c n` edge.

That incoming edge contradicts sourcehood of this same n. Both new interfaces
are explicit **open analyst commitments**, not attributed to Aquinas and not
asserted as identities between `CausesIn`, `m.Causes` and R. The proof does not
need the existing maximum-based route's maximality or causal-comparison
premises, nor the first-mover route's first-being premise. This compares
conditional routes; it does not defend one by counting its premises.
Necessary-support **union well-foundedness remains an input** through #636.
Connectivity and confluence are retained for its unique-source conclusion,
even though noncomposition alone requires only sourcehood.

The whole pinned article `AQUINAS-ST-I-Q3-A7` was materialized and read.
Its third proof says that a composite requires a cause uniting what is diverse
in itself, and that God has no cause as first efficient cause. The existing
claim already records reading that as a distinct cause of being. Neither the
passage nor the old Lean type supplies the modern `Ontic` world's endpoint
existence or the relation correspondence. Hence this connection creates no
new historical claim and provides no independent source defense of its two
interfaces. OCR defects elsewhere in the pinned transcription do not alter
the consulted third-proof clause; no source bytes were repinned.

`UNITING-CAUSE-INTERFACE-OMISSION-CONTROLS` separately witnesses both gaps:

- In `absentCause`, false is the only existing individual and is necessarily
  present, R-underived and the unique actual source. It is composite and has
  the alleged uniting cause true. The world-local causal edge is recorded,
  but true is absent. Presence fails; the actual-node graph has no incoming
  predecessor. This deliberately violates endpoint soundness: it tests the
  weaker encoded types, not a genuine cause by a nonexistent thing.
- In `differentCause`, both candidates exist and false causes true. False is
  again the same necessarily underived unique actual source and composite.
  The atemporal alleged uniting cause is true-to-false; this does not map to
  an actual causal edge. Presence holds and correspondence fails.

Both retain the existing q.3 uniting-cause reading. Their distinct cause need
not be outside the composite's parts: `c ≠ n` is numerical distinctness only.
No material-fusion, parthood or temporal claim is introduced. They establish
logical omission boundaries, not metaphysical possibility or a refutation
of actual composites. The original power-source countermodels remain the
stronger warning against transferring underivedness in one respect to whole
being without any interface.

**Actual premise comparison:** all eight #636 premises retained; the q.3
uniting-cause statement plus two open interfaces added to this conditional
connection. Zero open root premises independently defended or discharged;
no existing root argument rewired. Source correspondence, cause actuality,
the relation R's metaphysical applicability, and the original regress
premises remain open. The adjacent PSR audit in
[psr-scope-countermodels.md](psr-scope-countermodels.md) independently preserves
the distinction between an explanation and a necessitating reason; the
present causal connection does not discharge that explanatory bridge either.

## Five questions for direct existential support (#680, #686)

This audit concerns **R itself**, not the validity of the theorems parameterized
by R. It reuses `PresentEsseSupport`, `ActualNecessaryWellFounded`,
`PowerExistenceBoundary.Profile` and its existing boundary theorem; it does not
introduce another dependence relation. The actual-world theorem (#686) and
the union theorem used by #680 remain conditional consequences. Their intended
metaphysical interpretation has the following status.

### 1. What would R mean in ordinary reality?

The proposed reading is: **c is now actively responsible for b's existing at
all, as this very bearer, rather than merely for something b does or a state b
has.** The action is a cause of b's being, not only an earlier action making b
begin. “Now” selects the actual situation; it does not require repeated
creation, temporal succession in the giver, or instantaneous physical action.
This prospective concurrency is an interpretive requirement, not a consequence
of `ExistsAt w x`: Ontic has no time argument, and w may represent a complete
history. The existing `HistoryTimeScope` controls (#622) separate World and
Time; world-existence does not imply presence at a selected time or concurrent
activity. Any temporal application needs its own justified history/time and
causal interpretation. Worlds must not silently be treated as times.
“Direct” selects the esse-giving role itself, rather than every condition that
allows it to operate. This is an intended causal reading, not a completed
reductive analysis or an observation already established for every bearer.

For a positive application one must identify c and b independently, fix what
counts as the same bearer b, and explain the actual activity attributed to c
and why its effect is that bearer's existence. That last explanation must
exclude the weaker diagnosis that c changes a persisting bearer, maintains an
arrangement or removes a threat. Calling the activity “existence giving” does
not supply that explanation. R would be false on this reading where only
those weaker roles occur; a dispute over whether any giver is needed remains
a dispute over R's instantiation, not a reason to redefine the weaker role as R.
A claim that b would disappear without c can be evidence within an independently
specified causal account, but is not sufficient by itself: removal may destroy
b, remove a protector, or track a common cause. Mere covariance supplies no
direction or directness either.

There is an important gap between this interpretation and the exact code.
`PresentEsseSupport m R w c b` is only `m.ExistsAt w c ∧ R w c b`.
It does not establish the target's presence, distinctness, a causal mechanism,
or any of the ordinary-language conditions just described. The necessary-bearer
restrictions in the consuming arguments supply their own guards. A faithful
application must justify the relevant target presence and interpretation;
the wrapper's name cannot certify them. Self-support has not been excluded by
definition: the existing formal results exclude it when their WF premise holds.

### 2. What are clear examples, and which are only analogues?

No undisputed empirical example of **directly maintaining a substantial bearer's
existence as such** is supplied by the current corpus. This is a limitation of
the supplied examples, not a finding that R has no instances. Neither empirical
observability nor absence of philosophical disagreement is a requirement for
justification: a defended philosophical argument could establish an instance
or property despite dispute. The proposed central
instance, God continually giving creatures esse, is a substantive metaphysical
thesis whose defense cannot assume the conclusion of the regress argument.
The materialized `AQUINAS-ST-I-Q104-A1-EN`, response's paragraph beginning
“Now every creature may be compared” and reply 4, articulates that thesis through
participated being and continued esse-giving; it does not make it an independent
empirical observation. The article's complete objections and replies were reread
for this audit. The source's account and its truth retain separate statuses.

The following are useful **scope tests**, not new physical research claims or
verified R-instances. A powered lamp's illumination can illustrate a causal
exercise requiring an ongoing supply. The lamp's ceasing to shine does not
establish that the lamp ceases to exist. A maintained current or oscillation
can illustrate a continuing process; identifying b with that process changes
the target from its enduring material bearer. An arrangement maintained by
pressure, tension or control illustrates dependence of a structural state;
the continued existence of the materials is a different question. Life support
raises the more serious question whether an organism ceases to exist at death,
but neither that identity judgment nor the distinction between preventing
lethal corruption and directly giving esse follows from the phrase “life
support.” These cases need not be denied to prevent their being overread.

If processes or states are admitted as beings, some of these may become
candidates for a restricted R. One must then defend their identity criteria,
what maintains that very process or state, and its causal account. A theorem
about such bearers would concern that restricted domain. It cannot be exported
to every substance, or to the material subject that survives the process,
without a further argument. Naming light itself as b does not silently turn
an illumination example into conservation of the air's existence.

### 3. What is excluded, including near misses?

The q.104 a.1 response distinguishes preserving a child from fire, building a
house, and directly preserving being; objection 2 and reply 2 address persistence
after a maker ceases. Those distinctions prohibit an inference from “causal
condition for b” to “direct giver of b's esse.” A builder's completed production
is not already concurrent support; a guardian's prevention of corruption is
not already esse-giving. A prerequisite, fuel, permission or environmental
condition is not made direct merely because it is indispensable in a selected
scenario. A cause of movement, warmth or exercised power is not on that account
a cause of the bearer's being. The existing
`originalPowerBlocksEsseSupportIfItTransmits` states the conditional bridge
needed for one such transfer; it does not establish that bridge.

Nor are constitutive ground, efficient cause and adequate reason synonyms.
That the arrangement accounts for a house *as a house* leaves open whether the
arrangement is an agent, whether the parts are direct existential supporters,
and whether an additional uniting cause exists. A law or an explanation token
can explain a fact without being an existing individual actively conserving
its bearer. The existing PSR and q.3 vocabularies must retain their distinct
roles. Conversely, excluding those explanations from this **causal** R does
not refute them as accounts of persistence. It limits what the R-theorem answers.

### 4. Which structural properties have independent justification?

None of the following is independently established by choosing this meaning.
They must be defended for the same R, bearers and scope used in the theorem.

| Proposed property | Present status and exact burden |
| --- | --- |
| Actual endpoint presence | Intelligible for an actual causal application, but not supplied for b by `PresentEsseSupport`; the typed cause-presence and target-actuality interfaces remain separate. |
| Irreflexivity and asymmetry | OPEN. The thought that a recipient cannot confer its own existence needs an argument about causal priority in the same respect. Mutual dependence of activities or components does not settle whether reciprocal **esse**-giving is possible. Excluding efficient self-causation alone does not exclude a two-member cycle. WF implies these restrictions mathematically; that implication cannot defend WF. |
| Transitivity | OPEN, and potentially inappropriate for a **direct** relation. If c directly supports d and d directly supports b, c may be an indirect supporter of b without another direct edge. Closure under chains requires an independent account, or a separately stated indirect conclusion. Replacing R by its transitive closure changes the intended immediate/direct reading and must not happen silently. |
| Actual necessary-support WF (#686) | OPEN. Finite observed chains, local asymmetry and absence of known cycles do not rule out a beginningless upstream dependence series. The claim needs a reason why every such series must reach a nondependent source within this same existential sense. A theorem extracting a source from WF proves no such reason. |
| Union necessary-support WF (#680) | OPEN and stronger in scope. Even an independent defense at each world would not rule out a descending chain assembled from different worlds. The existing rotating-union controls already isolate that omission. A cross-world compatibility argument is required; an actual physical chain supplies none. |
| Necessity inheritance | OPEN. Actual support of a necessary bearer does not alone entail that this particular supporter exists at all accessible worlds. That requires the same supporter's indispensability across those alternatives, rather than interchangeable or optional support. The global no-contingent premise additionally quantifies over every admitted support world; the actual restriction does not. |

A defense must not build asymmetry or WF into the English definition and then
announce the needed premise as proved by that definition. Conversely, directness
is no license to assume transitivity. Independent arguments about causal
priority, essential dependence or infinite series may address these burdens,
but their applicability to existence as such remains part of what they must
show. Pure mathematical WF lemmas settle only their conditional consequences.

### 5. Why would the physical-to-existential abstraction survive?

The current evidence does **not** license that transfer. Abstraction is justified
when the discarded details do no work in the inference being preserved. In a
physical sustaining example, the relevant work can be done by an energy supply,
a dissipative process, a selected state variable or an identity criterion for
an organized system. Removing those details leaves no demonstrated reason that
a persisting bearer needs a concurrent giver of existence. A physical law that
settles when illumination stops does not by itself settle when the lamp,
material subject or substance ceases to be. This is a missing preservation
argument, not a technical inconvenience addressed by a more general graph.

A successful transfer needs (a) an independently supported account of why the
same bearer's existence is received or presently actualized rather than merely
its activity; (b) a reason that the causal dependence is on a present giver,
rather than adequately explained by prior existence plus no destructive change;
(c) a justified map to R and the supplied `CausesIn ... esse`, with their actual
endpoints; and (d) separate defenses of whichever order and modal restrictions
the chosen result consumes. A participation or essence–esse argument is a
candidate for (a), but only after its premises and causal exhaustiveness are
defended; merely applying that vocabulary to a lamp supplies no bridge.

The live replacement is the already inspected existential-inertia account:
prior existence together with no destructive causal change can explain
persistence without concurrent efficient sustenance. Its strongest form is
not “no explanation.” The Feser response recorded in
[eternity-dependence-connection.md](eternity-dependence-connection.md#existential-inertia-the-live-rival-and-the-remaining-bridge)
contests the sufficiency of that explanation through present actualization
and the alleged dependence of persistence powers on their substances. Those
are discriminating arguments, but their direction and actualization premises
remain disputed. No new source attribution or rival refutation is claimed here.

**Disposition and premise comparison:** retain R as a stipulated parameter for
the existing conditional results; withhold their use as actual metaphysical
evidence until the stated interpretation and property burdens are met. There
is no newly defended bridge, no source claim, no Lean type change and no
additional admitted premise. All root-route open-premise sets are unchanged
(delta zero). This audit narrows the proposed reading and identifies where
analogy stops; it neither discharges WF nor denies that a later independent
metaphysical argument could establish existential conservation.

## Same-respect self-actualization: reusable proof and application limit

On `research/lean-existential-self-actualization-20261031`, the two existing
First Way intermediate inferences are now separately exposed as
`SameRespectActualization.noSelfMotion` and `movedByAnother` under
`TruthCore.Results.Causality`. The source is the unchanged first-way reading
of ST I q.2 a.3 co.; the complete pinned `AQUINAS-ST-I-Q2-A3` passage was
materialized and reread. No new source claim or philosophical predicate is
introduced. The new result records consume the **existing** statement and
inference IDs rather than creating synonyms.

The four-line brief is:

- **Target:** make the same-respect no-self step reusable in an existential
  actualization investigation without strengthening its conclusion.
- **Reuse:** the existing three act/potency premise statements, mover-existence
  premise, no-self/moved-by-another statements and inference applications.
- **Missing step:** standalone Challenge/Solution/Comparator contracts and
  composition by both strong and relative First Way proofs.
- **Premise comparison:** identical end-theorem hypotheses and conclusions;
  no philosophical premise discharged. Existing end Challenges stay frozen.

The first theorem derives

```
∀ x r, MovedIn x r → ¬ MovesIn x x r
```

from `MovedOnlyAsInPotencyReading`, `MovesOnlyAsInActReading`, and
`NotActAndPotencyInSameRespectReading`. A self-mover that is being moved in
that respect would be both actual and potential there. The second theorem
adds the separately stated existence-of-a-mover law and derives

```
∀ x r, MovedIn x r → ∃ y, y ≠ x ∧ MovesIn y x r
```

The existential witness comes from the mover-existence premise; no-self only
makes that witness distinct. The two First Way Solutions import these results
instead of repeating both local derivations. The regress proof, its premises,
and the end theorem types are unchanged.

For an existential application, one may instantiate `r` with a supplied
`esse` respect **only after** justifying the interpretation of `MovedIn` and
`MovesIn` there. This theorem does not give `MovedIn x esse` from
`ExistsAt w x`, from `InAct x esse`, or from modal contingency. Nor does it
identify `MovesIn` with continuing existential support, a complete-history
explanation or a noncausal intrinsic reason. The existing actuality-as-being
law has direction from act in a respect to being; it supplies no reduction
premise in the reverse direction. The source's same-time/same-respect contrast
is represented at one implicit context, not a license to identify two times.

Three claims must remain distinct: a moved subject cannot be its own mover in
that same respect; an efficiently caused thing cannot efficiently originate
itself under the second-way priority premises; and a being cannot have any
intrinsic explanation of its existence. Only the first is concluded here.
The second has its own source/type and premises; the third is not supplied by
either the First Way intermediate or q.3 a.4's exclusion of efficient
self-origination. Different-respect activity and temporally separated feedback
are not refuted by dropping the qualifications from the first formula.

The standalone results are conditional consequences, not premise truth or a
proof of a necessary being. Existing act/potency omission controls remain the
authority for independence from their tested premises; no new omission model
or exhaustive metaphysical fork is claimed. This step improves composition
without silently treating a contingent bearer as an actualization event.

Verification: both new standalone results and the affected `AQUINAS-ST-I-Q2-A3-PRIMA-VIA`
and `AQUINAS-ST-I-Q2-A3-PRIMA-VIA-RELATIVE` results passed focused builds, exact
corpus type binding and Comparator/NanoDa with zero permitted axioms. The new
Challenge SHA256 is `3adfec801af9d4e6c63bca6d2b68cb7212af6c3e18d3f08d9c70f2105537cb25`.
Both original end Challenges are unchanged. Before/after route reports are
byte-identical, and open-root-premise membership is identical: 11 routes,
62 open premises (13 bare,49 sourced). No philosophical discharge is claimed.
Final delivered-head CI retains full-library and reverse-dependency coverage.


## Reality-correspondence follow-up: the positive illumination case (2026-10-31)

This bounded follow-up to #691 reread the materialized **PLATO-PHAEDO-99**
(full Stephanus99) and **AQUINAS-ST-I-Q104-A1-EN** (full article, objections,
response and replies). The Phaedo witness is the existing Perseus Greek edition,
`urn:cts:greekLit:tlg0059.tlg004.perseus-grc2`, repository
`PerseusDL/canonical-greekLit`, revision
`a065c359aab33c33bd17ddc2cac7d27fdc9cd870`, path
`data/tlg0059/tlg004/tlg0059.tlg004.perseus-grc2.xml`, Git blob
`d76020aa770f5a005e04a6ef0ae3ba60cf1faf86`. Q.104 uses the existing pinned
New Advent Dominican English1920 translation manifest
`corpus/passages/aquinas-summa-theologiae-q104-en.json`; no source bytes or
attributions were changed. For context only, the existing source fetch/hash
checker verified the full pinned Phaedo XML before extracting Stephanus98,
and the full Aristotle Metaphysics XML before extracting V.2. The latter is
`urn:cts:greekLit:tlg0086.tlg025.perseus-grc2`, same repository/revision, path
`data/tlg0086/tlg025/tlg0086.tlg025.perseus-grc2.xml`, blob
`4c03d2664d8acf43e49ce1b060d3e99f0e07c548`. These context ranges have no new
passage records or claims; they are not advertised as newly materialized IDs.

**Positive case and its exact object.** Q.104 a.1 co., the paragraph beginning
“Therefore as the becoming”, contrasts retained heat with the loss of light
when the illuminating action ceases. Reply4 again identifies conservation of
light with continued illumination. This supplies a concrete causal pattern:
an ongoing illuminating activity can account for the actual illumination of
a subject while that activity occurs. The target of that positive example is
the illumination, not the air's being at all. Its evidential force does not
require endorsing the article's ancient physical explanation of why air and
fire differ. Nor does it require claiming literally instantaneous disappearance
of light in modern physics: finite propagation, stored excitation and other
mediating processes require specifying the local effect and causal context.
The reliable scope is a causally sustained state/process under specified
conditions, rather than every light token or every substance universally.
The article itself distinguishes the material subject from its illumination;
reading its example as the sun giving the air bare existence would erase that
distinction before the subsequent metaphysical analogy is argued.

There are two honest applications. With air or lamp as b, illumination supports
only a state/power claim: b can persist without that exercise, so this example
does not establish R(c,b). With an independently individuated illumination
episode as b, continued causal production is a candidate for a restricted
process-domain application of R. It requires explaining which episode it is,
when that episode exists and which activity sustains it. This is positive
support for investigating that restricted instance, not an already verified
assignment of the current primitive R, and not a reason to replace the domain
of the necessary-bearer theorem with episodes silently. Such an episode's
being generated or contingent would in particular give no necessary bearer.

**Why the inference stops.** Phaedo99a–b distinguishes the genuine explanatory
cause from that without which it could not operate;98c–99a applies this to
Socrates's bones/sinews and his decision to remain. The source is addressing
rational action, not proving that bodily conditions are never efficient causes
or that all conditions are dispensable. Its relevant discrimination is narrow:
indispensability for an action does not by itself identify the explanatory
role for the question asked. Aristotle V.2,1013a24–1014a25, likewise distinguishes
material, formal, initiating and final causal roles; its ending contrasts an
actually operating builder with mere builder-capacity and explicitly permits
the house to survive the builder. Neither text licenses replacing these roles
with a single direct bare-existence edge. Q.104 a.1 co. itself separates removal
of corruption, becoming and direct dependence in being, and ad2 rejects the
builder comparison precisely because the builder is not the relevant cause
of being. Thus these sources positively support keeping the effect and causal
role fixed; they do not prove universal dependence on a concurrent giver.

**Weak constraint available now.** In an actual causal application of R, its
alleged recipient must actually exist in the selected situation: an absent
recipient is not actually being conserved there. This endpoint-admissibility
constraint is independently intelligible from the intended claim about an
actual effect, and is weaker than asymmetry, directness, transitivity, source
indispensability or foundation. It does not establish any R-instance and is
not a theorem of `PresentEsseSupport m R w c b := ExistsAt w c ∧ R w c b`;
that wrapper supplies only source presence. No code or premise record is
changed to hide the difference. If w is a complete history rather than a
moment, world-presence alone still supplies no temporal concurrence. This
constraint is a requirement on a faithful application, not a new account of
the source's metaphysical activity.

The strongest reply to the illumination limitation is Aquinas's own next
paragraph, beginning “Now every creature may be compared”: creaturely essence
is not its existence, whereas God is being through essence, so every creature
stands to God as illuminated air to the sun. That is a substantive proposed
bridge, not merely an illustration. To use it before establishing God, one
must independently defend received existence for the same bearer, the need
for its concurrent actualization, and the source identification without
assuming the regress conclusion. The existential-inertia rival can grant
ongoing production of illumination while maintaining that a substance persists
through its prior existence and absence of corruption. The reply needs to show
why this is insufficient for that substance; changing b to the illumination
episode answers a different question. Q.104 ad4 further excludes treating
conservation as successive new additions, so an argument from observable
changes alone does not settle its timeless esse-giving thesis.

**Actual delta:** no new claim, definition, relation, Lean theorem or admitted
philosophical premise. The positive finding is the defensible restricted
state/process pattern and the endpoint requirement for actual applications.
Bare-bearer conservation, actual existential WF, numerical unity and modal
inheritance remain open. Intended and actual root-premise change: zero.

## Actual prerequisite priority: positive scope for the first-being bridge (2026-10-31)

The new `NecessaryFirstBeing.necessaryFirst` retains actual population,
whole-roster nontrapping, contingent dependence, explicit excluded middle and
`STMT-SIMPLY-PRIOR-IS-ACTUAL-CONCRETE-GROUND`. Its pure-act continuation adds the
existing act-priority and same-respect non-simultaneity premises and imports
`FirstBeingNoPotency.firstBeingNoPotency`. The same necessary actual root is
preserved. There is no maximum/convergence or genus-causality premise. This
makes the semantic correspondence of priority the consequential remaining
interface, rather than another maxima-identity problem.

Re-materialized/read the complete pinned Latin `AQUINAS-ST-I-Q3-A1` and
`AQUINAS-ST-I-Q3-A7`, and re-materialized the previously read translation
`AQUINAS-ST-I-Q104-A1-EN`. Inspected the simply-prior bridge dossier and its
existing route attempts. These readings do not add source claims or change the
bridge's explicitly unattributed status.

### A positive restricted applicability argument

A **present ontic prerequisite of a bearer's actual being** must be actual in
the context in which it supplies that prerequisite. A merely absent candidate,
our concept of a constituent, or a proof that a constituent would suffice cannot
constitute the actual bearer. If distinct constituents genuinely constitute this
composite now, their actuality contributes to its being this actual composite;
the dependence remains even when nobody knows it. This direction is justified
by what changes when the constituents/constitutive arrangement fail: the same
composite is no longer constituted. The composite's existence may conversely
be evidence of its constituents, but that reverses epistemic inference, not the
constitutive dependence. This is independently intelligible restricted
applicability, not a definition of firstness as whatever the chosen root lacks.

Aquinas's q.3 a.7, corpus, second reason explicitly joins posteriority to
components with dependence on them. Q.104 a.1, corpus, makes the house's being
depend on the materials' natures and arrangement, while its becoming depends on
the builder's action. Together they motivate a real **current constitutive**
priority instance without requiring a presently acting builder. A persisting
house is thus a positive contrast between an actual prerequisite and a merely
historical producer. No conservation of the bare existence of every material
component has been inferred. A whole's organization also matters: selecting
one constituent as a partial prerequisite is not representing that constituent
as a complete sufficient reason for the whole.

For the proposed bridge, its three commitments can therefore be appraised
separately. **Presence:** a present ontic contributor must occur at the reading
world; an absent former builder is no counterexample to that restricted
contribution. **Concreteness:** an actual material constituent is a positive
example of the shared concrete-domain reading; an abstract form-description or
law is not automatically an individual in that domain. **Selected relation:**
if `grounds w` is independently specified as actual constitutive/existential
prerequisite dependence, the foregoing case is a reason for the corresponding
edge. If it is efficient production of bare esse, the case does not justify that
edge. A choice of the first interpretation is a coherent semantic profile with
an argument for this restricted application; it is not a proof that every simple
priority relation, or every source interpretation of `grounds`, has that meaning.

### What q.3 a.1 adds, and the exact remaining bridge

Q.3 a.1, corpus, second reason distinguishes temporal potency-before-act within
one changing thing from act's simple priority. Its reason invokes actualization
only by something in act. This supplies positive directed dependence for an
**actual reduction in the relevant respect**: the reduction is performed by an
actual agent in that respect, rather than by the patient's potentiality as such.
It does not identify the product with the patient's bare existence. Q.104's
being/becoming discrimination prevents silently performing that substitution.
The source's conclusion that every first being lacks all potency uses the
broader act-priority commitment already present in the corpus; it cannot serve
as its own independent justification by being cited a second time.

The strongest restricted application of the disputed bridge is therefore:
when `PriorSimply y x` identifies a distinct **current actual ontic prerequisite
of x's being**, rather than priority of explanation-to-us, an absent generator,
a comparative perfection, or only a possible actualizer, that prerequisite
belongs to the selected actual support relation at w. This has ordinary
constitutive instances and source-backed motivation. It gives a real research
standard for admitting an edge, not just a demand that the desired conclusion
hold. It is broader than ongoing efficient production and narrower than all
uses of priority. No transitivity or well-foundedness is inferred from it.

What remains for the five-/seven-premise route is **exhaustiveness of that
reading for the priorities the downstream proof uses**. In particular, if an
actual bearer has an unexercised potency, why must there be a distinct present
actual concrete prerequisite of that bearer's being, in the selected relation,
which is in act in the *same* respect? A presently unused capacity does not
by itself exhibit a current reducing act; its actual basis might be the bearer's
own constitution in another respect. Conversely, a demonstrated present reduction
shows the actualizer's contribution to that reduction without showing that the
whole bearer's existence depends on the actualizer. These are two specific
unpaid steps, not arguments that ordinary actualization is unreal.

One could restrict the relation to current actual reducers and obtain firstness
relative to those reducers. That yields absence of the corresponding actual
reduction at the root; it does not license the imported theorem's absence of
every potency. One could instead include every relevant constitutive priority in
`grounds`; then whole-roster nontrapping and contingent dependence must be
defended for that enriched relation. Neither move is a free consequence of the
old existential profile. Similarly, restricting the correspondence merely to
whatever threatens the selected root would restate the needed firstness instead
of defending its semantics. No replacement interface is admitted here.

**Premise comparison:** the positive current-constitutive reading supports some
actual instances and a principled presence requirement. It does not discharge
the universal `SimplyPriorIsActualConcreteGround` statement or the act-priority
application to every unexercised potency. All five original foundation/priority
premises and both pure-act premises remain. No relation, statement, theorem,
model or claim changes; no philosophical premise is added or established.

### Source-to-type clarification: act-priority is an attributed commitment

The preceding applicability audit must not be read as a finding that the existing
act-priority claim misquotes Aquinas, or that the new theorem silently needs an
extra premise saying every potency is currently being actualized. It does not.
The exact existing type is:

```lean
∀ x r, InPotency x r → ∃ y, InAct y r ∧ PriorSimply y x
```

It has neither `MovedIn x r` nor a time/world predicate. It does not directly say
that y is distinct, that y efficiently causes x's bare existence, or that x's
potency is currently being exercised. Distinctness follows only after the separate
same-respect non-simultaneity premise is applied. World-local actual concrete
presence and the selected grounding edge are supplied later by the open
`SimplyPriorIsActualConcreteGround` interface, not by this type. The
`necessaryFirstPureAct` proof lists the generic act-priority type itself as a
premise and faithfully uses its full force; it does not infer it from motion.

**What the source asserts.** In q.3 a.1, corpus, second proof, Aquinas explicitly
asserts act's simple priority, then applies it to exclude *any* potency in the
first being. His contrast with temporal priority in one changing thing and his
unqualified absence-of-potency conclusion support a generic priority commitment,
not merely a rule about those potencies that happen to be undergoing reduction.
Thus retaining broad priority as an attributed **commitment** is defensible. The
fact that its stated reason does not independently settle every case does not
make the attribution false. Weakening the attributed commitment to current
reducers would lose the use the same paragraph actually makes of it.

**What the respect-indexed type interprets.** The source does not literally write
quantifiers over every individual and every respect, or a separately indexed
same-respect predecessor relation in this sentence. The existing reading makes
that generic claim explicit using the repository's shared q.2 a.3 vocabulary,
where actuality and potency are compared in the same respect. It is therefore a
contextual formal reading, not a word-for-word transcription. Its strongest
support is the combination of act's generic priority, the source's no-potency-
in-any-way application, and the earlier same-respect actualization explanation.
No additional quantifier over times or accessible worlds is licensed. Nor does
`InAct y r` here require that the cause possess a perfection in exactly the
univocal/formal way as the effect: `DEF-ACT`/`DISAMB-IN-ACT` explicitly leave
formal versus virtual actuality open. An actual use must settle that reading
consistently with non-simultaneity. These are interpretation and application
questions; no definite quantifier reversal or source-scope bug was found.

**What the source argues for.** The actualization reason is positive: potency
considered merely as unactualized capacity cannot be the actuality that brings
it to fulfillment; an actual reduction therefore requires actuality. This
explains the direction rather than simply naming the actualizer “prior.” It
motivates the broader idea that derivative/limited capacity presupposes an
actual basis rather than manufacturing that basis by remaining possible.
It does not, without a further account of potency and its actual basis, establish
the exact existential predecessor theorem for every dormant respect. The
existing `ActPriorFromMotion` investigation already certifies this limited
motion-to-priority consequence and its boundary; this audit adds no new model.
There is no need to demand that every dormant capacity be undergoing change.
The philosophical question is whether the generic ontic priority can be defended
without that demand, and whether its witness is the kind of **present bearer-
existence prerequisite** to which the selected grounding norm applies.

This corrects the potential overreading of the preceding phrase “dormant potency
to distinct present same-respect actualizer.” For the delivered conditional,
the act-priority premise plus non-simultaneity already supplies a distinct
same-respect prior **being in act**. An exercising actualizer is not an additional
necessary hypothesis. What is still unpaid independently is warrant for that
broad reading in reality, followed by the new relation/presence correspondence;
those are different burdens. Q.3 a.7's component dependence can support a
restricted actual-basis instance without proving that every such prior being is
an efficient producer of bare esse.

A genuinely different, narrower reading is the existing
`ActPriorToActualizedPotencyReading`, already recorded separately. It is a faithful
formalization of the force of the **reason about reductions** alone, and it does
not replace the broader commitment Aquinas asserts and uses. No new sibling
claim is needed merely to repeat that distinction. Exact premise comparison:
all five foundation/priority premises and the two pure-act premises are retained;
no hidden current-actualization premise is added, no source commitment is
withdrawn, and no independent truth/application premise is discharged.

### Reuse finding: actual entity to esse, without a global modal promise

The corpus already has the exact one-way interface needed to express actual
entity-to-esse applicability: `STMT-EXISTING-IN-ACT-AT`, defined by
`ExistenceActuality.ExistingInActAt m InAct esse w` as
`∀ x, m.ExistsAt w x → InAct x esse`. Existing direct underived-essence proofs
consume it. `NecessaryConcreteRouteBridge.ActualConcretaHaveBeing` is the same
consequent restricted by concreteness; it is already available as vocabulary,
not a newly established premise. Neither declaration identifies the predicates
by definition or supplies a converse. No new statement/profile is needed.

Re-materialized/read the full pinned Latin q.3 a.4, q.4 a.1 and q.4 a.2;
inspected `DEF-ESSE`, `DEF-ACT`, `DEF-BEING-AS-ENTITY` and the existing
existence-to-esse dossier/attempts. The positive semantic case is modest but
real: if x is an actual entity, rather than an uninstantiated nature, merely
possible candidate or truth-bearing sentence, x **has being**. In the intended
Thomistic reading `esse` names that being-actual of x, not another empirical
quality arbitrarily assigned to the candidate. An actual horse has its being;
thinking of a possible horse does not bestow being on that horse. The interface
therefore need not posit an efficient conserver, necessary status, or a new
mechanism to make the semantic application intelligible.

Q.3 a.4, corpus, second reason supports this role by treating esse as actuality
of form/nature; q.4 a.1 ad 3 makes even forms actual insofar as they are, and
q.4 a.2 corpus says perfections belong to perfection of being. These are positive
reasons for using the same sense of actual entity/being rather than independent
arbitrary tables. But q.3 a.4 ad 2 expressly distinguishes actus essendi from
propositional composition/truth. Merely proving the sentence `ExistsAt w x`,
assigning a true flag to a candidate, or interpreting it as a true negative
proposition does not settle that it represents a real entity with esse. The
interface is source-shaped semantic correspondence under that real-entity
interpretation, not a theorem about every uninterpreted `Ontic` structure.
It asserts no essence/esse identity: participated and unparticipated being
both satisfy its having-esse consequent on the intended reading. Nor does
having esse imply every perfection; q.4 a.2 ad 3 distinguishes an entity merely
having being from living or wise being.

The existing `NecessaryBeingHasBeing` differs in **scope and origin**. It is an
open bridge introduced for the tertia-via modal vocabulary, not a deliberate
claim that contingent beings lack esse. Its antecedent is `IsNecessary`, read
as inability possibly not to be; on the arbitrary supplied frame that alone
does not yield presence at the selected world. It may hold vacuously where
there are no accessible alternatives. Thus `ExistingInActAt` cannot simply
prove the universal `NecessaryBeingHasBeing` without further presence/frame
conditions. Concreteness alone does not repair this modal issue.

For the actual root in the delivered route, however, `ActualRoot m w n` already
supplies `m.ExistsAt w n`. The convergence proof's only use of the universal
`hHasBeing` is precisely to establish `InAct n esse`, before a hypothetical
maximum is made to cause n's being. A witness-consuming helper could instead
accept that consequence, obtaining it from existing `ExistingInActAt` and the
root's independent actual presence. This preserves the same n and avoids
requiring presence for every modally necessary candidate. It is a genuine
available semantic reuse, not a new proof or code change in this audit. No
strict comparison of the complete premise bundles is asserted: the existing
actuality interface covers present contingent entities too, whereas the modal
bridge covers its separately specified necessary domain.

`hBeing : ActualityOnlyInsofarAsBeingReading InAct esse` has a separate task.
It takes `InAct x r` to `InAct x esse` for each other bearer/perfection considered
by the universal transfer/naming argument. It cannot start from `ExistsAt` and
cannot be replaced just by having-esse for n. Conversely
`ExistingInActAt` alone says nothing about an `InAct x r` token for which actual
presence has not been established. No converse `InAct x esse → ExistsAt w x`
is already certified by this interface.

The concrete reality-correspondence burden for universal naming is therefore
to keep all these quantifiers on one coherent reading: which roster members
represent actual entities, what actual perfection each supplied `InAct x r`
means, how formal versus eminent possession is distinguished in transfer,
and whether `ComponentOf`, `CausesIn` and `IsGod` concern those same actual
beings. On a rigid possibilist candidate carrier, perfections of absent candidates
cannot silently become actual effects/perfections merely because `InAct` is not
world-indexed. One may give it a selected-world reading with actual instances
only, but that interpretation needs independent fidelity/application; the
one-way existence-to-esse interface does not supply it. The source's distinction
between same-ratio and eminent perfection in q.4 a.2 must also survive that
reading, rather than equating all opposed properties literally in the source.

**Four-line candidate:** Target: the already actual necessary root's having esse
in reduced-root/naming convergence. Reuse: `STMT-EXISTING-IN-ACT-AT`, actual
root presence, the existing witness-specific per-se/convergence helper and
unchanged source esse vocabulary. Missing step: independently adopt the
same-sense actual-entity reading and consume its `InAct n esse` consequence
without a global modal-to-presence promise; separately maintain coherent actual
scope for the other-perfection/naming quantifiers. Premise comparison: a possible
replacement of the global modal bridge by the existing selected-world actuality
interface, not an implementation, equivalence, independent closure, or admission
of a new philosophical premise. All delivered theorem premises remain unchanged.

**Reverse-interface reuse check.** A bounded search of existing declarations
containing both `InAct` and `ExistsAt`, and the corresponding corpus interfaces,
found no generic existing `∀ x r, InAct x r → ExistsAt w x` (nor an equivalent
all-perfection presence predicate). `ActualEsseCausesSupportAt` assumes endpoint
presence; `UnitingCausesPresent` supplies presence of a distinct cause for an
already present target, not the presence of every bearer of a perfection.
`ModalCapacity` relates accessible actuality to capacity, not bearer existence;
`RespectSuffices` gives existence of an effect from a particular sufficient
respect, not existence of the bearer of arbitrary respects. None fills this
reverse role without new semantic assumptions. If such a universal presence
interface were later independently defended, composing it with the existing
`ExistingInActAt` would give `ActualityOnlyInsofarAsBeingReading` for every
recipient. That is a valid proposed composition, not reuse of an interface that
already exists or a discharged source premise. This audit introduces no such
interface. Keep `hBeing` retained for the present alternate-route proposal.

### Direct esse-cause correspondence: exact coverage and restricted warrant

The alternate route reuses the **pre-existing**, source-free
`NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround`:

```lean
∀ c x, c ≠ x → ActualConcrete m w x → CausesIn c x esse →
  ActualConcreteGround m w c x
```

Target actual concreteness is an antecedent. Cause concreteness, cause presence
at w, and the selected `grounds w c x` edge are all conclusions of this interface;
none is silently an additional input. The same bearer x is preserved. It does
not assert source existence in an unrelated situation, full sufficiency of this
one cause, modality of the cause/effect, or that every explanation is efficient
causation. Standalone DEF/STMT registration names the existing commitment; it
does not turn it into a sourced claim or establish its truth.

The old two-premise path has a different coverage profile:
`CauseOfNecessaryBeingCausesItsNecessity` sends an esse-cause of a modally
necessary target to a necessity-cause; then
`NecessityCausesAreActualConcreteGrounds` makes a distinct necessity-cause an
actual concrete ground. Their composition supplies the desired edge for a
necessary target, even without an actual-concrete target guard in those old
types. The direct interface also covers **actual contingent** targets, avoiding
any reason to reinterpret their esse-cause as a cause of necessity. Conversely
its actual-concrete guard does not cover merely modally necessary, absent or
non-concrete candidates. These are different semantic domains, not a global
weakening/equivalence claim. On the already actual concrete necessary root used
by the alternate proof, both interfaces provide the same needed edge, while the
direct one avoids the disputed necessity-causing detour.

The positive restricted warrant is this: an actual **current efficient cause of
this bearer's esse**, in the productive sense claimed, cannot be only an absent
candidate, an abstract description of a law, or our correlated observation.
Giving a real entity its actual being requires an actual producer; the producer
need not be material, embodied or temporally earlier. If the selected concrete
predicate admits real immaterial agents, actuality is compatible with that
concreteness. An abstraction that merely states which existence assignments are
permitted does not itself exhibit such production. This reasons from an
independently defended productive instance, rather than inferring productive
causation from a bare `CausesIn` label.

Q.3 a.4's efficient cause of esse is a source-shaped candidate for that reading;
q.104's being/becoming distinction shows why a ceased generator is not thereby
a current esse-contributor. But q.3 a.4's supplied `InAct` witness is not already
an `Ontic.ExistsAt` witness, and the texts do not automatically establish the
chosen concrete-domain criterion. Consequently actual producer presence and
concreteness remain real interpretation obligations of this interface. They
are not justified by registering its name. `ExistingInActAt` helps on the
already present target's having esse; its direction gives no cause presence.

The edge correspondence requires its own shared relation meaning. If `grounds`
is actual existential dependence broad enough to include genuine efficient
esse-contribution, the productive cause has a positive reason to count as a
ground: the target receives its being through that contribution, independently
of our description. If `grounds` instead means constitutive part-dependence
alone, efficient production is not automatically an instance; a cause need not
be a component. Likewise constitutional support of an organized bearer does
not itself demonstrate efficient giving of its bare esse. A mere correlation
or modal co-obtaining has neither interpretation merely by sharing a signature.
Thus the direct interface is a proposed inclusion between independently
specified real relations, not their identification.

Finally an admitted cause can be one indispensable contributor to a joint
productive basis. The interface neither says that each binary ground edge is
a full explanation nor that all required contributors/enablers are listed.
Concluding that a root cannot receive even such a genuine contribution uses
absence of *any* selected incoming ground, not a premise that a single
contributor is wholly sufficient. Full explanatory completion, adequate totality
reason and the whole-roster norm remain separate. The formal route's alternate
premise mapping improves correspondence but is no numerical evidence that more
philosophical truth has been established. No current semantic premise is
independently discharged by this audit.

### Constructive completeness connection after common-ground coverage

`DirectEsseRootRoute.necessaryRootCommonGround` preserves one necessary actual
root n and proves `ActualConcreteGround m w n x` for each other actual concrete
x. This is useful **common contribution coverage**, including contingent targets.
Its proof uses genus esse-causality and the direct interface; it does not show
that n alone supplies everything needed for x. Necessity of n's existence is
not necessity of n's productive exercise or its particular effect.

The exact reusable mechanism for a stronger conclusion is already present:
`DerivativeJointPower.Supply.intrinsic` supplies an admitted intrinsic source;
`Supply.joint g` then supplies an effect when **every contributor of that
admitted record** has Supply. `ExplanatoryClosure.FullSupply` applies the same
constructor to `allMembers h`, counting both contributors and enablers. Thus,
for a genuine complete/cumulative productive record for x, existing supply of
all its members immediately supplies x. This is a constructive inference rather
than another source-extraction result. `source_path` goes in the other direction:
Supply yields an intrinsic source/ancestral path when contributor sets are
nonempty; it does not turn a known common source/path into Supply.

There are two sharply different applications of that inference.

1. **On the unchanged recorded graph.** `JointGroups.recorded` has one record
   for each target with predecessors and makes its contributors **all incoming
   graph predecessors together**, with no enablers. A known n→x edge makes n
   one such contributor. To apply its joint constructor, every other incoming
   predecessor must already have Supply too. For a one-step proof from n's
   intrinsic supply, the exact sufficient condition is that the full incoming
   contributor set for x consists only of supplied intrinsic sources (the
   singleton {n} case is a special case). This is stronger than common-ground
   coverage. Merely calling n a complete/cumulative cause does not remove other
   edges from that record. Conversely, representing alternative sufficient
   suppliers as separate incoming edges in this adapter makes them conjunctive
   requirements; the adapter itself asserts no sufficiency. No graph edit or
   identification of alternatives with jointly indispensable contributors is
   justified by the new common-ground theorem.
2. **On an independently warranted productive group already expressible in
   `Groups`.** An admitted alternative record for x whose full productive basis
   is supplied allows `Supply.joint`; other alternative records need not be
   selected. If n alone really is the whole productive basis in that respect,
   an appropriately evidenced singleton contributor record gives a one-step
   derivation. For **FullSupply**, the claim must also account for all enablers,
   or show that none is required; otherwise the source's productive Supply and
   the explanation's FullSupply remain different. This uses the existing
   group/constructor semantics, not a new complete-explanation predicate.

The faithful additional philosophical step is consequently **record adequacy
plus actual member supply**: the chosen record must identify all real productive
contributors in the chosen respect and every needed enabling condition, and
those actual contributions must be supplied in the retained standard. Genuine
scenario sufficiency of that complete member set must be separately defended
if an explanatory-sufficiency conclusion is intended; admission or construction
of a Supply term is not itself a proof of that metaphysical sufficiency. A
complete/cumulative reading can justify a record only after this work, not by
renaming the original partial binary edge. Neither a new all-subsets WF premise
nor a new cycle control is needed merely to state this next connection.

The owner's joint-condition observation fits exactly at this point. In the
existing `JointCondition` vocabulary, fix **the same** member set S across the
accessible worlds and suppose all its members actually hold. If one member is
contingent, `JointCondition.contingent` proves that the joint condition is
contingent. `necessityEquivalence` says the fixed conjunction is necessary
exactly when every member is necessary. Accordingly, a necessary source together
with an indispensable contingent exercise/enabler can have a contingent joint
full condition. Nothing here creates a new composite being out of S, forbids
a necessary partial source, or implies that an arbitrary cause is sufficient
alone. Supplying only a necessary bearer does not supply the contingent member
or explain why that exercise/enabler obtains. If a **complete necessary** joint
condition were also defended as strictly necessitating the effect, the old
necessitation consequence would apply; the mixed joint condition avoids that
antecedent rather than refuting the consequence.

**Next constructive connection:** select one actual target and an independently
supported complete productive group for its existence; retain n as one real
contributor, identify any distinct contingent exercise/enabling members, and
reuse their existing Supply/FullSupply certificates before applying the joint
constructor. Compare the same fixed group across worlds with the already checked
joint-condition theorem. On the unchanged recorded graph, first show its entire
incoming set faithfully is that group; if it is not, do not market the adapter
as a complete explanation. No new model, definition, claim or theorem is added
by this audit, and no direct edge or constructor is advertised as independently
establishing full explanatory completion. No premise truth is discharged.

### One positive productive-group brief: illumination received by receptive air

The complete `AQUINAS-ST-I-Q104-A1-EN` witness was re-materialized and reread
for this group, with its existing dossier. The productive case is the
**received illumination process/state**, not production of the air's or sun's
bare existence. Q.104 a.1 ad 1 explicitly makes light result from the air's
diaphanous nature given the sun's action; corpus contrasts this continually
received light with retained heat in water, and ad 4 restates continual solar
influence. This is enough for a source-faithful, scoped conditional group that
can advance the existing corpus without claiming new physics.

**Target:** one specified region of receptive air a, its sun-derived
illumination L, and the sun's productive influence U **on that region**. U is
arrival/exercise of the influence, not merely existence of the sun or its being
above a horizon. R is that region's diaphanous receptivity. The full candidate
record has contributor U, enabler R and effect L. Keeping R as enabler, rather
than pretending it emits light, is a substantive causal distinction already
expressible by `Groups`. U and L have different bearers/roles; the group itself
is not a new substance. Admission records this proposed complete basis at the
chosen scope; actual exercise is a separate occurrence claim.

**Source-supported scenario clause:** within Aquinas's stated illumination
account, R and U together yield L. This is the direct conditional force of ad 1,
not a proposed inference from every member having some predecessor. To state
`Exercise.suffices {U,R} L` faithfully, allowed scenarios must preserve this
receptivity/received-action interpretation and the source's causal background.
A non-arriving ray or an opaque region does not satisfy U or R respectively;
this does not justify adding unknown successful conditions by defining U as
“whatever makes L happen.” A full independent physical group would need its
own evidenced optical specification. The source supports the historical
conditional reading and productive role; it is not an empirical certification
of a modern optical model over all possible interference/delay situations.

**Source-supported dependence clause:** corpus says the received light does
not remain when the sun's relevant action ceases. Thus, on the source's scoped
account, ¬U excludes this L. This motivates indispensability of U given R. The
existing formal indispensability test additionally needs an *allowed* deletion
scenario with R present, U absent and L absent; the temporal/hypothetical
cessation discussion motivates that scenario, but its encoding as a member of
an explicitly selected scenario space must be recorded. Ad 1 does not establish
that R is a productive contributor, nor test independent deletion of each
physical feature of transparency. No unnecessary second contributor is invented
to obtain plural causality.

**Actuality and modality:** the witness describes ordinary actual illumination,
but does not identify a timestamped particular a/U/L for an actual `Exercise`
record, and supplies no de re modal necessities of the sun, air or either event.
For a named real episode, actual U/R/L must therefore be independently observed
or sourced. Once an actual received illumination and a permitted cessation
scenario are warranted, that very L is contingent relative to the chosen
scenario relation. U is absent in that cessation scenario too. R may remain
throughout this comparison without being declared metaphysically necessary.
Nothing here assigns necessity to the sun as a concrete bearer. This is the
precise boundary between a positive source-backed group and a fabricated actual
or necessary/contingent witness assignment.

**Actionable formalization brief:** reuse `Groups`, `Exercise`, `suffices`,
`indispensable`, `allMembers`/`FullSupply` and the fixed-member `JointCondition`
theorems. Record U as contributor and R as enabler, preserving the source's
receptivity-plus-received-action conditional and cessation case. In a specified
actually exercised episode, supplying U alone gives productive `Supply` for L
only once U's own supply is supplied; supplying both U and R gives `FullSupply`
via the existing joint constructor. If U (or another retained member) is
contingent and the actual conjunction holds, reuse `JointCondition.contingent`
to show that this fixed full condition is contingent. Do not infer that U has
underived Supply, that the air's bare existence is produced, or that the sun is
a necessary being. The next evidence needed for an **actual** group certificate
is a specified illumination/cessation episode with warranted occurrence and
allowed scenarios, not another regress model. No new claim, theorem or model is
added in this brief; it identifies one faithful conditional group and exactly
which actual-instance evidence a substantive follow-up must furnish.


### SCG I.16: prior actualizer versus cause of a bearer's being (2026-10-31)

This bounded ledger-G source follow-up reuses the actual-prerequisite and
act-priority scope audits above and the already recorded IX.8 rejected readings;
it does not repeat that search. The complete existing primary witness
**AQUINAS-SCG-I-16-EN**, *Summa contra gentiles* I.16[1]–[7], was materialized
and read before this finding. The witness is the Anton C. Pegis1955 English
translation in the existing pinned `aquinas-summa-contra-gentiles-en.json`
snapshot of `https://isidore.co/aquinas/english/ContraGentiles1.htm`, response
SHA256`c46d9f71e075b6cd4508e37331029b32aff5432f2aff502a3015fcd93e6dd45c`;
selected chapter hash
`1cb2108606aea6ceb0153fde3e9fb22b893974230aa07c4a9bb1503b19518a91`.
This remains translation evidence, not an upgrade to a newly read Latin edition.
No claim, source record or candidate was changed.

**Positive argument.** I.16[3] distinguishes temporal potency-before-act in
one changing thing from act's absolute priority: a potential condition does not
actualize itself; its actualization requires something actual. The text then
states its generic any-potency priority conclusion and excludes potency in God
because God is already first being and first cause. [7] again argues from an
observed emergence into act to a prior actualizer, then uses its no-infinite-
regress premise. These are source-backed directed actualizer/prior roles,
not merely an existential presupposition inferred from a necessary condition.
The whole chapter supports keeping broad act-priority as an attributed
commitment; the audit does not revise its type to actual motions only. The
independent defense of applying its actualization reason to every unexercised
potency remains the existing philosophical question.

**What the chapter does not infer.** Neither [3] nor [7] identifies every
priority relatum with a cause of the patient's bare existence. The actualizer
explains the transition to act in the relevant respect. Replacing that
transition by the bearer's being would require a justified existential
application, not the word “prior”. [2] addresses potency to be, but reasons from
divine eternity to exclusion of that potency; it does not establish a universal
ontic-priority-to-esse-cause law. [4] argues within per-se-necessity and causal-
possibility commitments, not the bare de re `NecessaryAt` semantics. [5] uses
the already designated first agent to exclude partial/participated action;
[6] addresses passive potency, receptivity and the designated divine agent's
immutability. None converts every ontic prerequisite into efficient causation
of its bearer. The God-as-first-being-and-first-cause assertion in [3] is the
existing back-reference to preceding arguments, correctly recorded by
**AQUINAS-SCG-I-16-GOD-FIRST-BEING**; its two roles cannot be converted into a
universal implication between priority and causation simply because one
candidate is asserted to possess both.

Thus **STMT-SIMPLY-PRIOR-IS-CAUSE-OF-BEING** remains without a source argument
for its unrestricted formula. The direct actual-ground variant additionally
requires current presence, concreteness and membership in the selected grounds
relation. An actualizer of a currently occurring change motivates actual
agency in that respect; this chapter supplies neither its current efficient
causation of the patient's bare esse nor its concreteness under an arbitrary
Profile. The existing current-constitutive-prerequisite interpretation remains
a positive restricted application, not a coverage proof for every priority
used by the pure-act continuation. No efficient cause is inferred solely from
logical presupposition, and no change of causal respect is made.

The optional *In Metaphysicam* V lect.13 lead was not read or cited in this
bounded item. Its existing full-book source snapshot does not mean that lecture
has already been materialized as a passage. The candidate now advances to that precise lecture; this finding exhausts
the SCG I.16 lead only. Exact premise change: none; no
Lean theorem, new modal/source principle, model or root-frontier discharge.


### In Metaphysicam V lect.13: priority senses and the shared-Prior obligation (2026-10-31)

The precise queued lecture **V lect.13**, complete nn.1–18, anchors
**[82501]–[82518]**, has now been pinned as **AQUINAS-IN-METAPH-V-L13**,
materialized and read. Its new manifest
`corpus/passages/aquinas-in-metaphysicam-v-l13-lat.json` reuses the existing
book-V Latin snapshot of `https://www.corpusthomisticum.org/cmp05.html`, response
SHA256`230dcfb6b8fd45cefe50de8e185017961cf81739452a0286aa404885e17c28f1`,
encodingISO-8859-1; selection runs from the heading Lectio13 up to Lectio14.
The full eighteen numbered paragraphs, rather than an isolated priority
sentence, supply the evidence. No other lecture was read, no candidate was
edited, and no new attributed claim or formal interface is introduced.

**Sequential scope.** Nn.1–2 introduce priority relative to a principle and
separate ordering in becoming/motion/quantity, cognition, and being/nature.
Nn.3–6 cover place/time and choice of reference principle; nn.7–8 cover motion,
generation and effective command; nn.9–10 discrete ordering; nn.11–14 cognition;
nn.15–18 priority in being with its dependence, substance/accident, and
act/potency qualifications. Consequently the general vocabulary of prior,
principle or even simply cannot by itself pick the current formal relation.
N.11[82511] uses simply-prior language within the cognition discussion; it is
not permission to put every epistemic predecessor into ontic grounding.

**Positive ontic criterion.** N.15[82515] explicitly identifies a natural order
in being, then gives as one mode priority through commonality or dependence:
the prior can be without the posterior, whereas the posterior cannot be without
the prior. This is an asymmetrically directed separability/dependence criterion,
not just symmetric covariance. The immediately following Platonic universals,
surfaces, lines and number applications are reported as Plato's use of that
mode; the passage should not be made an endorsement of every Platonic instance.
N.16[82516] supplies a distinct subject/substance-over-accident mode, with a
per-se-existing primary subject. These are positive grounds for investigating
ontic prerequisite dependence. Neither paragraph says every such predecessor
is an efficient agent producing the posterior's bare esse or a concrete member
of an arbitrary supplied Profile.

**Act/potency is included, but with qualifications that do real work.**
N.17[82517] explicitly makes the act/potency division a third mode in this
natural/being-order discussion. Matter and parts are prior *in potency*;
with respect to actuality they are posterior, and parts become actual through
dissolution. N.18[82518] reduces the discussed modes, especially to asymmetric
independence, while distinguishing whole-before-parts in generation from
parts-without-whole after corruption. Thus the lecture does connect its modes
under a common dependence/separability account; it does not leave them as
wholly unrelated homonyms. But that reduction retains the qualified mode and
phase of being. It does not yield an unqualified rule that every named part is
an actually existing current efficient cause, or that a prior-in-potency role
is a distinct actual bearer in the selected world's support graph. A whole-first
comparison cannot ignore the actual/potential distinction in the examples.
This does not refute the explicit q.3 `CompositePosteriorToComponentsReading`
premise: q.3 constitutive principles need not be the detachable parts discussed
here. It requires correspondence of the SAME ComponentOf, Prior and qualified
respect before the source examples are used for or against that premise.

N.1[82501]'s father-as-principle and n.7[82507]'s mover/generator are genuine
causal examples. The latter calls the generator a principle simply and by
nature, unlike an arbitrary spatial reference. The child's generative order
and n.8[82508]'s command-to-execution order therefore give positive directed
causal cases, not a denial that natural priority can be causal. Their roles
remain generation or a particular commanded movement; neither proves a
universal continuing bare-existence cause for every natural priority. The
source's asymmetric independence criterion cannot be reversed into efficient
causation merely by replacing “cannot be without” by the word cause.

**The same-Prior constraint in the current proof.** Q.3/SCG I.16's generic act-
priority premise and this lecture's natural/being-order modes share an
act/potency and directed-dependence setting. V.13 expressly includes act/potency
under its natural-order discussion. There is nevertheless no sentence here
identifying every actualizer-prior individual in q.3/SCG with the natural-
priority criterion of the patient's *bare existence*, nor every natural
predecessor with an efficient esse giver. The source explanation of a
potency-to-act transition and the present-constitutive existence-prerequisite
reading remain different scoped roles until their agreement is defended.

This matters because `necessaryFirstPureAct` consumes the SAME `PriorSimply`
parameter in the act-priority premise and the bridge into selected actual
concrete grounds. Using the ontic-dependence criterion to defend the bridge,
then a producer-of-an-actualization reading to defend generic act-priority,
would silently change that shared parameter's meaning. It is not enough that
both predicates can be written with the same Lean function type or translated
as priority. The source's reduction of priority modes supports a possible
common account, but the actual-world presence, concrete-domain coverage and
same-esse-relatum requirements still need proof for the specific priorities
used by that theorem. Conversely a decision to restrict Prior to current
constitutive prerequisites would need the broad act-priority premise defended
for that restricted relation; the text's transition reason alone does not
provide it for every unexercised potency.

**Result for ledger G.** This lecture supplies a clearer positive criterion
of ontic dependence and its multiple qualified modes, not the unrestricted
**STMT-SIMPLY-PRIOR-IS-CAUSE-OF-BEING** or its direct actual-concrete-ground
variant. It also locates a shared-semantics obligation between G and the
act-priority premise rather than supplying another opaque universal bridge.
No presupposition-only-to-efficient-cause inference, respect-to-bare-being
substitution, new passive-potency claim, transitivity, well-foundedness or
modal support transport is admitted. Exact premise change: zero. The bounded
lecture is exhausted; queue/candidate handling remains coordinator-owned.

## Common modal priority (#950)

The [source and type audit](notes/modal-grounding-priority-950.md) distinguishes
necessary target truth, persistence of support and one common WF priority rank.
It composes the existing necessary-underived union route without defending its
metaphysical premises; rotating/parity/switching controls preserve the remaining
escapes and the separate no-contingent-supporter burden.

## Capacity and exercise vocabulary audit (#1659, #1652; 2026-11-17)

This analyst audit uses main `91bcc8dbaef83166c09fbd30e09586764438e191`,
not pending #1700. It repairs the dictionary for the existing #319 boundary
and #741 certificate; it neither adds a theorem nor discharges a root premise.
The two certificate conclusions are not themselves recorded root-route premises.
Their relevance is the power-to-being boundary and the actual capacity inputs
of the Eleatic/Cogito routes below. Historical readings in earlier sections
are not newly attributed or rechecked here.

### Five sense dispositions

The five UUIDs and stable labels in `power-capacity-exercise.json` are preserved.
The suffixes below all belong to `CAUSAL_CAPACITY_VERSUS_ACTUAL_EXERCISE`.

| Sense | Exact representation and disposition |
| --- | --- |
| `_1`, capacity | `8ce4f4d6-a221-5db8-aef5-2f0babdfb416`: expanded primitive prose, still no common named Lean declaration. #741 uses the parameter `cap : S → E → Prop`; the direct capacity consumers use `hasCausalPower : W → B → Prop`. Neither parameter defines capacity. |
| `_2`, actual transmission | `5aef0b49-016a-5716-9bd9-423d957b28ab`: now points to the existing primitive `PowerExistenceBoundary.Profile.transmitsPower`, with a `formal_gap`. Endpoint existence and causal status follow from `Coherent`, not the field alone. |
| `_3`, unborrowed power in a respect | Preserve `UnborrowedPowerAt`: existence, intrinsic-power marker and no incoming transmission in this channel. An outgoing edge remains a separate requirement. |
| `_4`, finite grounding | Preserve `FinitelyGroundedPower`: intrinsic seed or transmission from an already finitely grounded predecessor. This inductive standard is not the definition of every dependence relation. |
| `_5`, pure act | Preserve `SummaTheologiae.PureAct`: no potency in the supplied respects. No new source assertion, positive exercise condition, exhaustive respect coverage or link to capacity is added. |

The last three existing definitions and declarations are unchanged. Their
presence in Lean does not settle the interpretation of their predicate inputs.
Sense `_2` is now traced to a field, not upgraded to a reductive causal account.
Sense `_1` remains unfinished as a named sense; attaching a nominal wrapper
or an unrelated declaration would conceal that fact.

### Why the available capacity declarations are not interchangeable

`BorrowedExercise.Borrowed` quantifies over allowed scenarios where a supplied
capacity holds; `Retained` witnesses such a scenario without a lender.
`capOccurs` and `capAll` are deliberately different profiles on the same
exercise, not competing definitions silently interchangeable in every theorem.
`PowerRequired` only says actual occurrence implies actual capacity; it does
not define capacity, assert its exercise, or require it at every allowed
scenario. In particular, `Instrument` and `Secondary` do not themselves include
`cap m.actual e`; the fork supplies that through `PowerRequired`.

`CausalPowerConcreteness.IntendedProfile.hasCausalPower` is a genuine named
primitive, but its enclosing structure additionally requires power-implies-
existence, causal endpoints, exercise-implies-power and power-implies-concrete.
The generic Eleatic/Cogito formulas take a raw predicate without those fields.
Naming this projection as the common sense would falsely suggest that those
consumers reach it and inherit its contract. `NamingVeracityBatch1.Power.CanDo`
is task-indexed, while `BearerExercise.responseOntic` interprets one activated
response table; neither is an unrestricted replacement for the supplied profiles.
These are reuse findings, not reasons to duplicate those frameworks.

For an event/world correspondence one must supply maps from scenarios to worlds
and events to bearers, fix the effect/respect, and state which event-indexed
capacity corresponds to which bearer capacity. The existing `Exercise.bearer`
need not be injective: different exercises of one bearer cannot silently be
collapsed into one unspecified power. A process interpretation additionally
needs a time interpretation and explicit activation conditions. A fixed-context
primitive does not need a universal temporal theory merely to support a
conditional investigation. This audit therefore specifies the missing maps
without asserting a universal capacity-to-exercise law.

### Consumer coverage and claim/type self-sweep

The following is the complete direct `definition_ids` coverage of the two
edited definitions at the audit baseline. Filenames below are under
`corpus/statements/` or `corpus/arguments/`; each is an existing record, not a
new registry. All these records and their owning specs remain unchanged.

Capacity statements: `power-existence-simplicity-scope-boundary.json`,
`intellectual-exerciser-has-power.json`, `every-existent-has-causal-power.json`,
and `causal-power-requires-concreteness-at.json`.
Capacity arguments: `POWER-EXISTENCE-SIMPLICITY-SCOPE-BOUNDARY.json`,
`cogito-inhabited-concrete-from-causal-power.json`,
`causal-concreteness-commitment-strengthens-power.json`,
`cogito-inhabited-concrete-from-floor-power.json`,
`existing-in-act-at-from-eleatic-power.json`,
`intellectual-exercise-requires-act-from-active-power.json`, and
`existent-in-act-from-eleatic-power.json`.

Actual-transmission statements: `power-existence-simplicity-scope-boundary.json`,
`constitutive-nature-omission-controls.json`, `part-free-plurality-joint-control.json`,
`necessary-simple-plurality-joint-control.json`,
`root-intellect-will-pure-act-plurality.json`, and
`plural-root-confluence-control.json`.
The six corresponding argument filenames are identical except that the boundary
argument uses `POWER-EXISTENCE-SIMPLICITY-SCOPE-BOUNDARY.json`.

| Consumer | Exact type/prose boundary checked |
| --- | --- |
| `powerExistenceBoundary : Boundary` | Two existential model witnesses, each with `Coherent`, an actual source/effect edge and nonintrinsic effect. First: contingent source externally supported in esse. Second: necessary source without external support but with a proper component. No universal metaphysical counterexample is inferred. Capacity is linked as a contrast, not encoded in this model. |
| `EveryExistentHasCausalPowerAt`, `IntellectualExerciserHasPowerAt`, `PowerRequiresConcreteAt` | Respectively existence → capacity, intellectual attribution → capacity, capacity → concreteness, at a selected world. None defines the supplied capacity predicate or entails outgoing exercise. |
| `NecessarySimplePlurality.JointControl`, `PartFreePlurality.JointControl` | Their power views use the existing boundary Profile and include its Coherent condition in OntologyControl. The four-being and five-being models remain distinct. |
| `ConstitutiveNatureUniqueness.Control.Certificate`, `RootIntellectWillPureActPlurality.Control`, `PluralRootConfluence.Control` | Retain PartFreePlurality's JointControl and hence its supplied power view; no capacity activation bridge is added by the dictionary repair. |
| `BorrowedExercise.certificate : Certificate` | Uses the existing borrowed-power, joint-group and temporal vocabulary, and links this disambiguation rather than either edited DEF directly. Event occurrence (`occurs`) and actual group exercise (`exercised`) are separate fields; neither is the #319 binary transmission relation. |

In the last row, `Lender` requires admission, nonempty contributors and their
occurrence, plus group exercise at the actual scenario. It does **not** itself
require every enabler or the effect to occur: `Exercise.coherent` provides those
conditions for exercised records. It is therefore inaccurate to replace it by
“a sufficient group” or “an event with a predecessor.” `Retained` gives a
scenario without a lender and says nothing about acquisition of the power;
`SelfExercising` excludes a lender in this representation, not all causes or
existential supporters. `Essential` quantifies capacity over allowed scenarios,
not the bearer's de re necessary existence. No actual consumer examined here
licenses any of these substitutions.

The new technical lemma `exercise` includes `exercised`, `exercises` and
`exercising`. It traces this family's transmission, occurrence/group and staged
time uses to existing definitions. It is not an ordinary-word exemption and
does not claim exhaustive coverage of intellectual operation or will. Unlinked
uses in other families remain review work. `power` and `capacity` now also
point to the already existing borrowed-power profile; no duplicate profile is
introduced.

### Assessment, limits and next discriminating step

The precise mismatch repaired is the claim that the transmission field alone
supplies existing endpoints. Lean's separate `Coherent` condition positively
justifies that correction. No substantive objection to keeping capacity,
exercise, intrinsic source status and uncaused esse distinct was identified.
The strongest standing alternative in the existing #741 investigation is the
source-free globally organized account: it accepts local lending and occurrence
but rejects finite `Supply` as a necessary standard of explanation. The existing
coherent, sufficient regress witnesses show that local conditions do not entail
that standard. They do not establish real instantiation or count as evidence
against a metaphysical source premise without independent application warrant.
This vocabulary audit neither ranks that rival lower nor decides it.

The next discriminating step for `_1` is a narrow, explicitly primitive common
capacity interface with a checked adapter to the actual `cap` and
`hasCausalPower` consumers, preserving the existing `capOccurs`/`capAll`
contrast and `PowerOmission` control. Test whether the proposed event/bearer
mapping loses distinct powers of one bearer before adopting it. An activation
claim must be its own assumption, not a definitional identification. Changes to
those shared consumer modules/specs need coordinator assignment beyond the
current record ownership.

Readiness also limits verification here: this isolated checkout has neither
`.lake/packages` nor `.lake/build` (indeed no `.lake` directory), and no preview
was supplied. The authorized prepared CLI from the coordinator checkout is used
with `--root` pointing here; both source checkouts were at the baseline above.
No cold build, new checkout, source fetch, generated status edit or unverified
Lean module was introduced. A prepared dependency/build seed is needed for any
new Lean adapter and for the coordinator's status refresh/binding checks. The
new projection link awaits that generated formal-status refresh; its primitive
classification is justified by the existing structure declaration, not claimed
as freshly computed evidence. Independent semantic challenge and final CI remain
coordinator-owned before publication.

Focused validation of this record-only proposal: `truth check` passed in the
repository's warn mode, `scripts/bundle_audit.py` passed, the sense, definition
and lexicon ratchets passed, and `git diff --check` passed. The lexicon display
confirms the intended trace and exposes `_1` as `no_lean_declaration` and the
new `_2` link as `not_computed`; other-family exercise uses with no relevant
link remain visible. New/changed prose still produces lexical backfill warnings;
no ordinary gloss or allowlist change suppresses them. The sense ratchet identifies
`1dc8b928-44d3-442a-a886-d6148a9e71a4` as removable from the shared allowlist;
that cleanup is left to its coordinator owner.

Computed `frontier-diff --base 91bcc8dbaef83166c09fbd30e09586764438e191`
reported **no change**, with zero verified support alternatives added. This is
premise-delta evidence, not a judgment about the philosophical premises.
No statements, claims, arguments, results, specs or Lean sources changed;
the table above is the claim/type self-sweep for the edited meanings. Formal
status refresh, affected binding, semantic challenge and required final CI have
not been run in this unprepared checkout.

Policy sourceRevision: `15f348b072188255da837578eaafc8a98f12fdf0`.
CLI source checkout: `/home/moenarch/moritzbrantner/truth-core`, observed HEAD
`91bcc8dbaef83166c09fbd30e09586764438e191`; binary SHA-256
`7b3c1c1c2196e313eebbe6ec96275bd6c358b6542f6ddd01abee14d17a4910be`.
The prepared binary does not report an embedded source revision; the observed
checkout revision is not an independent build-provenance attestation. All CLI
checks selected this isolated checkout with `--root` through
`python3 scripts/worker_env.py --`.

### Independent semantic challenge and repair (2026-11-17)

The review of `38fc9e1f33691eb5735e730f5154eaf98e89c6f9` supported the
primitive transmission linkage, Coherent boundary and inspected consumers. It
found that the exercise entry's broad disambiguation links admitted non-exercise
definitions. In particular, intellectual-exerciser-has-power passed the lexical
check through its capacity definition despite using IntellectualExercise. Both
broad navigation links were removed from the entry; only its four directly
selected definitions now count. Intellectual-operation coverage remains pending.
Thus the trace described above is a scoped mapping, not certification that every
consumer already links its relevant exercise meaning. No checker exemption or
allowlist growth masks the remaining uses. The capacity adapter remains the next
implementation step, with explicit event/bearer/respect correspondence and
activation assumptions.

Coordinator integration verification: the incremental `lake build` passed on the
combined record changes with unchanged Lean sources. A subsequent generated
`definitions refresh --write` adds only the new transmission projection's status;
its primitive classification is now computed. The selected boundary result
`a268b937-edc1-5f68-b996-9f3489809979` passes `bind-check` (one bound, no mismatch).
Final CI remains required. Prepared artifacts were copied into both research
worktrees for the continuing interface and vocabulary work; they do not verify
subsequent edits.
## Indexed capacity adapter (#1659, #1652; continuation)

This continuation is a delta from `38fc9e1f33691eb5735e730f5154eaf98e89c6f9`.
The coordinator authorized a narrow adapter and its own result bundle, leaving
existing consumer modules and frozen Challenges untouched. The earlier audit's
missing interface is addressed here; its philosophical application burdens
remain. The coordinator's review correction to the `exercise` entry is also
applied: remove both broad disambiguation links, preserve all four direct DEF
links. Capacity or PureAct alone must not license a use of the word exercise.
Intellectual-operation coverage remains pending in its own family.

### Meaning, representation and exact agreement condition

`TruthCore.Causality.CapacityInterface.Capacity W B R` supplies the primitive
`possesses w b r`: bearer b has the capacity for the specified effect/respect r
in situation w, including when not exercised. It provides no causal direction,
activation law, effect occurrence, source status, existential support,
concreteness, or cross-world persistence. A disconnected charged battery is an
illustration of possession distinct from exercise, not a newly sourced claim.
Situation may represent a world or a time-sensitive context; the adapter imposes
no interpretation of time or accessibility on it. A respect must distinguish
powers for different effects when that difference matters to the application.

The adapter is more than a new name for an arbitrary predicate: it exposes and
tests the exact information loss involved in the proposed reuse. `Indexing`
supplies three maps: scenario → situation, event → bearer, event → respect.
`eventProfile` reads possession at those indices. `Corresponds` requires
pointwise equivalence with the original `cap s e`, for **all** scenario/event
pairs. This is stronger than agreement only on allowed scenarios; an application
needing only allowed scenarios should explicitly restrict the index domain.

`FiberAgreement` says that whenever two pairs (s,e), (t,f) map to the same
situation, bearer and respect, `cap s e ↔ cap t f`. It includes different events
of one bearer/respect and different scenarios mapped to one situation. No
injectivity or surjectivity is assumed. The proposed `Factorization` theorem
states exactly:

```
FiberAgreement i cap ↔ ∃ p : Capacity W B R, Corresponds i cap p
```

It also supplies a canonical witness `descend`: possession holds if some
scenario/event pair maps to those three indices and has capacity. Forward
recovery uses the agreement assumption; reverse necessity uses equality of the
three possession arguments. `descend` is false outside the represented image.
This is a mathematical extension choice, not evidence that unmapped bearers or
respects lack capacity. Correspondence does not determine values there.
No claim of global uniqueness of the resulting capacity profile is made.

The finite controls can fail in exactly the intended way. With one scenario,
two Boolean events, one bearer and one respect, assign capacity only to event
true. No profile on the collapsed indices can recover both truth values.
A separate control holds event/bearer/respect fixed while identifying two
Boolean scenarios with different capacity values. Conversely one bearer can
have different capacities for the two different Boolean respects without any
contradiction. These are logical controls on representation, not objections to
metaphysical capacity or evidence against any existing source premise.

### Lossless fallback and actual consumers

An arbitrary event profile need not meet `FiberAgreement`. `fromEvents` therefore
retains the original scenario, the **actual** `Exercise.bearer` mapping, and the
pair `(specified respect, event identity)`. Its possession clause checks that
the retained event belongs to that bearer and respect and then reads the original
capacity. `retainedIndex` recovers the original profile exactly. This works when
multiple events have the same bearer/respect because their identities remain;
it does not prove that identity can subsequently be forgotten. No new Exercise,
group, occurrence table or activation claim is invented.

`fromBearer` embeds an existing `hasCausalPower : W → B → Prop` with a Unit
respect. This represents its already selected or unspecified respect; it does
not assert that every distinct power has the same truth value. `bearerProfile p r`
fixes one explicit respect and yields the exact W → B → Prop interface. It does
not silently existentially aggregate powers over respects. The round trip of a
thin profile is definitionally equal to that original profile.

The certificate's `BorrowedTransport` instantiates `exerciseIndex` with an
existing Exercise, a scenario/situation map and an event/respect map. Under
`Corresponds`, its actual `Borrowed`, `Retained` and `PowerRequired` formulas
are preserved. Pointwise equivalence gives equality of the profiles, so these
are the same claims about the same groups, occurrences, allowed scenarios and
actual scenario, not reinterpreted approximations. `PowerRequired` remains a
separate premise; the adapter neither proves it nor supplies a converse from
capacity to exercise.

`RootConsumerTransport` explicitly uses the existing
`EveryExistentHasCausalPowerAt`, `IntellectualExerciserHasPowerAt` and
`PowerRequiresConcreteAt` declarations with the recovered thin profile. It
proves equivalence to their original formulas, not existence-to-power,
intellect-to-power or concreteness themselves. This is the precise connection
to the same Eleatic/Cogito root-route inputs audited above. Existing consumers
are unchanged, so the new primitive is available through an adapter, not
silently substituted for their supplied parameters. The new certificate is
not wired as a root premise and claims no root discharge.

`ExistingControls` reuses the original `instrument_regress`, `secondary_regress`
and `power_omission` theorems of the BorrowedExercise Solution. Their exact
`capOccurs`/`capAll` assignments and no-power omission are unchanged. The general
`fromEvents` round trip applies to each original profile, including the all-false
profile of PowerOmission. No activation axiom is added to rule it out by fiat.
These are reused evidence, not newly discovered rival defeats. A common-bearer
factorization of an arbitrary profile would be false; the finite control is
positive evidence for retaining the agreement condition, rather than a merely
conceivable objection.

### Proposed outcome, self-sweep and integration boundary

All five sense UUIDs and labels remain stable. `_1` now names
`CapacityInterface.Capacity.possesses`, with a `formal_gap` describing its
primitive meaning, examples, exclusions and application obligations. `_2`
through `_5` remain exactly as in the previous commit. The new interface is an
explicit primitive plus substantive adapter conditions; it is not a completed
reductive analysis of causal ability. No source or claim record is added.

The bounded bundle is `specs/capacity-interface.toml`, vocabulary
`TruthCore/Causality/CapacityInterface.lean`, and new
`TruthCore/Results/Causality/CapacityInterface/{Solution,Challenge}.lean`.
Result `d26f85e9-262c-426d-888c-2a09fef96a17` binds
`TruthCore.Results.Causality.CapacityInterface.certificate` to statement
`813bbcdf-df59-49fe-93f6-54d505259540` (`CapacityInterface.Certificate`).
Argument `6acc63b4-5d25-4fcb-a1ee-ddcd2351aa43` has no external premises:
the universally quantified correspondence and agreement assumptions occur
inside the explicitly conditional conclusions, not as hidden philosophical
commitments. The conjunction retains the exact old controls. The self-sweep
checks all quantifiers, the fixed respect of the thin adapter, actual bearer
preservation, the possibility of many events per bearer/respect, cross-scenario
collisions, and the distinction between a represented profile and its real
applicability. No new historical attribution or source-fidelity claim occurs.

Shared imports, generated formal status, allowlists and existing consumer specs
remain coordinator-owned. The coordinator must generate imports for the new
modules on integration; a focused build directly targets the Solution without
requiring a root-aggregator edit. The generic consumers' raw parameters still
need an explicit adapter adoption if future sense binding is to reach the new
constant. That migration is separate from this representation theorem.

The substantive reassessment point is now precise: exact mathematical reuse
requires agreement on the indices actually forgotten, and the event-retaining
adapter supplies a lossless alternative when such agreement is unavailable.
Application to a chosen real power still needs its effect/respect, scenario
interpretation and activation evidence. No additional philosophical objection
to this scoped representation was identified. The earlier source-free account
remains a standing rival about explanatory Supply, untouched by these adapters.
The next discriminating application is to choose one actual root-route profile
and justify its index correspondence, rather than assume all events of a bearer
instantiate one power. Publication still requires independent semantic challenge
of this new adapter outcome.

### Focused verification of the adapter slice

The coordinator subsequently supplied copied pinned packages and a completed
warm build, resolving the earlier readiness gap. Under
`flock /tmp/moenarch/truth-core-heavy.lock`, through `worker_env.py`:

- `lake build TruthCore.Results.Causality.CapacityInterface.Solution` passed.
- `truth bind-check --result d26f85e9-262c-426d-888c-2a09fef96a17` reported
  **1 bound, 0 pinned, 0 mismatch**, including the declared capacity sense.
- `scripts/verify-result.sh d26f85e9-262c-426d-888c-2a09fef96a17` passed
  Comparator and its independent NanoDa solution check. The generated frozen
  Challenge contains the expected `sorry`; the Solution contains none.
- The exact certificate's axiom report is `[propext, Classical.choice,
  Quot.sound]`. Its spec permits precisely this standard policy set. The first
  generated zero-axiom config rejected `Quot.sound`; the spec was corrected to
  the actual extensional/classical dependency set and regenerated. No new axiom
  or weakened philosophical premise was introduced. This result is not evidence
  against the intuitionist rival or for excluded middle.
- The existing `DefinitionStatus.lean` exporter, with the new vocabulary as
  `root_module` and only `Capacity.possesses` requested, returned `found: true`,
  `kind: projection`, `proof: false`, `parameter_wrapper: false`. This is focused
  evidence for the explicit primitive boundary, not a shared-cache refresh.

Offline corpus validation, bundle audit, module-format check, spec regeneration
check, sense/definition/lexicon ratchets and whitespace check passed. Lexical
backfill warnings and missing generated status entries remain visible. No global
allowlist, generated formal-status cache or import aggregator was edited.
The existing transmission-boundary verification supplied by the coordinator was
not repeated. The computed frontier delta against
`38fc9e1f33691eb5735e730f5154eaf98e89c6f9` is **no change**, zero support
alternatives added on root routes. The local checks cover the unchanged final
Lean sources and binding; later prose changes record their outcome and do not
alter the checked theorem. The exact new result ID above is the reproduction
entry point. Independent review of this new consequential interface, shared
import/status generation and delivered-head integration CI remain outstanding.

### Adapter and role integration review (2026-11-17)

Independent semantic challenge of f4058906f5c494a86bd6d9b6f426c227a62adad7 by GPT-6.1 Sol found no findings across the 14-file delta. It confirmed exact factorization agreement, scenario collisions, event-retaining fallback, fixed-respect transport, primitive obligations and preserved consumer formulas. Mechanical verification was reused, not repeated. Next is one explicit Cogito consumer adoption with a justified intellectual-effect respect and retained exercise-to-capacity premise.

### Selected intellectual-capacity Cogito consumer (2026-11-17)

**Complete proposed outcome for independent semantic challenge.** The sibling
`CogitoCapacityInterface.inhabitedFromSelectedCapacity` explicitly applies
`Round4Revisited.inhabitedFromPower` to `bearerProfile p intellectualEffect`.
It concludes the **existing** `InhabitedConcreteAt m concrete w`, statement
`56f68b40-9737-59a0-8cac-5610980a1547`, with precisely the six premise statements
of argument `fe08da3c-27e2-5f0c-b688-400e583d0be3`, in the same order:
`e81971f1-601c-57f5-be2d-c4b0624d0cad`,
`30e6e01c-b7f1-536c-86ae-0a9be35dd160`,
`8cf54bde-0c97-5428-9179-0d567293675d`,
`8061edec-5af6-5d25-81b4-e1ccd98207fa`,
`c821487b-9c5e-5836-bf27-dcb47f210c94`, and
`61b6e188-39aa-57d9-9e0b-dedc05226995`.
The sibling argument is `660673ca-0506-42b2-9265-00c96fb52cf4`, result
`39454df8-dd97-46b5-afe8-7ac84a0443b1`. It is honestly classified as
`instantiation`: consumer adoption supplies no new independent warrant or
premise discharge. The original frozen contracts remain untouched.

Here the **selected intellectual effect** is performing an act of understanding
or judging, under suitable cognitive conditions. It need not be the production
of an inner word, a separate object or an external change. Possession means
ability for that operation whether or not exercised. A judgement exercised by
its bearer is an intended application of the exercise-to-capacity premise;
mere storage of a sentence, or a capacity for locomotion alone, is not that
application. These are analyst interpretations with attribution deferred, not
new empirical or historical findings. The generic respect parameter permits a
specified operation/content class; the theorem does not warrant substituting
an arbitrary effect for the intended intellectual effect.

No extra capacity definition is needed: `Capacity.possesses` is the existing
interpreted primitive, with its open effect, conditions and applicability
obligations. Naming `intellectualEffect` makes the application explicit but does
not complete a reductive analysis. Suitable conditions must be specified in an
application without defining them retrospectively as whatever yields success.
The structure contains no causal mechanism or activation law. The existing
`IntellectualExerciserHasPowerAt` premise carries the substantive claim that
an attributed exercise entails the selected ability. It remains unproved;
its converse (possession entails actual exercise) is neither used nor asserted.
The capacity-to-concreteness premise and the selected-world existence bridge
remain equally explicit. No premise says that every event of a bearer is one
power, or that every existent possesses the selected intellectual capacity.

**Old/new formulas.** `SelectedMapping power p r w` is exactly
`∀ b, power w b ↔ p.possesses w b r`. Under this explicit assumption,
`formula_transport` proves equivalence of each of the old exercise-to-power and
power-to-concreteness formulas with its fixed-respect version. Agreement at
other worlds, on other respects, or about event identity is unnecessary for this
consumer. This is a sufficient local mapping for transport, not a claim that
equivalence of these two formulas alone forces pointwise agreement.
`thinRecovery` actually consumes the checked generic
`CapacityInterface.certificate` (result `d26f85e9-262c-426d-888c-2a09fef96a17`)
for `bearerProfile (fromBearer power) () = power`. The sibling consumer accepts
an arbitrary indexed capacity and selected respect, beyond the Unit embedding.
The new certificate result is `401885b1-4a3a-49c6-8d74-a5eba441d304`, statement
`e68fba46-8eb7-4d84-b8cb-ebf97eaef4fc`.

**Discriminating models.** One world, bearer and episode are Unit; the episode
occurs, is borne and is attributed an intellectual exercise; the bearer exists.
There are two respects, Bool. `otherPower` is possessed only at false, while the
selected intellectual respect is true. Nothing is concrete.
`MissingActivation` retains all four noncapacity premises and
power-to-concreteness (vacuously for the absent selected capacity), while
exercise-to-selected-capacity and the conclusion fail. Despite its short name,
this tests the *exercise-to-possession* direction, not possession-to-activation.
Thus an actual exercise is not identified definitionally with capacity.
`MissingMapping` instead makes the old thin profile everywhere true: old
exercise-to-power and selected-profile-to-concreteness hold, but their local
mapping and the conclusion fail. This is a concrete mixed-profile inference
failure. The original old-profile concreteness premise would be false here;
the model is not advertised as satisfying the original complete bundle.
Neither model supports doubt about actual exercise or real capacity: each
establishes only the precise logical omission failure it was built to test.
No substantive objection to the scoped conditional adoption was identified.

**Claim/type self-sweep.** The consumer retains the exact six premise constants,
world, bearer, episode and concrete predicate, with the identical fixed-respect
profile in both capacity premises. The independent formula/control certificate
has no external premises; its universally quantified mapping occurs inside a
conditional, not as an asserted global correspondence. The derived occurrence
to population bridge is annotated as the conclusion of the complete bundle;
the capacity-to-concreteness premise is the explicit bridge to the chosen
CONCRETE_6 predicate, not an equivalence of causal and esse criteria. No new
source/claim record, owner commitment, primitive, sense or allowlist is added.
The raw `concrete` parameter still needs its intended esse interpretation; the
Lean theorem does not establish that interpretation. No sourcehood, finite
support, persistence, necessity or root truth is inferred.

**Premise comparison and root connection.** The existing conclusion reaches the
Catholicism root in the corpus graph; the context command reports no enumerated
root route specifically touching this argument. We add an explicit sibling at
that same graph destination, not a newly established route or a discharge.
The computed `truth frontier-diff --base
d69634db451aabb99ba0be7f2c231747169a478f` reports **no change**: root-reaching open
premises 490 → 490 (349 bare, 90 supported, 51 stated), lowest expanded route
cost 16 → 16, verified support alternatives 489 → 489, added 0. This is expected
for an instantiation plus a transport/control certificate; no premise is
removed or replaced. Direct assumption and all previous support options remain.

The bounded semantic question is answered conditionally: this actual Cogito
consumer can use a specified intellectual-effect profile without global event
collapse or an existence-to-that-respect principle. Actual applicability still
requires interpreting the intellectual operation, its suitable conditions,
exercise attribution and the two metaphysical bridges. Next discriminating
work is to defend that exercise-to-ability application on a specified judgement
and conditions, or compare a positively justified rival account of that same
operation. No unsupported rival is invented. Independent challenge should test
the selected-effect interpretation, formula correspondence, finite witnesses,
bridge annotations and the instantiation/closure boundary before substantive
integration.

**Worker evidence and exact readiness boundary.** Checkout:
`/home/moenarch/.t3/worktrees/truth-core/t3-fa5a0c4a-037c0c7f5743a85b`,
baseline `d69634db451aabb99ba0be7f2c231747169a478f`. Shared conventions were
read from the supplied resolved stack, sourceRevision
`15f348b072188255da837578eaafc8a98f12fdf0`. No preflight was repeated.
The worktree initially lacked `.lake`; direct focused Lean compilation used
read-only warm parent imports with temporary local output modules under
`/tmp/cogito-capacity-olean`, through worker_env and the heavy-job lock. Vocabulary,
Solution and generated Challenge compiled; only the expected frozen Challenge
`sorry` warnings occurred. This is new-module compilation, not a full Lake build.
The two-result BindTypes export against those modules reports **2 bound, 0
pinned, 0 mismatch**. The command still exits 1 on a global Maximal/Maximum alias
report (`4f1d0cf6`); no unrelated alias repair or allowlist change was attempted.
Comparator starts its own sandboxed `lake build` in this unprepared worktree,
attempts to fetch mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`,
and fails `cannot exec 'remote-https': Permission denied`. This is an environment
readiness failure, not a theorem rejection; no cold build was continued.
Comparator/NanoDa remain **unverified for this slice**. The coordinator should
prepare the warm local artifacts, then run scoped binding and
`scripts/verify-result.sh` for the two new result IDs above, reuse the unchanged
focused proofs, and retain required final CI. Generated imports, status caches
and any global alias reconciliation remain coordinator-owned.

Axiom inspection on the compiled final modules reports **none** for
`inhabitedFromSelectedCapacity` and `certificate`; `thinRecovery` inherits
`[propext, Classical.choice, Quot.sound]` through the reused generic certificate.
Spec regeneration is unchanged; offline `truth check` and `git diff --check`
pass (existing/backfill lexical and status warnings remain). The generated
certificate dossier was inspected after recording the attempt. These results
are focused evidence only and do not change the pending gates above.

### Cogito integration checks (2026-11-17)

The coordinator's prepared checkout verified both new results with Comparator
and NanoDa. Scoped binding passes with two bound, zero pins and zero mismatches;
the baseline Maximal/Maximum alias exceptions were retained separately. The
integrated offline corpus check, bundle audits and spec regeneration pass.
Result references in the attempt summary were moved to its supported evidence
field; the exact argument/result mapping remains in this note. No theorem or
philosophical meaning changed. Independent semantic challenge is still pending.

Independent GPT-6.1 Sol challenge of worker 311134df9374d4107715e7f2fc66614ffa4fd25c
and coordinator repairs at b059c1ceec604e1fcd2986a1654107be297060c8 found no
corrections needed. It confirmed the actual original-theorem application, six
contracts, fixed profile, local transport, exact omission bundles, sense bridges
and instantiation boundary. Actual applicability and premise warrant remain open.
The next application question concerns one specified judgement and independently
described suitable conditions; it is not a missing generic transport theorem.

## #319: applying the two uniting-cause interfaces (2026-11-17)

**Complete proposed outcome for independent semantic challenge.** At baseline
`cd1c362d14100936c602a48b3c54508a4dca33ad`, the bounded question is what warrants
`STMT-UNITING-CAUSES-PRESENT` (`7ce040a2-7e9c-58e0-8ec1-ce99a60b587b`) and
`STMT-UNITING-CAUSES-ARE-ACTUAL` (`53a4f189-099c-52ab-bd6c-f53251c9e294`)
for the **same** alleged uniter and actual target, in the esse respect. The
answer is restricted: independently warranted effective contribution to this
target's being gives a positive rationale for presence and causal inclusion;
composition, functional individuation and a record of generation do not by
themselves establish that contribution. This sharpens application conditions;
it supplies no new formal premise discharge or universal conservation proof.

The current issue body/comments, both dossiers, related results, brief and
novelty retrieval were inspected. Prior work already records the restricted
productive rationale and historical/structural alternatives. This is a
consumer-specific clarification of that evidence, not discovery of a new
conservation argument. `context NECESSARY-UNION-COMMON-NONCOMPOSITE` and the
seed's brief report **no current enumerated Catholicism-root route through this
result**. The graph destination is the existing same-witness #319 conclusion
`740a44f0-b77d-55b2-bd1b-8517ff85d02a`; a further connection into an active root
route is OPEN. Independent review confirmed zero premise consumers of this
conclusion in canonical argument records and its absence from the complete
backward root closure. The missing downstream step is a registered consumer
connecting its existential same-witness tuple to a named root-reaching
obligation. The tuple supplies neither maximality nor God identification; its
witness cannot replace a classical-route witness without an explicit bridge.
The issue's intended role must not be reported as an existing root derivation.

### What the actual consumer asks for

`UnderivedNonComposite.from_union` imports #636's `causal_from_union` and keeps
its witness n. Assuming `Composite n`, the existing q.3 a.7
`CompositeHasAUnitingCauseReading` supplies one c with `c ≠ n` and `CausesIn c n esse`. Presence supplies
`m.ExistsAt w c`; correspondence supplies `m.Causes w c n`. Sourcehood of this
same n excludes that incoming edge. No replacement of n by another source is
permitted. The target is already present; its presence does not supply c's.
The declaration is
`TruthCore.Latin.Aquinas.SummaTheologiae.CompositeHasAUnitingCauseReading`.

Both interface definitions quantify over **all** distinct cause/target pairs
with the displayed guards at the selected w. An independently defended case
therefore illustrates their rationale without establishing these quantified
premises. The proof uses them only at its generated pair c,n, but a proof-local
use does not weaken the registered premise's scope. No narrower sibling is
introduced: the missing result is warrant for application, not another lambda
that packages the same implication.

World locality is also not temporal simultaneity. `Ontic` supplies worlds and
accessibility, no time index; `CausesIn` has neither. A sustaining application
must specify which situation its predicates represent. Saying “at w” cannot
by itself mean “exercising now.” Conversely, sustaining production need not be
motion, a succession of replacement creations, or a temporally earlier act.
The existing q.104 discussion permits continuing esse-giving without those
features. No times-as-worlds substitution is made here.

### Positive warrant and its application boundary

The positive argument starts with a real contribution, not an unexplained
predicate: if c effectively gives or sustains x's being in the selected
situation, the productive basis cannot consist solely of an absent candidate
or our description. There is something actually responsible for the effect.
This supports cause presence **provided that the responsible bearer is the
same c**, represented in the chosen existence domain. A past activity, a law
sentence and a currently existing bearer with unused capacity do not each
supply that identification. The argument does not require materiality, exclusive
sufficiency, an independently prior proof of every causal primitive, or a
separate cause for each temporal instant.

Correspondence then requires that `Ontic.Causes` include this actual kind of
effective esse-contribution. If it denotes only local changes or originating
events, a sustaining or primary cause working through secondary agents is not
included merely by calling the relation ordinary causation. If it already
includes the independently identified productive contribution, inclusion has a
positive semantic rationale: the very dependence described by the first
relation falls within the second's specified scope. That is not an equation
of the two relations. Its application must preserve c, x, the selected situation
and the esse effect. Relabeling an organizing principle as an efficient agent
would assume the disputed step.

`ActualCauseSupportsEsse` is a further interface, not part of either argument
above: it maps **every** ordinary edge with actual endpoints to R. Ordinary
event causation need not support the target's esse. The existing
`UnderivedEssenceEsse.actual_not_not_identity_direct` instead consumes
`ActualEsseCausesSupportAt` on the actual q.3 esse-cause pair; its existing
`TypedCorrespondenceControl` retains an event edge while the broader map fails.
These are already encoded/tested distinctions. No new adapter or replacement
proof is needed. For the noncomposition consumer, absence of incoming ordinary
causes is already obtained through #636; retaining that result also retains
#636's broader mapping premise. This note does not silently remove it.

### Standing alternatives and replies on the same target

The historical account has a specific mechanism: a generator establishes an
arrangement, after which the materials and their maintained relations account
for its persistence. The existing house/builder discussion in
[composition-causal-scope.md](notes/composition-causal-scope.md#source-discrimination-immanent-unity-becoming-and-continued-esse)
and the recorded retained-heat contrast support distinguishing origin from
current production. Even a builder who remains alive is not thereby still
building that house. Thus **actual endpoints alone** do not convert historical
production into present exercise. This challenges the application of
correspondence when `CausesIn` is read historically and `Ontic.Causes` as present
productive dependence. It is not a counterexample to presence of a genuinely
sustaining cause. A history-inclusive graph could retain the old edge, but then
its sourcehood would be a different causal question from present support.

The structural account explains the current bearer through actual constitution
and organization. Its affirmative explanatory role is the dependence of the
bearer's identity and operations on that constitution, with the replacement
and priority qualifications already recorded in the composition note. It
challenges the uniter-to-productive-esse inference: prerequisites of being this
organized thing do not identify a distinct agent currently giving its bare
esse. Treating the arrangement as c can additionally change the candidate
domain from beings to structural facts. This is a concrete mismatch of role
and domain, not a merely conceivable objection to causation. The account still
owes its direction of constitution and adequacy for the actual target; no
universal sufficiency or whole-first priority is inferred here. The settled
#336/#331 ordering and organ-to-derivative-power audit is not reopened.

The positive external-giver response is stronger than “the parts need a tie”:
if this bearer's esse is genuinely received, rather than explained solely by
its constitution or past, its present receipt calls for a real giver in that
respect. Given that productive application and the specified causal inclusion,
the two interfaces are well motivated. What remains disputed is the receipt
and coverage claim for the allegedly composite underived n. Borrowing an
already identified God's universal conservation to establish that pre-divine
application would not supply independent warrant for this route.

The historical-law persistence account already preserved in
[eternity-dependence-connection.md](eternity-dependence-connection.md#existential-inertia-the-live-rival-and-the-remaining-bridge)
adds earlier existence plus absence of destructive change; it is not merely
brute persistence. Its strongest recorded challenge concerns whether the past
and persistence powers suffice to account for current existence. Neither
response is settled by endpoint presence or the composition label. No new
historical attribution is made; these references reuse recorded findings,
not a fresh reading of their external witnesses.

### Disposition, rejected paths and next discriminating test

The interfaces receive a **restricted positive application rationale**, not an
unconditional verdict. Historical generation and real constitution explain
why their extension to arbitrary alleged uniters needs the specific productive
step. No substantive objection to the conditional inference *once that step
and the causal inclusion are warranted* was identified. None of the standing
accounts has been refuted, and none is certified adequate merely by surviving
this comparison. Actual target existence, cause presence, productive activity,
ordinary causal inclusion and R-support remain separate obligations.

Rejected paths: inferring current giving from two existing endpoints; inferring
cause actuality from target actuality; reifying an arrangement as a second
agent; treating non-self-production as proof of external production; extending
illumination of air to the air's substantial esse; identifying ordinary event
causation with R; and adding a transport/omission theorem already provided by
#655 and UnderivedEssenceEsse. Each rejection concerns the named inference or
application, not an evidential penalty for open primitives or shared premises.

The precise remaining dependency is positive same-bearer **esse receipt** for
the selected candidate and a scope argument reaching the c,n generated by the
composition premise. Existing illumination work establishes a state of an
already existing bearer and explicitly leaves that dependency open. Repeating
it, the organ audit or generic omission assignments cannot supply the missing
evidence. This application gap is separate from the downstream #319 gap above.
Reallocate receipt work explicitly to the existing root-reaching statement
`732302a1-f7bf-594d-9a8a-cb4bd00687a7`,
`ParticipatedEsseHasDistinctCause`, using the connection plan in
[eternity-dependence-connection.md](eternity-dependence-connection.md).
Test an existing received-being argument for same-substantial-bearer positive
esse receipt, coverage, source distinctness and local receipt-to-CausesIn
correspondence against historical-law persistence. This names a destination
with existing root-reaching consumers; it does not establish any of those
application premises or connect the #319 existential tuple to the root.
No divine identification is assumed. Independently justified productive receipt would favor
the external-giver application; an adequate constitution/history account of
that same esse would weaken its asserted necessity. A new actual uniter with
specified productive role would also reopen application here. These are exact
research dependencies, not a request for an owner-selected metaphysical winner.

**Claim/type self-sweep.** Only this note and the existing attempt are changed.
No definition, statement, claim, theorem, frozen contract, sense, source witness
or computed status changes. The quantifier and world/time limits above are
those of the unchanged definitions; no proposed universal interface is claimed
proved. The existing same-witness proof, direct support consumer and omission
controls are reused, with no new metaphysical possibility claim. Independent
semantic challenge of this complete proposed outcome remains required before
its substantive judgment is integrated.

**Worker evidence.** Live convention resolution matched supplied sourceRevision
`15f348b072188255da837578eaafc8a98f12fdf0`; repository policy and research/reuse
skills were read. Authorized warm preparation copied pinned packages, checked
their HEADs/cleanliness and seeded the build through the existing helper under
the heavy lock; it is readiness evidence only. No worker preflight repeated.
Through `worker_env.py`, offline `truth check` passes with existing lexical and
formal-status warnings; `attribution-check --base
cd1c362d14100936c602a48b3c54508a4dca33ad` reports no new or changed stating
claim. `git diff --check` passes. Computed `truth frontier-diff --base
cd1c362d14100936c602a48b3c54508a4dca33ad` reports **no change**: root-reaching
open premises 494 → 494 (353 bare, 90 supported, 51 stated), lowest expanded
route cost 16 → 16, verified support alternatives 494 → 494, added 0.
No Lean or binding inputs changed, so no new proof-verifier result is claimed
and unchanged proof checks are not repeated. Fresh semantic challenge and final
integration CI remain coordinator-owned. No PR, push, watch or merge.

Coordinator review disposition: independent challenge accepted the restricted
conditional rationale and found one allocation P2. The repair above separates
application from downstream connection and names the root-reaching receipt
target; it adds no graph edge or philosophical premise. Unchanged semantic and
mechanical evidence is reused; final integrated CI remains pending.
