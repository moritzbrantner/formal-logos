# PRD: Root-local goodness of an ultimate existential source

[Original PR #1917](https://github.com/moritzbrantner/formal-logos/pull/1917)

- **Project** Formal Logos (`moritzbrantner/formal-logos`)
- **Date** 2026-11-24
- **Status** Independently reviewed research specification merged in PR #1917 at `233857c34`. Formal implementation remains open.
- **Target** `00e962ae-f109-55f7-a7fd-f107ce0dea6b` — `GoodnessIsActualityReading`
- **Primary consumer** `e0dae79f-c042-5a08-a148-725d0468df91` — `GodIsSupremelyGood`
- **Evidence baseline** Repository evidence at `0ce1e78ed5e42962586356631a778e24a832c546` and historical route analysis at `fd78b77e6`.
- **Publication disposition** The owner authorized publication as a draft documentation checkpoint on 2026-11-24.

## 1. Executive decision

Preserve the unrestricted goodness–actuality thesis as a separate open proposition. Add a narrower, independently assessable **forward goodness principle at esse** and an optional **subsistent-esse-specific support route**. Keep the existing causal goodness endpoint and every frozen Challenge unchanged. Integrate new arguments as sibling support options, not semantic replacements for the original statement.

The substantive finding is that the existing divine-goodness result does not need a general theory evaluating every positive determination. After independent selection of the source and proof of its causal responsibility for the actual perfections of distinct effects, the exact remaining pointwise obligation is `GoodIn n esse`. Under #1116's existing due-actuality thesis, and given actual esse, that obligation is equivalent to `Due f n f.substantial` when the dictionaries and substantial respect are correctly identified.

The direct philosophical case is that constitutive actuality supplies a non-instrumental ontological good. The selected-source subsistence argument needs actual esse, subsistence in the intended reception profile, and a positive evaluative bridge at that same source. The bridge from constitutive perfection to desirability is the open step.

## 2. Scope, requirements, and non-goals

### In scope

- Establish the exact logical goodness residual with the original causal background held fixed.
- Compare unrestricted, esse-only, maximum-local, and identity-guarded readings without conflating their eligibility conditions.
- Connect the existing form/end account locally; investigate the grounding of due status rather than assume a favorable assessment table.
- Reuse independently established same-source essence–esse identity where already available. Reorder derivations if necessary; never infer identity just from relative maximality.
- Preserve the distinction between ontological, intrinsic, causal and moral goodness and document which consumers need which scope.
- Compare the strongest neutral-source rival and distinguish privation from absence of positive goodness.
- Provide formal sibling specifications, finite controls, an explicit premise-effect contract, and review/verification gates.

### Out of scope

This specification contributes one scoped investigation to the open #1116. The general definition campaign, moral-first argument (#1812), divine-love investigation (#1732), redefinition of `IsSupremelyGood`, adoption of new floor items, proof of universal perfection transfer, and general modal-necessity investigation are outside its scope. Source claims and formal integration belong to separately reviewed work.

## 3. Existing implementation and exact proof use

[`GoodnessIsActualityReading`](../../TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/Question5/Article1.lean#L50) identifies goodness and actuality at each bearer and respect.

[`IsSupremelyGood`](../../TruthCore/Case/Catholicism/StageTwo.lean#L100) requires goodness at esse and causation of every perfection of the other bearers.

`GodIsSupremelyGood` universally quantifies this over supplied `IsGod` witnesses. In the original `godIsSupremelyGood` proof, the entire use of the unrestricted goodness thesis is `(hGoodness g esse).mpr hMax.1`. The restricted causal-transfer sibling (`CausalPerfectionTransfer.goodness`) and `DirectEsseRootPerfectionGoodness.supremelyGoodOfMaximum` use the same goodness instance. Their causal premises differ.

Let A(x,r) denote `InAct x r`, G(x,r) denote `GoodIn x r`, M(x) denote `IsMaximumIn InAct MoreIn esse x`, and C(x) denote `CausesEveryPerfectionOfOthers InAct CausesIn x`. All use the same respect and bearer dictionaries.

Each residual proof holds its consumer's causal background fixed. Let U(c) denote `CausesAllInGenus InAct CausesIn esse c`, which requires c to cause the esse of every other bearer actual in esse.

| Consumer | Transfer premise |
|---|---|
| Original stage-two `godIsSupremelyGood` | `CauseOfBeingCausesEveryPerfection` (`f8ba2429`). For every c, x and r, `CausesIn c x esse` and A(x,r) imply `CausesIn c x r`. |
| `CausalPerfectionTransfer.goodness` and `DirectEsseRootPerfectionGoodness.supremelyGoodOfMaximum` | `UniversalCauseTransfersPerfections` (`b26c10a0`). The same inference requires U(c) and x ≠ c. |

For a supplied maximum n, the applicable genus premise gives U(n). For each distinct x with A(x,r), actuality-to-being gives A(x,esse) and U(n) gives `CausesIn n x esse`. The applicable transfer premise now gives `CausesIn n x r`, yielding C(n). This yields the proposed exact residual:

> `IsSupremelyGood ... n ↔ GoodIn n esse`.

The forward direction projects the first conjunct of the endpoint. The backward direction pairs the supplied goodness with C(n). In both stage-two versions, the corresponding universal residual is `GodIsSupremelyGood ... ↔ ∀ g, IsGod g → GoodIn g esse` under the given version's God-to-maximum, genus, actuality-to-being and transfer premises. The four-role concurrent control in §8 tests the selected-witness equivalence with restricted transfer. The existing stage-two singleton control tests omission of goodness under the unrestricted background.

This establishes what is logically sufficient and necessary **relative to that background**. It does not justify the remaining goodness predicate or assert existence. Without the causal background, the equivalence fails; the already verified secondary-only omission control `DirectEsseRootGoodnessOmission` gives a source good in esse without supreme causal goodness.

## 4. Proposed scope alternatives

| Candidate | Exact proposition | Intended use |
|---|---|---|
| Original `00e962ae` | ∀ x r, G(x,r) ↔ A(x,r) | Preserve all existing consumers and direct-assumption option. |
| Esse-forward | ∀ x, A(x,esse) → G(x,esse) | Main reusable candidate: no reverse direction or other respects. |
| Maximum-local | ∀ x, M(x) → G(x,esse) | Pre-naming sufficient interface; may include finite relative maxima. |
| Identity-guarded | ∀ x, esseOf x = essenceOf x → A(x,esse) → G(x,esse) | Sufficient interface where the consumer already derives represented identity. The universal bridge is open. |
| Selected-source | G(n,esse) for the already selected n | Exact pointwise residual, not by itself a philosophical argument. |

Original implies esse-forward, which implies both maximum-local and identity-guarded. The latter two guards are incomparable with unlinked eligibility. A link from maximum to represented identity lets the identity-guarded rule supply the maximum-local one. A link from actual represented identity to maximum lets the maximum-local rule supply the identity-guarded one. At a selected n with both eligibility conditions, either rule gives G(n,esse). If n is the unique maximum, maximum-local is equivalent to G(n,esse) under that background.

The universal `IsGod`-guarded residual is the exact goodness requirement for the universal endpoint under the corresponding causal premises. The pre-naming alternatives use supplied metaphysical eligibility. A case for the selected witness supplies G(n,esse). Any further eligible bearers still need warrant to support a universal rule. §5.2 describes one case for n.

### Recommended implementation order

1. Exact residual lemmas and scope comparison; use the unchanged causal dictionary and consumers.
2. Esse-forward sibling first, because its positive content is directly about being and it can be used by existing modal-free stage-two signatures without adding identity, modality, or an extra witness.
3. Identity-guarded route as a separate alternative where represented identity is already obtained independently. Treat the selected-source subsistence argument as a separate way to supply its goodness obligation, with the reception and evaluative premises in §5.2. The goodness inference itself uses actuality at n.
4. Keep form/end and source-constitutive warrant explicit. Do not turn `GoodIn` into a definitional alias of actuality or due status.

## 5. Philosophical investigation: is esse itself a genuine good?

### 5.1 Direct constitutive-actuality route

**Claim:** Actual esse constitutes an intrinsic ontological perfection of its bearer, rather than merely an enabling condition for desirable outcomes.

Consider the difference between the kind of being one has, the act by which one actually is, and subsequent determinations of an already actual bearer. An actual eye can lack sight. Substantial actuality and the failure to realize an operation can coexist. The eye and privation examples distinguish the respects of evaluation, while a descriptive neutralist can accept the same distinctions.

The positive warrant has three steps:

1. **Constitution:** actual esse is the act by which the nature is actually instantiated, not merely a condition external to that subject.
2. **Fit:** in respect of being itself, the actuality constituting that subject realizes the relevant constitutive standard. This is an ontological standard, not a claim that every possible subject ought to exist or that the universe is better with it.
3. **Evaluation:** the fulfillment in (2) is an intrinsic perfection of the bearer and, as such, a fitting object of natural appetite. On the account of good as desirable, this gives positive ontological goodness in that respect. The discriminating commitment is that constitutive perfection in esse is desirable in this sense. The tendency toward actuality and the preservation of attained being are offered as evidence for an end-directed account of esse in the sources discussed in §6.

These steps support esse-forward within its intended domain. The strongest neutralist can accept (1) and (2) as descriptive, interpreting the dispositions to persist and realize characteristic operations as features of a nature. That account disputes step (3), where fittingness must have evaluative force. Instrumental necessity for further goods is shared by conditions that also enable harms, so it supplies no verdict here.

The argument does not assert that every essential predicate is a good in every sense. For example, toxicity constitutive of a particular kind can be good-for its characteristic function but bad for another organism. Nor does the argument rank entire lives against never having existed. A subject can suffer catastrophic privations while retaining a positive existential actuality on this reading. A rival that denies even that limited ascription, rather than disputing welfare, directly targets the premise.

### 5.2 Subsistence and an internal standard

The existing same-source derivations give represented equality `p.esseOf n = p.essenceOf n`. For the subsistence argument, reuse `Q44SourceSupply.ownBeingOfIdentity` with that equality in the matched reception profile. Its four premises require reception only in the bearer's own essence (`6dfe01ab`), the receiver's potency to received esse (`7fcfcee8`), irreflexivity of receptive potency (`14325c83`), and the inference from unreceived esse to `OwnBeing` (`bc1810e5`). The first three rule out reception at n, and the fourth supplies `OwnBeing n`. Represented equality alone is weaker than this bundle. [Q44SourceSupply](../../TruthCore/Results/Causality/Q44SourceSupply/Solution.lean)

At the same independently selected n, require `InAct n esse` with the esse respect and actuality matched to that profile. The positive case is that unreceived, actual esse realizes the existential standard intrinsic to what n is. That constitutive fit still needs the evaluative bridge in §5.1 step 3. In form/end terms, the same application requires a defended `Due f n f.substantial` and the positive due-actuality rule of §5.3, with the dictionaries matched at n. These are ways to support the selected witness. Warrant for the universal identity-guarded rule would need to cover every bearer satisfying its represented equality and actuality antecedents.

This reading treats the source's act as internal to its own being. The absence of a receiver or external measure leaves the positive standard open on its own. The limiting principles, further due perfections, and actuality of other pure perfections remain distinct questions.

Do not define the due standard as whatever the source actually possesses. That would make arbitrary positive determinations good by construction. Independently fix the standard by what constitutes actual being, not by a list of properties observed in an already selected source. For creaturely form/end comparisons, natural aptitude does not necessarily require unrealized potency: the term must admit a fulfilled nature. For subsistent actuality, the form/end profile requires explicit interpretation; assigning `form := essenceOf` and `end := source` is not evidence that the supplied `DueFor` represents an actual intrinsic standard. No assumption that God is already the final end of all things is required for this narrow conclusion.

### 5.3 Exact bridge to #1116 (new restricted boundary)

The existing `GoodnessFormEnd.Frame` defines `Due f x p` by `DueFor` at that bearer's supplied form and end. `DueActualityThesis f` says `GoodIn x p ↔ Due f x p ∧ Has x p`. `GoodnessDueToUnrestricted.dueToUnrestricted` uses `AllActualitiesDue f` to recover `00e962ae`.

Given the thesis and substantial actuality at n, goodness at that respect is equivalent to due status. [`goodIffDueAtSubstantial`](../../TruthCore/Metaethics/FulfilledRespect.lean#L38)

Across bearers, the rule assigning goodness to every actual bearer at the substantial respect is equivalent to assigning due status there. [`substantialGoodnessIffDue`](../../TruthCore/Metaethics/FulfilledRespect.lean#L45)

The latter is conditional on `DueActualityThesis f`. In the positive direction only, even the full biconditional is unnecessary: a local rule `Due f n f.substantial ∧ f.Has n f.substantial → f.GoodIn n f.substantial` suffices. Keep the full existing thesis as a support option; do not pretend the restricted normative bridge is established by writing it as a definition.

Under the full due thesis, the exact missing input at an actual n is `Due f n f.substantial`. Its independent warrant requires an interpretation of `DueFor` that gives the bearer a constitutive existential standard. If due status is read descriptively, the positive due-actuality rule also needs the evaluative warrant of §5.1 step 3. Link the existing dictionaries (`Has = InAct`, the same `GoodIn`, and `substantial = esse`) explicitly, or express the proof directly in the existing parameters.

### 5.4 Privation, pure perfection, and arbitrary positive determinations

`EvilIsPrivationReading` in q.48 encodes `Evil x ↔ ∃ p, Due x p ∧ ¬ Has x p`. Having every due actuality excludes evil in this sense and leaves `GoodIn x esse` open. `UltimateDuePerfectionRequiredReading` encodes only the exclusion of `GoodSimply` in the absence of due ultimate perfection. ST I q.5 a.1 ad 1 also ascribes relative goodness in primary actuality and goodness simply in complete actuality. The positive ascriptions are additional textual warrant beyond that Lean exclusion. [ST I q.5 a.1 ad 1](https://www.newadvent.org/summa/1005.htm)

Actual perfection must be assessed in a fixed respect and sense. A pure perfection is not merely any positive predicate. Even a universal `IsPerfect InAct n` in the existing respect dictionary is not a declaration that every described state is appropriately possessed, morally good, or free from all limitation. Keep the already separate pure-perfection and formal/eminent-possession questions independent. In a model of arbitrary positive determinations, an actuality in another respect can be non-due while esse remains due and good. Do not attribute such a model, without further metaphysical realization, to an absolutely simple Thomistic source.

### 5.5 Causal desirability is supporting evidence, not a substitute

If effects have intrinsically good actualities, and the source genuinely exemplifies or supplies them, there is a reason to regard the source as an objective ground of those goods. But a source good *for* something need not have intrinsic goodness solely because it is an efficient means to it. To infer intrinsic goodness via causal desirability requires the further perfection/likeness and non-instrumental desirability commitments. ST I q.6 a.1 supplies the historical route; do not use `f8ba2429`, `64498e7e`, or an effect's goodness by themselves to erase this distinction. This is a cumulative route, not a second independent proof of the same proposition from causation alone.

## 6. Source findings and attribution boundaries

Selected external passages were read as research evidence, not imported or certified against a pinned corpus witness. Before creating a claim, use the canonical source-evidence workflow to identify or acquire the exact existing passage, read its pinned witness, and bind it faithfully. A search of the inspected repository found the q.5 a.1 reading, the q.5 a.1 ad 1 exclusion and q.48 privation, not a dedicated esse-only q.5 a.3 statement; confirm with `truth related` and local search before creating new records.

| Passage | Positive contribution | Boundary |
|---|---|---|
| [ST I q.5 a.3, body and replies 2–4](https://www.newadvent.org/summa/1005.htm) | Actual real being is good insofar as it is actual, through the argument from perfection to desirability. The replies distinguish deficiency, merely potential being, and logical being. | Source support for the universal esse-forward rule requires that A(x,esse) pick out actual real being for every eligible x, or an explicit real-being guard. The same boundary applies to all eligible bearers of the other universal guards. |
| [ST I q.6 a.3, body and replies](https://www.newadvent.org/summa/1006.htm) | Distinguishes constitutive being, operation and end. Grounds the first kind in essence/esse identity when discussing the divine case. | The full essential-goodness conclusion uses all three kinds and further divine attributes; identity alone does not establish goodness simply, moral goodness, or uniqueness. |
| [ST I q.6 a.1–2](https://www.newadvent.org/summa/1006.htm) | Causal desirability and analogical supremacy; the source is not compared as a member of a shared genus. | Requires the perfection/likeness account, not mere enabling. The existing case predicate is a restricted formal representation, not every aspect of Aquinas's thesis. |
| [De veritate q.21 a.1–2, especially a.1 ad 2 and a.2 body](https://isidore.co/aquinas/english/QDdeVer21.htm) | Goodness has the character of an end. The argument in a.2 appeals to natural appetite for actuality and the preservation of attained being to support goodness from the act of existing. | The positive rationale depends on interpreting those tendencies as directed toward esse as an end. It leaves open the neutralist's descriptive reading of preservation and the reach of this warrant to the selected source. |

No source quote is used to claim that the new analyst-specific identity guard or the exact Lean residual was stated by Aquinas. Source support and logical consequence remain different statuses.

## 7. Rival comparison and provisional judgment

Compare on one shared task: explain whether and why the selected source has a positive good in its existential respect. Do not penalize an impersonal account for failing to explain morality when the immediate target is ontological.

| Account | Positive explanation of esse goodness | Main surviving issue | Consequence for existing endpoint |
|---|---|---|---|
| Perfect impersonal source with objective constitutive goodness | Actual nature's fulfillment is intrinsically good without anyone's approval. | Must defend objective goodness for non-appetitive reality. Does not explain moral agency. | Can satisfy the endpoint with causal transfer. |
| Intrinsically good personal source | Same constitutive grounding; rational agency may additionally have due perfections and right ends. | Personal status alone does not prove goodness of will; cannot derive love or moral infallibility here. | Same endpoint possible; personality is not required by the goodness proof. |
| Source with arbitrary positive determinations | Positive existence may be good even when arbitrary determinations are not due. | No automatic entitlement to call every actual determination a pure perfection. Needs non-arbitrary criterion for intrinsic standards. | Can satisfy causal goodness while unrestricted coextension fails. |
| Evaluatively neutral source | Structure, existence and causal powers are descriptive facts; normative or evaluative facts attach only where there are interests, ends, or further principles. | Must explain the status of ordinary fulfillment/privation distinctions if it accepts objective due standards; may consistently regard them as merely descriptive. | Denies the remaining intrinsic-goodness premise, even if causal coverage is granted. |

The existing rival `1085f3aa` keeps goodness-to-actuality and asserts some actual perfection without goodness. At the selected source the descriptive neutralist gives a specific account of that failure. It can accept represented identity, maximality, actuality, no privation and causal responsibility while taking constitutive fulfillment and preservation as descriptive facts. If it grants the positive due-actuality rule and due status at the actual source, denying `GoodIn n esse` would contradict those commitments. Its live objection targets §5.1 step 3, which gives constitutive perfection positive evaluative force. [Rival statement](../../corpus/statements/1085f3aa-ebce-4dda-ae98-5406f77c24ba.json)

**Overall provisional judgment:** prioritize esse-forward as the reusable candidate. The positive warrant is the account of actual esse as a constitutive perfection and a fitting end of natural appetite, especially in preservation of being. The descriptive neutralist also accommodates fulfillment, privation and the observed tendency to persist. The assessment therefore turns on the interpretation of desirability in §5.1 step 3. Retain the conditional subsistence argument for the selected source, with the reception and evaluation obligations of §5.2. The scope check supplies a smaller sufficient interface and leaves its warrant open.

**Reopening conditions:** a genuine example of an actual bearer whose constitutive existential actuality is not an ontological good (not merely a bad life or harmful effect); a neutralist account that explains intrinsic due fulfillment without evaluative import; evidence that constitutive-goodness attribution equivocates with instrumental or moral goodness; or a stronger independently warranted bridge grounding due status at the selected source. Pursue these questions rather than new equivalent formulations.

## 8. Formal research and model results

The original author reported an uncompiled `RootEsseGoodnessFollowup.lean` draft, `check_goodness_boundary.py` and `check-results.txt` outside this repository checkpoint. The declaration names below identify proposed results, and the finite assignments are given below. The formal implementation can reuse existing declarations.

| Declaration | Intended conclusion |
|---|---|
| `esseOfGlobal`, `maximalOfEsse`, `subsistentOfEsse` | Exact scope implications in unchanged parameters. |
| `selectedResidual` | Pointwise causal endpoint iff source esse goodness under the corresponding transfer background in §3. |
| `godResidual` | Universal stage-two endpoint iff goodness of every supplied `IsGod` witness, with the hypotheses of the particular stage-two version. |
| `dueResidual`, `dueEsseResidual` | Exact local and esse-forward due boundaries. |
| `godGoodFromIdentity` | Existing simplicity/composition proof of represented equality, followed by the supplied universal identity-guarded goodness rule. |

`godGoodFromIdentity` uses the same `hKinds` branch as `GodIsInfinite.godIsInfinite`; it requires the existing `ExcludedMiddle` at principle identity (or an existing identity-specific decision interface). It needs neither `Infinite` nor an attribute naming conclusion. Do not add stronger logical axioms to a weaker existing route; preserve the local decisions in `ClassicalAttributesIdentity` and `ClassicalAttributesLocalLogic`.

### Existing checked controls

The one-bearer, one-respect `SpineRivalsAttributes.actualityWithoutGoodness_holds` in result `120dd28f` witnesses `1085f3aa` with the other four original stage-two premises. The bearer is God in the model, maximal and actual, with empty `GoodIn` and `CausesIn`. Distinct-effect coverage is vacuous, unrestricted transfer has no causal instance, and goodness-to-actuality has an empty antecedent. The negative endpoint is explained by the missing goodness conjunct. [Lean proof](../../TruthCore/Results/Causality/SpineRivalsAttributes/Solution.lean) · [Result record](../../corpus/results/120dd28f-c1e6-4fa2-8acf-26d0c1d5162a.json)

`DirectEsseRootGoodnessOmission` supplies the complementary secondary-only control. There the source is good in esse and causal coverage fails. A future populated represented-identity control can reuse the role, act, cause, and identity assignments of `RootPositiveIntellectWillControl`. Drop its old `GoodnessIsActualityReading` conjunct and compare `GoodIn` with source esse omitted and restored. Check the retained inputs and the resulting endpoint on the same witness. The existing certificate checks its original goodness assignment. [Populated control](../../TruthCore/Causality/RootPositiveIntellectWillControl.lean)

### Finite table checks

An independent reconstruction checked the following finite comparisons. The assignments and tests are given here so the counts can be reproduced from the note.

| Fixed input | Assignment |
|---|---|
| Bearers and respects | `source` (n), `supporter`, `producer`, `recipient`; `esse` and `skill`. |
| Actuality and order | All eight bearer–respect cells are actual. In each respect the strict order is given by ranks 4, 3, 2, 1 in the listed bearer order, with higher ranks more in that respect. |
| Esse causation | n causes each of the other three bearers. The supporter also causes the recipient. |
| Skill causation | n causes each of the other three bearers. The producer also causes the recipient. |

Every causal pair outside the listed assignments is false. This is the concurrent table `transferCause true`. The source is the unique maximum and the only universal esse cause. Its restricted transfer has actual distinct effects, including skill in the recipient. Unrestricted transfer fails at supporter → recipient in skill, where the supporter causes the recipient's esse and the recipient has skill. [Concurrent transfer model](../../TruthCore/Case/Catholicism/CausalPerfectionTransfer.lean)

- **256 goodness tables.** For each subset of the eight cells, use it as `GoodIn` and keep the concurrent inputs fixed. Test `IsSupremelyGood ... n ↔ GoodIn n esse`, the implication from the original goodness biconditional to esse-forward, and the implication from esse-forward to maximum-local. All pass. Goodness-to-actuality holds automatically in this all-act model. Dropping that reverse direction alone makes no difference on these tables.
- **65,536 actuality/due pairs.** Independently choose any two subsets of the eight cells as `Has` and `Due`, then set `GoodIn` to their intersection. For each pair test §5.3's local equivalence at each bearer with actual esse, its esse-forward equivalence over all bearers, and the unrestricted equivalence with `AllActualitiesDue`. All pass. This is an extensional due table check. Each table can be factored through a formal frame by giving each role a distinct form, taking a single end, and reading the table's role index as that form in `DueFor`. Such a factorization supplies no independently defended form/end standard.

For concrete cells in the all-act table, let E be the four esse cells and eₙ the source esse cell. With `Due = E` and `GoodIn = E \ {eₙ}`, the source lacks goodness, goodness elsewhere is nonempty, and the positive due-actuality rule fails at n. With all eight cells actual, the set of missing due actualities is empty for every due table. With `Due = GoodIn = E \ {eₙ}`, even the full due thesis holds while the source remains neutral. Add eₙ to the due table and impose the thesis with the same actuality table, and goodness at eₙ follows. This restoration stipulates due status. Taking `Due = GoodIn = E` gives universal esse goodness with actual skill outside `Due`, so unrestricted coextension fails.

For the scope comparison alone, assign represented identity only to the recipient, for example by taking `esseOf x = x` and `essenceOf x = recipient` on the role carrier. Then maximum-local holds with only the source esse cell good, and identity-guarded holds with only the recipient esse cell good. Each assignment fails the other rule. This unlinked eligibility control supplies no reception profile or `OwnBeing` interpretation. `GoodSimply`, will and moral goodness lie outside the endpoint's signature.

These finite comparisons test conditional consequences in the specified tables. They leave the interpretation of subsistence, due status and the evaluative bridge in §§5.1–5.3 open.

## 9. Implementation plan and exact downstream premise effects

### 9.1 First checkpoint: reusable results

- Run `truth related 00e962ae`, `truth dossier`/`context --proof-use` and `truth lean-reuse` as appropriate on current main. Search for exact matching candidates and existing sense records; use them if semantically identical. Confirm scope against the canonical `AGENTS.md` and installed conventions.
- Register the reusable esse-forward sibling and exact residual/due boundaries. Use opaque UUIDs, appropriate existing definition/disambiguation records, explicit dependencies and frozen Challenge/Solution pairs with existing module and Comparator conventions. Preserve `00e962ae`, its source claims, and its direct-assumption option.
- Give the candidate independent direct warrant and due/identity support options. If adding q.5 a.3 or q.6 a.3 claims, use pinned passage evidence and scope-limited attribution; do not invent a claim that the passage states the Lean theorem literally.
- Keep no new global axiom, definition of `GoodIn`, modal requirement or source-specific proxy that assumes the desired endpoint.

### 9.2 Consumers and ordering

| Consumer inspected | Required change / exact limitation |
|---|---|
| `StageTwo.GodIsSupremelyGood.godIsSupremelyGood` | Sibling: one goodness input replaced by esse-forward or maximum-local; keep maximality, genus, actuality-to-being and unrestricted transfer unchanged. |
| `CausalPerfectionTransfer.goodness` (`0011703b`) | Same one-input substitution; keep its existing *restricted* transfer `b26c10a0`, do not accidentally reintroduce unrestricted transfer. |
| `DirectEsseRootPerfectionGoodness.derive` (`818f5532` → `469b92a8`) | Reuse `DirectEsseRootPerfection.derive` and the same selected maximum. The esse-forward sibling replaces one goodness input and retains the other 11 inputs, including restricted transfer. Use esse-forward on this interface, which lacks identity premises. |
| `ClassicalAttributes`, `ClassicalAttributesAll`, `ClassicalAttributesIdentity`, `ClassicalAttributesLocalLogic` | Parallel sibling assemblies use the new goodness producer. In the fuller assemblies, simplicity and composition-kind premises already yield represented identity (see `GodIsInfinite` and the inline identity proof). Reuse that derivation before applying a supplied identity-guarded rule. Preserve existing logical floor, the remaining eight attribute obligations, maximality and naming/sufficiency. The minimal `ClassicalAttributes` signature uses esse-forward. |
| `RootPositiveIntellectWill`, `PerfectRootPositiveIntellectWill` | The derivation of `hIdentity` at the perfect-root witness uses none of `hGood`'s content. Start from the prior perfect-root witness, derive simplicity and represented identity, then apply the supplied identity-guarded rule and derive causal goodness at that same n. In `PerfectRootPositiveIntellectWill`, keep the existing uniqueness equality transporting identity from the witness in `ofNonlimitation`. For a selected-source subsistence argument, add the matched reception and evaluative premises of §5.2 where required. |
| `NecessaryClassicalGodRoot`, downstream same-source root families | Use the sibling producer, preserve exact witness, modal inputs where already required, and all nominal/attribute constraints. Audit every consumer's actual proof use; a new lower producer does not automatically migrate flattened theorem types. |
| `DivineLoveBridge.divineWillsGoodForAllExisting` | Its independent goodness use is `(hActualGood x esse).2 hx` at arbitrary recipient x, so root-local goodness is insufficient. Esse-forward can replace this *particular* goodness use, not the existing causal-willing or love bridges. No work on those bridges in this scope. |
| Other users of `00e962ae` (problem of evil, metaethics, comparison/model theory) | No global replacement. They may use a wider per-perfection scope or reverse direction. Preserve all old results. |

### 9.3 Premise delta contract

- Original five-input stage-two goodness arguments retain four other inputs, replace one goodness input with a narrower candidate. Conditional application, not a premise closure. The original 12-input direct root argument retains 11 other inputs in the esse-forward sibling. The direct pointwise residual is equivalent only conditional on its fixed causal background.
- A route through the full `DueActualityThesis` and an appropriate due-esse condition may expose two open commitments instead of one, or a restricted positive rule plus its anchoring condition. This may be better targeted despite an expanded premise count. Never claim a saved premise simply because its name changes.
- An identity-guarded route can reuse represented identity already derived from existing premises where available. The selected-source subsistence route has the additional premises in §5.2. The actual comparison depends on the registered proof and its inputs.
- The merged analysis in #1902 reports all 25 modal-free routes blocked when `00e962ae` is excluded at its historical baseline. New scope siblings could remove that bottleneck for migrated routes. The remaining reductio work is a future research question. [Historical analysis](https://github.com/moritzbrantner/formal-logos/pull/1902)
- The documentation checkpoint changes no registered graph inputs. The original PR head's computed frontier delta was `no change` (§10). Migration and its effects on actual reachability would require verified consuming paths.

After integrating formal siblings and migrating selected consumers, run `target/release/truth frontier-diff --base <merge-base>` and the existing least-fixpoint exclusion test for `00e962ae` under the historical method. Record the exact comparison and affected route families, including shared dependencies and remaining blockers.

## 10. Semantic challenge and acceptance criteria

### Self-challenge of the complete proposed outcome

| Challenged assertion | Concrete risk | Disposition / repair |
|---|---|---|
| "This is the weakest premise." | Weakest absolute moral principle or hidden circularity. | Qualify as exact remaining pointwise requirement given causal background; separate logical sufficiency from positive warrant. |
| "A maximum is good by subsistence." | A relative maximum need not have represented identity. Equality alone is weaker than subsistence. | Require actual esse and the matched reception/profile and evaluative bridges at the same n for the subsistence argument. |
| "Identity proves due status." | Supplied equality and an arbitrary form/end assignment can omit due esse. | Retain independent calibration of the standard. The extensional due table illustrates the omission. |
| "No privation implies goodness." | All-act leaves no missing due actualities even with source goodness omitted. | The positive bridge is needed. The q.5 a.1 ad 1 Lean encoding gives only the exclusion involving ultimate perfection. |
| "Constitutive good settles arbitrary positive determinations." | Essential role can be instrumentally harmful or inappropriate to another bearer. | Restrict to actual esse and the bearer; no welfare or whole-life comparison. |
| "Goodness is moral perfection." | `IsSupremelyGood` only conjoins esse goodness and causal responsibility. | Preserve distinct sense and consumer requirements; no love, right willing, or moral agency conclusion. |
| "The concurrent table checks the original causal background." | The supporter causes the recipient's esse and lacks the corresponding skill edge. | Scope the table to restricted transfer. Use the existing checked singleton for the omission of goodness under the original causal premises. |
| "The model represents the neutralist's full metaphysics." | Represented identity and due assignments supply no interpretation of subsistence or evaluation. | Report the specified structural non-entailments and retain the substantive rival in §7. |
| "Aquinas states the new guard." | q.6 a.3 uses three kinds of perfection; q.5 a.3 excludes merely logical entities in reply. | Keep the source's scope, use supports where needed, and mark dictionary/attribution conditions OPEN. |
| "25 routes are now fixed." | Lower-level theorem migration is not corpus reachability. | No route migration count or frontier closure claimed. |

The independent semantic challenge covered the original documentation at `b03c55570d796d1841d0481b4da71abd203139c1` and prompted the scoped repairs in this draft. A targeted re-review accepted the documentation specification at `a7f53fea1a14026a91929335e2d19d942b07a0e5` with no remaining semantic findings. Subsequent formal findings need their own challenge of the final records, proofs, model assignments, any source evidence used for attribution, and the provisional judgment. [Review procedure](../systematic-corpus-loop.md#final-outcome-review-and-repair)

### Acceptance checklist for subsequent formal implementation

- [ ] Reconcile current main revision, run canonical related/dossier and read installed conventions and local instructions. No duplicate vocabulary, definition, or source claim.
- [ ] Exact scope and residual results: original and replacement premise bundles mapped to their types; original premise and frozen Challenges unchanged.
- [ ] Preserve existing same-witness identity derivations and local logic interfaces. For the selected-source subsistence argument, verify whether the existing inputs supply the matched reception profile, actuality and evaluative bridge at that witness.
- [ ] Formal positive and negative controls with fixed causal dictionaries, explicit due/identity calibration gaps and restoration. Record which claims have populated test cases and which are vacuous.
- [ ] Check sense coverage, including actual real being across the eligible domain. When adding source claims, read the pinned passages and restrict attribution to their scope.
- [ ] Register statement/inference/argument/result records with permanent UUIDs, Comparator config and generated area imports by existing tooling; perform claim/type self-sweep.
- [ ] The coordinator runs `python3 scripts/worker_env.py --check` once for the selected warm-clone setup. Workers use its supplied setup with `python3 scripts/worker_env.py -- <command> <args...>`. Run the applicable build, corpus, binding, axiom, Comparator, NanoDa and CI checks specified in `AGENTS.md` for the formal inputs.
- [ ] Obtain independent semantic challenge of the actual final findings; repair and re-review affected claims within canonical cap.
- [ ] At route migration, compute `truth frontier-diff` and the same-method exclusion test. Record affected obligations and remaining route blockers.
- [ ] Persist the existing research attempt/linked note and one current handoff with exact revision; do not create a competing tracker; integrate formal findings only after the required review and verification gates.

### Documentation checkpoint evidence

PR #1917 CI on the original docs head `b03c55570d796d1841d0481b4da71abd203139c1` passed the corpus and offline source-binding checks. “Report the premise frontier” returned `no change`. Lean setup and binding steps and Comparator shards were skipped for that docs revision. This evidence covers that historical head. The independent documentation review and §8's finite comparisons assess the proposal. Lean proof, registration, Comparator, NanoDa and downstream migration are subsequent formal work. [Original CI job and premise delta](https://github.com/moritzbrantner/formal-logos/actions/runs/45322820579/job/138205649056)

## 11. Next discriminating research question

**Does a correct, non-evaluative account of the actualization of a bearer through esse already license a positive intrinsic standard, or is a distinct evaluative principle required?**

Test the strongest neutralist account at the level of constitutive fulfillment itself, not by adding moral examples or more equivalent goodness predicates. Ask whether the neutralist uses "due" as merely constitutive/functional correctness or as genuinely evaluative; compare the same account of the subject's actuality across source and recipient. Investigate whether it can accept objectively fitting intrinsic realization while denying even its limited ontological good. If it can, state its substantive commitment and preserve it as a serious rival; if a contradiction is found, identify the exact positive commitments it contradicts. If the positive evaluative rule remains primitive but well warranted, retain that as an explicit direct support option rather than requiring an endless further derivation.

## 12. Evidence index

Repository links use the inspected evidence baseline unless otherwise noted.

- [AGENTS.md](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/AGENTS.md), [canonical systematic loop](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/docs/systematic-corpus-loop.md), [open investigation #1116](https://github.com/moritzbrantner/formal-logos/issues/1116).
- `corpus/statements/goodness-is-actuality.json`, `god-is-supremely-good.json`; `corpus/disambiguations/goodness-unrestricted-due-and-ultimate.json` (`f5b1a1e9`); `corpus/definitions/supremely-good.json` (`58e0de99`), `DEF-GOOD-AS-BEING-IN-ACT` (`4c8f0e6b`).
- [GoodnessFormEnd](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Metaethics/GoodnessFormEnd.lean), [GoodnessFormEndBoundary](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Results/Metaethics/GoodnessFormEndBoundary/Solution.lean), `TruthCore/Results/Metaethics/GoodnessDueToUnrestricted/Solution.lean`.
- [GodIsSupremelyGood](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Results/Case/Catholicism/StageTwo/GodIsSupremelyGood/Solution.lean), [DirectEsseRootPerfectionGoodness](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Causality/DirectEsseRootPerfectionGoodness.lean), `TruthCore/Results/Causality/DirectEsseRootPerfectionGoodness/Solution.lean`, `TruthCore/Causality/DirectEsseRootGoodnessOmission.lean` and its checked Solution.
- `TruthCore/Case/Catholicism/CausalPerfectionTransfer.lean` and `TruthCore/Results/Aquinas/SummaTheologiae/CausalPerfectionTransfer/Solution.lean`; `corpus/arguments/CAUSAL-PERFECTION-TRANSFER-GOODNESS.json`, `corpus/arguments/direct-esse-root-perfection-goodness.json`.
- [RootPositiveIntellectWill](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Results/Causality/RootPositiveIntellectWill/Solution.lean), `TruthCore/Results/Causality/PerfectRootPositiveIntellectWill/Solution.lean`, `TruthCore/Results/Case/Catholicism/StageTwo/GodIsInfinite/Solution.lean`, `ClassicalAttributesIdentity/Solution.lean`.
- `TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/Question5/Article1.lean`, `Question5/UltimatePerfection.lean`, `Question48/Articles2and3.lean`, `InfinityEternity.lean`; `TruthCore/Causality/EsseReception.lean`.
- `TruthCore/Case/Catholicism/DivineLoveBridge.lean`; [historical root route analysis](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/docs/notes/root-route-modal-load.md).

## Does a warranted judgment of improvement settle positive goodness?

Fix the same eye, the same viewing task and the same otherwise suitable conditions. An independently specified success criterion is resolving a pair of lines as two at a fixed separation. Suppose an optical defect prevents this, and a correction restores it. The image formation and the discrimination task explain why the second condition fulfills a capacity of this eye. The two arrangements are equally real. The aberration is an actual optical configuration and a privation of the specified resolution in that task. Its reality licenses no inference that it realizes the missing excellence. Goodness in the fulfilled respect, goodness as an organism overall, and the moral goodness of an agent's choice have different subjects or standards here.

Grant a stronger neutralist concession than an accurate functional description. Suppose both sides agree that restoration is *better* for this bearer in this respect. Does even this ordering settle that success is positively good? Compare two assignments to the actual performance states. In one, failure is neutral and attainment positive. In the other, failure is bad and attainment neutral. Both give all the same strict comparisons between performances. The second gives an intelligible reason to repair a defect while withholding a positive verdict on the restored state. A Thomist can readily judge both that failure is bad and attainment is good; nothing requires a local privation to be neutral. The first assignment isolates what is needed for the positive verdict, without purporting to exhaust the Thomistic position.

The following local control uses three ordered marks, with 1 designated neutral, solely to test how much information those comparisons contain. Positivity represents one candidate evaluation of the single attained perfection. The same bearer exists in both conditions. The two checks use the actual biconditional and require no axioms. They make no assumption of additive metaphysical value.

[Lean proofs of `sameComparisons` and `differentVerdicts`](../../TruthCore/Metaethics/FulfilledRespect.lean#L21)

**Judgment.** There is positive warrant for crediting the bearer with an excellence where a due capacity actually attains its own end. The attained discrimination supplies an intelligible object of pursuit and preservation even when we consider the successful operation itself, apart from the relief of a prior defect or any further use. This supports a primitive constitutive reading of goodness: attainment fulfills the bearer *in this respect*. The rival can grant the same restoration history, ranking and reason to avoid impairment, and identify normal success with meeting a requirement whose violation is bad. A ranking of repairs cannot decide between those accounts. A reason to pursue the realized operation for its own sake, identifiable independently of avoiding a loss or a further benefit, bears directly on the disputed positive attribution. Observed pursuit by itself also admits instrumental explanations.

At the independently selected source, the relevant inference is narrower still: given its actuality in esse, ascribe goodness to that very source in esse. Argument `0011703b` uses just this forward instance of `00e962ae` for its goodness conjunct; its causal conjunct has its own premises. There is no defective-but-existing condition of the same subject in which it wholly lacks esse. One cannot carry over the eye's repair ranking by assigning nonexistence a score for the absent subject. The strongest affirmative rationale is internal: esse realizes this bearer as actual, and such constitutive realization is positively perfective of the bearer. A neutralist can accept the first step while denying evaluative force to that fulfillment. I favor the limited ontological ascription on the constitutive reading. Its warrant rests on that evaluative principle, and neither this case nor the root proof extends it to arbitrary determinations or morally right willing. The full biconditional retains its direct assumption and the due-actuality derivation with explicitly universal due coverage.

## Research attempts citing this note

- [Owner selected a proposition, superseding adopted-definition proposal](../../corpus/attempts/goodness-form-end-forks-1116.json)
