# PRD: Root-local goodness of an ultimate existential source

**Project:** Formal Logos (`moritzbrantner/formal-logos`)  
**Date:** 2026-11-24  
**Status:** Draft research and implementation specification (not integrated or reviewed); conditional derivations drafted, independent semantic review and Lean verification outstanding.  
**Target:** `00e962ae-f109-55f7-a7fd-f107ce0dea6b` — `GoodnessIsActualityReading`  
**Primary consumer:** `e0dae79f-c042-5a08-a148-725d0468df91` — `GodIsSupremelyGood`  
**Evidence baseline:** repository files inspected at `0ce1e78ed5e42962586356631a778e24a832c546`; the 25-route result is the historical analysis at `fd78b77e6`, not a newly computed count.  
**Publication disposition:** owner authorized publishing this specification as a draft documentation checkpoint on 2026-11-24. No formal corpus or proof changes are authorized by this checkpoint.

## 1. Executive decision

Preserve the unrestricted goodness–actuality thesis as a separate open proposition. Add a narrower, independently assessable **forward goodness principle at esse** and an optional **subsistent-esse-specific support route**. Keep the existing causal goodness endpoint and every frozen Challenge unchanged. Integrate new arguments as sibling support options, not semantic replacements for the original statement.

The substantive finding is that the existing divine-goodness result does not need a general theory evaluating every positive determination. After independent selection of the source and proof of its causal responsibility for the actual perfections of distinct effects, the exact remaining pointwise obligation is `GoodIn n esse`. Under #1116's existing due-actuality thesis, and given actual esse, that obligation is equivalent to `Due f n f.substantial` when the dictionaries and substantial respect are correctly identified.

The strongest direct philosophical case is that constitutive actuality, as distinct from accidental actuality or successful operation, supplies a non-instrumental ontological good. Subsistent esse provides a particularly strong instance because its own act is not received into a distinct essence. This is not a theorem of bare identity: a positive evaluative bridge remains open. The next work should defend that bridge, not attempt to establish every instance of `AllActualitiesDue`.

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

No new general definition campaign (#1116), moral-first argument (#1812), divine-love investigation (#1732), redefinition of `IsSupremelyGood`, adoption of new floor items, proof of universal perfection transfer, or general modal-necessity investigation. Do not alter source claims or integrate unverified formal results. No infrastructure or parallel corpus authority.

## 3. Existing implementation and exact proof use

The original proposition is:

```lean
GoodnessIsActualityReading GoodIn InAct :=
  ∀ x r, GoodIn x r ↔ InAct x r
```

The current endpoint in `TruthCore/Case/Catholicism/StageTwo.lean` is:

```lean
IsSupremelyGood InAct GoodIn CausesIn esse n :=
  GoodIn n esse ∧ CausesEveryPerfectionOfOthers InAct CausesIn n
```

`GodIsSupremelyGood` universally quantifies this over `IsGod`. It does not create a God witness. In the original `godIsSupremelyGood` proof, the entire use of the unrestricted goodness thesis is `(hGoodness g esse).mpr hMax.1`. The restricted causal-transfer sibling (`CausalPerfectionTransfer.goodness`) and `DirectEsseRootPerfectionGoodness.supremelyGoodOfMaximum` use the same instance. Everything else in those proofs establishes causal responsibility.

Let A(x,r) denote `InAct x r`, G(x,r) denote `GoodIn x r`, M(x) denote `IsMaximumIn InAct MoreIn esse x`, and C(x) denote `CausesEveryPerfectionOfOthers InAct CausesIn x`. All use the same respect and bearer dictionaries.

**New exact residual:** under independently supplied maximum-at-esse, maximum-to-universal-esse-cause, actuality-to-being, and universal perfection-transfer hypotheses for n, C(n) is derivable. Consequently:

> `IsSupremelyGood ... n ↔ GoodIn n esse`.

Forward direction is the first conjunct of the existing endpoint. Backward direction reuses the existing universal cause and perfection-transfer proof for the second conjunct. No new causal premise or scope change is needed. With the original stage-two causal background, the corresponding universal residual is `GodIsSupremelyGood ... ↔ ∀ g, IsGod g → GoodIn g esse`.

This establishes what is logically sufficient and necessary **relative to that background**. It does not justify the remaining goodness predicate or assert existence. Without the causal background, the equivalence fails; the already verified secondary-only omission control `DirectEsseRootGoodnessOmission` gives a source good in esse without supreme causal goodness.

## 4. Proposed scope alternatives

| Candidate | Exact proposition | Intended use |
|---|---|---|
| Original `00e962ae` | ∀ x r, G(x,r) ↔ A(x,r) | Preserve all existing consumers and direct-assumption option. |
| Esse-forward | ∀ x, A(x,esse) → G(x,esse) | Main reusable candidate: no reverse direction or other respects. |
| Maximum-local | ∀ x, M(x) → G(x,esse) | Pre-naming sufficient interface; may include finite relative maxima. |
| Identity-guarded | ∀ x, esseOf x = essenceOf x → A(x,esse) → G(x,esse) | Use when existing metaphysical derivation independently establishes represented subsistence. |
| Selected-source | G(n,esse) for the already selected n | Exact pointwise residual, not by itself a philosophical argument. |

Original implies esse-forward; esse-forward implies both maximum-local and identity-guarded. The last two are **not interchangeable without eligibility**. Maximum-local does not establish identity; identity-guarded does not establish maximality or sourcehood. They may imply the same application on the selected witness. If the same background ensures a unique maximum and the selected source is that maximum, maximum-local is equivalent to the pointwise goodness obligation under that background.

A universal `IsGod`-guarded residual is mechanically weakest for the corresponding universal theorem but is not the preferred pre-naming premise: it risks confusing goodness warrant with naming. Use maximum-local as a scope adapter only when independently justified, and the identity guard when the proof has actually established identity. Do not automatically transfer source-specific warrant to arbitrary maxima.

### Recommended implementation order

1. Exact residual lemmas and scope comparison; use the unchanged causal dictionary and consumers.
2. Esse-forward sibling first, because its positive content is directly about being and it can be used by existing modal-free stage-two signatures without adding identity, modality, or an extra witness.
3. Identity-guarded route as a separate alternative where identity is already obtained independently. Do not require a proof of necessary existence to get goodness.
4. Keep form/end and source-constitutive warrant explicit. Do not turn `GoodIn` into a definitional alias of actuality or due status.

## 5. Philosophical investigation: is esse itself a genuine good?

### 5.1 Direct constitutive-actuality route

**Claim:** Actual esse constitutes an intrinsic ontological perfection of its bearer, rather than merely an enabling condition for desirable outcomes.

Consider the difference between having the kind of being one has, the act by which one actually is, and subsequent determinations of an already actual bearer. The first is not an additional contingent feature, the second is not just a property possessed after existence, and the third includes states that may be dysfunctional or inappropriate. An actual eye may lack sight. Its actual existence does not make blindness good; conversely blindness does not erase every positive actuality of the eye. Goodness qua esse and good functioning can be distinguished without treating either as a moral evaluation.

The positive warrant has three steps:

1. **Constitution:** actual esse is the act by which the nature is actually instantiated, not merely a condition external to that subject.
2. **Fit:** in respect of being itself, the actuality constituting that subject realizes the relevant constitutive standard. This is an ontological standard, not a claim that every possible subject ought to exist or that the universe is better with it.
3. **Evaluation:** constitutive fulfillment is a genuine good of the bearer in that respect, independently of whether an observer approves of it. This is an explicit positive metaphysical commitment, warranted in part by ordinary distinctions between actuality, fulfillment, and privation; it is not a logical consequence of the word "actual".

These steps give an argument for esse-forward, not the full per-perfection coextension. The strongest objection is that being constitutive is only an identity or explanatory condition. A neutralist can accept (1) and (2) while denying evaluative force in (3). Merely being necessary for further goods cannot settle this: conditions enabling harms can be necessary too. The crucial content of (3) is the *intrinsic* realization of the subject in the existential respect, not the instrumental usefulness of existence.

The argument does not assert that every essential predicate is a good in every sense. For example, toxicity constitutive of a particular kind can be good-for its characteristic function but bad for another organism. Nor does the argument rank entire lives against never having existed. A subject can suffer catastrophic privations while retaining a positive existential actuality on this reading. A rival that denies even that limited ascription, rather than disputing welfare, directly targets the premise.

### 5.2 Subsistence and an internal standard

For the selected source n, if `esseOf n = essenceOf n` has been established in the intended metaphysics, its existential actuality is not a further completion of a distinct receptive essence. This removes one important source of an intrinsic mismatch between actuality and constitutive nature. It supports an account of goodness internal to what the source is, without treating an externally assigned purpose, another being's preferences, or an accidental determination as its standard.

**Limit:** the absence of a distinct receiver does not prove the absence of all limiting principles, all due perfections, or the actuality of every pure perfection. Those are separate results and assumptions. Nor does bare equality of two parameter values prove that they genuinely denote essence and act of existence. The existing identity and reception investigations remain authoritative for their applicability.

There is a stronger proposed inference: if the ultimate source has neither an external evaluator nor a distinct receptive nature, then it must be good. Reject this inference as stated. It equivocates between absence of an external measure and existence of a positive intrinsic standard. A neutral source could have no external measure and no evaluative status. The warranted formulation is conditional: an actual subsistent esse meets its constitutive existential standard **if** identity and genuine constitutive fulfillment are established; meeting that standard yields ontological goodness **if** the positive bridge holds.

Do not define the due standard as whatever the source actually possesses. That would make arbitrary positive determinations good by construction. Independently fix the standard by what constitutes actual being, not by a list of properties observed in an already selected source. For creaturely form/end comparisons, natural aptitude does not necessarily require unrealized potency: the term must admit a fulfilled nature. For subsistent actuality, the form/end profile requires explicit interpretation; assigning `form := essenceOf` and `end := source` is not evidence that the supplied `DueFor` represents an actual intrinsic standard. No assumption that God is already the final end of all things is required for this narrow conclusion.

### 5.3 Exact bridge to #1116 (new restricted boundary)

The existing `GoodnessFormEnd.Frame` defines `Due f x p` by `DueFor` at that bearer's supplied form and end. `DueActualityThesis f` says `GoodIn x p ↔ Due f x p ∧ Has x p`. `GoodnessDueToUnrestricted.dueToUnrestricted` uses `AllActualitiesDue f` to recover `00e962ae`.

Under the same thesis and `f.Has n f.substantial`, the exact narrower equivalence is:

```lean
f.GoodIn n f.substantial ↔ Due f n f.substantial
```

A further exact boundary is:

```lean
EsseGoodness f.Has f.GoodIn f.substantial ↔
  (∀ x, f.Has x f.substantial → Due f x f.substantial)
```

The latter is conditional on `DueActualityThesis f`. In the positive direction only, even the full biconditional is unnecessary: a local rule `Due f n f.substantial ∧ f.Has n f.substantial → f.GoodIn n f.substantial` suffices. Keep the full existing thesis as a support option; do not pretend the restricted normative bridge is established by writing it as a definition.

**Decisive missing premise:** a correct actual esse is constitutively due to the relevant bearer, in the selected ontological sense. Under a full form/end profile this requires a defended standard, not arbitrary `DueFor`. Under an identity-specific profile it requires the actual, independently selected source and the correct esse/essence meaning. Link the existing dictionaries (`Has = InAct`, `GoodIn` unchanged, `substantial = esse`) explicitly or express the proof directly in the existing parameters. Do not hide these correspondences in an existentially chosen frame.

### 5.4 Privation, pure perfection, and arbitrary positive determinations

`EvilIsPrivationReading` in q.48 encodes `Evil x ↔ ∃ p, Due x p ∧ ¬ Has x p`. Even with that account granted, having every due actuality excludes evil in the stated privative sense; it does **not** imply `GoodIn x esse`. A model can assign no missing due actuality and nevertheless withhold that positive predicate. The negation of goodness is not automatically evil. Likewise `UltimateDuePerfectionRequiredReading` is an exclusion when ultimate perfection is lacking; its converse is not supplied.

Actual perfection must be assessed in a fixed respect and sense. A pure perfection is not merely any positive predicate. Even a universal `IsPerfect InAct n` in the existing respect dictionary is not a declaration that every described state is appropriately possessed, morally good, or free from all limitation. Keep the already separate pure-perfection and formal/eminent-possession questions independent. In a model of arbitrary positive determinations, an actuality in another respect can be non-due while esse remains due and good. Do not attribute such a model, without further metaphysical realization, to an absolutely simple Thomistic source.

### 5.5 Causal desirability is supporting evidence, not a substitute

If effects have intrinsically good actualities, and the source genuinely exemplifies or supplies them, there is a reason to regard the source as an objective ground of those goods. But a source good *for* something need not have intrinsic goodness solely because it is an efficient means to it. To infer intrinsic goodness via causal desirability requires the further perfection/likeness and non-instrumental desirability commitments. ST I q.6 a.1 supplies the historical route; do not use `f8ba2429`, `64498e7e`, or an effect's goodness by themselves to erase this distinction. This is a cumulative route, not a second independent proof of the same proposition from causation alone.

## 6. Source findings and attribution boundaries

Selected external passages were read as research evidence, not imported or certified against a pinned corpus witness. Before creating a claim, use the canonical source-evidence workflow to identify or acquire the exact existing passage, read its pinned witness, and bind it faithfully. A search of the inspected repository found the q.5 a.1 reading, the q.5 a.1 ad 1 exclusion and q.48 privation, not a dedicated esse-only q.5 a.3 statement; confirm with `truth related` and local search before creating new records.

| Passage | Positive contribution | Boundary |
|---|---|---|
| [ST I q.5 a.3, body and replies 2–4](https://www.newadvent.org/summa/1005.htm) | Direct support for goodness of a real being insofar as it is actual; distinguishes deficiencies and merely logical being. | The encoded one-way esse instance is a selected reading, not an unrestricted evaluation of every arbitrary predicate. The proof still depends on perfection and desirability. |
| [ST I q.6 a.3, body and replies](https://www.newadvent.org/summa/1006.htm) | Distinguishes constitutive being, operation and end. Grounds the first kind in essence/esse identity when discussing the divine case. | The full essential-goodness conclusion uses all three kinds and further divine attributes; identity alone does not establish goodness simply, moral goodness, or uniqueness. |
| [ST I q.6 a.1–2](https://www.newadvent.org/summa/1006.htm) | Causal desirability and analogical supremacy; the source is not compared as a member of a shared genus. | Requires the perfection/likeness account, not mere enabling. The existing case predicate is a restricted formal representation, not every aspect of Aquinas's thesis. |
| [De veritate q.21 a.1–2, especially a.1 ad 2 and a.2 body](https://isidore.co/aquinas/english/QDdeVer21.htm) | Goodness as a conceptual relation founded in reality, with final-causal character; distinguishes concept from additional property. | Not a proof that all assessment standards are correct; not the same as an intensional identity theorem or moral obligation. |

No source quote is used to claim that the new analyst-specific identity guard or the exact Lean residual was stated by Aquinas. Source support and logical consequence remain different statuses.

## 7. Rival comparison and provisional judgment

Compare on one shared task: explain whether and why the selected source has a positive good in its existential respect. Do not penalize an impersonal account for failing to explain morality when the immediate target is ontological.

| Account | Positive explanation of esse goodness | Main surviving issue | Consequence for existing endpoint |
|---|---|---|---|
| Perfect impersonal source with objective constitutive goodness | Actual nature's fulfillment is intrinsically good without anyone's approval. | Must defend objective goodness for non-appetitive reality. Does not explain moral agency. | Can satisfy the endpoint with causal transfer. |
| Intrinsically good personal source | Same constitutive grounding; rational agency may additionally have due perfections and right ends. | Personal status alone does not prove goodness of will; cannot derive love or moral infallibility here. | Same endpoint possible; personality is not required by the goodness proof. |
| Source with arbitrary positive determinations | Positive existence may be good even when arbitrary determinations are not due. | No automatic entitlement to call every actual determination a pure perfection. Needs non-arbitrary criterion for intrinsic standards. | Can satisfy causal goodness while unrestricted coextension fails. |
| Evaluatively neutral source | Structure, existence and causal powers are descriptive facts; normative or evaluative facts attach only where there are interests, ends, or further principles. | Must explain the status of ordinary fulfillment/privation distinctions if it accepts objective due standards; may consistently regard them as merely descriptive. | Denies the remaining intrinsic-goodness premise, even if causal coverage is granted. |

The neutralist is the strongest remaining rival. It can concede essence–esse identity, maximality, actuality, no privation and causal sufficiency while declining intrinsic value. If it accepts genuinely evaluative due status and the positive due-actuality rule at esse, then denying `GoodIn n esse` contradicts those accepted commitments. If it instead interprets due status descriptively or restricts it to interest-bearing entities, the contradiction does not follow. The relevant disagreement is the positive evaluative import of constitutive realization, not existence or identity itself.

**Overall provisional judgment:** prefer esse-forward as the main broad, directly source-supported candidate; retain the identity-specific argument as a particularly fitting source-local support option. The weaker scope is logically established by simple reasoning and structurally tested. The philosophical commitment has positive warrant from constitutive rather than arbitrary actualities, but remains contestable. No rival has been refuted as a complete worldview; no premise is newly established. The fact that the identity-guarded rule is narrower does not by itself give it stronger warrant.

**Reopening conditions:** a genuine example of an actual bearer whose constitutive existential actuality is not an ontological good (not merely a bad life or harmful effect); a neutralist account that explains intrinsic due fulfillment without evaluative import; evidence that constitutive-goodness attribution equivocates with instrumental or moral goodness; or a stronger independently warranted bridge grounding due status at the selected source. Pursue these questions rather than new equivalent formulations.

## 8. Formal research and model results

The companion `RootEsseGoodnessFollowup.lean` is an **uncompiled candidate**, using existing declarations. It supersedes overlapping vocabulary in the earlier scratch draft; do not install both. Candidate results:

| Declaration | Intended conclusion |
|---|---|
| `esseOfGlobal`, `maximalOfEsse`, `subsistentOfEsse` | Exact scope implications in unchanged parameters. |
| `selectedResidual` | Pointwise causal endpoint iff source esse goodness under fixed causal background. |
| `godResidual` | Universal stage-two endpoint iff goodness of every supplied `IsGod` witness, under the old causal hypotheses. |
| `dueResidual`, `dueEsseResidual` | Exact local and esse-forward due boundaries. |
| `godGoodFromIdentity` | Existing simplicity/composition identity proof followed by the open identity-specific goodness commitment. |

`godGoodFromIdentity` uses the same `hKinds` branch as `GodIsInfinite.godIsInfinite`; it requires the existing `ExcludedMiddle` at principle identity (or an existing identity-specific decision interface). It needs neither `Infinite` nor an attribute naming conclusion. Do not add stronger logical axioms to a weaker existing route; preserve the local decisions in `ClassicalAttributesIdentity` and `ClassicalAttributesLocalLogic`.

### Structural controls actually executed

`check_goodness_boundary.py` reuses the four-role concurrent causal pattern (`source`, `supporter`, `producer`, `recipient`; two respects `esse` and `skill`). The original all-act, ordered and concurrent-causal background is retained. `GoodIn` and due tables are varied independently. Results:

- All **256** possible `GoodIn` assignments under that fixed causal table satisfy the exact selected-source residual. The global-to-esse and esse-to-maximum implications hold.
- All **65,536** assignments of `Has` and `Due` across the eight cells, with `GoodIn = Has ∧ Due`, satisfy the exact local and esse-only due boundaries and the earlier unrestricted boundary. This separate enumeration tests the due logic, not causal applicability at each assignment.
- Source omission survives with identity, actuality, no potency and no missing due stipulated, retaining nonempty goodness elsewhere. It disappears when the same due standard and positive due-goodness thesis are both supplied.
- Even the full due thesis allows a neutral source when the supplied due standard omits its esse. Restoring the independently warranted due status restores source goodness. Thus neither the due thesis alone nor structural identity alone anchors the standard.
- A due-and-good esse at every actual bearer coexists with a non-due positive determination, so universal esse goodness does not require unrestricted coextension.
- Maximum and identity scope comparisons separate if their eligibility sets differ. This is a scope control, not a model of a fully interpreted subsistent source. Moral and `GoodSimply` predicates do not occur in the endpoint; varying unused flags demonstrates only signature independence.

See `check-results.txt`. These are finite Python checks of the stated encodings, **not** Lean verification or evidence that every model is metaphysically realizable. In particular, the neutral-source extension stipulates identity and no potency but does not encode a complete metaphysics of subsistence or all pure perfections. Its strongest implication is formal non-entailment with an omitted goodness bridge. The existing secondary-only causal model remains a separate negative control; do not claim that supplying source goodness repairs missing causal transfer.

## 9. Implementation plan and exact downstream premise effects

### 9.1 First checkpoint: reusable results

- Run `truth related 00e962ae`, `truth dossier`/`context --proof-use` and `truth lean-reuse` as appropriate on current main. Search for exact matching candidates and existing sense records; use them if semantically identical. Confirm scope against the canonical `AGENTS.md` and installed conventions.
- Register the smallest sufficient sibling statement (prefer esse-forward) and exact residual/due boundaries. Use opaque UUIDs, appropriate existing definition/disambiguation records, explicit dependencies and frozen Challenge/Solution pairs with existing module and Comparator conventions. Preserve `00e962ae`, its source claims, and its direct-assumption option.
- Give the candidate independent direct warrant and due/identity support options. If adding q.5 a.3 or q.6 a.3 claims, use pinned passage evidence and scope-limited attribution; do not invent a claim that the passage states the Lean theorem literally.
- Keep no new global axiom, definition of `GoodIn`, modal requirement or source-specific proxy that assumes the desired endpoint.

### 9.2 Consumers and ordering

| Consumer inspected | Required change / exact limitation |
|---|---|
| `StageTwo.GodIsSupremelyGood.godIsSupremelyGood` | Sibling: one goodness input replaced by esse-forward or maximum-local; keep maximality, genus, actuality-to-being and unrestricted transfer unchanged. |
| `CausalPerfectionTransfer.goodness` (`0011703b`) | Same one-input substitution; keep its existing *restricted* transfer `b26c10a0`, do not accidentally reintroduce unrestricted transfer. |
| `DirectEsseRootPerfectionGoodness.derive` (`818f5532` → `469b92a8`) | Reuse `DirectEsseRootPerfection.derive` and the same selected maximum. Replace only the goodness input; the other 11 of its 12 inputs remain unchanged in the esse-forward sibling. Identity is not yet in this producer's signature; do not add it just to use the identity route. |
| `ClassicalAttributes`, `ClassicalAttributesAll`, `ClassicalAttributesIdentity`, `ClassicalAttributesLocalLogic` | Parallel sibling assemblies use the new goodness producer. In the fuller assemblies, simplicity and composition-kind premises already support identity (see `GodIsInfinite` and the inline identity proof). Reuse that derivation *before* goodness for the identity branch. Preserve existing logical floor, the remaining eight attribute obligations, maximality and naming/sufficiency. The minimal `ClassicalAttributes` signature lacks these identity premises; use esse-forward there. |
| `RootPositiveIntellectWill`, `PerfectRootPositiveIntellectWill` | Their existing `hIdentity` proof is independent of `hGood`. Start from the prior perfect-root witness, derive simple/identity, apply the identity-specific rule at that same n, then causal goodness and the remaining attributes. Avoid calling the old goodness-producing theorem first. In `PerfectRootPositiveIntellectWill`, reuse the existing uniqueness witness equality when transporting identity from `ofNonlimitation`. |
| `NecessaryClassicalGodRoot`, downstream same-source root families | Use the sibling producer, preserve exact witness, modal inputs where already required, and all nominal/attribute constraints. Audit every consumer's actual proof use; a new lower producer does not automatically migrate flattened theorem types. |
| `DivineLoveBridge.divineWillsGoodForAllExisting` | Its independent goodness use is `(hActualGood x esse).2 hx` at arbitrary recipient x, so root-local goodness is insufficient. Esse-forward can replace this *particular* goodness use, not the existing causal-willing or love bridges. No work on those bridges in this scope. |
| Other users of `00e962ae` (problem of evil, metaethics, comparison/model theory) | No global replacement. They may use a wider per-perfection scope or reverse direction. Preserve all old results. |

### 9.3 Premise delta contract

- Original five-input stage-two goodness arguments retain four other inputs, replace one goodness input with a narrower candidate. Conditional application, not a premise closure. The original 12-input direct root argument retains 11 other inputs in the esse-forward sibling. The direct pointwise residual is equivalent only conditional on its fixed causal background.
- A route through the full `DueActualityThesis` and an appropriate due-esse condition may expose two open commitments instead of one, or a restricted positive rule plus its anchoring condition. This may be better targeted despite an expanded premise count. Never claim a saved premise simply because its name changes.
- An identity-guarded route can reuse identity already derived from existing premises where available. Where absent, additional explicit premises are required; do not report that as one-for-one without the computed argument comparison.
- The existing historical `root-route-modal-load.md` reports all 25 modal-free routes blocked when `00e962ae` is excluded at its baseline. New scope siblings **could** remove that bottleneck for migrated routes. No specific number of migrated/closed routes follows until the whole verified path and its dependencies are checked.
- Actual change to repository or computed frontier in this documentation checkpoint: **no registered graph changes**. A computed frontier comparison is unavailable. Do not equate the planned one-input substitution with actual root reachability, independence, a new established premise, or a cheaper route.

After integration locally, run `target/release/truth frontier-diff --base <merge-base>`; record its exact output and perform the existing least-fixpoint exclusion test for `00e962ae` under the same historical method on the new baseline. Report per-family support options, paths still blocked, and whether replacement premises share dependencies with the original. No new graph infrastructure.

## 10. Semantic challenge and acceptance criteria

### Self-challenge of the complete proposed outcome

| Challenged assertion | Concrete risk | Disposition / repair |
|---|---|---|
| "This is the weakest premise." | Weakest absolute moral principle or hidden circularity. | Qualify as exact remaining pointwise requirement given causal background; separate logical sufficiency from positive warrant. |
| "A maximum is good by subsistence." | A relative maximum need not be identical with its esse. | Separate maximum-local and identity-guarded scopes; require actual same-witness identity. |
| "Identity proves due status." | Supplied equality and arbitrary form/end assignment can omit due esse. | Retain explicit standard calibration; unanchored-Due control shows the omission. |
| "No privation implies goodness." | Neutral third option; q.5 a.1 ad 1 is only a necessary condition. | Withdraw inference; retain positive due-goodness bridge and no-privation control. |
| "Constitutive good settles arbitrary positive determinations." | Essential role can be instrumentally harmful or inappropriate to another bearer. | Restrict to actual esse and the bearer; no welfare or whole-life comparison. |
| "Goodness is moral perfection." | `IsSupremelyGood` only conjoins esse goodness and causal responsibility. | Preserve distinct sense and consumer requirements; no love, right willing, or moral agency conclusion. |
| "The model represents the neutralist's full metaphysics." | Identity/potency and assessment assignments are stipulations, not real source interpretations. | Report structural non-entailment only; preserve rival at full philosophical strength. |
| "Aquinas states the new guard." | q.6 a.3 uses three kinds of perfection; q.5 a.3 excludes merely logical entities in reply. | Keep the source's scope, use supports where needed, and mark dictionary/attribution conditions OPEN. |
| "25 routes are now fixed." | Lower-level theorem migration is not corpus reachability. | No route migration count or frontier closure claimed. |

This is a **self-challenge**, not the independent fresh-worker semantic challenge required by the repository. A separate reviewer must receive the complete final candidate records, proofs, model assignments, exact source witness and this judgment. Review against the seven recurring defects in `docs/systematic-corpus-loop.md` and preserve review revision/disposition. Follow the bounded review-and-repair contract; do not report reviewer acceptance or premise establishment without evidence.

### Acceptance checklist for subsequent formal implementation

- [ ] Reconcile current main revision, run canonical related/dossier and read installed conventions and local instructions. No duplicate vocabulary, definition, or source claim.
- [ ] Exact scope and residual results: original and replacement premise bundles mapped to their types; original premise and frozen Challenges unchanged.
- [ ] Actual same-witness identity proof where used; no hidden necessity or naming premise. Preserve weaker logic interfaces.
- [ ] Formal nonvacuous positive and negative controls with fixed causal dictionaries, explicit due/identity calibration gaps and restoration. Distinguish structural satisfiability from metaphysical possibility.
- [ ] Source fidelity and sense coverage; locate pinned passages before attribution; no unrestricted or moral conclusion inferred from narrower text.
- [ ] Register statement/inference/argument/result records with permanent UUIDs, Comparator config and generated area imports by existing tooling; perform claim/type self-sweep.
- [ ] Run `python3 scripts/worker_env.py --check` with supplied warm-clone setup; affected `lake build`, `target/release/truth check`, `python3 scripts/bundle_audit.py`, `truth bind-check --result <ID>` or `--affected --base`, `scripts/verify-result.sh <RESULT-ID>`, appropriate NanoDa, module/root-import checks, attribution check and relevant CI-equivalent gates as required by `AGENTS.md`. Do not mark a mechanically verified result before Comparator passes.
- [ ] Obtain independent semantic challenge of the actual final findings; repair and re-review affected claims within canonical cap.
- [ ] Compute actual `truth frontier-diff` and same-method exclusion test; document unchanged obligations and any remaining open route blockers.
- [ ] Persist the existing research attempt/linked note and one current handoff with exact revision; do not create a competing tracker; integrate formal findings only after the required review and verification gates.

### Completed in this checkpoint

Repository read-only evidence and source reading; exact logical analysis; refined candidate proof source; exhaustive finite-table checks; comparative philosophical warrant and semantic self-challenge; this local PRD. Local Lean/Lake, Rust truth CLI, a prepared checkout and independent worker are not available in this environment. Lean, corpus registration, Comparator, NanoDa, independent semantic challenge and computed frontier comparison remain unverified or pending, not failed. No formal corpus or library files have been changed by this documentation checkpoint.

## 11. Next discriminating research question

**Does a correct, non-evaluative account of the actualization of a bearer through esse already license a positive intrinsic standard, or is a distinct evaluative principle required?**

Test the strongest neutralist account at the level of constitutive fulfillment itself, not by adding moral examples or more equivalent goodness predicates. Ask whether the neutralist uses "due" as merely constitutive/functional correctness or as genuinely evaluative; compare the same account of the subject's actuality across source and recipient. Investigate whether it can accept objectively fitting intrinsic realization while denying even its limited ontological good. If it can, state its substantive commitment and preserve it as a serious rival; if a contradiction is found, identify the exact positive commitments it contradicts. If the positive evaluative rule remains primitive but well warranted, retain that as an explicit direct support option rather than requiring an endless further derivation.

## 12. Evidence index

Repository links use the inspected evidence baseline unless otherwise noted.

- [AGENTS.md](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/AGENTS.md), [canonical systematic loop](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/docs/systematic-corpus-loop.md), [#1116](https://github.com/moritzbrantner/formal-logos/issues/1116).
- `corpus/statements/goodness-is-actuality.json`, `god-is-supremely-good.json`; `corpus/disambiguations/goodness-unrestricted-due-and-ultimate.json` (`f5b1a1e9`); `corpus/definitions/supremely-good.json` (`58e0de99`), `DEF-GOOD-AS-BEING-IN-ACT` (`4c8f0e6b`).
- [GoodnessFormEnd](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Metaethics/GoodnessFormEnd.lean), [GoodnessFormEndBoundary](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Results/Metaethics/GoodnessFormEndBoundary/Solution.lean), `TruthCore/Results/Metaethics/GoodnessDueToUnrestricted/Solution.lean`.
- [GodIsSupremelyGood](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Results/Case/Catholicism/StageTwo/GodIsSupremelyGood/Solution.lean), [DirectEsseRootPerfectionGoodness](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Causality/DirectEsseRootPerfectionGoodness.lean), `TruthCore/Results/Causality/DirectEsseRootPerfectionGoodness/Solution.lean`, `TruthCore/Causality/DirectEsseRootGoodnessOmission.lean` and its checked Solution.
- `TruthCore/Case/Catholicism/CausalPerfectionTransfer.lean` and `TruthCore/Results/Aquinas/SummaTheologiae/CausalPerfectionTransfer/Solution.lean`; `corpus/arguments/CAUSAL-PERFECTION-TRANSFER-GOODNESS.json`, `corpus/arguments/direct-esse-root-perfection-goodness.json`.
- [RootPositiveIntellectWill](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/TruthCore/Results/Causality/RootPositiveIntellectWill/Solution.lean), `TruthCore/Results/Causality/PerfectRootPositiveIntellectWill/Solution.lean`, `TruthCore/Results/Case/Catholicism/StageTwo/GodIsInfinite/Solution.lean`, `ClassicalAttributesIdentity/Solution.lean`.
- `TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/Question5/Article1.lean`, `Question5/UltimatePerfection.lean`, `Question48/Articles2and3.lean`, `InfinityEternity.lean`; `TruthCore/Causality/EsseReception.lean`.
- `TruthCore/Case/Catholicism/DivineLoveBridge.lean`; [historical root route analysis](https://github.com/moritzbrantner/formal-logos/blob/0ce1e78ed5e42962586356631a778e24a832c546/docs/notes/root-route-modal-load.md).

**Companion files:** `RootEsseGoodnessFollowup.lean` (uncompiled), `check_goodness_boundary.py` (reproducible with Python 3), `check-results.txt` (executed results). This PRD is a scoped research proposal linked to #1116, not a new repository tracker. The companion draft Lean and Python package was delivered locally; it is not an imported library module or registered result. The executed finite-check transcript is reproduced below.

### Finite-check transcript (rerun before publication)

```text
PASS: exact selected-source residual and scope implications for all 256 GoodIn tables.
PASS: exact local and esse-only due boundaries across 65,536 Has/Due tables.
PASS: neutral-source, unanchored-Due, restored-Due and arbitrary-positive-determination controls.
PASS: strict global/esse/max scope separations; identity scope not interchangeable with maximum scope.
PASS: signature independence of unencoded GoodSimply, will and moral goodness.
No Lean, Comparator, NanoDa, corpus registration or frontier-diff performed.
```
