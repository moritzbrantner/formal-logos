# Strength-order consumer audit (2026-11-28)

Audit of the 986 (argument, strong premise) pairs behind the 75 `truth check` warnings "used by N argument(s) without strong_version_needed …" (#1017; issues #1517, #1519) at main `722f5eab2`. The strength order and the `strong_version_needed` field are specified in [corpus model, Strength order](../corpus-model.md). The registrations themselves were audited in [the strength-order audit](strength-order-audit.md). Attempt record: [`corpus/attempts/2288b7ec-ca21-4cf9-81fb-0314b5c696a0.json`](../../corpus/attempts/2288b7ec-ca21-4cf9-81fb-0314b5c696a0.json). Ids are shown by their first eight characters; `truth context <id>` expands them.

## Method

**Proof-use tracer.** A throwaway Lean metaprogram, kept out of the repository because no `scripts/` tool covers proof-term inspection, was run against the built library (`import TruthCore`). For each result theorem of a warned argument it:

1. finds every binder whose type head is the strong statement's `lean_declaration`;
2. walks the proof term, following the hypothesis into every lemma it is passed to by beta-reducing that lemma's value at the actual arguments, so instances appear in the theorem's own terms;
3. records each leaf use: the arguments at which the hypothesis is applied, with up to four enclosing heads (`Iff.mpr`, `And.right`, …), projections, opaque eliminations, and binders that are never used.

Each family was then classified against the strong and weak definitions, and the Solution and lemma sources were read wherever the trace alone did not settle a pair.

**What counts as a recorded reason.** A `strong_version_needed` reason is written only when the trace or the source shows that this Solution uses something the registered weak version lacks:

- an instance outside the weak version's scope: a respect other than esse, an arbitrary or accessible world instead of the selected one, a cause or bearer for which the weak version's extra antecedent (distinctness, identity of esse and essence, universality, actual concreteness, a sustaining or per se link, a relevance relation) is not available;
- the converse direction of a biconditional, or a conjunct the weak version drops;
- an excluded-middle instance outside LocalLogic (identity with an established GOD_4 candidate in act, or double-negation elimination on that candidate's esse–essence identity);
- a conclusion that contains the strong statement itself, or passes it whole to an interface typed by it.

Where a model or control shows that the weak version fails outright (for example a three-cycle against NoMutualCauseReading, ClosedEsseSource RootedCycleControl, BegunComingToBe Control.zeno), the reason cites it.

**Limits.**

- A recorded reason is a fact about how this Solution uses the strong premise. It does not show that no other proof could use the weak version, except where it cites a model or control.
- A weak-suffices verdict is not Lean-checked unless it cites an existing sibling result that proves the same conclusion from the weak version. The others need a Lean re-proof before any frozen Challenge or result is re-routed; some also need an adapter (stated per group below).
- The trace does not see uses hidden in tactic-generated auxiliary definitions without values; none was reported for the 511 theorems traced.

## Outcome categories

- **reason recorded** (644 pairs, 456 arguments): the reason is in the argument's `strong_version_needed`. Spec-generated arguments were edited in `specs/*.toml` and regenerated with `argument_batch.py records --write --fix`; the others in `corpus/arguments/*.json`.
- **weak suffices** (342 pairs): no field was added, so the `truth check` warnings remain as the re-route queue (below).
- **undecided** (0 pairs).

| strong | lean declaration | reason | weak suffices |
|---|---|---|---|
| ee4ab504 | `ExcludedMiddle` | 348 | 23 |
| d9fad785 | `MaximumInGenusCausesAllInGenusReading` | 1 | 71 |
| cb1cdea9 | `EsseCauseIsActualConcreteGround` | 64 | 0 |
| d5a94eb1 | `CauseOfQualityInAnotherIsMoreSuchReading` | 2 | 62 |
| d7741cdc | `MatterFormAndEsseEssenceAreCompositionsReading` | 56 | 8 |
| 64498e7e | `PerfectionsOfEffectPreexistInCauseReading` | 1 | 58 |
| 6c27657f | `GradesByApproachToAMaximumReading` | 38 | 9 |
| f8ba2429 | `CauseOfBeingCausesEveryPerfection` | 3 | 42 |
| 62b4a40a | `Euclidean` | 2 | 10 |
| 3b2d2d46 | `IndependentPriority` | 0 | 11 |
| 2e248016 | `ActualDependenceIsGrounding` | 4 | 4 |
| cffad050 | `CauseOfBeingIsMoreInBeing` | 5 | 2 |
| 2068f91c | `EsseEffectDependsOnItsCause` | 6 | 0 |
| 3a2bb5f9 | `ThinkerGroundingAccessible` | 6 | 0 |
| 658814de | `NaturalBodiesActRegularlyForTheBestReading` | 5 | 1 |
| 957a71fe | `MaximeEnsIsGod` | 4 | 2 |
| b19ffd92 | `NecessaryConcreteAt` | 6 | 0 |
| c94b5446 | `SomeActualContingentAt` | 6 | 0 |
| cf4364f6 | `AtomicParts` | 2 | 4 |
| f56b2ee7 | `ThereAreEpistemicReasons` | 6 | 0 |
| 8bf775e9 | `InfiniteCauseOfAllIsImmense` | 5 | 0 |
| b4987085 | `ActualEsseCauseComposes` | 5 | 0 |
| e39a4fce | `GodNamesTheUniqueMaximeEns` | 5 | 0 |
| f8dafcc7 | `ThinkerAncestryGrounded` | 5 | 0 |
| 0628359b | `BeingMovedIsActualizationOfPotencyReading` | 2 | 2 |
| 0e02cd69 | `EveryExistentConcreteAt` | 4 | 0 |
| dc397705 | `ActualRootExistsAt` | 4 | 0 |
| dd41c165 | `NoContingentConcreteSupport` | 2 | 2 |
| e27489c3 | `OwnerCommitmentAt` | 1 | 3 |
| eb6611a5 | `CauseAndGovernorOfAllIsLord` | 4 | 0 |
| ef69a630 | `LocalCausalPrinciple` | 2 | 2 |
| 6dfe01ab | `EsseReceivedOnlyInOwnEssence` | 0 | 3 |
| 8a22ae75 | `SecondEfficientCausesCauseOnlyAsCausedReading` | 3 | 0 |
| bbe8900a | `ActualPartsExistAt` | 2 | 1 |
| e27ea8e3 | `ActualConcreteBorrowingEscape` | 1 | 2 |
| 1773079b | `PureActLivesReading` | 0 | 2 |
| 1e47e6db | `SecondMoversMoveOnlyAsMovedReading` | 2 | 0 |
| 37e9e7a0 | `NoCausalLoops` | 2 | 0 |
| 3b38aa55 | `ActualAccessNeedsBelief` | 0 | 2 |
| 7361a77f | `ActualAlwaysOpen` | 0 | 2 |
| 7a22ab5d | `AccessNeedsBelief` | 0 | 2 |
| 82cfaf26 | `ActualGroundingWF` | 2 | 0 |
| 91b085c4 | `UniqueNecessaryActualRootAt` | 2 | 0 |
| 964928dc | `ReceptionIsPresent` | 2 | 0 |
| c85e8ef5 | `PotencyIsUnactualizedCapacityReading` | 2 | 0 |
| cdf897a8 | `NecessaryRootBoxK` | 2 | 0 |
| ee440511 | `ThoughtAffirmsOrDeniesEveryPropositionReading` | 2 | 0 |
| fce4ac74 | `PopulatedPastsFounded` | 2 | 0 |
| fd12ad3d | `NoInfiniteActualEsseCauseRegress` | 0 | 2 |
| 0edc0b38 | `GodLoves` | 0 | 1 |
| 1dd68893 | `OrderedExistenceWilling` | 1 | 0 |
| 251bbfdd | `DirectionPassesToMoversOfDirectors` | 0 | 1 |
| 293d7219 | `GodTruthComplete` | 1 | 0 |
| 3b40009e | `GoodGeneralFavouringIsApprehension` | 0 | 1 |
| 402cf70f | `SupportIsDistinctEsseCauseEverywhere` | 1 | 0 |
| 4ccb319f | `CauseOfBeingInActAsToBeing` | 0 | 1 |
| 516be275 | `OnlyAbsentCausers` | 1 | 0 |
| 76d2cc96 | `ConcurrentlyActualizedByAnother` | 1 | 0 |
| 78a44599 | `PossiblyFoundedComingToBe` | 0 | 1 |
| 7dfa068a | `NoInfiniteAscentInBeing` | 1 | 0 |
| 820771a7 | `ChurchFoundedInCommissionedApostles` | 1 | 0 |
| 878b92c3 | `JointAbsence` | 1 | 0 |
| 89d82643 | `ActualizedQuiddityReceivesEsse` | 1 | 0 |
| 962a62c9 | `AlwaysOpen` | 0 | 1 |
| 9709d14f | `DistinctCausePrinciple` | 1 | 0 |
| 9ff2814e | `CommonUncausedCauseOfReceived` | 1 | 0 |
| a94a02e3 | `OtherCounter` | 1 | 0 |
| b62deb46 | `DeRe` | 1 | 0 |
| b699ecfb | `CausesHaveActualEndpointsAt` | 0 | 1 |
| be90bb15 | `OriginHasProductiveExercise` | 0 | 1 |
| c36b509c | `ConcreteSupportActualPaths` | 1 | 0 |
| da3facd6 | `NecessaryClassicalGodRootAt` | 1 | 0 |
| da573220 | `CommissionReportsGoBackToJesus` | 0 | 1 |
| df6c64a6 | `DivinePlanRejectsBenefitOmission` | 0 | 1 |
| ff30c214 | `UnrestrictedRecombinationAt` | 1 | 0 |

## Weak suffices: candidate re-routes

Grouped by strong → weak statement. Within a group, arguments that share one finding are listed together. A *sibling* is an existing result proving the same conclusion from the weak version; *re-proof needed* marks a sketch; *caveat* names an adapter a re-route needs.

### d9fad785 `MaximumInGenusCausesAllInGenusReading` → `MaximumInBeingCausesAllBeingsReading` (da09703b): 71

- 0011703b 07d16972 0a639ec4 0ae291ce 100fd420 117cc323 1375ca5f 18dae702 1a88e3e9 1ac60473 1b0b6233 1b9cd51e 1c154f2f 1f42ffcd 279e9475 2b96f446 3367bf93 34293f25 34d0c2cf 39c30529 3b0f4fa5 3d06eda4 3e86eea5 3fdc8ab7 44782677 51fd6d58 53819d8a 57cedd02 5d2c8320 5e8e6054 5ed93bb0 661ce61d 697b7dc4 70b9fa04 7217cf65 72391d4d 732e38d5 79252a71 7be49bc0 7ce8ad4e 846a7b31 87ba10fe 87dd8489 93b55dd2 969ae822 9f7e31d8 aad2f961 abccd997 ac6c9243 acdcf1dd bc0cff0b be0cc025 beec1dc1 c1834d8b c719249b c80c6911 c8aa7df3 d36057d6 d49eccc1 d6e5072d db6ab332 df653f4e e02bea79 e2a7ffb3 ee93f52b ef122ccf f53dd124 f7cff910 f8992ef7 fc46b7f9 fd1f7e75: Every application of the genus principle, including those inside the lemmas it is passed to (quartaVia, atMostOneMaximeEns, godIsPerfect, maximeEnsIsGod…), is at the respect esse. That is exactly MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse (da09703b). Evidence: trace: all APPLY (esse ; …).

### d5a94eb1 `CauseOfQualityInAnotherIsMoreSuchReading` → `CauseOfBeingIsMoreInBeing` (cffad050): 62

- 07d16972 0acc8761 100fd420 117cc323 13338e9c 18dae702 1a88e3e9 1ac60473 1b0b6233 1c648123 1f42ffcd 210019ee 26e368d3 2b96f446 34293f25 39c30529 3b0f4fa5 3d06eda4 3e86eea5 3eafe507 44782677 4c30239f 51fd6d58 528ccadd 53819d8a 57cedd02 5d2c8320 5ed93bb0 661ce61d 6948b865 6c6549ae 7217cf65 732e38d5 7366a9b4 79252a71 7be49bc0 7ce8ad4e 815d22c8 827fa9cd 846a7b31 87ba10fe 87dd8489 8bbe817d 93b55dd2 aad2f961 abccd997 ac6c9243 bc0cff0b beec1dc1 c1834d8b c473ec4b c80c6911 c8aa7df3 d49eccc1 d6e5072d d8529011 e02bea79 ef122ccf f7cff910 f8992ef7 fa24c576 fd1f7e75: Every application of the cause-is-more-such premise, including those inside the lemmas it is passed to (godIsSimple, atMostOneMaximeEns, maximeEnsIsGodViaFullDescription, …), is at the respect esse. That is exactly CauseOfBeingIsMoreInBeing CausesIn MoreIn esse (cffad050). Evidence: trace: all APPLY (y ; x ; esse ; …).

### 64498e7e `PerfectionsOfEffectPreexistInCauseReading` → `CauseOfABeingHasBeing` (4a5a43a5), `UniversalSourcePreexistence` (60176223), `WholeEffectContainmentInTotalCause` (4643a655): 58

- 046e96c9 07d16972 100fd420 18dae702 1a6363fe 1a88e3e9 1b0b6233 1deb1d29 1f42ffcd 2b96f446 334e8640 3357fa30 34293f25 379399d1 3a56507d 3b0f4fa5 44782677 4487819b 51fd6d58 53819d8a 57cedd02 5d2c8320 60193114 61ed8286 625e9993 669aca2b 69affa96 6c6549ae 70b9fa04 7217cf65 732e38d5 79252a71 7ae73896 818f5532 87ba10fe 8e61d00e 8f956c81 9253999d a693bf86 aad2f961 abccd997 ac6c9243 b074dfdd bc03d6a8 c1834d8b c63f3afa c80c6911 c8aa7df3 d49eccc1 d6e5072d db2dead0 ec8182d6 ee93f52b f7cff910: The premise is applied only at a cause that causes all in its genus at esse (a maximum n/m/g, via hGenus/hCauses/hAll/GodCausesBeingOfAllOthers) and an effect x ≠ that cause (excluded middle on x = g), for arbitrary r. That is exactly the antecedent of UniversalSourcePreexistence (60176223). Caveat: 60176223 is stated over a GradesFrame and this theorem uses free InAct/CausesIn/esse, so a re-route needs a frame adapter; the restriction itself suffices. Evidence: trace: instances (n|m|g|f ; x ; r ; ⋯ ; hx) in perfectOfMaximum/godIsPerfect/perfectFrom*.
- 0acc8761 1c648123 827fa9cd ea6317cf: The premise is applied only at a cause that causes all in its genus at esse (a maximum n/m/g, via hGenus/hCauses/hAll/GodCausesBeingOfAllOthers) and an effect x ≠ that cause (excluded middle on x = g), for arbitrary r. That is exactly the antecedent of UniversalSourcePreexistence (60176223). The theorem already works over a GradesFrame, so the weak version applies directly. Evidence: trace: instances (n|m|g|f ; x ; r ; ⋯ ; hx) in perfectOfMaximum/godIsPerfect/perfectFrom*.

### f8ba2429 `CauseOfBeingCausesEveryPerfection` → `UniversalCauseTransfersPerfections` (b26c10a0), `ResidualPerfectionTransfer` (5a4afaa5): 42

- 07d16972 0acc8761 100fd420 18dae702 1a88e3e9 1b0b6233 1f42ffcd 279e9475 2b96f446 2dc44ef4 34293f25 3b0f4fa5 3d06eda4 3e86eea5 44782677 51fd6d58 53819d8a 57cedd02 5d2c8320 661ce61d 678ff65f 6c6549ae 7217cf65 732e38d5 79252a71 7be49bc0 87ba10fe 93b55dd2 aad2f961 abccd997 ac6c9243 bed2cc9f c1834d8b c80c6911 c8aa7df3 d49eccc1 d6e5072d e02bea79 f7cff910 fa24c576 fd1f7e75: Every use (directly or in maximeEnsIsGodViaFullDescription, godIsSupremelyGood, goodFromGodCause or godExistsFromMaximeEnsCausingAll) applies the premise at a cause m/g that causes all in its genus at esse (hCauses / hGenus esse m hMax / GodCausesBeingOfAllOthers) and at an effect x ≠ m/g (hOther or hn). That is exactly the antecedent of UniversalCauseTransfersPerfections (b26c10a0) on the same InAct, CausesIn and esse. Evidence: trace: all instances (m|g|f ; x ; r ; ⋯) inside those lemmas; e.g. MaximeEnsIsGodViaFullDescription/Solution.lean:44-45.
- 827fa9cd: The proof passes the premise to goodFromSource only as (fun c _ x r _ => hPerfections c x r), i.e. it derives and uses UniversalCauseTransfersPerfections (b26c10a0) inline. The weak version can be taken directly. Evidence: AttributesFromEsse/Solution.lean:191-192.

### ee4ab504 `ExcludedMiddle` → `LocalLogic` (ca432e24): 23

- ad86a700 b420c497 b8b176cf f34268a3: The excluded-middle hypothesis is never used in the proof (the trace finds no occurrence; e.g. the binder is _hEM). Any weaker version, or none, suffices: the premise could be dropped rather than weakened. Evidence: trace: UNUSED.
- 70b9fa04: EM is used only at x = g in godIsPerfect, with hg : IsGod g and hx : InAct x r, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- ea6317cf: EM is used only at x = g in perfectFromGodCause, with hg : IsGod g and hx : InAct x r, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- 902b55b4: EM is used only at x = g, with hg : IsGod g and hx : InAct x r, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- 1c648123: EM is used only at x = g (hx : InAct x r) and, in namedSource, at g = m, where g is a GOD_4 candidate and m the maximum source (in act in esse by IsMaximumIn), all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- 4c30239f d8529011: EM is used only in namedSource at g = m, where g is a GOD_4 candidate (hg) and m the maximum source (in act in esse by IsMaximumIn), all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- 827fa9cd: EM is used only at g = m (namedSource; m in act as maximum), at x = g (perfectFromSource; hx : InAct x r), and at esseOf g = essenceOf g in godIsInfinite, whose negative branch is absurd, so double-negation elimination for the GOD_4 candidate suffices, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Evidence: trace EM instances; source inspected.
- 0acc8761: EM is used only at x = g (perfectFromGodCause; hx : InAct x r), at k = g (oneFromGodMaximal; k in act as maximal by hMax k hk), and at esseOf g = essenceOf g in godIsInfinite, whose negative branch is absurd, so double-negation elimination for the GOD_4 candidate suffices, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Evidence: trace EM instances; source inspected.
- 6948b865: EM is used only at esseOf g = essenceOf g for hg : IsGod g, and the negative branch is absurd (hKinds and simplicity), so the double-negation elimination in LocalLogic's second conjunct suffices, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Evidence: trace EM instances; source inspected.
- 7366a9b4: EM is used only in godIsInfinite at esseOf g = essenceOf g for a GOD_4 candidate g, whose negative branch is absurd, so LocalLogic's double-negation elimination suffices, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Evidence: trace EM instances; source inspected.
- d25980a4: EM is used only at k = g for GOD_4 candidates g and k, with k in act in esse by hMax k hk (GodIsMaximalInBeing), all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- e7278952: EM is used only in oneFromActualRecipients at g = m, for a GOD_4 candidate g and the maximal witness m (hm.1 : InAct m esse), all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- 482f4ad2 4d1efe91: EM is used only at z = g, for hg : IsGod g and z with MoreIn esse z g, which is in act by hHas esse z g hz, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- acdcf1dd: EM is used only at f = m in firstMoverIsMaximeEns. m is a GOD_4 candidate there (God m by hGod m hMax), and the first mover f is in act in the respect in which it moves (hInAct), all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- 697b7dc4: EM is used only at f = m inside firstMoverIsMaximeEns. m is a GOD_4 candidate (God m by hGod m hMax), and f is in act in the respect in which it moves (hInAct), all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- ee93f52b: EM is used only at f = m (firstMoverIsMaximeEns; God m by hGod, f in act by hInAct) and at x = m with hx : InAct x r, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.
- aba2aba4: EM is used only in maximumIsAncestor at g = n (g a GOD_4 candidate, the source n in act in esse) and at x = n after rewriting n = g (so n is the GOD_4 candidate), with actual : InAct x r, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Evidence: trace EM instances; source inspected.
- ae45ef40: EM is used only in maximumIsAncestor at g = n and k = n, for GOD_4 candidates g and k and the source n in act in esse, all within LocalLogic (ca432e24) instantiated at the theorem's GOD_4 predicate. Caveat: the theorem has no esseOf/essenceOf maps, so only LocalLogic's first conjunct is used, and a re-route must supply those maps or a first-conjunct sibling statement. Evidence: trace EM instances; source inspected.

### 3b2d2d46 `IndependentPriority` → `FirstBeingActPriority` (61ad11f3): 11

- 046e96c9 0acc8761 1a6363fe 334e8640 625e9993 669aca2b 6c6549ae 827fa9cd 8f956c81 b074dfdd ec8182d6: Act priority is used only inside FirstBeingNoPotency.firstBeingNoPotency, applied at f with hFirstBeing : IsFirstBeing PriorSimply f (hPrior f r hPot). FirstBeingActPriority (61ad11f3) on the same InAct, InPotency and PriorSimply supplies exactly this instance. Evidence: trace: every APPLY is @FirstBeingNoPotency.firstBeingNoPotency; FirstBeingNoPotency/Solution.lean:16-23.

### 62b4a40a `Euclidean` → `EuclideanAt` (1b1462e6): 10

- 15374d2f 2754c58d 6f534573 81676321 bcccc94c c9936c30 cdcc49f3 d9cbeaad e5351fc0 f2251a3d: Every use of Euclideanness, including those inside the lemmas it is passed to, has the theorem's selected world w as its first argument (hEuclidean w v z …). EuclideanAt frame w (1b1462e6) suffices; ActualEuclidean.necessaryAtOrigin is the existing weak-version form of this step. Evidence: trace: all APPLY instances have first argument w.

### 6c27657f `GradesByApproachToAMaximumReading` → `GradesToMaximumAtBeing` (e4e6b0cd): 9

- 1c154f2f 210019ee 34d0c2cf 4723de84 5e8e6054 72391d4d abdc26b0 be0cc025 c98328f1: Every application of the grades premise is at the respect esse (via QuartaViaMaximumInBeing.actualCore or directly), i.e. GradesToMaximumAtBeing InAct MoreIn esse (e4e6b0cd); restrictGrades is exactly this instantiation. Evidence: trace: all APPLY (esse ; …).

### d7741cdc `MatterFormAndEsseEssenceAreCompositionsReading` → `MatterFormIsComposite` (6a9199b7): 8

- 13338e9c 1fa790f2 26e368d3 4da3e7db 62bc6263 85e17d75 85fc8c5a ad8e261e: Only the first conjunct (And.left: matter–form → composite) is used, in GodHasIntellect.godHasIntellect, RootIntellectWill.ofNonlimitation or nineGiveDeiFilius. That is exactly MatterFormIsComposite (6a9199b7) on the same ComposedOfMatterAndForm and Composite. Evidence: trace: every APPLY under And.left.

### 2e248016 `ActualDependenceIsGrounding` → `ActualDistinctDependenceIsGrounding` (a8298fbd): 4

- 915ad35a: Applied only at (c, x) after intro c x hne …, so c ≠ x is in context; ActualDistinctDependenceIsGrounding (a8298fbd) on the same m w DependsForBeing suffices. Evidence: Round2Grounding/Solution.lean:24-31.
- f501bad3: Applied only at (c, x) after intro c x hne …, so c ≠ x is in context; ActualDistinctDependenceIsGrounding (a8298fbd) suffices. Evidence: CauseOfBeingHasBeing/Solution.lean: hGround c x hx ⟨hcC, hcE⟩ (hDep c x hne hc).
- 931319ea: Applied at (y, x) where intro y x _ hp binds y ≠ x (SimplyPriorIsActualConcreteGround quantifies over distinct y, x); ActualDistinctDependenceIsGrounding (a8298fbd) suffices. Evidence: Round2Grounding/Solution.lean:37-45.
- eddef85a: Applied at (c, x) where intro c x _ hc binds c ≠ x (NecessityCausesAreActualConcreteGrounds quantifies over distinct c, x); ActualDistinctDependenceIsGrounding (a8298fbd) suffices. Evidence: Round2Grounding/Solution.lean:73-81.

### cf4364f6 `AtomicParts` → `ContingentAtomicParts` (83fdeb19): 4

- 10a47b38 1a621d09 43f9545d abe97ecb: The conclusion is a necessary being (NecessaryBeing m w, or NecessaryConcreteAt via the concrete ontic), and the argument has ExcludedMiddle. ContingentAtomicity.necessaryBeing shows the pattern: either a necessary being exists (done), or every actual individual is contingent, and then ContingentAtomicParts (83fdeb19) yields full AtomicParts, so the original proof runs. For 43f9545d that sibling result is literally the same theorem with the weak premise. Evidence: ContingentAtomicity/Solution.lean:22-41.

### e27489c3 `OwnerCommitmentAt` → `PowerRequiresConcreteAt` (61b6e188), `CausersRequireConcreteAt` (bc2af29f): 3

- 563414ac: Only the second conjunct hFloor.2 (CausersRequireConcreteAt) is used, which is exactly the weak version bc2af29f. Evidence: RootWiring/Solution.lean:44-46.
- 7bd58160: Only the first conjunct hFloor.1 (PowerRequiresConcreteAt) is used, which is exactly the weak version 61b6e188. Evidence: RootWiring/Solution.lean:60-62.
- 84ac831f: Only the second conjunct hFloor.2 (CausersRequireConcreteAt), applied to the universe's cause, is used, which is exactly the weak version bc2af29f. Evidence: Ontology/Naturalism/RefutesN2/Solution.lean:16-20.

### 6dfe01ab `EsseReceivedOnlyInOwnEssence` → `IdentityScopedEsseReception` (65f3d0c7), `IdentityScopedOwnEssence` (b9316115), `RestrictedOwnEssence` (7590d341): 3

- 12bc6bf0 6077cce0 d8509a73: The reception premise is used only in Q44SourceSupply.ownBeingOfIdentity, at a bearer n with hIdentity : esseOf n = essenceOf n (hOwn n r hr). IdentityScopedEsseReception f.essenceOf f.esseOf Received (65f3d0c7, FirstMoverNecessity) is generic over the same maps and reception relation, needs no separate Frame, and supplies exactly this instance. Evidence: Q44SourceSupply/Solution.lean:34-45.

### 0628359b `BeingMovedIsActualizationOfPotencyReading` → `NoMovedWithoutPotency` (6948dde0), `MovedOnlyAsInPotencyReading` (4be9a4ac): 2

- 6838d6af: Proof uses only ((hMotion x r).mp hr).1 : MovedIn x r -> InPotency x r, exactly MovedOnlyAsInPotencyReading (4be9a4ac). Evidence: SuccessionPotency/Solution.lean:22.
- 6a3386c7: Proof uses only ((hAnalysis y r).mp hMoved).1 : MovedIn y r -> InPotency y r, exactly MovedOnlyAsInPotencyReading (4be9a4ac). Evidence: Aristotle/Physics/Typed/NoMoverMovesItself/Solution.lean:32.

### 1773079b `PureActLivesReading` → `NineLiveSomeTime` (280770e3): 2

- 4da3e7db: PureActLivesReading is applied only at g with hNine : HasTheNine … g (via h.immutable), exactly the antecedent of NineLiveSomeTime (280770e3). The sibling nineGiveDeiFiliusLivingFromNine (DeiFiliusLivingNineScope) already proves the same conclusion from the weak version. Evidence: DeiFiliusLivingSelfOperation/Solution.lean: hPureLives g h.immutable.
- b074dfdd: PureActLivesReading is applied only at the root n, for which deiFiliusRoot supplies all nine attributes (h.one … h.will), so NineLiveSomeTime (280770e3) applies. The sibling deiFiliusRootLivingFromNine (DeiFiliusLivingNineScope) already proves the same conclusion from the weak version. Evidence: DeiFiliusLivingSelfOperation/Solution.lean: hPureLives n h.immutable.

### 3b38aa55 `ActualAccessNeedsBelief` → `WitnessAccess` (c18f6b6a): 2

- 28c8e892: ActualAccessNeedsBelief is applied only at the NonresistantNonbelief witness (p, t), which is capable, nonresistant and nonbelieving, i.e. Gap s p t; WitnessAccess (c18f6b6a) suffices. WitnessLocalHiddenness.selectWitness/noGod already run this route from the weak versions. Evidence: Hiddenness/ActualRoot/Solution.lean:19-23.
- c4e41a1e: Only passes the premise to ActualRoot.noGod, where it is applied at the NonresistantNonbelief witness (a Gap); WitnessAccess (c18f6b6a) suffices, as WitnessLocalHiddenness.noRouteGod shows. Evidence: Hiddenness/ActualRoot/Solution.lean:25-30.

### 7361a77f `ActualAlwaysOpen` → `WitnessOpen` (16fde4e8): 2

- 28c8e892: ActualAlwaysOpen is applied only at the NonresistantNonbelief witness (p, t), capable, nonresistant and (hLacks) nonbelieving, i.e. Gap s p t; WitnessOpen (16fde4e8) suffices. WitnessLocalHiddenness.selectWitness/noGod already run this route from the weak versions. Evidence: Hiddenness/ActualRoot/Solution.lean:19-23.
- c4e41a1e: Only passes the premise to ActualRoot.noGod, where it is applied at the NonresistantNonbelief witness (a Gap); WitnessOpen (16fde4e8) suffices, as WitnessLocalHiddenness.noRouteGod shows. Evidence: Hiddenness/ActualRoot/Solution.lean:25-30.

### 7a22ab5d `AccessNeedsBelief` → `ActualAccessNeedsBelief` (3b38aa55): 2

- 257cf330: AccessNeedsBelief is applied only at s.actual (hBelief s.actual p t hLacks), which is exactly ActualAccessNeedsBelief (3b38aa55). Evidence: Hiddenness/GapHasReason/Solution.lean:12.
- 7d96f15a: AccessNeedsBelief is applied only at s.actual, which is exactly ActualAccessNeedsBelief (3b38aa55); ActualRoot.noGod is the sibling route. Evidence: Hiddenness/NoGod/Solution.lean:15.

### 957a71fe `MaximeEnsIsGod` → `GodNamesTheUniqueMaximeEns` (e39a4fce): 2

- 39c30529 f8992ef7: MaximeEnsIsGod is applied to a maximum m in esse. The weak version GodNamesTheUniqueMaximeEns (e39a4fce) additionally needs CausesAllInGenus at m (from hGenus esse m hMax) and uniqueness of maxima. Uniqueness follows from this argument's own premises: for a second maximum m' ≠ m (excluded middle), hGenus gives CausesIn m m' esse, and CauseOfQualityInAnotherIsMoreSuchReading gives MoreIn esse m m', contradicting the maximality of m'. Re-proof needed; not yet checked in Lean. Evidence: premises include MaximumInGenusCausesAllInGenusReading, CauseOfQualityInAnotherIsMoreSuchReading, ExcludedMiddle.

### dd41c165 `NoContingentConcreteSupport` → `ActualNoContingentConcreteSupport` (84751fc2): 2

- 9de79a41: Applied only at the selected world w (hNoCont w ⟨c, hcc⟩ … hce hna hcg), to a support edge at w from an existing source. That instance is exactly ActualNoContingentConcreteSupport (84751fc2) on the same concrete ontic and support relation. Evidence: NecessarySupportCoverage/Solution.lean:101-103.
- e099de52: Applied only at the selected world w (hNoCont w ⟨y, hy.1⟩ ⟨x, hx.1.1⟩ …). That instance is exactly ActualNoContingentConcreteSupport (84751fc2). Evidence: ClosedGroundingRoots/Solution.lean:96-110.

### e27ea8e3 `ActualConcreteBorrowingEscape` → `WholeRosterNotTrapped` (5c898d24): 2

- 0d88a858: Escape is used only at the whole actual roster Set.univ, which is made nonempty by hPop, to obtain supply. With hPop and hEM, WholeRosterNotTrapped (5c898d24) gives an actual root (WholeRosterFoundation.actualRootExists), and SupplyRootEquivalence turns that into ActualConcreteSupply. The rest of the proof is unchanged. Evidence: ConcreteExistentialSupply/Solution.lean:65-77; WholeRosterFoundation/Solution.lean:34.
- c9b9d4a5: Only passes the premise, with hPop and hEM, to necessaryConcreteOfBorrowingEscape, which uses Escape only at Set.univ. WholeRosterNotTrapped (5c898d24) with population and EM gives the same supply (see arg 0d88a858). Evidence: NecessaryWitnessConnection/Solution.lean:23-27.

### ef69a630 `LocalCausalPrinciple` → `SelectedActualCausalCoverage` (d8a1fb16): 2

- 9b14e6d7: Applied only at the selected world w (hLocal w x hcont), and the distinctness conjunct is discarded (obtain ⟨y, hyE, hyx, _⟩). SelectedActualCausalCoverage (d8a1fb16) on the same ontic and world suffices. Evidence: Round2Grounding/Solution.lean:98-104.
- 10a47b38: Applied only at the selected world w (source_necessary_at m w …, which calls hCausal v c with v := w), and distinctness is discarded. SelectedActualCausalCoverage (d8a1fb16) suffices. ScopedActualCausality.necessaryBeing (selectedSourceNecessary) is the sibling using exactly that premise. Evidence: AtomisticNecessaryBeing/Solution.lean:18-30; PossibleCausalSourceNecessity/Solution.lean:19-27.

### fd12ad3d `NoInfiniteActualEsseCauseRegress` → `ClosedActualEsseCollectionsRooted` (20babef7), `NoInfinitePerSeActualEsseCauseRegress` (ea251340): 2

- 6503fc58: ClosedEsseSource.distinctSourceOfClosed proves the same conclusion EveryDistinctEsseHasEsseIsEssenceSource from the same remaining premises (DistinctEsseHasOtherActualCause, ExcludedMiddle) with ClosedActualEsseCollectionsRooted (20babef7) in place of well-foundedness. Evidence: ClosedEsseSource/Solution.lean:55-66 vs EsseSource/Solution.lean:75.
- 5ab6cc2b: Well-foundedness is used only through not_transGen_self, to show that the identity source n has no actual esse cause. Sketch with ClosedActualEsseCollectionsRooted (20babef7), not Lean-checked: the actual ancestors-or-self of n form a ground-closed collection, so it contains a root r. If r has distinct esse, hSource gives an identity source of r, which equals n by hOne, so r has a cause and is not a root. Hence r has esse = essence, so r = n by hOne (excluded middle decides), and n is uncaused. The rest uses hSource unchanged. commonSourceOfClosed is a related sibling with hOther instead of hSource. Needs a Lean re-proof before re-routing. Evidence: EsseSource/Solution.lean:97-112; ClosedEsseSource/Solution.lean:70-87.

### cffad050 `CauseOfBeingIsMoreInBeing` → `IdentityCauseAscent` (8176a284): 2

- dd09ba2e: Applied only at (e, m), where e is the common uncaused cause, identity e he hu gives esseOf e = essenceOf e, and he and hm.1 give both in act. That is exactly the antecedent of IdentityCauseAscent p MoreIn (8176a284). Evidence: AggregateEsseCause/Solution.lean:98-125.
- f4df2153: Applied only at the common source n, which has esse = essence by hSource. SourceScopedAscent.maximalCausesFromIdentityAscent (arg 0609389b) is the same proof with IdentityCauseAscent (8176a284). Evidence: MaximalFromEsseSource/Solution.lean:22-40 vs SourceScopedAscent/Solution.lean:61-80.

### 0edc0b38 `GodLoves` → `ActualGodLoves` (5e5aa271): 1

- 7d96f15a: GodLoves is used only at s.actual (hLove s.actual hGod), which is exactly ActualGodLoves (5e5aa271). Evidence: Hiddenness/NoGod/Solution.lean:14.

### 251bbfdd `DirectionPassesToMoversOfDirectors` → `SameEndMoverSelection` (e8ffcdad): 1

- 6535db07: The induction needs, for a director f of natural body x that is moved by another, some director of x that moves f, and SameEndMoverSelection (e8ffcdad) supplies such a mover with hx : NaturalBody x (introduced but unused here). Its sibling fromSelection (DirectorInheritance, arg b076343a) runs the same regress with the weak version, and this route's hReduction and hNotBoth supply the distinct mover that MovedByAnotherReading supplies there. Evidence: QuintaViaDirectorRegress/Solution.lean vs DirectorInheritance/Solution.lean.

### 962a62c9 `AlwaysOpen` → `ActualAlwaysOpen` (7361a77f): 1

- 7d96f15a: AlwaysOpen is applied only at s.actual, which is exactly ActualAlwaysOpen (7361a77f); ActualRoot.noGod is the sibling route. Evidence: Hiddenness/NoGod/Solution.lean:14.

### 3b40009e `GoodGeneralFavouringIsApprehension` → `RootGoodGeneralFavouringIsApprehension` (b371638a): 1

- cc00d109: Applied only at r with hr : ActualRoot m w r (intro r hr); RootGoodGeneralFavouringIsApprehension (b371638a) on the same m w Has favours … suffices. Evidence: ImpersonalFoundationJoint/Solution.lean:72-87.

### 4ccb319f `CauseOfBeingInActAsToBeing` → `CauseOfABeingHasBeing` (4a5a43a5): 1

- 42908cf8: Applied at (c, x), where hDistinct : DistinctEsseAt p x includes p.InAct x p.esse, so CauseOfABeingHasBeing (4a5a43a5) gives InAct c esse from hCause and hDistinct.1. Evidence: DeEnte/ExtrinsicSource/Solution.lean:54-62; DistinctEsseAt (Question3/Article4.lean:41).

### 78a44599 `PossiblyFoundedComingToBe` → `PossiblyBegunComingToBe` (6d71688e): 1

- 43543f14: Foundedness (Acc of <) is used only to obtain a moment with nothing earlier. BegunComingToBe.possibleContingentFreePast proves the same conclusion PossiblyContingentsAbsentThenPresent from PossiblyBegunComingToBe (6d71688e). Evidence: ContingentComingToBe/Solution.lean:54-59; BegunComingToBe/Solution.lean:52.

### b699ecfb `CausesHaveActualEndpointsAt` → `WholeCausersExist` (41e17b00): 1

- 5ef4e323: Only (hActual c sum hc).1 is used: some cause c of the selected sum exists. That is WholeCausersExist (41e17b00) for a Frame whose whole is sum. Caveat for the re-route: 41e17b00's frame whole is read as the universe, so instantiating it at the selected fusion sum needs a fidelity check. Evidence: LocalActualFusion/Solution.lean:16-33 (hcActual).

### bbe8900a `ActualPartsExistAt` → `SelectedFusionPartsExistAt` (3423b8ec): 1

- 16e6a153: hParts is applied only to parts of the selected sum (hNoParts sum hFusion.1) and to parts of an existing cause c of sum (hNoParts c hcActual), both SelectedFusionPart m w sum. With hFusion.1 : ExistsAt w sum, SelectedFusionPartsExistAt m w sum (3423b8ec) suffices. LocalActualFusion.necessaryConcrete runs the same argument from the weak version (with a concreteness premise added for its concrete conclusion). Evidence: ActualFusionNecessaryBeing/Solution.lean:14-29.

### be90bb15 `OriginHasProductiveExercise` → `OriginHasProductiveSelfExercise` (83ec280a): 1

- e9a9eeaf: Applied only at (x, x) for a self-originating x (hOrigin x x hCausesOrigin), which is exactly OriginHasProductiveSelfExercise (83ec280a). Evidence: OriginExerciseBridge/Solution.lean:21-24.

### da573220 `CommissionReportsGoBackToJesus` → `Matthew28GoesBack` (5baad26f), `GoverningGrantExists` (568fdb96): 1

- cce0145f: Only the governing component (commission_reports_give_teach_and_governing E hReports).2 : ∃ p, p.Governing = true ∧ E.Gave p is used, which is exactly GoverningGrantExists (568fdb96). selectedChurchOfGoverningGift in the same file already takes that form. Evidence: Round3ChristChurch/Solution.lean:87-107.

### df6c64a6 `DivinePlanRejectsBenefitOmission` → `SomeGoverningPlanRejectsBenefitOmission` (1733629b): 1

- 3095c750: The omission premise is applied only to a governing plan k that coverage supplies. SomeGoverningPlanRejectsBenefitOmission (1733629b) supplies some governing plan that rejects the omission, and recognition (RequiredBenefitIsWilled) holds for every governing plan, so the proof goes through. BenefitPlanWitness.recipientOfSomeGoverningPlan proves the same conclusion from the same coverage and recognition premises and the weak version. Evidence: PracticalSpecification/Solution.lean:16-33; BenefitPlanWitness/Solution.lean:24-41.

### 658814de `NaturalBodiesActRegularlyForTheBestReading` → `SomeNaturalBodiesActRegularlyForTheBestReading` (fa37dde9): 1

- ad5ad184: Only one natural body is used: x from hObs.1, with the directedness of that x. SomeNaturalBodiesActRegularlyForTheBestReading (fa37dde9) supplies such an x together with its regularly attained best end e, which is all the per-body reasoning of eachDirected needs at x. WitnessLocalTeleology.firstMover shows the same derivation from a single witness. Evidence: TeleologyFirstMover/Solution.lean:12-35; WitnessLocalTeleology/Solution.lean:9-29.

## Re-pinned bundle-audit rows

Adding `strong_version_needed` changes the record bytes of these 16 audited arguments, so `bundle_audit.py` required review. Each was re-inspected: only the field was added, and premises, conclusion, inferences, meaning and term links are unchanged. The `reviewed_sha256` was updated and the `finding` appended with a dated re-inspection note.

| audit | argument | record |
|---|---|---|
| classical-attributes-migration.json | 1f42ffcd | `corpus/arguments/CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES.json` |
| classical-attributes-all-migration.json | 07d16972 | `corpus/arguments/CATHOLICISM-QUARTA-VIA-CLASSICAL-WITNESS.json` |
| classical-attributes-all-migration.json | 79252a71 | `corpus/arguments/CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-ALL.json` |
| classical-attributes-all-migration.json | 53819d8a | `corpus/arguments/CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-IDENTITY.json` |
| classical-attributes-all-migration.json | 5d2c8320 | `corpus/arguments/CATHOLICISM-STAGES-ONE-TWO-Q11-NATURE.json` |
| classical-attributes-all-migration.json | d49eccc1 | `corpus/arguments/CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS.json` |
| naming-first-mover-migration.json | acdcf1dd | `corpus/arguments/AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS.json` |
| naming-first-mover-migration.json | db6ab332 | `corpus/arguments/AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS-IDENTITY.json` |
| naming-first-mover-migration.json | 3e86eea5 | `corpus/arguments/AQUINAS-ST-I-Q2-A3-MAXIME-ENS-IS-GOD-VIA-FULL-DESCRIPTION.json` |
| naming-first-mover-migration.json | 3b0f4fa5 | `corpus/arguments/CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES.json` |
| naming-first-mover-migration.json | 1a88e3e9 | `corpus/arguments/CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES-IDENTITY.json` |
| naming-first-mover-migration.json | 44782677 | `corpus/arguments/CATHOLICISM-FROM-PRIMA-VIA-WITH-CLASSICAL-ATTRIBUTES.json` |
| naming-first-mover-migration.json | 57cedd02 | `corpus/arguments/CATHOLICISM-FROM-PRIMA-VIA-WITH-CLASSICAL-ATTRIBUTES-IDENTITY.json` |
| naming-first-mover-migration.json | fd1f7e75 | `corpus/arguments/CATHOLICISM-STAGE1-VIA-FULL-DESCRIPTION.json` |
| naming-first-mover-migration.json | d49eccc1 | `corpus/arguments/CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS.json` |
| naming-first-mover-migration.json | aad2f961 | `corpus/arguments/CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS-IDENTITY.json` |
