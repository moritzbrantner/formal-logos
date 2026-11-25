# Orphan graft map (#1926)

A map of the verified results that do not reach the root, and of the ways they
could join a root route. It is a research note, not a tracker. Counts describe
corpus scale; they are not progress. The grafts implemented with this note are
in `specs/nar-grafts.toml` (Lean: `TruthCore.Causality.NarGrafts`,
`TruthCore.Results.Causality.NarGrafts`); attempt [`e0253e6b`](../../corpus/attempts/e0253e6b-0086-4081-a79e-a4de8f7b1ab2.json).

Baseline: `main` at `61acfd56`, `truth --json orphans --by module|family`:
1,676 of 2,481 verified results disconnected (1,420 non-transcription, 256
transcription). A result counts as connected when its conclusion reaches the
root or when it supports a verified recorded refutation of an `alternative_to`
rival of a root-path node (`truth/README.md`, "`orphans`").

**Coverage.** This is a map of *selected* clusters, about 670 of the 1,676
disconnected results, chosen by size and by nearness to the God-existence
route. The rest is unmapped. The largest unmapped remainder is in
`TruthCore.Causality` (563 disconnected results across about 305 modules, of
which about 70 are covered by the rows below); smaller unmapped remainders
are in Logic, Explanation and Alternatives beyond the named families.

## 1. What separates a genuine graft from a nominal one

- **Genuine:** a verified, non-transcription argument whose premises include
  the orphan conclusion (or certificate) and whose conclusion is a root-path
  node, or a refutation of a recorded rival of one. Every extra premise is an
  explicit open bridge.
- **Nominal (rejected):** a bridge premise "orphan conclusion → root node"
  that the proof only applies (invariant 16), or a relation recorded without a
  rival that actually conflicts with the root node.
- **Conditional rivals:** a rival that conflicts with a root-path node only
  under further premises is recorded with that condition stated in the
  relation note, as `ea6a4838` (the world-level optimizer) and `9d1f08e0` do.
- **Legitimately off-route:** controls, finite models, omission
  countermodels, inconsistency cores ("Logical falsity", 24 results) whose
  rival is not recorded, rival-worldview consistency models, and transcription
  maps of source arguments. They answer questions *about* a route. Forcing them
  in would be nominal.

## 2. Clusters

Size = disconnected results in the area (non-transcription / transcription);
"touch" = arguments with a root-path premise or relation.

| Cluster | Size | Nearest root-route node | Missing bridge | Warrant status of the bridge | Blocker | Value |
| --- | --- | --- | --- | --- | --- | --- |
| Stage 1-2 same-witness endpoints: `UniqueClassicalGodExists` `20a2b6a3` (StagesOneTwo, Q11 and identity witnesses, quarta via classical witness; 8 results, 6 non-transcription) | 8 | `d5ac1620` GodHasClassicalAttributes, a premise of the root arguments | none: `UniqueClassicalGodExists σ → GodHasClassicalAttributes σ` is a uniqueness transfer (`IsTheOneGod`), a genuine two-line derivation | no new premise | `20a2b6a3` carries 40 inherited `definition_ids` (GOD_1/2/4, CAUSE_1/2, PER_SE_1/3, ...), so any new argument from it is an unbridged sense mixing; pruning them to its Lean vocabulary changes records pinned by the reviewed bundle audits (`classical-attributes-all-migration.json`, `naming-first-mover-migration.json`). Support cycle: the existing assembly `398f4323` (classical-god-assembly) concludes `20a2b6a3` from `8626f8a5`, `33b18ae7` and `d5ac1620`, so `d5ac1620` ← `20a2b6a3` closes a cycle; it is grounded through the other seven routes, and the assembly result's own "connection" through it would be nominal | **high, cheap after a reviewed prune** |
| Necessary-root attribute siblings: `73f6b3c8`, `593d7307` (NecessaryFirstBeing), `f2a65d16`, `2c886717`, `124e21e6`, `6c37be2d`, `469b92a8` ("∃ the same actual necessary root with property X") | ~15 | `d164f730` necessary roots (done here from `91b085c4`), and the attribute nodes of the quarta-via bundle `da3facd6` | at-most-one actual root `49fdec01` (existing) | existing premises only | legacy definition links: NECESSARY_11 enters through DEF `f8948e28` (WORLDS_9) and WELL_FOUNDEDNESS_AND_ANTI_BRUTE_ROOT_1 through DEF `c86cc1d1`, while the types reach those declarations only as carriers (the Kripke frame of `Ontic`; `ActualConcreteGround` inside `ActualRoot`), exactly as `d164f730` and `91b085c4` do without the links; no box-over-formulas or well-foundedness sense is used. The prune must keep or re-point a definition for ACTUAL_CONCRETE_GROUND_1. DEFs `baddf770` (DE_RE_NECESSITY_2) and `e1ff44df` (FIXED_ROSTER_2) may be the same kind of residue | high after the same #216 prune |
| Necessary-being totality closures: Kant `NecessaryBeing` `c778a6ca` (ActualCover, ActualFusion, Atomistic, ContingentAtomicity, CountTemporal, Witness, ScopedActualCausality; Explanation's Accessible/Autonomous/FixedConstituent/WeakAccount) | 21 | the necessary horn of `NecessaryRootFork`, `91b085c4` | "the necessary individual is concrete and an actual root" | open and substantive: this is the concreteness obstacle (93 attempts in #1926), not a formality | a bridge that only asserts it would be a transcription | medium; needs a concreteness argument |
| Optimal creation / selected effect (Modal: `OptimalCreationChoice` `1822b59d`, `SelectedEffectBridge` `2757f6a3`, `SimplicityCollapse`) | ~10 | WN `0266eac2`, (a) `fbd0a6d3` | the giving-output adapter (`givingProfile`) | definitional adapter, no new primitive | none for the certificate (**done, G1**); `SelectedEffectBridge`'s necessity theorem needs `RealizedOutputs`, which ties `Ontic` causes to giving and is not asserted | done for `1822b59d`; medium for the rest |
| NAR / WN controls (`b8ee1a50`) and other premise-free certificates of root-route batches | many | the batch's own rivals | none: use the certificate as a premise of a refutation or derivation that needs one of its laws | premise-free | only where a law is genuinely used | done for `b8ee1a50` (G1) |
| Retorsion (Logic: EpistemicNihilism, Knowledge, Scientism, Verificationism, Relativism, AssertionRetorsion side outputs) | ~40 | floor items with sceptical rivals: observation `fbc516c1`, non-contradiction `c425f0c5`; the cogito premises `b45ca9db`, `1edfc1d1` | audit the exact rivals and reuse the already registered relations; see §6 | premise-free certificates are not necessarily premise-free refutations | scope, actuality and witness alignment; a nominal alternative or circular floor defence is invalid | **high** for comparison, conditional for root grafts |
| Rival refutations of route premises (Alternatives: Megarian, Night cosmogony, McTaggart, inertial rival, potency partition) | ~30 (29 touch) | prima via premises, e.g. `bc4051e9` "whatever is moved is in potency" | re-record the rival as `alternative_to` where it is now an `attacks`, or where no relation exists | the refutations exist; most rest on open premises and would not count | per rival: is it the denial of that premise? | medium-high |
| Naturalism (Ontology: refutations of N1, N2, N3, N3i; `Outside`, `Atemporal`) | ~10 | GOD_4 exists `8626f8a5` or the root's concreteness node | N1 is a rival of `8626f8a5` only with "GOD_4 is not a part of spacetime" | open bridge | without it the `alternative_to` would be nominal | medium |
| First being and act/potency (`0cf675c4` "the first being is in potency in no respect", 5 results; ActPriority, EsseCausePriority, DependenceGroundingPriority) | ~15 | PURE_ACT nodes of the attribute bundle | identify "first being" with the selected actual root (simple priority vs grounding: #1942's one order) | open, partly done by #1942 | sense splits (PRIOR_1 vs PRIOR_4, #1950) | medium |
| GOD_4 unicity `33b18ae7` (DirectEsseRootGodUniqueness, NecessaryRootGodUniqueness) | 4 | `IsTheOneGod` clause consumed through `20a2b6a3` / `b9816722` | as in the first row | none | the same over-linking | medium |
| Dependence-order senses (#1942/#1950: PRIOR_4 well-founded, existential per se series) | 7 | consumers of `86efed1a`; the secunda via join `3d01134d` | PRIOR_4 siblings of the PRIOR_1 consumers | open (#1950 next tests) | per-sense arguments | medium |
| Modal library (K/T/S4/B/S5 modal-collapse results, StandardCorrespondence, actualist domains) | ~90 | T schema `cb456382`, KT reading `0aa36cd6` on the fork route `8df2faad` | reflexivity of the route's frame (T validity ⇔ reflexivity is proved in `StandardCorrespondence`) | `0aa36cd6` names frame class KT but asserts no frame law | the fork route is the packing artifact of #1940: these leaves do no work at the root step | low until the phase-4 packing view |
| Explanation / PSR (PSRStrength, StoppingPoints, GroundingBaseline, brute-contingency parity) | ~100 | `c71c068c` EveryContingentGroundedAt (root path) | reason-for-existence ⇒ concrete grounding inclusion | open; rigor contract 5 forbids identifying them | an explicit inclusion bridge with its own warrant | medium |
| Aristotle Physics maps | 110 (102 transcriptions, 8 not) | prima via premises | none for the transcriptions, which close nothing; the 8 non-transcription results are not examined here | — | invariant 16 | off-route (transcriptions); 8 unexamined |
| Comparison, Metaethics, Hiddenness, Mereology, Science, Epistemology, Greek, Modern, Kant | ~190 | stage 3 and comparative questions; Hiddenness `NoGod` against `8626f8a5` | rival-model consistency, not support; `NoGod` needs the hiddenness God identified with GOD_4 (bridge candidate 02) | open | most are legitimately comparative | low for the God-existence phase |
| Isabelle Gödel/Scott (18) | 18 | `8626f8a5` | "God-like ⇒ GOD_4" | a naming bridge from positive properties to the classical attributes; nominal unless the attributes are derived | transcription risk | low |

Two orphan pieces compose in the implemented G1: the #1737 certificate
supplies stability, #1947's controls supply law 2, and neither alone touches
the root. The first two rows compose the same way once unblocked: an orphan
existence-with-property conclusion plus the root-path at-most-one premise
`49fdec01` yields a root-path universal.

**Main mechanical blocker found.** The most valuable grafts are blocked by
inherited `definition_ids` on hub conclusion statements, not by missing
philosophy. The sense rules treat every linked sense as used, so a hub that
lists the vocabulary of its whole derivation cannot be a premise of a new
argument. The fix is a reviewed prune of each hub's links to its Lean
vocabulary (#216), with the bundle audits that pin those records re-reviewed.

## 3. Implemented grafts

- **G1** (`6c2ae534`, `optimalRivalRefuted`, zero axioms). The rival
  `b72a790a` is a narrow being-level "one best effect" variant: every actual
  root gives by total optimal output over a fixed candidate set of beings and
  quality scale, with at most one optimal candidate. Since every given being
  is optimal and at most one is, **a unique optimum makes each root give being
  to exactly one being at each accessible world where it exists; with (b1)
  and the common root's reach there is at most one actual concretum besides
  the root.** It is closer to *ex uno non fit nisi unum* than to Rowe's
  world-level argument, which is not represented. It is refuted from #1947's
  law-2 premises (b1) `2dd1f217`, factive giving `3ef41442`, the common root
  of `0c27f65a`, necessary roots `d164f730`, some contingent `c76b6e2c`, and
  the two premise-free certificates `1822b59d` and `b8ee1a50`. It does not use
  WN or SS. The refutation does not count (#999): its premises are open.
  `0c27f65a` stands for the bare common root `a6b46d2e`, which is blocked by
  legacy links (gap 5 of [nar-derivation.md](nar-derivation.md)).
  - *Scope.* It excludes the rival only through law 2, and so only through the
    common root's direct reach. It does not touch the mediated creator: #1947's
    `chainG` satisfies the rival with candidates `{g}` (G3's `MediatedOptimum`). Nor does it touch the
    world-level optimizer, Rowe's argument, ties, a no-best regime or selective
    necessary diffusion.
  - *Recorded rivals of WN.* `b72a790a` is not WN's only recorded alternative.
    This batch also records two standing rivals, unrefuted:
    - selective necessary diffusion `ea1425c0` (`SelectiveNecessaryDiffusionAtRoot`);
    - the world-level optimizer over complete outputs, ties allowed `78af5042`
      (`ActualRootsGiveOptimalCompleteOutputs`).

    WN therefore cannot become "defended" by refuting the one-creature
    surrogate alone. The conflict of `b72a790a` with WN is itself conditional:
    it needs SS and a rational exercise (G3 law 3).
- **G2** (`7670662c`, `necessaryRootsFromUniqueNecessaryRoot`, zero axioms).
  `d164f730` (every actual root is NECESSARY_2, bare until now; gap 6 of
  [nar-derivation.md](nar-derivation.md)) from `91b085c4` (a unique necessary
  actual root), registered `strengthens`.
- **G3** (`f0eb2f96`, controls, Mathlib three axioms). Law 1: under
  `givingProfile`, stable output is fixity toward each given being. Law 2: a
  unique optimum makes a root fixed toward every effect, so two-way toward
  none, so a unique-optimum root cannot be a mixed-mode root. Law 3: with SS,
  a unique-optimum root that gives another being by a rational exercise makes
  WN fail. Law 4: such a root gives being to at most one being at `w`. Law 5: with
  (b1) and the common root's reach, it leaves at most one actual concretum
  besides itself. Model `MediatedOptimum`: on `chainG` the rival holds with
  candidates `{g}`, direct reach fails and some concretum is contingent, so
  without direct reach a unique-optimum root can be a mediated creator. Model
  `TiedOptimum`: the refutation's other
  premises hold, the root gives by total optimal output over two tied
  candidates, and here the tied root is two-way toward a contingent. Encoding
  disclosures: quality is constant, `G` (`gGroundsOthers`) and existence are
  fixed by construction, the frame's `Ontic` causal field and other relations
  are empty, and `d` exists only at the second world. A control, legitimately
  off-route.

Computed effect: `d164f730` moves from bare to closed (proved from open
premises, not established); `1822b59d`'s result `a1990e04` and `b8ee1a50`'s
result `0cf250b9` now reach the root through the recorded refutation; G3 is a
new off-route control (net orphans 1,676 → 1,675).

## 4. The WN / optimal-creation finding

[nar-derivation.md](nar-derivation.md) lists Rowe's argument among WN's
rivals and excludes Leibniz, whose moral necessity is not a metaphysical
fixity. `OptimalCreationChoice` formalizes a metaphysical, being-level
version: total optimal output plus a unique optimum gives cross-world stable
output. Composed with the root's giving, it yields a **narrow rival
refutation, not a constraint on the selective rival**:

- **Refutation (G1).** The being-level one-best-effect root is incompatible
  with the premises of law 2. Its derived price: deny that the root is
  necessary, that some concretum is contingent, (b1), factive giving or the
  common root's direct reach, or the uniqueness of the optimum. The first two
  together are modal collapse of what the root gives.
- **No constraint on the selective rival.** A unique-optimum root cannot be a
  mixed-mode root, because it is fixed toward every effect and gives being to
  at most one being at `w` (laws 2 and 4). Without direct reach, however, it can be the
  mediated creator: `chainG` satisfies the rival (`MediatedOptimum`), so being-level optimization *can* select a necessary
  intermediary, and G1 does not touch that case. With direct reach it
  collapses to one creature (law 5). Ties do not force fixity (`TiedOptimum`, in one
  encoding).
- **What it does not show.** It leaves untouched:
  - the mediated creator, a rival of G1's reach premise `0c27f65a`, which may
    be the historical Avicennian system (*Ilāhiyyāt* IX.4, unread);
  - the world-level optimizer `78af5042` (one best complete output, or a tied
    family whose members all contain `d`);
  - Rowe's world-level argument;
  - ties (`TiedOptimum`);
  - a no-best regime (where #1737's certificate shows no candidate is
    optimal, so the rival's total optimal output cannot hold);
  - selective necessary diffusion `ea1425c0`, which needs no optimization
    premise. Its Lean statement fixes the root toward some `x`; neither
    necessity nor intermediacy of `x` is stated. The diffusion component is
    cited to Plotinus, Avicenna and Kretzmann (navigation); no source is
    recorded as holding the combination with free giving of the contingents.
- **Warrant for WN:** unchanged overall (moderate, on the means-to-end
  reading). One narrow rival variant has a recorded conditional refutation
  that does not beg the question against WN. Standing rivals of WN: selective
  diffusion (`ea1425c0`) and the world-level optimizer (`78af5042`), both
  recorded as `alternative_to` WN and unrefuted. The mediated creator is a
  standing rival of G1's reach premise, `0c27f65a`.

Revision conditions: a world-level `OptimalOutputs` over complete outputs
that keeps law 2's premises would test the world-level optimizer; a selection
principle for `d` from diffusion would sharpen the WN dispute.

## 5. Next graft slices, ranked

1. Reviewed prune of `20a2b6a3`'s definition links, with the two bundle audits
   updated; then `d5ac1620` from `20a2b6a3` (8 stage 1-2 endpoints join).
2. The same prune for the `73f6b3c8` family; then existence + `49fdec01` to
   the attribute nodes.
3. Retorsion: distinguish counted refutations from conditional comparisons;
   use §6's exact target and bridge audit rather than adding blanket rivals
   to observation or cogito premises.
4. Alternatives refutations re-recorded as `alternative_to` the prima via
   premises they deny.
5. World-level optimization (`78af5042`) against law 2, and the mediated
   creator against direct reach (continuation of G1).
6. Naturalism refutations with the bridge "GOD_4 is not a part of spacetime".
7. The `c778a6ca` family through a concreteness argument.

## 6. Retorsion graft audit (#1926, #1963, #1007, #1008)

Baseline: `5bf0ce3656c1b9b6c94807c1b862d621f451be68`. The roughly 40
orphans in the original map are a historical estimate, not a fresh count.
This is a draft semantic and relation audit of the named clusters, not a
new Lean verification or a claim of exhaustive orphan coverage. Reuse
[self-undermining-views.md](self-undermining-views.md),
[retorsion dilemmas](../retorsion-dilemmas.md),
[verificationism showcase](../showcase-verificationism.md),
[epistemic-underminer boundaries](epistemic-underminer-boundaries.md), and
[scientism and meaning rival boundaries](scientism-meaning-rival-boundary.md).
The earlier recommendation to put the global sceptical theses directly on
the observation/cogito floor was too broad.

### 6.1 Classification and exact scope

A certificate without external premises can have an implication, a dilemma,
or a satisfiable model as its conclusion. A rival is refuted only if the
conclusion excludes that rival in the same profile. Distinguish:
(1) exclusion of the rival; (2) incompatibility with an additional premise;
(3) self-undermining in warrant, assertion, or acceptance; (4) an unanswered
explanatory demand. Neither (3) nor (4) implies (1). A floor premise cannot
be independently defended by an argument that presupposes that very premise.

| Existing result / argument | Exact rival and threatened proposition | Classification, surviving reading and action |
| --- | --- | --- |
| EPISTEMIC-NIHILISM-SELF-UNDERMINING `ec80b13d` (`f8e82f70`) | Global no epistemic reason `38f44eff`, already alternative to F6 `f56b2ee7` | Premise-free self-undermining, not falsity; the reasonless truth model survives. New non-counting attack `52c867cc`. |
| `146b502b` (`8e216377`) | Same nihilism; F6 in the same relation | Incompatibility assuming F6. New attack `7bb6698c`; no counted refutation of F6's own rival using F6. |
| `40ae0ae9`, `0c32687e` | Global denial of normative reasons; F6 thin reason witness | No adoption reason under denial, and incompatibility with the F6 witness when the scopes agree. No general proof of normative realism; retain the reasonless model and weaker theories of normative authority. |
| LOGIC-KNOWLEDGE-RETORSION `72288c48` (`c9cb4b0b`) | Universal ignorance (no knowledge), not no epistemic reasons or no motion | Factivity is a theorem-internal antecedent. Known universal ignorance is impossible; mere ignorance, suspension, and false assertions remain possible. Need a known proposition in the same profile to refute ignorance. |
| WITTGENSTEIN-UNIVERSAL-DOUBT-FAILS | Actual universal doubt `b30587bf`; failure `1994160a` (already related) | Given the exemption condition, active universal doubt fails. Not a refutation of suspension, ungrounded hinges or denial of sensory warrant. Does not imply F4. |
| SCIENTISM-STRONG-DILEMMA `0a3d0ed8` (`98451a18`) | Scoped norm `d190bb85`; exact global negative existential `66e84d62` is already alternative to `70118ddd` | Two horns under `2faf3d39` (self in scope) and `aa9893e1` (self not empirically established). New attack `4feb048b` on scoped norm only. Truth without establishment, restricted scope and comparative scientism survive. |
| SCIENTISM-SCOPE-GUARDED-NONEMPIRICAL-NEGATIVE `2a84bfbe` | Global absence of established nonempirical claims `66e84d62` | Scoped norm alone is insufficient; existing bridge `31cf9a3d` transfers a nonempirical witness into scope. Stronger scope premises `deea0f62` and `eb89527e` are not automatically established. |
| Weak scientism demarcation / weak model | Restricted establishment norm | Survives the dilemma if the formulation is out of scope. No edge to F1/F4/F6 merely because a rival favors scientific methods. |
| RELATIVISM-NO-ABSOLUTE-TRUTH-SELF-FALSIFYING `dbc2fb38` (`114d2581`) | Scoped no absolute truth `a249ccbc`; global `bff72296` already alternative to `f625ad83` | Under `5c18a8c4` (scope) and `de454f1e` (disquotation), the formulation cannot be absolutely true. New attack `322d4ccb` on scoped denial. Relative-private assertion and exemption survive. Neither objective truth nor classical noncontradiction follows. |
| TRUTH-NONTRIVIALITY-CORE; LOGIC-NOT-EVERY-PROPOSITION-FAILS / HOLDS | Every proposition is false or every proposition is true in the encoded logic | Logical controls distinguish true and false propositions. A transfer to a rival's object-language truth or negation needs semantic calibration. These are not refutations of every relative or paraconsistent logic. |
| VERIFICATIONISM-SELF-APPLICATION-DILEMMA `0bd651df` (`a3c1988e`) | Scoped verification principle `12527c0e` | Conditional under `6dc3f04a`, `4e72c49e`, `18b8adb3` (scope, nonanalytic, nonverifiable). New attack `42900430`, not an unconditional exclusion. Criterion as proposal or scoped norm survives. |
| V1 law exclusion (`32b3030e`) | V1 package `895fc3f2`; weak negation closure floor `3f979107` | Existing refutes relation; relies on approved weak closure and package conditions. Do not broaden to every verification criterion or all empirical inquiry. |
| AYER-1936-EXCLUSION-FAILS (`c93862da`) | V2 package `92ad4e06` | Existing premise-free refutation of the exact package with unrestricted auxiliaries; no new relation needed. Restricted auxiliaries need separate tests. |
| CHURCH-1949-TRIVIALIZATION; AYER-1946-EXCLUSION-FAILS (`00ceab1d`) | V3 exclusion package `fd01a8b5`; Ayer-1946 negative exclusion | Existing refutation of the specific package; the observation setting is inside the construction. No blanket positive meaningfulness or truth of every sentence. |
| AYER-1946-EXCLUDES-A-NEGATION-FAILS | Stronger V3 exclusion against strong negation closure | Keep the additional closure condition and observation assumptions. Existing V1/V2/V3 results do not exclude V4's joint proposal survivor, which avoids truth assertion; its adequacy as a replacement for ordinary meaning is a separate issue. |
| `bec15d81` (`8a3dcfc2`) | No meaningful content `aee6dbdf` vs some `f7e3ad49` | Existing exact alternative and refutes relations under actual assertion and meaningfulness; the speech-marker control survives. Not automatically an attack on verificationism or a proof of a particular God sentence. |
| `2f466ae8` (`8cb04e80`) | No belief `b1f30c51` vs some belief `98f4c491` | Existing exact alternative/refutes; sincere actual assertion is required. Insincere utterance and reason without belief survive. Folk-taxonomy revision need not deny this belief relation. |
| `0c9d64e6` (`397c1b44`) | No phenomenal occurrence `4ef2306a` vs some `77e57686` | Existing exact alternative/refutes under the occurrence and phenomenal realization premises. Nonphenomenal markers and taxonomy revision survive; no physicalism-wide refutation. |
| `46c875b1` (`afc88915`) | Nothing exists in interpretation `82441670` vs some `43253cd8` | Existing exact alternative/refutes under occurrence and representation. Need world-specific existence; cannot infer concrete existence merely from a syntactic token. |
| `cc1a4204` (`f93f2dfd`), COGITO-PERFORMED-DOUBT-SELF-REFUTING (`8697bb2d`) | No thought occurrence, exact negation of `e81971f1` in the same Occurs predicate | Actual assertion `b45ca9db` and realization `1edfc1d1` yield a thought. A performed denial can defeat its content, but the certificate does not supply a performance. Omission control `306fab99`; no blanket rivals on the assertion premises. |
| `bfda68fd`, controls `f7df7705`, `3fab8a6b` | Accurate performed denial of episode occurrence | Certificate rules out accurate denial in that profile. Empty and static controls prevent inferring existence or change unconditionally; F4 requires something actually moved in some respect. |

The remaining underminer results in the existing boundary note are
cross-checked at the consequence level; their precise premise IDs,
calibrations and model boundaries are retained in that note and attempt
`7a269548`. They are not independent grounds for F6:

| Result | Threat / exact consequence boundary |
| --- | --- |
| `1db47fd9`, control `cf896bd6` | No justified beliefs; eligible reason uptake plus warrant calibration can yield warranted acceptance. Thin reason without warrant remains. |
| `0ce1e941`, control `721646f2` | No reliable method; reliability on a selected benchmark, not reliability of all reasoning or independently verified actual warrant. |
| `e03147fa`, control `b203c461` | No valid inference; identity inference in the chosen semantics is valid, an invalid inference is also possible. Does not settle every rival logic or identify truth with a method. |
| `d2b63ed6`, `2930b66a` | Denial of preference-independent epistemic authority; conditional incompatibility with the specified actual-force, answerability and preference conditions, not with thin F6 alone. |
| `a70546f7`, `721646f2` | Invariant answer across opposite-truth states is incompatible with accuracy at both; responsiveness alone is not accuracy. |
| `64e1aa15`, `20ed92f4` | Requiring a known prior premise plus well-foundedness excludes knowledge; weak certificate or non-well-founded alternatives survive. |
| `fe69aa38`, `eea262e9`; `60425b3c`, `92a88754` | Evolutionary and debunking challenges under their reliability/history conditions. Conditional, not a refutation of naturalism; retain the stated models and history alternatives. |

### 6.2 Root-route alignment (no new substantive premise)

The actual root is `8626f8a5-9531-5da7-9ebd-f901e74b1129`. There are two
already merged relevant derivations on this baseline, not proposed new work:

- #1979: assertion plus realization gives thought; phenomenal realization
  gives experience. With the appropriate existing bearer premise the
  episode yields a bearer (`06ce17e9`); the existing presence and esse
  contract yield concrete population (`6801590a`, `56f68b40`). The
  bearer must be of the relevant occurrence, not merely an arbitrary
  asserting agent.
- #1980: `1db47fd9` feeds warranted acceptance; `b3ddb7c4` under
  AcceptedWarrantNeedsBasis and SurvivingBasisGivesReason supplies F6;
  `b50727e1` under ReasonBearerPresentAt and the esse contract supplies
  concrete population `56f68b40`. The direct-esse argument `72391d4d`
  consumes this population on its way to the God-existence root. The
  eligible-uptake argument already has a reason among its inputs, so the
  full chain is not an independent proof of F6.

Thus the exact nihilism, occurrence and existence objections concern
real root-path requirements, without assuming that the objections
establish those requirements. F1 `c425f0c5` is classical case
noncontradiction; its exact recorded rival `e5097538` and existing
refutation are logic-relative. F4 `fbc516c1` is something moved in some
respect; the two standing motion/judgment rivals remain distinct. No
reason, belief, or semantic witness by itself supplies motion. Knowledge
scepticism attacks a different notion from the existential fact observed.

### 6.3 Proposed semantic bridges and discriminating tests

These are reproduction targets, not newly certified Lean results or corpus
premises. The arrows below preserve the same predicates and scope; a
propositional implication is not a claim of its antecedent's actuality.

1. **Occurrence:** with the exact shared `Occurs : Episode → Prop`,
   `ThoughtOccurs Occurs → ¬ NoEpisodeOccurs Occurs` follows by applying
   the negative existential to the witness. Check whether the exact
   negation already has a statement ID before proposing a new statement
   or relation. Reuse `cc1a4204` for actual occurrence from assertion and
   realization; the empty and static controls defeat unconditional
   occurrence and motion grafts. Do not add alternatives to
   `b45ca9db` or `1edfc1d1` unless the rival really denies the
   respective assertion or realization condition.
2. **Scientism:** in one existing EpistemicFrame, for a content p,
   `E.established p ∧ ¬ E.empiricallyEstablished p ∧ scope p →
   ¬ ScopedScientism E scope`. This is direct norm application;
   use the existing dilemma or witness-transfer route rather than a
   duplicate derivation. The unresolved work is an independently
   warranted nonempirical p and its scope membership. A Lean proof or
   owner-approved premise is not by definition an actual established
   claim in E. Test a logical theorem as p with explicit calibration,
   and retain the model where the criterion is restricted to
   empirical questions or the thesis lacks establishment.
3. **Absolute truth:** if the content d is in scope and disquotes the
   actual scoped denial, and the same profile asserts that d is
   absolutely true, derive contradiction by the existing
   self-application result. To use the global denial, show that the
   scoped content actually expresses the global quantifier (not just
   a restricted denial). An independent absolute-truth witness
   `∃ p, trueAbs p` in the same profile directly contradicts global
   absence. Negation of global absence alone is not constructively
   such an existential. Do not identify the rival's relative truth
   with attitude-independent truth or Lean's Prop.
4. **Meaning:** reuse `MeaningDefinitionFork.Calibration`, which
   connects the independent predicate M to criterion verdicts only
   on its specified scope. For designated content g, a God-existence
   application requires a content/world interpretation
   `Holds(w,g) ↔ GodExists(σ)` and compatibility of negation,
   scope, observation and world assignments. This is a proposed
   semantic alignment, not a proof of GOD_4. V3's Church-observation
   result can constrain criterion verdicts of g or its negation
   in the matched profile; stronger closure supplies additional
   consequences only with that closure. The actual meaning of g
   cannot be inferred from a refuted criterion, and the truth of g
   cannot be inferred from meaningfulness. Test restricted auxiliaries
   and the existing V4 proposal survivor.
5. **F6 / knowledge:** an actual reason for some p in the same R
   directly contradicts `∀ a p, ¬ R a p`; `146b502b` already
   implements this from F6. Do not elevate its attack to a counted
   refutation of the rival on F6. A distinct known p (with the
   factive knowledge predicate) contradicts universal ignorance,
   but neither the no-knowledge certificate nor thin F6 produces
   such a witness. For #1980, perform the matched recount described
   in `7a269548`, observing the investigator and residual defeaters;
   this can motivate the existing local calibrations without
   postulating a new global epistemic law.

### 6.4 Registered checkpoint and local reproduction

Five new `attacks` relations reuse existing argument IDs and target
statement IDs; no `alternative_to`, `refutes`, theorem, result, floor
marking, or new philosophical assumption is introduced. Existing
refutations, conditional refutations and surviving countermodels remain
unchanged. The relation changes connect the rival comparison graph, not the counted
orphan refutation-support walk. Static inspection: `truth/src/frontier.rs`
separates attacks into its objections map, and `truth/src/orphans.rs`
seeds refutation support only from verified argument `refutes` edges to
recorded root-path alternatives. The existing regression
`verified_refutation_support_connects_without_closing_open_premises`
explicitly tests that an argument attack does not count as that support.
Accordingly the predicted change is comparison visibility, not proof
closure or newly connected results by this mechanism. This is a source
inspection, not a computed numerical delta. All five committed relation
files were reread as JSON and checked for the exact expected IDs,
endpoint kinds, unique subject/object pairs, nonempty notes and predicate.

Repository reads and endpoint/meaning inspection were possible via the
GitHub connector. The local shell cannot fetch the repository or run
Cargo/Lean/the project CLI. No independent semantic challenger was
available. This is a draft checkpoint: full validation and independently
reviewed scope alignment are required before promotion. In particular,
no frontier or orphan delta is asserted, even if a relation-only change
is expected not to change the counted frontier. No historical theorem
has been reverified in this checkpoint.

Run in a normal checkout, on the PR head; use the actual merge base for
the final comparison:

```bash
gh pr checkout 1987
git fetch origin main
base=$(git merge-base HEAD origin/main)
root=8626f8a5-9531-5da7-9ebd-f901e74b1129
cargo build --locked --release -p truth
truth=target/release/truth
"$truth" check
cargo test --locked -p truth verified_refutation_support_connects_without_closing_open_premises
"$truth" bind-check --affected --base "$base" --head HEAD
"$truth" --json frontier --reaching-root --routes --frontier-root "$root"
"$truth" --json frontier-diff --base "$base" --head HEAD --frontier-root "$root"
"$truth" --json orphans --frontier-root "$root" --by module
"$truth" --json orphans --frontier-root "$root" --by family
"$truth" --json orphans --base "$base" --frontier-root "$root"
"$truth" --json frontier-diff --base "$base" --head HEAD
"$truth" --json orphans --base "$base"
"$truth" --json semantics "$root" --frontier-root "$root"
"$truth" --json bind-check --result ec80b13d-0c87-5f71-bc70-16b42dc4c0e6 --result 146b502b-e5fd-40cf-8a39-9ed2d45e59bb --result 0a3d0ed8-773c-5878-8bbb-aaa61e654d3e --result 0bd651df-63c6-5b96-90df-4b488b1735f1 --result dbc2fb38-580c-5f0c-813d-767076523c8b
```

Compare actual reaching sets, counted refutations, floor states, per-route
leaves and support alternatives, not just cheapest cost or aggregate
counts. Inspect dossier/semantics for F6, F1, F4 and the exact targets in
§6.1; run the existing convention and CI gates. If any relation has a
closure effect, explain the cause or withdraw it. Keep this PR draft
until the scope audit and checks are complete. Subsequent independent
research should prioritize the actual nonempirical witness and the
specific same-profile reason/occurrence witness, rather than manufacturing
new counted refutations from already proved conditionals.
