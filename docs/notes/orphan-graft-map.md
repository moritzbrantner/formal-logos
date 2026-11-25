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

The comparison uses main at `21a64a7ff`, including #1979, #1980 and #1985.
The original estimate of roughly 40 results selected a cluster for investigation.
For the scoped applications and controls below, see
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
| Weak scientism demarcation / weak model | Restricted establishment norm | A restricted empirical norm can exempt its own formulation. If that formulation lies within the broader norm’s domain and is established without empirical establishment, it witnesses `SomeNonEmpiricalEstablished` and defeats the broader norm. [Weak demarcation](../../TruthCore/Results/Logic/Scientism/WeakDemarcation/Challenge.lean) |
| RELATIVISM-NO-ABSOLUTE-TRUTH-SELF-FALSIFYING `dbc2fb38` (`114d2581`) | Scoped no absolute truth `a249ccbc`; global `bff72296` already alternative to `f625ad83` | Under `5c18a8c4` (scope) and `de454f1e` (disquotation), the formulation cannot be absolutely true. New attack `322d4ccb` on scoped denial. A speaker may affirm the exempt formulation as true relative to them. If the formulation is absolutely true, it witnesses `SomeAbsoluteTruth` and defeats global denial. In that case, truth ascent makes every iterate absolutely true, so the restricted denial requires every iterate to be exempt, even when iterates coincide. [Exemption result](../../TruthCore/Results/Aristotle/Metaphysics/ExemptionRegress/Challenge.lean) |
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
| `cc1a4204` (`f93f2dfd`), COGITO-PERFORMED-DOUBT-SELF-REFUTING (result `d7295336`, conclusion `8697bb2d`) | No thought occurrence, exact negation of `e81971f1` in the same Occurs predicate | Actual assertion `b45ca9db` and realization `1edfc1d1` yield a thought. A performed denial can defeat its content, but the certificate does not supply a performance. Omission control `306fab99`; no blanket rivals on the assertion premises. |
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

### 6.2 Which witness reaches the existence argument?

The repository root is Catholicism `53964cbe`. At its God-existence stage
`8626f8a5`, direct-esse argument `72391d4d` takes concrete population
`56f68b40` together with its grounding, actuality and divine-identification
premises. Three witness paths matter here.

- **Bearer of a thought (#1979).** Given an actual assertion, its occurring
  realization and the phenomenal classification, `0c9d64e6` gives an
  experienced occurring episode. With the phenomenal bearer premise `ac0a151f`,
  `06ce17e9` gives a subject bearing that episode. Result `6801590a` takes
  this borne episode, bearer concreteness `a7040bf1` and bearer presence
  `c821487b`. Its population witness is that subject. An impersonal account
  can locate the perspective in the organization of the event and contest
  the bearer premise. The omission control holds experience fixed while
  emptying the bearer relation.
- **Representative of an episode (#1980).** `46c875b1` uses occurrence
  `e81971f1` and episode representation `13b5b929`. With the existence
  extension specialized to the selected world, the candidate is
  `represent e`. The companion `RepresentedOccurrence.assertionWitness`
  retains the asserting agent, selected content and realizing episode when
  occurrence comes from an assertion. Its type does not equate the agent
  with the candidate. The selected-world in-act contract `0436de86` then
  classifies the existing candidate. The populated control has one existent
  and a different classified candidate, so this last step can fail.
- **Representative of a reason bearer (#1980).** `b3ddb7c4` eliminates an
  actual warranted acceptance `6280fbf0` using the surviving-basis
  requirement `0e2bbd59` and favorable-bearing bridge `6b4e3331`. The
  resulting reason belongs to that agent for that content. `b50727e1`
  applies presence `ada25623` to the same pair and `0436de86` at the same
  world to the agent's representative. The producer `1db47fd9` starts
  with eligible uptake of a reason. Following it back to F6 gives no
  independent warrant for F6. The belief-specific concession `3f888d00`
  also requires favorable force for believing the selected content. Force
  for checking or withholding leaves that witness open.

There is already a counted use of the *negative* Cogito result. From the
realization premise `1722a80f`, `d7295336` gives the conditional
`8697bb2d`. Result `a89475b3` applies it to an actual performed doubt
`95c5138f` and uses excluded middle on occurrence `ee4ab504` to recover
`e81971f1`. Reusing the positive realization witness gives the direct path
with the same realization commitment. The bare predicate `NoEpisodeOccurs`
has no standalone statement binding here. Its appearances inside the
conditional and the empty control do not warrant another
`alternative_to` or a premise-free refutation of its truth.
The static occurrence control also leaves F4 `fbc516c1` open. F1
`c425f0c5` already has its case-logic rival `e5097538`; the scoped
absolute-truth dilemma supplies neither a new case contradiction nor its
exclusion.

### 6.3 A nonempirical candidate with a checkable scope control

Let *p* say that, on the one-token carrier, a performed denial cannot
accurately deny **all episodes in the occurrence predicate to which its own
token belongs**. Occurrence and denial may have any extensions on this
carrier. The more general result `bfda68fd` proves *p* by specialization. There is positive warrant for this
claim independent of endorsing an epistemic norm. Given a supposed
counterexample, extract its token `e` and proof `hOccurs` of its
occurrence. The accuracy clause `hNo` rules out exactly the witness
`⟨e, hOccurs⟩`. This proves the universal by examining an arbitrary
counterexample, with no observation of an actual episode and no F6 premise.
[Existing two-line proof](../../TruthCore/Results/Logic/PerformedDenial/NoAccurateDenial/Solution.lean)

Change just the extension targeted by the content: a speaking episode
denies that anyone is singing. In the one-token interpretation
`speaks () = True`, `deniesSinging () = True`, `sings () = False`,
the token occurs and its denial of singing is accurate. This tests why the
same-predicate condition matters. A local Lean replay checked the original
theorem at the populated carrier `Unit` and the following counterexample to
the changed inference. The original theorem reports zero axioms.

```lean
open TruthCore.Logic.PerformedDenial in
example : ∃ (speaks sings deniesSinging : Unit → Prop) (e : Unit),
    speaks e ∧ deniesSinging e ∧ NoEpisodeOccurs sings := by
  exact ⟨fun _ => True, fun _ => False, fun _ => True, (), trivial, trivial,
    fun ⟨_, h⟩ => h⟩
```

For an explicit two-claim comparison let *q* say that the cited Solution
file contains the line `exact hNo ⟨e, hOccurs⟩`. Direct inspection establishes
*q* about that file. In a frame classifying the **grounds used here**,
deduction establishes *p* and inspection establishes *q*. Reading the file
also helps one find the deduction. The difference in grounds is testable:
changing the spelling in the file could falsify *q* while the same-witness
proof of *p* would still go through. In this reading of
`EpistemicFrame`, the norm on both claims fails at *p*. Restricting it to
file observations retains *q* in a populated scope and removes the
counterexample. This is direct application of `ScopedScientism` to a
particular claim, distinct from applying the self-formulation dilemma
`0a3d0ed8` to the scientistic thesis itself.

The following replay makes the classification explicit. The two Bool
values index claims. The first branch requires the proof of *p* and the
second an input for the observed file fact. The empirical column records
only the file inspection admitted in this exercise. This last assignment
is a scope choice for the comparison. A reader's evidence can extend
beyond it.

```lean
import TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial.Solution
import TruthCore.Logic.Scientism
open TruthCore.Logic.Scientism TruthCore.Logic.PerformedDenial
open TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial

-- Bool.true indexes the same-token theorem; Bool.false indexes the file report.
example (FileReport : Prop) (readLine : FileReport) :
    let E : EpistemicFrame Bool :=
      ⟨(fun c => if c then ∀ O D : Unit → Prop, AccurateDenialImpossible O D else FileReport),
       (fun c => c = false ∧ FileReport)⟩
    SomeNonEmpiricalEstablished E ∧ ¬ ScopedScientism E (fun _ => True) ∧
      ScopedScientism E (fun c => c = false) ∧ E.established false := by
  dsimp only
  have proofGround : ∀ O D : Unit → Prop, AccurateDenialImpossible O D := noAccurateDenial
  exact ⟨⟨true, proofGround, fun h => Bool.noConfusion h.1⟩,
    fun norm => Bool.noConfusion (norm true trivial proofGround).1,
    fun _ inScope _ => ⟨inScope, readLine⟩, readLine⟩
```

**Provisional assessment.** The exhibited proof gives strong warrant for
*p* on the fixed meanings and favors counting deduction as a sufficient
ground in its own right. The strongest broader reading of the rival allows
several sufficient grounds: testimony about a reliable checker could
empirically establish that very theorem for someone who cannot reconstruct
it. Having a sufficient deductive ground alone does not decide
`¬ E.empiricallyEstablished p` on that reading. To transfer the result,
fix the audience, whether the predicate tracks actual grounds or available
routes, which reports it has and their reliability, and whether semantic
claims like *p* lie in scope. A calibrated empirical report bearing on *p*
would defeat the proposed negative classification for that audience.
Likewise the proof report by itself supplies no warrant attribution to a
particular believer and no representative at the selected world.

The other retorsions retain distinct conditions. An absolute assertion must
disquote to the same scoped denial. The global negative requires coverage
of all contents. Denying that negative alone does not constructively
supply an absolute-truth witness. An application of Church's criterion to
a God-existence sentence *g* requires `MeaningDefinitionFork.Calibration`
on the relevant scope, a content interpretation relating `Holds(w,g)` to
`GodExists(σ)`, and matching negation, observations and worlds. A verdict
about *g* or its negation does not deliver the existence witness. The V4 language proposal avoids the
truth assertion tested by self-application. For global ignorance the missing
witness is knowledge in the same factive profile. A reasonless nihilist can
forgo offering epistemic grounds for nihilism without contradicting it.
#1985's reviewed basis-defeat result `8f0f44e5` supplies a separate test of
warrant loss for the specified debunker's basis, with actual reliance, other
grounds and calibration still at issue. Its conclusion supplies no positive
reason for believing a claim. [Basis-defeat assessment](self-undermining-views.md#when-does-a-genealogy-defeat-its-own-evidential-basis-1615-2026-11-25)

### 6.4 Graph comparison and issue scope

Relative to main `21a64a7ff`, the five argument-to-statement attacks in
§6.1 and the two in §6.5 add contextual objections. The identity argument takes a content in the
fixed semantics, and the nontriviality certificate constrains globally
denied absolute truth. These entries describe what threatens a rival.
The actual premise bundles remain those of the seven source arguments.
Comparing the sorted result IDs in the module-grouped orphan reports gives:

| Root selected | Disconnected on main | Disconnected here | IDs entering | IDs leaving |
| --- | ---: | ---: | --- | --- |
| Catholicism `53964cbe` | 1,690 | 1,690 | none | none |
| God exists `8626f8a5` | 1,814 | 1,814 | none | none |

All seven objection producers and the two logical witnesses `bfda68fd` and
`b41427d3` remain in both disconnected sets. The computed premise comparisons give **no change**
for both roots (verified support alternatives 661 → 661 and 568 → 568,
respectively). The full reports agree on reaching statements, floor markings,
refutations, statement statuses, support options and routes. Existing V1–V3 refutations and the positive population
routes retain their premise bundles. Reproduce with `truth frontier-diff
--base 21a64a7ff` and `truth orphans --base 21a64a7ff`, repeating with
`--frontier-root 8626f8a5-9531-5da7-9ebd-f901e74b1129`. To compare IDs,
run `truth --json orphans --by module` on each tree with the same root
and sort `.groups[].results[].result_id`.

This answers the retorsion part of #1963's proposed floor-graft search
within #1926 and #1007. The orphan proofs supply the scope comparison above and the three
applications in §6.5. The same-predicate, actuality and epistemic
conditions explain why promoting these objections to root support would
misstate them. #1926 and #1007 retain their broader research scopes.
#1008's verificationism showcase and #1615's debunking tests were already
delivered. The next applicability test for F6 remains the matched
investigator and evidential basis specified in the
[existing attempt](../../corpus/attempts/7a269548-3bc6-4aa8-af8e-f4397ece9448.json).

### 6.5 One proof, three applications

The live question is whether a single adequately grasped deductive proof gives
a nonempirical case of establishment, an epistemic reason and an absolute
truth, without assuming a whole theory of knowledge. This is a shared
application test, not an identification of the three predicates. Fix the
existing proposition `TruthCore.Logic.TruthPilot.NotEveryPropositionFails`:
not every proposition fails in the encoded logic. The actual existing
[solution](../../TruthCore/Results/Logic/TruthPilot/NotEveryPropositionFails/Solution.lean)
(`b41427d3`) imports the witnessed `SomePropositionHolds` proof. That
[proof](../../TruthCore/Results/Logic/TruthPilot/SomePropositionHolds/Solution.lean)
uses `True` and its constructor. If all propositions failed, True would fail,
contradicting its constructor. The proof is constructive; no measurement,
induction from sampled cases, or observation proposition enters the logical
derivation. It is inspectable by a person without trusting the empirical
performance of a particular proof checker. This is positive, content-specific
warrant for the theorem in the encoded logic, not a general proof that
all our logical intuitions are reliable.

Distinguish four questions in the application:

| Question | Positive finding | What remains to establish |
| --- | --- | --- |
| Truth in the fixed logic | An existing proof of the selected proposition, with explicit True witness. | Interpretation of that content in the rival's object language and its absolute truth predicate. |
| Rational access | A competent subject can inspect the witness and contradiction and compare an invalid replacement. | Actual availability and adequate grasp by the selected subject, not just existence of a proof file. |
| Basis of establishment | No indispensable observational proposition in the derivation. | Whether the subject's sufficient warrant genuinely rests on grasp of the proof rather than solely testimony about a tool's output. |
| Scope | Universal empirical-only scientism quantifies over logic as well as observational questions. | The actual selected scope of any weaker claim. Restricted empirical standards remain compatible with this proof. |

#### Scientism: existential empirical sufficiency versus exclusivity

The nearby [empirical-proof barrier](scoped-empirical-proof-barrier.md)
already supplies an essential control: `ConclusivelyVerifiable` admits a
tautology from **empty** observations when the world type is inhabited.
Hence proving a tautology deductively does not show that its conclusive
verifiability predicate fails. Also, an empirical learning history or
embodied implementation is compatible with a proof whose epistemically
indispensable premises are not empirical. Do not conflate these.

For a fixed set of available adequate bases, write `S(p,b)` for basis b
being sufficient for establishment of p, and `O(b)` for a basis with an
indispensable observational premise. This is a proposed analyst
classification of bases, not a new corpus definition of knowledge, nor
an assumption that every basis has either tag in advance. Hold content,
subject, meaning and relevant defeaters fixed.

- **Existential reading:** every established content has at least one
  sufficient observation-dependent basis. In the existing `EpistemicFrame`,
  interpret established as `∃ b, S(p,b)` and empiricallyEstablished as
  `∃ b, S(p,b) ∧ O(b)`. One deductive basis does not refute this reading:
  a second, empirical basis might be sufficient too.
- **Exclusive-origin reading:** every sufficient basis for every in-scope
  content is observation-dependent. This is the stronger thesis that
  empirical evidence is indispensable to every sufficient justification.
  A single in-scope sufficient basis with no indispensable observational
  premise defeats this reading, even if the same conclusion also has
  empirical support.
- **Actual-basing reading:** the subject's particular establishment is
  produced by an empirical basis. Assess the actual episode. The mere
  existence of a valid deduction does not prove that a particular person
  knows the conclusion via that deduction.
- **Analytic exemption / restricted science:** allow deduction of logical
  truths and confine the exclusive norm to some empirical questions.
  This preserves a genuine role for empirical inquiry but gives up a
  universal ban on establishment by nonempirical justification. A
  broad use of "science" including mathematics and deduction can likewise
  concede the present point without conceding any controversial metaphysical
  proposition.

The exact old global negative `66e84d62` is not automatically the
exclusive-origin rival: its meaning depends on the calibration of
`empiricallyEstablished`. Under the existential reading a sufficient
nonempirical basis and an empirical one may coexist. Do not rewrite the
old frame to choose the stronger rival.

For the actual proof example, compare the same content p and the proposed
sufficient basis D (grasp of the proof) with an experimental/testimonial
basis O (e.g. a report that a program accepted it). Suppose for the moment
that D suffices and contains no indispensable observational premise.
An empirical origin requirement can survive only by denying that D
suffices as justification, assigning an indispensable empirical premise,
or excluding p from scope. A rival can coherently contend that formal
manipulation of stipulated rules is all that occurs and that no actual
knowledge is conferred; then it must explain what rational status its own
accepted inferences have. Simply observing that D was learned or expressed
through sensory means does not identify an indispensable epistemic premise
of the conclusion. A claim that empirical evidence warrants a global
methodological norm also needs a rationale connecting those observations
to the normative restriction, not just successful applications of the
method. These are live disputes, not refutations of all empiricism.

**Finite discriminating test (executed in Python, not Lean).** Take two
contents L (the logical claim), Q (an observational claim), and two bases
D (non-observation-dependent), O (observation-dependent). Fix S(L,D)
and S(Q,O) true, vary the two remaining sufficiency entries, and vary
scope between both contents and Q only. The fixed assignments are
controls for the proposed profile, not empirical findings about a subject.
The eight cases were enumerated:

| S(L,O) | S(Q,D) | Global existential norm | Global exclusive norm | Q-only existential norm | Q-only exclusive norm |
| --- | --- | --- | --- | --- | --- |
| 0 | 0 | false | false | true | true |
| 0 | 1 | false | false | true | false |
| 1 | 0 | true | false | true | true |
| 1 | 1 | true | false | true | false |

Reproduce the finite test (no dependencies):

```python
from itertools import product
for lo, qd, global_scope in product((False, True), repeat=3):
    S = {"L": {"D": True, "O": lo}, "Q": {"D": qd, "O": True}}
    scope = ("L", "Q") if global_scope else ("Q",)
    exists = all(not any(S[p].values()) or S[p]["O"] for p in scope)
    exclusive = all(not S[p]["D"] for p in scope)
    assert exists == (lo if global_scope else True)
    assert exclusive == (False if global_scope else not qd)
```

In particular, L having both bases and Q having its empirical basis is
a populated control for why a deductive proof alone does not contradict
the existential reading. This is a finite Boolean check of the proposed
basis split, not verification of an actual philosophical calibration.

#### One witness, three separately calibrated projections

The logical proof provides a candidate for three nearby bridges, with
no new general philosophical assumption required for the proposed
propositional consequences:

1. **Absolute truth.** If the same object-language content c expresses
   the proved proposition and the truth predicate captures that content
   in the direction `NotEveryPropositionFails → T.trueAbs c`, an
   absolute-truth witness follows constructively. Since
   `NotEveryPropositionFails` is proved, this capture condition for the
   designated c is equivalent to `T.trueAbs c`. Applying it requires an
   independently justified interpretation identifying this very content and
   licensing the truth attribution. A separate route uses
   `Expressive T.trueAbs` at `True` to supply some absolutely true
   content. That witness may differ from c. Disquotation alone supplies
   neither witness. This supplies an existential, unlike simply negating
   global denial via its own formulation. The existing
   [TruthNontrivialityCore](../../corpus/arguments/TRUTH-NONTRIVIALITY-CORE.json)
   has conditional consequences via `GlobalDenialPrice`; a new
   `attacks` edge `b98c8b29` records that objection to the exact
   global rival `bff72296`. The relative-only model, in which capture
   fails, remains. No inference from the encoded `Prop` to truth
   independent of minds or endorsement is assumed.
2. **F6.** In the existing `ReliabilityFrame`, the person who grasps
   the proof can have a supporting basis available without already
   assenting to the conclusion. The existing pro tanto calibration
   `6b4e3331` (`SurvivingBasisGivesReason`) yields F6 from one
   actual supporting, non-undercut basis. No requirement for a warranted
   acceptance is needed on this direct route; neither
   `AcceptedWarrantNeedsBasis` nor eligible uptake is required.
   The prior #1980 warrant route is retained. A proof existing in
   a file is not yet evidence that an actual subject has an available
   non-undercut basis. If the selected subject judges an invalid
   rival proof and recognizes precisely why its inference fails, the
   contrast is evidence bearing on this local attribution. Actual
   subject, access, content and basis calibration remain open.
   F6 is not independently defended by using it to refute its denial.
3. **Scientism.** An established content c failing empirical
   establishment in the exact existing frame yields `70118ddd`
   and the failure of `66e84d62`; if c is in scope, it excludes
   `ScopedScientism` directly. This is the local specialization
   of the already registered norm and scope results, not a new
   theorem claimed on the graph. An adequate deductive basis lacking an indispensable observational
   premise challenges exclusive empirical origin for a claim in scope, but to use this existing
   frame under the existential reading one must additionally exclude
   other sufficient empirical bases.

The four examples below passed Lean on the existing declarations. The
first supplies the proved content to an explicit capture assumption. The
second takes the subject, basis and content as inputs, the third takes an
established in-scope witness, and the fourth tests the exclusive-origin
reading. These are local checks of the applications.

```lean
import TruthCore.Results.Logic.TruthPilot.NotEveryPropositionFails.Solution
import TruthCore.Logic.TruthNontriviality
import TruthCore.Logic.EpistemicReasonBearer
import TruthCore.Logic.ScientismScopeBoundary

open TruthCore.Logic.TruthPilot
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Relativism
open TruthCore.Logic.GlobalThesisBoundaries
open TruthCore.Logic.EpistemicReasonBearer
open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.Scientism
open TruthCore.Logic.ScientismScopeBoundary

-- Only the capture direction for one proved content is needed.
example {Agent Content : Type} (T : TruthSemantics Agent Content)
    (c : Content) (capture : NotEveryPropositionFails → T.trueAbs c) :
    SomeAbsoluteTruth T ∧ ¬ GlobalNoAbsoluteTruth T := by
  have hc := capture
    TruthCore.Results.Logic.TruthPilot.NotEveryPropositionFails.notEveryPropositionFails
  exact ⟨⟨c, hc⟩, fun h => h c hc⟩

-- No prior actual acceptance or warrant needed; the evidence is available.
example (f : ReliabilityFrame) (R : f.Agent → f.Content → Prop)
    (a : f.Agent) (b : f.Basis) (p : f.Content)
    (hs : f.supports a b p) (hu : ¬ f.undercuts a b)
    (hCounts : SurvivingBasisGivesReason f R) :
    ThereAreEpistemicReasons R :=
  ⟨a, p, hCounts a b p hs hu⟩

-- Witness to the exact negation and, when in scope, failure of the norm.
example {Claim : Type} (E : EpistemicFrame Claim) (scope : Claim → Prop)
    (c : Claim) (he : E.established c)
    (hn : ¬ E.empiricallyEstablished c) (hi : scope c) :
    SomeNonEmpiricalEstablished E ∧
      ¬ NoNonEmpiricalEstablished E ∧ ¬ ScopedScientism E scope := by
  have hw : SomeNonEmpiricalEstablished E := ⟨c, he, hn⟩
  exact ⟨hw, fun h => h hw, fun h => hn (h c hi he)⟩

-- The separate exclusive-origin reading; not the existing norm by fiat.
example {Claim Basis : Type} (S : Claim → Basis → Prop)
    (O : Basis → Prop) (scope : Claim → Prop)
    (p : Claim) (b : Basis) (hi : scope p) (hs : S p b) (hn : ¬ O b) :
    ¬ (∀ p b, scope p → S p b → O b) := by
  intro h
  exact hn (h p b hi hs)
```

The direct evidence comparison can use the same logical statement with two
candidate proof tokens. A correct reconstruction instantiates the universal
denial at True and applies it to True.intro. An invalid reconstruction
instantiates at False and tries to obtain an inhabitant of False without
any additional premise. Distinguish identifying the bad step from simply
observing the proof checker's acceptance of one string. The rival may deny
that the successful reconstruction constitutes knowledge, while conceding
that it supports belief more than the failed one. In that case F6 remains
the thinner application, and the stronger knowledge claim remains open.

The second relation `abdc2b50` records the existing singleton-identity
argument `17a2c392` (`e03147fa`) as an attack on the exact
`NoValidInference` rival `3e6a8e08`. Its frozen theorem takes a
content parameter `p : Claim` even though its record has no proposition
premises. It does not cover an empty content carrier: with `Claim = Empty`,
the denial of every entailment is vacuous. More importantly, a rival
restricting actual or ampliative inference is not thereby refuted.
Use the existing validity and invalidity control `b203c461` and
the above actual inference comparison; no `refutes` edge is added.

**Provisional assessment:** the strongest specific objection to universal
empirical-origin exclusivity is the actual deductive basis, provided it
is adequate for a subject. The same available, non-undercut basis offers
a concrete positive case for thin epistemic reasons. Those two local
calibrations deserve priority over yet another global self-application
certificate. The existential-empirical reading, logic-exempt empirical
practice, reasonless truth and relative-only interpretations survive the
formal tests as stated; they owe different positive accounts, and their
falsity does not follow solely from lacking a reason for adoption.
No conclusion here establishes the PSR, divine attributes, or GOD_4.

For an actual F6 application, the discriminating evidence would be the
selected subject's access to the proof, their performance on the valid
and invalid reconstructions, and the status of any defeaters for that
basis. For an absolute-truth application, defend the direction of capture
for that very content. Neither the replay nor the Boolean enumeration
measures a person's grasp or licenses the proposed capture.
