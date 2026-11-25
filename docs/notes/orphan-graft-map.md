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
| Retorsion (Logic: EpistemicNihilism, Knowledge, Scientism, Verificationism, Relativism, AssertionRetorsion side outputs) | ~40 | floor items with sceptical rivals: observation `fbc516c1`, non-contradiction `c425f0c5`; the cogito premises `b45ca9db`, `1edfc1d1` | record the global sceptical theses as `alternative_to` those premises, with the premise-free retorsions as `refutes` | premise-free refutations are established, so they would *count* | each recording is a semantic judgment that the thesis denies the premise; the floor marking's `disagreement` must be updated | **high**, relation work plus semantic challenge |
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
3. Retorsion results as `refutes` of global sceptical rivals recorded on the
   observation and cogito floor premises (premise-free, so they count).
4. Alternatives refutations re-recorded as `alternative_to` the prima via
   premises they deny.
5. World-level optimization (`78af5042`) against law 2, and the mediated
   creator against direct reach (continuation of G1).
6. Naturalism refutations with the bridge "GOD_4 is not a part of spacetime".
7. The `c778a6ca` family through a concreteness argument.
