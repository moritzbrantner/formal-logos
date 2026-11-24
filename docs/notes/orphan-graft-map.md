# Orphan graft map (#1926)

A map of the verified results that do not reach the root, and of the ways they
could join a root route. It is a research note, not a tracker. Counts describe
corpus scale; they are not progress. The grafts implemented with this note are
in `specs/nar-grafts.toml` (Lean: `TruthCore.Causality.NarGrafts`,
`TruthCore.Results.Causality.NarGrafts`); attempt `e0253e6b`.

Baseline: `main` at `61acfd56`, `truth --json orphans --by module|family`:
1,676 of 2,481 verified results disconnected (1,420 non-transcription, 256
transcription). A result counts as connected when its conclusion reaches the
root or when it supports a verified recorded refutation of an `alternative_to`
rival of a root-path node (`truth/README.md`, "`orphans`").

## 1. What separates a genuine graft from a nominal one

- **Genuine:** a verified, non-transcription argument whose premises include
  the orphan conclusion (or certificate) and whose conclusion is a root-path
  node, or a refutation of a recorded rival of one. Every extra premise is an
  explicit open bridge.
- **Nominal (rejected):** a bridge premise "orphan conclusion → root node"
  that the proof only applies (invariant 16), or a relation recorded without a
  rival that actually conflicts with the root node.
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
| Stage 1-2 same-witness endpoints: `UniqueClassicalGodExists` `20a2b6a3` (StagesOneTwo, Q11 and identity witnesses, quarta via classical witness; 8 results, 6 non-transcription) | 8 | `d5ac1620` GodHasClassicalAttributes, a premise of the root arguments | none: `UniqueClassicalGodExists σ → GodHasClassicalAttributes σ` is a uniqueness transfer (`IsTheOneGod`), a genuine two-line derivation | no new premise | `20a2b6a3` carries 40 inherited `definition_ids` (GOD_1/2/4, CAUSE_1/2, PER_SE_1/3, ...), so any new argument from it is an unbridged sense mixing; pruning them to its Lean vocabulary changes records pinned by the reviewed bundle audits (`classical-attributes-all-migration.json`, `naming-first-mover-migration.json`) | **high, cheap after a reviewed prune** |
| Necessary-root attribute siblings: `73f6b3c8`, `593d7307` (NecessaryFirstBeing), `f2a65d16`, `2c886717`, `124e21e6`, `6c37be2d`, `469b92a8` ("∃ the same actual necessary root with property X") | ~15 | `d164f730` necessary roots (done here from `91b085c4`), and the attribute nodes of the quarta-via bundle `da3facd6` | at-most-one actual root `49fdec01` (existing) | existing premises only | legacy definition links: NECESSARY_11 enters through DEF `f8948e28` (WORLDS_9) and WELL_FOUNDEDNESS_AND_ANTI_BRUTE_ROOT_1 through DEF `c86cc1d1`, though the Lean types use only `NecessaryAt` and `ActualRoot` | high after the same #216 prune |
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
| Aristotle Physics maps | 110 (102 transcriptions) | prima via premises | none possible: transcriptions close nothing | — | invariant 16 | off-route |
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

- **G1** (`6c2ae534`, `optimalRivalRefuted`, zero axioms). The optimizing
  creator `b72a790a` (every actual root gives by total optimal output over a
  fixed candidate set and quality scale with a unique optimum; recorded
  `alternative_to` WN) is refuted from #1947's law-2 premises (b1)
  `2dd1f217`, factive giving `3ef41442`, the common root of `0c27f65a`,
  necessary roots `d164f730`, some contingent `c76b6e2c`, and the two
  premise-free certificates `1822b59d` and `b8ee1a50`. It does not use WN or
  SS. The refutation does not count (#999): its premises are open.
- **G2** (`7670662c`, `necessaryRootsFromUniqueNecessaryRoot`, zero axioms).
  `d164f730` (every actual root is NECESSARY_2, bare until now; gap 6 of
  [nar-derivation.md](nar-derivation.md)) from `91b085c4` (a unique necessary
  actual root), registered `strengthens`.
- **G3** (`f0eb2f96`, controls, Mathlib three axioms). Law 1: under
  `givingProfile`, stable output is fixity toward each given being. Law 2: a
  unique optimum makes a root fixed toward every effect, so two-way toward
  none. Law 3: with SS, a unique-optimum root that gives another being by a
  rational exercise makes WN fail. Model `TiedOptimum`: the refutation's other
  premises hold, the root gives by total optimal output over two tied
  candidates, and it is two-way toward a contingent. Encoding disclosures:
  quality is constant, `G` (`gGroundsOthers`) and existence are fixed by
  construction, the frame's `Ontic` causal field and other relations are
  empty, and `d` exists only at the second world. A control, legitimately
  off-route.

Computed effect: `d164f730` moves from bare to closed (proved from open
premises, not established); `1822b59d`'s result `a1990e04` and `b8ee1a50`'s
result `0cf250b9` now reach the root through the recorded refutation; G3 is a
new off-route control (net orphans 1,676 → 1,675).

## 4. The WN / optimal-creation finding

[nar-derivation.md](nar-derivation.md) lists Rowe's argument among WN's
rivals and excludes Leibniz, whose moral necessity is not a metaphysical
fixity. `OptimalCreationChoice` formalizes the metaphysical version: total
optimal output plus a unique optimum gives cross-world stable output. Composed
with the root's giving, it is a **rival refutation and a constraint, not a
rival model**:

- **Refutation (G1).** The being-level optimizing creator with a unique
  optimum is incompatible with the premises of law 2. Its derived price:
  deny that the root is necessary, that some concretum is contingent, (b1),
  factive giving or the common root's reach, or the uniqueness of the
  optimum. The first two together are modal collapse of what the root gives.
- **Constraint on the selective rival.** Being-level optimization cannot be
  the selecting principle that #1947's §9 asks for. A unique optimum fixes
  every effect (law 2 here), and ties do not force fixity (`TiedOptimum` keeps a tied root two-way toward a contingent, in one encoding). A rival that
  is fixed toward a necessary intermediary `d` and two-way toward the
  contingents needs a different selector.
- **What it does not show.** It leaves the world-level optimizer untouched:
  one best complete order of effects that includes `d` and leaves the
  contingents open. It says nothing against ties (`TiedOptimum`) or a no-best regime
  (where #1737's certificate shows no candidate is optimal, so the rival's
  total optimal output cannot hold). It does not refute the
  necessary diffusion of the good, which needs no optimization premise.
- **Warrant for WN:** unchanged overall (moderate, on the means-to-end
  reading). One named rival variant now has a recorded conditional refutation
  that does not beg the question against WN. The decisive rival (selective
  necessary diffusion) stands.

Revision conditions: a world-level `OptimalOutputs` over complete outputs
that keeps law 2's premises would reopen the Rowe variant; a selection
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
5. World-level optimization against law 2 (continuation of G1).
6. Naturalism refutations with the bridge "GOD_4 is not a part of spacetime".
7. The `c778a6ca` family through a concreteness argument.
