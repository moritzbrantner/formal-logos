# Is modal necessity load-bearing for the root? (2026-11-23)

This is the first of four follow-up questions after #1887. All of the #1870 → #1884 → #1887 work (C2, power-grounded possibility, Pruss's argument, existence in essence) bears on one modal crux: whether a foundational, simple being's possible absence needs a ground. This note asks which routes to the root actually depend on that crux. It is a structural question about the graph and makes no claim of warrant.

## Method

The data is the frontier and corpus at `main` `fd78b77e6`. The method is a least fixpoint over verified arguments:

1. **Excluded statements.** A statement is excluded when its label, paraphrase or Lean declaration name mentions modal necessity or contingency. This covers NECESSARY_2 and NECESSARY_6–12 (Kripke-world, actualist-K, essence-exemplification and frame senses), `NecessaryAt`, `ContingentAt`, CONTINGENCY_1, accessible worlds, Kripke frames and frame classes. This gives 244 statements. A second variant also excludes Aquinas's "cannot not-be" senses (NECESSARY_1/3/4, `IsNecessary`, necessary per se), which gives 264.
2. **Allowed leaves.** A statement is a leaf if the frontier reports it as an open premise (`statement_depths`: bare, stated or supported) or no verified argument concludes it. A statement the frontier reports as proved-but-unestablished is not a leaf. It counts only if one of its verified arguments has all premises derivable.
3. **The test.** Derivability is computed while excluded statements are never allowed. Each verified root argument then counts as modal-free when all its premises are derivable.

Taking any statement as an open premise would make the test trivial. This version asks instead whether a route's *verified derivation*, down to the frontier's own open leaves, can avoid modal necessity.

**Lean-level spot check.** The analysis classifies statements by label. So for three representative modal-free routes I collected every statement in the derivation tree and searched the `def` of each one's Lean declaration for `NecessaryAt`, `ContingentAt`, `Box`, `NecessaryExistence` and `IsNecessary`. The routes were the prima via (`1c5edad9`, 19 declarations), the quarta via (`fa24c576`, 16) and the designated efficient-regress route (`3b0f4fa5`, 38). None of the 73 definitions matched.

## Result

**26 of the 28 verified root arguments have modal-free derivations, under both exclusion variants.** These are every prima-via, quarta-via, efficient-regress, identity-witness and q.11 route, the cheapest route (`8df2faad`) and the designated route (`3b0f4fa5`).

The only two routes that need modal necessity are the necessary-root routes `1deb1d29` and `3357fa30`, which cost 52 and 53, the highest of the 28. Both are blocked at a single node: `c71c068c` (STMT-EVERY-CONTINGENT-GROUNDED-AT, "every actual contingent concretum has an actual ground"). Every other excluded statement on those routes lies downstream of it.

**Consequence.** The modal crux is load-bearing only for the necessary-root (modal-spine) routes. This includes STMT-NECESSARY-CONCRETE-AT `b19ffd92` and everything that reaches it: C2, PGP, Pruss, and existence in essence. These routes add support options at that node. They are not on the critical path of the 26 cheaper routes, so settling the modal crux in either direction would not change whether those routes go through.

**Limits.**
- The classification is by label, paraphrase and declaration name. The Lean-level check covers three routes, not all 26.
- The result concerns *verified* derivations to the frontier's leaves. An open leaf may still be *motivated* by modal considerations in its notes; the test does not detect that.
- Necessity enters some non-modal routes through other senses, such as the Third Way's "cannot not-be". The second exclusion variant shows these senses are not load-bearing either.

## Crux inventory of the 26 modal-free routes (stages 1–2)

These are the open leaves in the modal-free derivations whose stages include 1 or 2. The count is the number of the 26 routes that use the leaf.

| Family | Leaves (number of routes) |
|---|---|
| Fourth Way | being in act implies having being `7067553d` (22); the cause of a quality is "more such" `d5a94eb1` (22); grades are found in things `a9622441` (21); the maximum in a genus causes the perfection in all others `d9fad785` (21); grades have a maximum `6c27657f` (21); the cause of being causes the perfections `f8ba2429` (20); maximal in being is first `eaa4c679` (20); maximally TRUE_3 is maximally a being `101bdd62` (19) |
| First Way | the motion principle `4a952b96` (16); the mover is in act `f296a694` (16); nothing is moved except as in POTENCY_1 `4be9a4ac` (16); a moved mover moves only as moved `1e47e6db` (16); no infinite per se mover series `226c38f6` (12); no infinite per se efficient series `97f5850f` (4); act–potency non-contradiction `c6d6379b` (12); the dilemma "first mover or none" `ca075552` (14, bare); observation `fbc516c1` (16) |
| Composition and priority | every composite has a cause `ca07cae9` (16); composite iff matter–form or esse ≠ essence `d7741cdc` (16); no component is first `09c6d5f0` (20); act is SIMPLY_PRIOR_1 to POTENCY_1 `a4d3261a` (16) |
| Attribute bridges | immaterial → intellectual `180f5ad2` (16); intellect → will `090be689` (16); immutable → eternal `0659227c` (16); subsistent being → infinite `75a37a91` (16); a cause's perfections are in it formally or eminently `64498e7e` (16); good = actually having a perfection `00e962ae` (16) |
| Naming | the classical attribute bundle → GOD_4 `818a73cc` (16, supported); GOD_4 is maximal in being `4c79298d` (13); first pure-act unique mover → GOD_4 `a594d8c4` (4); the skeleton's attribute field `d5ac1620` (9, bare) |

The root routes also share stage-3 historical premises, which are out of scope under the current owner focus.

## Implication for the next research

If the goal is to test whether a crux of the case yields unacceptable consequences, the leaves above are where a defeat would remove routes. The Fourth Way principles, especially the causal-superiority premise `d5a94eb1` and maximum-causes-all `d9fad785`, carry 21–22 routes. The First Way's no-infinite-series premises and the attribute bridges carry about 16 each. The modal crux carries 2.

Reproduction: `truth frontier --json` and the corpus arguments and results, with the fixpoint above. No CLI command performs this "route free of a statement class" query yet, and adding one is part of the tooling follow-up.
