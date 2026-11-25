# Is modal necessity load-bearing for the root? (2026-11-23)

This is the first of four follow-up questions after #1887. All of the #1870 → #1884 → #1887 work (C2, power-grounded possibility, Pruss's argument, existence in essence) bears on one modal crux: whether a foundational, simple being's possible absence needs a ground. This note asks which routes to the root depend on modal necessity at all, and which depend on that crux in particular. It is a structural question about the graph and makes no claim about warrant. [Original PR #1902](https://github.com/moritzbrantner/formal-logos/pull/1902)

## Method

The data is the frontier and corpus at `main` `fd78b77e6`. The method is a least fixpoint over verified arguments.

1. **Excluded statements**, in three variants:
   - (a) statements whose label, paraphrase or Lean declaration name mentions modal necessity or contingency (244 statements). This covers NECESSARY_2 and NECESSARY_6–12, `NecessaryAt`, `ContingentAt`, CONTINGENCY_1, accessible worlds, and Kripke frames and frame classes;
   - (b) (a) plus Aquinas's "cannot not-be" senses (264 statements): NECESSARY_1/3/4, `IsNecessary` and necessary per se;
   - (c) the Lean-level classification. Each statement's `lean_declaration` was resolved by namespace, and its `def`/`abbrev` body was unfolded up to two levels and searched for `NecessaryAt`, `ContingentAt`, `.access`, `Box`, `Diamond`, `□`, `◇`, `NecessaryBeing`, `IsNecessary` and `NecessaryExistence`. This finds 656 statements. Variant (a) misses 439 of them, and (a) and (b) together miss 423.
2. **Leaves** follow the leaf rule of `truth frontier --routes`. A statement is a leaf if it is established, stated or supported (whether or not proved), has no verified non-transcription argument, or sits in an ungrounded cycle. Other proved statements must be derived through a verified argument whose premises are all derivable. A stricter rule also expands proved statements that are stated or supported. It gives the same counts, provided statements closed by transcription can still be expanded through their transcription arguments. If only non-transcription arguments are allowed, every route fails, even with no modal exclusion: the stage-3 node `a04f711a` depends on the transcription closure of `5baad26f`. That dependence has nothing to do with modality. (`statement_depths` covers every statement, so it cannot serve as the leaf test.)
3. **The test.** Derivability is computed with excluded statements never allowed. A verified root argument is modal-free when all of its premises are derivable. This is a question about which verified derivations exist down to the frontier's own leaves. It is not a question about which statements may be assumed.

The first draft of this note used `statement_depths` as the leaf test. That made every statement a leaf, so the test checked only direct premises. The independent challenge caught this, rebuilt the analysis, and confirmed the corrected results below under all three variants and both leaf rules. Its scripts are in the coordinator's scratchpad and are not part of this repository.

## Result

**25 of the 28 verified root arguments have modal-free derivations, under every variant.** They cover all the prima-via, quarta-via, efficient-regress, identity-witness and q.11 routes, plus the designated route `3b0f4fa5`. With Lean-level exclusion, their witness trees contain no modal statement at all: 67 statements under the route leaf rule and 301 under the strict rule. No route is modal-free only because of a transcription.

**Three routes need modal necessity:**

| Route | Cost | Blocked at | Through |
|---|---|---|---|
| `1deb1d29` | 52 | `c71c068c` STMT-EVERY-CONTINGENT-GROUNDED-AT ("every actual contingent concretum has an actual ground"; Lean: `ContingentAt`, accessible worlds) | the necessary-root closure, which is the modal crux |
| `3357fa30` | 53 | `c71c068c` | the same |
| `8df2faad` (cheapest) | 16 | `bed94ec2` STMT-NECESSARY-ROOT-ON-INTENDED-READING (Lean: `Box`, `IsNecessary`) | the KT/KTB/S4/S5 frame-correspondence arguments for NECESSARY_2 |

- **The first two routes** have `c71c068c` as their only blocking premise. Every other premise has a modal-free derivation. Some other modal statements appear in their support graph, but only on alternative derivations of other premises.
- **The cheapest route** depends on modal necessity, but not on `c71c068c`. If only `c71c068c` is excluded, it still goes through via the KT reading (`03a8322c`). Its frontier leaves include the T schema `cb456382` and the KT reading `0aa36cd6`.

**What this means for the modal crux.** It is load-bearing for exactly two routes: the two necessary-root routes, through `c71c068c`. Modal necessity more broadly, which includes the frame-correspondence readings, is load-bearing for three. For the other 25 routes, no verified derivation needs modal necessity.

This is a claim about which derivations exist. It does not say that the modal crux has no effect on those 25 routes. One of `c71c068c`'s three verified arguments (`2162ca9d`, via participation) uses `cb1cdea9`, and `cb1cdea9`'s derivation rests on leaves shared with the 25 routes: `7067553d`, `d5a94eb1`, `f8ba2429`, `64498e7e`, `c6d6379b` and `f296a694`. A defeat of `c71c068c` would therefore put disjunctive pressure, by modus tollens, on that derivation's premises, which include those shared leaves. It removes no premise from the 25 routes. The dependence is shared, not critical.

## Crux inventory of the 25 modal-free routes (stages 1–2)

This table is taken from the frontier's own per-route leaves (`routes[].open_premise_statement_ids`), restricted to leaves whose stages include 1 or 2. The count is the number of the 25 routes that have the statement as an open leaf.

| Routes | Leaves |
|---|---|
| **all 25** | `d5a94eb1` whatever causes a quality is more such; `d9fad785` the maximum in a genus causes the perfection in all others; `f8ba2429` the cause of being causes every perfection; `64498e7e` a cause's perfections are in it formally or eminently; `7067553d` nothing is in act except insofar as it is; `00e962ae` good = actually having a perfection; `ca07cae9` every composite has a uniting cause; `818a73cc` the classical attribute bundle names GOD_4 (supported) |
| 19–22 | `4c79298d` GOD_4 is maximal in being (22); `6c27657f` grades have a maximum (21); `a9622441` grades are found in things (21); `09c6d5f0` no component is the first being (20); `1ec205ed` fuller nominal profile (20); `eaa4c679` maximal in being is first (20); `a4d3261a` act is SIMPLY_PRIOR_1 to POTENCY_1 (20); `101bdd62` maximally TRUE_3 is maximally a being (19) |
| 12–16 | immaterial → intellectual `180f5ad2`; intellect → will `090be689`; immutable → eternal `0659227c`; subsistent being → infinite `75a37a91`; composite iff matter–form or esse ≠ essence `d7741cdc`; First Way core `4a952b96`, `f296a694`, `4be9a4ac`, `1e47e6db` (16 each); created agents act as applied `777646a5` (14); act–potency non-contradiction `c6d6379b` (12); no infinite per se mover series `226c38f6` (12) |
| ≤ 9 | the five GOD_4 attribute leaves `29818edd` (intellect), `66aecdd7` (will), `5bec93b3` (eternal), `b0132989` (infinite), `fb3802a8` (immutable) (9 each); firstness `74eb9113`, the unique pure-act mover is GOD_4 `a594d8c4`, no infinite per se efficient series `97f5850f`, per se mover link `c2880fe0` (4 each); the q.11 uniqueness premises (3 each); `034eb68f`, `bc44e1cd`, `e39a4fce` (2 each); `89cbb0af` (Meditation V premise), `cdc7a58f`, `0881e859` (1 each) |

Some statements are not open leaves. The observation `fbc516c1` is established as self-evident, and the dilemma "first mover or none" `ca075552` is closed by transcription from closed premises. All 25 routes also share stage-3 historical premises, which the current owner focus leaves out.

**Open leaf in every route versus needed by every derivation.** The counts above say how many routes have a statement as an open leaf in the frontier's chosen expansion. A separate test excludes each statement, on top of the modal exclusion, and reruns the fixpoint. It finds that seven of the eight "all 25" premises each remove all 25 routes. The exception is `d9fad785` (the maximum in a genus causes all): four routes have other verified derivations that avoid it, so excluding it removes 21. For the other rows the removal counts match the table: `4c79298d` removes 22, `6c27657f` and `a9622441` remove 21 each, `4a952b96` removes 16 and `226c38f6` removes 12.

## Implication for the next research

Eight premises are open leaves of **every** modal-free route. Together they form the common core of the God-existence and attribute stages on those routes:
- three causal-perfection principles: causal superiority `d5a94eb1`, the maximum causes all `d9fad785`, and the cause of being causes every perfection `f8ba2429`;
- perfections pre-exist in the cause `64498e7e`;
- actuality only through being `7067553d`;
- goodness = actuality `00e962ae`;
- composition needs a cause `ca07cae9`;
- the naming premise `818a73cc`.

To test whether a crux has unacceptable consequences, these are the premises whose defeat would remove the modal-free routes. Seven of them would each remove all 25 routes at once. `d9fad785` would remove 21. The Fourth Way grade premises carry 19–22 routes, the First Way core and the attribute bridges about 12–16, and the modal crux (`c71c068c`) carries 2.

Reproduction uses `truth frontier --json` and `truth frontier --routes --json`, the corpus arguments and results, and the fixpoint above. No CLI command answers the query "which routes are free of a class of statements" yet. Adding one belongs to the tooling follow-up.
