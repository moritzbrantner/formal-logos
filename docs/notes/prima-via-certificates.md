# Prima via certificates (#1751)

Formal certificates for the findings of the 2026-11-18 cluster assessments of
the prima via route to GOD_4 exists (argument `ed7c588a`, root `8626f8a5`):
lane A, `prima-via-strength-consumers.md` (attempt `a82b06b6`, PR #1768), and
lane B, `causal-dependence-support-investigation.md` (attempt `9d71e28d`,
PR #1769). Batch spec `specs/prima-via-certificates.toml`; vocabulary
`TruthCore/Causality/PrimaViaCertificates.lean`; Solution
`TruthCore/Results/Causality/PrimaViaCertificates/Solution.lean`; attempt
`8915af42`.

## Slice 1: certificates and the regress rebinding (2026-11-19)

Every proof is constructive and uses no axiom. Each result passes Comparator
and NanoDa. An incompatibility shows only that its premises cannot all hold
under one interpretation of their shared parameters. It does not choose which
premise to reject.

| Result | Theorem | Premises → conclusion | Lane finding certified |
| --- | --- | --- | --- |
| `b4f8b7d3` | `causesInIncompatible` | `fbc516c1`, `6b9fedc2`, `4be9a4ac`, `6a0b545c`, `67aa5b5c` → ⊥ (adopted POTENCY_1) | A: aspect of `CausesIn` |
| `1d947387` | `reciprocityIncompatible` | `6ca87431`, `7ad36aca`, `32d77f18`, `8d4502a7` → ⊥ | A+B: respect-free simple priority |
| `44826b71` | `reciprocityIncompatibleViaDependence` | `6ca87431`, `47aff057`, `8d4502a7` → ⊥ | B (d) 6: no transitivity needed |
| `4ff8cd35` | `selfDependenceIncompatible` | `8ab3d114`, `6ad27c23`, `2e248016`, `98efaa9e`, `56f68b40` → ⊥ | B (d) 3: self-dependence package |
| `76e07e1a` | `actualGroundDistinctOfEverywhere` | `402cf70f` → `98efaa9e` (strength, relation `c0e70e30`) | B (d) 5: unregistered strength pair |
| `b0622871` | `perSeRegressOfWellFoundedHistory` | `42890b45`, `f10d5632` → `97f5850f` | Bypass B1 |
| `4bba0c41` | `wellFoundedHistoryOfPerSeRegress` | `97f5850f`, `6c084877` → `42890b45` | B (f): bind spine I to the per se regress premise |

New open statements: `8d4502a7` (the reciprocal cross-respect moving case, an
unattributed observation premise), `6ad27c23` (nothing can be without itself,
a meaning-postulate candidate for DEF-CAN-BE-WITHOUT) and `6c084877` (every
edge of the studied causal history is a per se link, the converse of
`f10d5632`). None is established here.

**Senses.** The `CausesIn` certificate passes from moving (CAUSE_1) to
causing a perfection (CAUSE_2) only through `6a0b545c`, listed as its sense
bridge. Under adopted POTENCY_1 the non-overlap premise `c6d6379b` is
definitional and is not a member. The six-member set on generic potency is the
same derivation, but `c6d6379b` carries POTENCY_2 and `4be9a4ac` POTENCY_1.
No bridge between those senses is registered, so that set is not certified.
Likewise `402cf70f` links the PresentEsseSupport sense of disambiguation
`6f1d1395`, while `56f68b40` links the Ontic sense. The self-dependence core
is therefore certified with `98efaa9e`. The `402cf70f` version follows in
Lean by composition with the verified strength step `76e07e1a`. This is
sense-legitimate only if `402cf70f`'s PresentEsseSupport link (`b242943a`,
sense _3 of `6f1d1395`) is a mis-link. That is an open record question for its
owner; its Lean type uses `m.grounds` and `ExistsAt`. Bypass B1 lists
`f10d5632` as its FINITE_CAUSAL_HISTORY_AND_PER_SE_3 → _4 bridge. The bridge is
legitimate, but the compound disambiguation `bedfab81` lists propositions
rather than senses of one term (precedent `b58472dd`, allowlisted).

**Minimality and models.** Closed controls witness every single deletion from
the `CausesIn` core (`causesInControls`) and from the four-member reciprocity
core (`reciprocityControls`), so both are inclusion-minimal in their stated
vocabularies. `repairedPackageModel` is a two-concretum interpretation of one
repaired package: `a8298fbd` in place of `2e248016`, with `8ab3d114`,
`6ad27c23`, `98efaa9e`, `402cf70f`, an actual concretum and a nonempty strict
part of D. `2e248016` fails in it. These controls are facts about their
interpretations and are not registered models. Inclusion-minimality of the
self-dependence core is not tested.

**Regress target.** The route's regress step already consumes `97f5850f`
directly: `c1b68c21` ← `675b71d2` ← `226c38f6` ← `f1ef9206` (`97f5850f`,
`c2880fe0`). No new argument for `c1b68c21` was needed. Spine I reached
`d85de8e1` and the all-respects `e078f07b` only by expanding the stated
`97f5850f` through `b58472dd` → `e529c42f` → `1bca81ef` → `42890b45` →
`e229bb2c`. On the GOD_4 route, `42890b45` is consumed only by that chain.
The rebinding `4bba0c41` therefore adds no support to `97f5850f`. Under the
per se selection (`f10d5632`, `6c084877`), `42890b45` and `97f5850f` are
interderivable. So the `e229bb2c` support of `42890b45` bears on `97f5850f`
exactly as far as `57552dce`, `e078f07b` and `d85de8e1` are warranted. Whether
`d85de8e1` adds independent warrant is a separate, open warrant question.
Provisional judgment, not certified here: spine I then rests on `97f5850f` on
its own q.2 a.3 claims, against the infinitist rival recorded by lane B (row 4).
Its ground is lane B's finding that `d85de8e1` with all-respects `e078f07b`
faces a counterexample on either reading of the priority relation. That
assessment is accepted in review but not yet merged (PR #1769).

**Frontier.** `frontier-diff` against main shows the same open-premise counts
for both roots. One bare premise is added (`6c084877`), and `98efaa9e` moves
from bare to proved: it now rests on the open `402cf70f`. Three verified
support alternatives are added. The registered strength order now also flags
that `815d22c8` uses `402cf70f` without `strong_version_needed`. Lane B's
row 14 already notes that `98efaa9e` avoids the cross-world export.

**Next (slice 2).** Split SIMPLY_PRIOR_1 into priority in causing and priority
in being, re-bind the spines, and check whether `3e2366b5` then needs the
bridge "nothing other than the first being is prior to it in act in any
respect". Separately, give `6a0b545c` a non-factive, in-progress reading of
`CausesIn`, or give its two routes distinct relations.
