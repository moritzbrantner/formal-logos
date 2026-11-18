# Prima via: priority in act in a respect and priority in being (#1751)

Companion to `prima-via-certificates.md` (slice 1, PR #1771). This note
is separate so that the two open PRs do not both add the same file. Batch spec
`specs/priority-in-being.toml`; vocabulary
`TruthCore/Causality/PriorityInBeing.lean`; Solution
`TruthCore/Results/Causality/PriorityInBeing/Solution.lean`; attempt
`45fc1037`.

## Slice 2: the PRIOR_4 split (2026-11-19)

**The fork.** Lane B's 2026-11-18 assessment (PR #1769, item (d) 4) found that
one relation, `PriorSimply` (PRIOR_1, DEF-SIMPLE-PRIORITY), was used on the
prima via route in two senses:

- priority in act in a respect, the gloss of the definition, carried by
  `a4d3261a`, `e078f07b` and `6ca87431`;
- priority in being, *In V Metaph.* lect. 13 nn. 15-18, used by `47aff057` and
  `97fa3a0b`, and by `5dacb0db` through `70e98bb5`.

**The new sense.** PRIOR_4 is appended to DISAMB-PRIORITY-SIMPLE-OR-IN-TIME as
sense `11d1b100`, with definition `f4365b55`. Its Lean form is
`PriorInBeing W y x := W y x ∧ ¬ W x y`, where `W` is the primitive
`CanBeWithout` (DEF-CAN-BE-WITHOUT). This is the n. 15 criterion, and claim
`ab5ec574` supports it.

The definition hides no contested bridge:
- The step from the criterion to PRIOR_1 (the open step of `97fa3a0b`) does
  not arise for PRIOR_4.
- The step from being-without to dependence for being (n. 18) stays in the
  open premises `000e1f65` and `8ab3d114`.
- PRIOR_4 is asymmetric by definition.

PRIOR_1 to PRIOR_3 and all original statements are unchanged.

| Result | Theorem | Premises → conclusion | Sense |
| --- | --- | --- | --- |
| `b00b452a` | `beingWithoutCriterion` | none → `ec5ffe6b` (n. 15 criterion, sibling of `97fa3a0b`), definitional | PRIOR_4 |
| `94dc553f` | `priorityInBeingRequiresNonmutualDependence` | `000e1f65`, `8ab3d114`, `ee4ab504` → `c4bb0481` (sibling of `47aff057`) | PRIOR_4 |
| `af233664` | `priorInBeingCausesBeing` | `c4bb0481`, `5dacb0db` → `6eacb281` (sibling of `70e98bb5`) | PRIOR_4 |
| `3c795147` | `firstMoverIsFirstInBeing` | premises of `f8992ef7` with `6eacb281` for `70e98bb5` → `c51a07a1` (sibling of `74eb9113`) | PRIOR_4 |
| `fb8fba1e` | `firstMoverPureActFromFirstInBeing` | `c51a07a1`, bridge `954fe018`, `a4d3261a` → `6c18d52b`, adopted POTENCY_1 | PRIOR_4 → PRIOR_1 by `954fe018` |
| `27599762` | `moverPriorityAsPriorityInBeingExcludesReciprocity` | none → control `feb950c1` (`sense_mixing_control`) | mixing control |

`5dacb0db` (whatever a thing depends on for its being is a cause of its being)
has no priority term, so it needs no sibling.

All six proofs use no axioms. Excluded middle appears only as the explicit
premise `ee4ab504`. Comparator and NanoDa accept all six results.

**The bridge and `3e2366b5`.** Argument `3e2366b5` (`74eb9113`, `a4d3261a`,
`c6d6379b` → pure act) still derives unchanged. In the PRIOR term it uses
PRIOR_1 alone. The `truth semantics` preflight of PR #1767, run on it as a
new argument, reports only its legacy POTENCY_1/POTENCY_2 mixing.

The split changes the standing of its premise `74eb9113`:
- Its existing support `f8992ef7` passes through `70e98bb5` ← `47aff057` on a
  single relation, which is exactly where the two senses were conflated.
- A sense-respecting support reaches first-in-being (`c51a07a1`, PRIOR_4) only.
  Going from there to pure act needs exactly the bridge `954fe018`:
  a first unmoved mover first in being is first in PRIOR_1.
- The preflight passes `fb8fba1e` with the bridge listed and fails it without.

The bridge is the weakest one the derivation needs. It is restricted to first
unmoved movers that are first in being, and it is not a general inclusion of
PRIOR_1 in PRIOR_4. A general inclusion would fail under reciprocal
cross-respect moving if PRIOR_1 comes from moving in any respect: see the
control `27599762` and the slice-1 certificates.

The bridge has one rival on file. The `firstWayDoesNotYieldPureAct` model of
result `afd52425` has a first unmoved mover in potency to a respect in which
it moves nothing, and another being, in act in that respect, is PRIOR_1 to it.
The bridge requires that such a being be identical with the first mover,
which in effect makes it prior in being. Whether that requirement holds is
now the crux of the pure-act step.

**Other records.** The sibling `c51a07a1` lists `777646a5` (CAUSE_1 → CAUSE_2)
and `101bdd62` (MAXIMAL _6 → _1) as sense bridges. These mixings come from
`f8992ef7`, where they are on the legacy allowlist.

**Frontier.** On both roots one bare premise is added (`954fe018`) and four
support alternatives are added. The cheapest GOD_4 route is still `ed7c588a`
at cost 6.

**Not done.**
- The respect-sense uses keep the respect-free PRIOR_1. No relation indexed by
  respect is introduced, so the slice-1 reciprocity certificates still apply to
  `6ca87431`.
- No PRIOR_4 reading of act's priority is formalized. It would make the bridge
  unnecessary, but it faces reciprocal moving.
- Spine II (`931319ea`) and the order laws `7ad36aca` and `32d77f18` have no
  PRIOR_4 siblings yet.
