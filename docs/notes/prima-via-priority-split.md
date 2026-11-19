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
`CanBeWithout` (DEF-CAN-BE-WITHOUT). It formalizes the **first mode** of
priority in being, by being-without (n. 15), and claim `ab5ec574` supports it.
In the pinned passage `184c633c`, read for the review of #1774:
- n. 15 says priority by nature and substance is said *tripliciter*. The first
  mode is *ratione communitatis aut dependentiae*.
- n. 16 gives the second mode: the subject, as substance is prior to accident.
- n. 17 gives the third mode, by the division of being into act and potency.
- n. 18 reduces all modes to these, *praecipue ad primum*, and concludes
  *omnia priora aliquo modo possunt esse sine posterioribus*.

The second and third modes are not formalized as senses.

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

What the split does for its premise `74eb9113`:
- Its existing support `f8992ef7` passes through `70e98bb5` ← `47aff057` on a
  single relation, which is exactly where the two senses were conflated.
- A support that keeps the senses apart reaches only first-in-being
  (`c51a07a1`, PRIOR_4). From there, `fb8fba1e` reaches pure act through the
  bridge `954fe018`: a first unmoved mover first in being is first in PRIOR_1.
- The preflight passes `fb8fba1e` with the bridge listed and fails it without.

**What the bridge amounts to.** The bridge is sufficient but not the weakest
available. A respect-matched weaker variant also suffices: a being in act in a
respect in which the first mover f is in potency, and PRIOR_1 to f, is f. The
checked controls are `RespectMatchedFirstInBeingBridge`,
`respectMatchedBridge_of_bridge` and `pureActOfRespectMatchedBridge` in the
vocabulary module.

Given `c51a07a1`, the bridge is equivalent to the content of `74eb9113`
(checked control `firstInActBridge_iff_firstBeing`):
- with an empty `CanBeWithout`, `c51a07a1` holds trivially
  (`firstInBeing_of_emptyCanBeWithout`);
- on DEF-CAN-BE-WITHOUT's real-possibility reading, nothing is PRIOR_4 to a
  necessarily existing f;
- so for the classical first mover, the bridge just is `74eb9113`.

**The split route therefore gives no new warrant for PRIOR_1-firstness.** Its
gain is sense hygiene. The equivocation in `47aff057` leaves the support, and
`c6d6379b` (POTENCY_2) is discharged by adopted POTENCY_1.

The bridge is restricted to first unmoved movers that are first in being. It
is not a general inclusion of PRIOR_1 in PRIOR_4. That a general inclusion
fails is an unchecked one-step composition: control `27599762`, `6ca87431` and
an admitted case of reciprocal cross-respect moving.

**Positive warrant and next test.** The strongest positive warrant for the
bridge on file is n. 18, *omnia priora aliquo modo possunt esse sine
posterioribus*. It reduces the act–potency mode of n. 17 to being-without, but
only *aliquo modo*. The qualifier suggests that one unindexed `CanBeWithout` is
too coarse to carry that reduction. Next test: a CanBeWithout indexed by mode
or respect under which the n. 17 to n. 15 reduction can be stated and checked.

**Rival.** One rival is on file: the `firstWayDoesNotYieldPureAct` model of
result `afd52425`. In it, a first unmoved mover f is in potency to a respect in
which it moves nothing, and another being, in act in that respect, is PRIOR_1
to f. In that model the bridge holds only if some other being is PRIOR_4 to f.
Together with `c51a07a1`, it therefore excludes the model.

**Inherited failure case.** The siblings `c4bb0481` and `6eacb281` inherit the
failure case recorded for `8ab3d114`: if the second relatum is necessary, the
first may be independent of it although no world has the first without it.
- On the real-possibility reading, a necessary y is PRIOR_4 to every contingent
  x that y can be without, because x cannot be without a necessary y.
- `c4bb0481` then makes each such x depend for its being on y, and `6eacb281`
  makes y a cause of its being.
- The derivation `94dc553f` applies `8ab3d114` as `¬ D x y → W x y`, with
  y necessary, which is exactly that case.

**Record issue (not repaired here).** DEF-CAN-BE-WITHOUT (`d0b06beb`) names
`PriorityByBeingWithout` as its `lean_declaration`. That is the declaration of
a premise statement (`97fa3a0b`), not the primitive W. This is a record
question for its owner.

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
