# Cheapest-route packing in the fork route (2026-11-24, #1926 phase 0)

The cheapest root route is `8df2faad`, with cost 16. This note asks why it is so
cheap, and whether the classical GOD_4 root `da3facd6` can take the place of the
leaf that makes it cheap. It is a structural note about the graph and the
route-cost diagnostic. It judges no premise's warrant. The attempt record is
`6becc920` ("Cheapest-route packing of the God-existence leaf in the fork
route"). The batch is `specs/necessary-classical-god-root-box-k.toml`.

## The chain

```
8df2faad  root  <- bed94ec2 (fork node) + 7 stage 3-6 premises
03a8322c  bed94ec2 <- 8239eddf, cdf897a8 (box K node), cb456382 (T schema), 0aa36cd6 (KT reading)
0b9f4b1c  cdf897a8 <- e068a626, 48366fb2 (theory on cone), ab83e6d3 (dictionary), b9816722
```

`b9816722` (`RootFactsForBearer`) unfolds to `RootFacts` (`NecessarySenseFork.lean`).
`RootFacts` is `ActualRoot ∧ σ.IsGod n ∧ IsTheOneGod σ.IsGod n ∧
σ.HasClassicalAttributes n`. So one bare leaf states that the bearer is GOD_4, is
the one GOD_4 and has the classical attributes field. `0b9f4b1c` derives only the
box-existence conjunct of `cdf897a8`. The other conjuncts pass through unchanged
from `b9816722`.

## The projection: type-correct, but an assembly

`da3facd6` and `cdf897a8` take the same `Signature`, the same `Profile m` and the
same world `w`. The necessity clause of `da3facd6`, `NecessaryAt m.ontic w n`, is
`BoxExistsAt m.ontic w n` over the same frame (`necessaryAt_iff_boxExistsAt`,
`Iff.rfl`). The projection
`NecessaryClassicalGodRootBoxK.boxKOfClassicalGodRoot` (result `f4395e76`)
is verified with no axioms. It is registered as `strengthens` from `da3facd6` to
`cdf897a8`. Its one-point separator (result `4e83dbac`) shows that the converse
fails.

The proof only destructures its hypothesis and rebuilds the conclusion. So it is
declared `transcription: assembly`, like the sibling projections `822de823` and
`0e932825` from the same node. An assembly never expands a statement in the
route-cost diagnostic and is not a support bundle. It closes `cdf897a8` only if
`da3facd6` is closed. **Route costs and closure are unchanged.**

## Why no derivation can remove the packing

`cdf897a8` already has a verified non-transcription derivation without the
packed leaf: `a693bf86`. It uses the same 25 quarta-via premises as the
`da3facd6` derivation `3a56507d`. The route-cost rule picks the proof with the
smallest leaf union for each statement. `truth frontier --routes --frontier-root`
gives the following costs:

| Derivation of `cdf897a8` | Cost |
|---|---|
| packed bundle `0b9f4b1c` | 4 |
| naming-node bundle `25135d6e` | 6 |
| projection from `da3facd6` (the cheapest derivation of `da3facd6`, `379399d1`, costs 35) | 35, assembly |
| unpacked bundle `a693bf86` | 43 |

The naming-node bundle is not usable in the full graph. Its premise `8540b456` is
derived only from `cdf897a8` itself (`eceaaacc`). So the packed bundle wins,
however many unpacked derivations are added. That would hold even if the
projection were not an assembly.

A counterfactual diagnostic shows the size of the artifact. It was run on a
scratch copy of `main` `6ecc2d87c` with `0b9f4b1c` and its result removed:

| | fork route `8df2faad` | cheapest route |
|---|---|---|
| main | 16 (5 bare, 11 proved) | `8df2faad`, 16 |
| without `0b9f4b1c` | 55 (20 bare, 8 supported, 27 proved) | `88671579` (from GOD_4 exists), 26 |

This comparison is not a cost reduction, and it says nothing against `b9816722`.
A direct assumption remains a legitimate support option.

## Modal premises discarded at the root step

`catholicismFromIntendedReading` destructures the fork node and uses only the
witness `g`, `IsGod g`, `IsTheOneGod` and `HasClassicalAttributes`. It discards
the sense choice, the uniqueness of that sense, `NecessaryIn` and `ActualRoot`.
So the route's five modal leaves (`cb456382`, `0aa36cd6`, `48366fb2`, `ab83e6d3`
and `e068a626`) are needed to prove the fork node. None of their content reaches
the root conclusion. The GOD_4 content enters the route only through `b9816722`.
Nothing was deleted.

## Next test

A computed view could list two kinds of premise:

- premises that contain conjuncts of their own argument's conclusion;
- premises whose content a later root step discards.

This is #1926 phase 4. Changing the route-cost rule needs an owner decision. A
certified difference for the new `strengthens` registration (#1598) is still
open, as it is for most registrations.
