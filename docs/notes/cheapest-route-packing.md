# Cheapest-route packing in the fork route (2026-11-24, #1926 phase 0)

The cheapest root route is `8df2faad`, with cost 16. This note asks why it is so
cheap, and whether the classical GOD_4 root `da3facd6` can take the place of the
leaf that makes it cheap. It is a structural note about the graph and the
route-cost diagnostic. It judges no premise's warrant. The attempt records are `6becc920`
("Projection of the classical GOD_4 root onto the box K node of the fork
route", succeeded) and `b3467390` ("Re-routing the fork route's box K node off
the packed GOD_4 leaf", blocked). The batch is
`specs/necessary-classical-god-root-box-k.toml`.

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
`cdf897a8`.

The proof only destructures its hypothesis and rebuilds the conclusion. So it is
declared `transcription: assembly`, like the sibling projections `822de823` and
`0e932825` from the same node. An assembly never expands a statement in the
route-cost diagnostic and is not a support bundle. It closes `cdf897a8` by rule
(d) only if `da3facd6` is closed.

`truth frontier --json` on the merged head (`main` `62bb4ce3c` plus this batch)
gives `da3facd6`, `cdf897a8` and `bed94ec2` the status `proved`. Each is closed
by rule (a), proved from open premises, and none is established. `cdf897a8` was
already closed by rule (a) through `0b9f4b1c` and `a693bf86`. So rule (d)
through the assembly adds no closure. **Route costs and closure are unchanged.**

### Strictness separator

The separator (result `4e83dbac`) is a two-point model. Both candidates are
concrete, exist at the one self-accessing world and are grounded by nothing, so
both are actual roots. Only one of them is GOD_4. In the main model, goodness,
infinity, eternity, intellect and will are everywhere true, and `CausesIn` is
total. Six relations are empty: potency, the more-than relation, simple
priority, component-of, composition and matter/form. So immutability, maximum,
firstness, remoteness, simplicity and matter/form exclusion hold vacuously at
both candidates. The Lean `Separator` proves on this model:

1. the box K node holds, with the GOD_4 candidate as witness;
2. the classical root fails;
3. the classical root is equivalent to "some candidate satisfies every other
   conjunct of the root's body and is the only actual root";
4. the GOD_4 candidate satisfies every other conjunct;
5. the other candidate is an actual root and is not GOD_4.

It adds a restored-relation control on the same signature and Profile, so the
box K node of item 1 still holds there. All the relations above except
component-of are non-empty: the GOD_4 candidate is more in esse than the other
and simply prior to it, `CausesIn` runs only from it to the other, and only the
other is in potency, composite and composed of matter and form. The `Separator`
proves:

6. the classical root still fails, and it is again equivalent to "the rest of
   the body plus being the only actual root";
7. the GOD_4 candidate satisfies the rest of the body;
8. maximum and firstness fail at the other candidate.

So in both models the classical root fails only through the selected-root
uniqueness conjunct of `PerfectRootAt` (`∀ x, ActualRoot m w x → x = n`). The
box K node has only `IsTheOneGod`, uniqueness among GOD_4 bearers, which does
not exclude a second, non-GOD_4 actual root. The separation is non-degenerate
in this sense: no supplied predicate is emptied so that an attribute fails, and
the failing conjunct uses `ActualRoot`, which both nodes contain. The restored
control shows that it does not rest on the vacuous clauses; only remoteness
stays vacuous there. A first draft failed only by emptying `HasIntellect`, a
free parameter the box K node does not mention; it was replaced.

The classical root also adds maximum, perfection, firstness, esse/essence
identity, matter/form exclusion, remoteness and eight case predicates. That is
a syntactic comparison of the two definitions; neither model separates the
nodes on any of it. No certified difference (`strength_comparison`, #1598) is
registered. The sense-fork precedents factor through a witness-independent
frame condition. Here the added content constrains the witness of an
existential, so a delta would need a new same-witness delta statement and its
equivalence proof.

## Why no derivation can remove the packing

`cdf897a8` already has a verified non-transcription derivation without the
packed leaf: `a693bf86`. It uses the same 25 quarta-via premises as the
`da3facd6` derivation `3a56507d`. The route-cost rule expands an intermediate
statement through the verified non-transcription proof with the smallest leaf
union, chosen greedily per statement (docs/corpus-model.md, `--routes`).
`truth frontier --routes --frontier-root cdf897a8-5490-561a-b9d2-507486a3f192`
gives the following costs:

| Derivation of `cdf897a8` | Cost |
|---|---|
| assembly `25bfe291` from the actualist K node `7f24ce4d` | 1, transcription |
| packed bundle `0b9f4b1c` | 4 |
| naming-node bundle `25135d6e` | 6 |
| projection `e3d120ed` from `da3facd6` (the cheapest derivation of `da3facd6`, `379399d1`, costs 35) | 35, transcription |
| unpacked bundle `a693bf86` | 43 |

The listing marks `25bfe291` `[cheapest, transcription]`. As a transcription it
expands nothing under the `--routes` rule, so it does not compete for the
expansion of `cdf897a8`. The naming-node bundle is not an independent
alternative either. Its premise `8540b456` is derived only from `cdf897a8`
itself (`eceaaacc`), so it runs back through the packed bundle; without
`0b9f4b1c` it costs 45.

So the packed bundle, with a union of 4, wins against:

- any derivation with a leaf union above 4;
- every existing derivation not through `b9816722`, which costs at least 35;
- any derivation from `da3facd6`, which costs at least cost(`da3facd6`) = 35.

A new derivation would replace it only with a union not above 4 that avoids
`b9816722` (exactly 4 only if it wins the tie order), and no such candidate is
known. This holds whether or not the
projection is an assembly. Attempt `b3467390` records this as blocked at the
rule level.

A counterfactual diagnostic shows the size of the artifact. It was run on a
scratch copy of the merged head (`main` `62bb4ce3c` plus this batch, which
changes no route cost) with `0b9f4b1c` and its result `8348fe91` removed:

| | fork route `8df2faad` | cheapest route |
|---|---|---|
| merged head | 16 (5 bare, 11 proved) | `8df2faad`, 16 |
| without `0b9f4b1c` | 55 (22 bare, 6 supported, 27 proved) | `88671579` (from GOD_4 exists), 26 |

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
certified difference for the new `strengthens` registration (#1598) needs a
same-witness delta statement and is still open, as it is for most
registrations.

## Second instance: root existence for whole-roster nontrapping (2026-11-24, #1926 slice 2a)

Slice 2a registered root existence `dc397705` as strengthening whole-roster
nontrapping `5c898d24` (relation `67afbf3d`, certified difference `e9512c5c`).
The order is correct, and registering every strong-to-weak implication is owner
policy, so the registration stays.

The new support option is circular in the current corpus. The only derivation
of `dc397705` is `6560ccfa` (result `9f7c8201`). That result is an assembly
transcription, and it consumes `5c898d24` together with population and excluded
middle. So the option adds no warrant.

It still lowers two route costs: `1deb1d29` drops from 52 to 50 and `3357fa30`
from 53 to 51. `--routes` cannot expand a transcription, so `dc397705` stands as
one `proved_unestablished` leaf. Those routes now assume root existence in place
of the three potential-gap premises `516c4fee`, `5adb2dc9` and `838f7cca`.

This is a packing artifact of the same kind as the fork route's `b9816722`.

**Tooling gap.** Route expansion does not apply the support-cycle set-aside of
[the strength-registration decision](../decisions/2026-11-12-03-strength-registrations-reach.md).
Closure does apply it.

The well-founded registration `577cd3b6` is the slice's non-circular new
support option for `5c898d24`.
