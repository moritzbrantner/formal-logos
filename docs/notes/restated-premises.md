# Restated premises: which coincide and which only look alike

Issue #1926, phase 2, slice 1 (2026-11-24). The #1926 survey reported several
groups of open premises as restatements of one another. This note records,
group by group, whether the premises coincide in sense, quantifier, world and
carrier, and what was registered.

- Spec: `specs/restated-premises-1926.toml`.
- Lean: `TruthCore/Causality/RestatedPremises.lean` and `TruthCore/Results/Causality/RestatedPremises/`.
- Attempt: "Consolidation of the restated premises reported by the #1926 survey".

**Outcome.**

- **Presentational duplicates factored:** three equivalence pairs.
- **No change:** the joint-absence power premises, the duplicate argument groups (apart from transcription labels) and the occurrence premises.

No record is deleted or merged, no existing argument gains a premise, and no
relation is identified with another.

A common strong principle for the grounding premises, with `strengthens`
registrations to its instances, is a separate slice (1b, branch
`refactor/1926-grounding-principle`). It is not a factoring: the instances
stay distinct premises, and the universal principle is a new bare premise.

## Same proposition, two records

Each pair is registered as `logically_equivalent_to`. Each is verified by an
`Iff.rfl` theorem that Comparator checks in the controls result `554f060b`.
No argument is registered in either direction, because each would be an
identity transcription.

`merged_legacy_ids` is not used. Each record binds a different Lean
declaration in frozen Challenges, so merging would require changing them.

| Pair | Why the same | Why two records |
| --- | --- | --- |
| `732302a1` (q.44 a.1 co.) and `2b25a78c` (q.44 a.1 ad 1) | Same body over the same parameters (`participatedCauseReadingsIff`). Both bodies are `CausesIn c x esse` with `c ≠ x` (CAUSING_AN_EFFECT_3; DISAMB-BECOMING-BEING-CAUSE places STMT-PARTICIPATED-HAS-OTHER-CAUSE in sense 3). | Different source readings (ad 1, co.). Different Lean declarations, bound by `ComponentFirstness` and `Round2Grounding` results. Both feed the same conclusion `09c6d5f0` in sibling arguments. |
| `22954087` (the meditator thinks) and `b0fd6cc1` (the selected being bears an occurring thought) | The first is the second with occurrence, bearing and the selected being fixed as the idea frame's fields (`meditatorThinksIff`). Same occurrence and bearer senses. | Different carriers (`IdeaFrame` and bare parameters) and routes. The equivalence holds at that instantiation. It does not say that every selected being is a meditator. |
| `c76b6e2c` (frame) and `c94b5446` (profile): some concrete being is contingent at `w` | Same proposition on the frame and on its ground profile, for any grounding relation (`someContingentConcreteIff`). Same contingency sense (MODAL_CONTINGENCY_1). Every profile is the ground profile of some frame on its own ontic, so the equivalence needs only the same concreteness predicate. | Different carriers. The `c94b5446` record reads the concreteness parameter as CONCRETE_6; `c76b6e2c` leaves it open. |

**Sense tags of the q.44 pair.** The ad 1 record `2b25a78c` links `196be87e`
(CAUSING_AN_EFFECT_2, whose `HasExternalEsseCause` adds that the cause is in act
as to esse). That does not match its body. It is a pre-existing mis-tag, and
it is why `truth semantics` reports the pair under different senses. The
equivalence holds between the bound declarations; it does not identify senses
2 and 3.

Replacing the link with `211a6432` (sense 3) on its own breaks `truth check`:
argument `358d8c6e` would then use two senses of "causing an effect" without
linking `c3c01e92`. The repair is a follow-up under #216.

No other open premise was found stating "some concrete contingent exists".
The survey's count of five included premises that state the *possibility* of
absence (`18e5bd4e`, `0dc833c1`) or are about the holder of a power. These are
different propositions.

## Power for joint absence: different propositions

The survey counted 12 premises that "restate the power-for-joint-absence
principle". This slice examined the 16 related bare premises listed below.
They are not restatements.

Eight of them state different properties of the holder of that power:

- it exists at `w` (`b517ca3e`);
- it is concrete (`a6906cab`);
- it has one power (`9856239a`);
- it has an invariant set-up (`a065c332`);
- it gives being to each contingent (`9f7b1778`);
- it has power over each one's esse (`f0ac2f76`);
- its exercise differs in giving (`5cf75a6b`);
- GOD_4 holds it (`0050b6ed`).

They share a subject term, not a content.

Nine of them share a schema instead. `ModalGrounding` defines three schemas,
each for one proposition `p` at one world:

- Aristotelian grounding (`AristotelianGroundingFor`);
- initiator presence (`InitiatorPresentFor`);
- concreteness of holders (`PowerHoldersConcreteFor`).

The nine premises are these schemas at three propositions (`a6906cab` is in
both lists, hence 16 premises in all):

| Schema | Global absence at `w` | Actual contingents' absence at `w` | `w` obtaining, at each absence world |
| --- | --- | --- | --- |
| grounding | `94393b5b` | `95bf8780` (P1′) | `607e94cf` |
| initiator presence | `fffa0693` | `906f5c39` | `9c8e99e7` |
| holders concrete | `2d2be120` | `a6906cab` | `887d5efc` |

Slice 1b states Aristotelian modality once and registers it as strengthening
P1′ and `607e94cf`, with a separator. It certifies each difference with a
constructive disjunctive delta: at every world-proposition pair, either
grounding holds or the pair is the instance's own. Each delta comes with an
equivalence of the form universal ↔ instance ∧ delta. No case split on equality
of propositions is needed.

The strength order `5cf75a6b` → `906f5c39` is expected but unverified. The
differing exercise would add to initiator presence that the holder's giving
differs at the absence world. Argument `61e207fc` uses `5cf75a6b` where
`259571ae` uses `906f5c39`.

## Duplicate argument groups

`truth index duplicates` lists three groups of arguments with the same premises
and conclusion. None is an identical record. In each group, one argument
instantiates the other's parametric theorem at a sense carrier. That is a
distinct formal step, and the one-argument-per-sense rule requires it.

| Parametric | Carrier instance | Carrier |
| --- | --- | --- |
| `784f2278` (`lovesAllExisting`, result `a2366ca4`) | `aff41a69` (`lovesAllExistingAtCarriers`, `a66e4ce3`) | CREATURE_WILLING_1 and LOVE_1 |
| `12865cf3` (`willsGoodForAllExisting`, `7209fa2f`) | `ba458489` (`willsGoodForAllExistingAtCarrier`, `54a9ccd9`) | CREATURE_WILLING_1 |
| `fe08da3c` (`inhabitedFromPower`, `6364be2c`) | `660673ca` (`inhabitedFromSelectedCapacity`, `39454df8`) | `CapacityInterface.bearerProfile` |

The cogito instance already declared itself a transcription of kind
`instantiation`. The two love corollaries now declare the same, in
`specs/divine-love-senses-1732.toml`. Closure is unchanged: the
non-transcription parametric siblings `7209fa2f` and `a2366ca4` conclude
`c691e3d0` and `e3d5bece` from identical premise sets.

## Alike in shape only: assertion, doubt, thinking

The occurrence premises share no primitive:

- `b45ca9db` (someone asserts the content) uses `Asserts`;
- `95c5138f` (some doubt whether thought occurs is performed) uses `Performed` and `DoubtsThought`;
- `b0fd6cc1` and `22954087` (a selected being bears an occurring thought) use `Occurs` and `Bears`.

An entailment between them would need a bridge premise relating `Asserts`,
`Performed`/`DoubtsThought` and `Occurs`/`Bears`. None is proved or
registered.

What they share is a conclusion. Each reaches "some thought episode occurs"
(`e81971f1`) by its own argument:

- the thinking premise alone (`3f9339f0`, already registered as a strength order);
- doubt with the open bridge `PerformedDoubtIsThought` (`7d7b89e7`), or with the performed-denial retorsion and excluded middle (`187646ad`);
- assertion with the open bridge `AssertionRealized` (`f93f2dfd`).

So these are three premises for one conclusion, not one assumption. Nothing
was registered.

## Why the frontier counts do not merge

`truth/src/frontier.rs` reads only the relations `strengthens`,
`alternative_to`, `refutes`, `root_route` and `attacks`. So
`logically_equivalent_to` and `instance_of_schema` registrations leave every
premise count unchanged (`docs/corpus-model.md`).

`instance_of_schema` cannot register open premises either. It needs
premise-free proofs of both the instance and the schema: `bind-check` binds
both theorems with no proposition hypothesis.

Counting equivalent premises as one leaf would need a rule change: a frontier
view that quotients premises by verified equivalence. That belongs to the
phase-4 decisions, next to the packing view.
