# Restated premises: which coincide and which only look alike

Issue #1926, phase 2, slice 1 (2026-11-24). The #1926 survey reported several
groups of open premises as restatements of one another. This note records,
group by group, whether the premises coincide in sense, quantifier, world and
carrier, and what was registered. Spec: `specs/restated-premises-1926.toml`.
Lean: `TruthCore/Causality/RestatedPremises.lean` and
`TruthCore/Results/Causality/RestatedPremises/`. Attempt: "Consolidation of the
restated premises reported by the #1926 survey".

**Outcome: presentational duplicates factored** for three pairs (equivalence
registrations) and one principle stated once (strength registrations from it
to two of its instances). **No change** for the duplicate argument groups and
the occurrence premises. No record is deleted or merged, no existing argument
gains a premise, and no relation is identified with another.

## Same proposition, two records

Each pair is registered as `logically_equivalent_to`, verified by an `Iff.rfl`
theorem checked by Comparator in the controls result `554f060b`. No argument
is registered in either direction: each would be an identity transcription.
`merged_legacy_ids` is not used, because each record binds a different Lean
declaration in frozen Challenges, and merging would require changing them.

| Pair | Why the same | Why two records |
| --- | --- | --- |
| `732302a1` (q.44 a.1 co.) and `2b25a78c` (q.44 a.1 ad 1) | Same body over the same parameters: every participated `x` has a cause of its esse other than `x` (`participatedCauseReadingsIff`). Both link ESSE_BY_PARTICIPATION_1 and esse; the cause is mode-unspecified in both (CAUSE_2 at esse, and the external cause of esse with mode unspecified). | Different source readings (ad 1, co.); different Lean declarations bound by `ComponentFirstness` and `Round2Grounding` results. Both feed the same conclusion `09c6d5f0` in sibling arguments. |
| `22954087` (the meditator thinks) and `b0fd6cc1` (the selected being bears an occurring thought) | The first is the second with occurrence, bearing and the selected being fixed as the idea frame's fields (`meditatorThinksIff`). Same occurrence and bearer senses. | Different carriers (`IdeaFrame` and bare parameters) and routes. The equivalence holds at that instantiation; it does not say that every selected being is a meditator. |
| `c76b6e2c` (frame) and `c94b5446` (profile): some concrete being is contingent at `w` | Same proposition on the frame and on its ground profile, for any grounding relation (`someContingentConcreteIff`). Same contingency sense (MODAL_CONTINGENCY_1). | Different carriers. The `c94b5446` record reads the concreteness parameter as CONCRETE_6, while `c76b6e2c` leaves it open, so the equivalence holds when the same predicate is supplied. The adapter runs from frames to profiles only. |

No other premise was found stating "some concrete contingent exists". The
survey's count of five included premises that state the *possibility* of
absence (`18e5bd4e`, `0dc833c1`) or are about the holder of a power; these are
different propositions.

## One principle, several instances

The survey reported 12 bare premises that "restate the power-for-joint-absence
principle". They are not restatements. Most of them state different properties
of the holder of that power: it exists at `w` (`b517ca3e`), is concrete
(`a6906cab`), has one power (`9856239a`), has an invariant set-up (`a065c332`),
gives being to each contingent (`9f7b1778`), has power over each one's esse
(`f0ac2f76`), its exercise differs in giving (`5cf75a6b`), and GOD_4 holds it
(`0050b6ed`). They share a subject term, not a content.

What they do share is a schema. `ModalGrounding` defines three schemas, each
for one proposition `p` at one world: Aristotelian grounding
(`AristotelianGroundingFor`), initiator presence (`InitiatorPresentFor`) and
concreteness of holders (`PowerHoldersConcreteFor`). Nine bare premises are
these schemas instantiated at three propositions:

| Schema | Global absence at `w` | Actual contingents' absence at `w` | `w` obtaining, at each absence world |
| --- | --- | --- | --- |
| grounding | `94393b5b` | `95bf8780` (P1′) | `607e94cf` |
| initiator presence | `fffa0693` | `906f5c39` | `9c8e99e7` |
| holders concrete | `2d2be120` | `a6906cab` | `887d5efc` |

The new statement `31d9564c` (`AristotelianGroundingEverywhere`) states
Aristotelian modality once: at every world, every accessible possibility that
fails there is the object of a power held there by an existing being. It is an
analyst formulation of Pruss's principle (*Actuality, Possibility, and Worlds*,
2011; navigation only, attribution deferred).

It is registered as strengthening two instances: P1′ `95bf8780` (relation
`2673a2b5`, result `89359310`) and `607e94cf` (relation `be2a372e`, result
`b66f2424`). Both results are declared transcriptions of kind
`instantiation`. The controls separator is a three-world frame with
contingent concreta. On it, P1′ holds (not vacuously), `607e94cf` holds and
`94393b5b` holds, but the universal principle fails for the proposition that a
third world obtains. So the instances, singly or together, do not entail the
universal principle. The universal principle is satisfiable on the same frame.

**Frontier effect.** The diff adds the universal principle as a bare premise
and changes nothing else. P1′ and `607e94cf` stay open and bare, because a
transcription closes its conclusion only when all its premises are closed. A
transcription never expands a premise in the route-cost diagnostic. This is
the intended honest reading: the registration shows that the routes use one
principle at several propositions. It adds no warrant to any instance. The
routes keep the weaker instances.

**Not done in this slice** (30-file limit): the grounding registration for
`94393b5b`; the initiator-presence and holder-concreteness universals with
their six instances; and the strength order `5cf75a6b` → `906f5c39`.
`ActualAbsenceExerciseDiffers` adds to initiator presence that the holder's
giving differs at the absence world. Argument `61e207fc` uses it where
`259571ae` uses `906f5c39`. Each registration needs a backing argument, an
inference, a result, a Comparator config and a relation, so each one adds five
files.

## Duplicate argument groups

`truth index duplicates` lists three groups of arguments with the same premises
and conclusion. None is an identical record. In each group, one argument
instantiates the other's parametric theorem at a sense carrier. Each is a
distinct formal step that the one-argument-per-sense rule requires.

| Parametric | Carrier instance | Carrier |
| --- | --- | --- |
| `784f2278` (`lovesAllExisting`, result `a2366ca4`) | `aff41a69` (`lovesAllExistingAtCarriers`, `a66e4ce3`) | CREATURE_WILLING_1 and LOVE_1 |
| `12865cf3` (`willsGoodForAllExisting`, `7209fa2f`) | `ba458489` (`willsGoodForAllExistingAtCarrier`, `54a9ccd9`) | CREATURE_WILLING_1 |
| `fe08da3c` (`inhabitedFromPower`, `6364be2c`) | `660673ca` (`inhabitedFromSelectedCapacity`, `39454df8`) | `CapacityInterface.bearerProfile` |

The cogito instance already declared itself a transcription of kind
`instantiation`. The two love corollaries now declare it too, in
`specs/divine-love-senses-1732.toml`. Their proofs only apply the parametric
theorem. Closure is unchanged, because their parametric siblings derive the
same conclusions from the same premises.

## Alike in shape only: assertion, doubt, thinking

The occurrence premises `b45ca9db` (someone asserts the content), `95c5138f`
(some doubt whether thought occurs is performed) and `b0fd6cc1` / `22954087`
(a selected being bears an occurring thought) use disjoint primitives:
`Asserts`; `Performed` and `DoubtsThought`; `Occurs` and `Bears`. None entails
another. Their shared node is a conclusion: each reaches "some thought episode
occurs" (`e81971f1`) by its own argument:

- the thinking premise alone (`3f9339f0`, already registered as a strength
  order);
- doubt with the open bridge `PerformedDoubtIsThought` (`7d7b89e7`), or with
  the performed-denial retorsion and excluded middle (`187646ad`);
- assertion with the open bridge `AssertionRealized` (`f93f2dfd`).

So they are three premises that support one shared conclusion, each through a
different open bridge. They are not one assumption. Nothing was registered.

## Why the frontier counts do not merge

`logically_equivalent_to` and `instance_of_schema` are registrations: the
frontier and route-cost rules do not read them. `instance_of_schema` needs
premise-free proofs of both the instance and the schema (`bind-check` binds
both theorems with no proposition hypothesis), so it cannot register open
premises. A `strengthens` registration backed by an instantiation is a
transcription, and closes or expands nothing while the universal is open.
Counting equivalent premises as one leaf would therefore need a rule change: a
frontier view that quotients premises by verified equivalence. That belongs to
the phase-4 decisions, next to the packing view.
