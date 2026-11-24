# Modal ontology: 120 propositions for the epistemic frontier

This is the complete 2026-10-26 **research inventory**, organized as twelve groups of ten. The `IMP-01`–`EPI-10` identifiers are stable **intake identifiers**, not replacements for canonical `STMT-…` IDs. The wording is preserved from the original proposal; identifying a proposition does not assert that it is true, source-grounded, metaphysically possible, or Lean-verified.

The original **F** and **H** markers are retained as triage labels: F marks an intended formal/semantic test; H marks a substantive philosophical hypothesis. **Neither means proved.** In particular, F entries that mention models are claims *about stated formal semantics* and still need a matching Lean theorem/countermodel before being treated as established. H entries may contradict each other; retain these as rival hypotheses until investigated. An item whose meaning overlaps an existing `STMT-…` must **reuse or link** that identity after a meaning audit, not create a duplicate statement just to make a new dot. A statement becomes a canonical corpus node only with a meaning-checked registration; a source attribution additionally requires a materialized passage witness.

This inventory gives the workloop an exhaustive **enumeration of the proposed questions**, not an exhaustive disjunction of metaphysical theories. Lean can establish consequences and exhibit countermodels relative to explicit assumptions; no unexamined combination is declared impossible or classified as leading to God. The [configuration elimination and composition loop](configuration-elimination-loop.md) governs the next stage: intake ID → meaning-audited canonical `STMT-…` → explicit semantic profile → proof, model, or recorded unresolved attempt. The research matrix is [#461](https://github.com/moritzbrantner/truth-core/issues/461), linked to existing issues #435–#441 and targeted follow-ups #462–#471. No root-path premise is discharged by recording these items.

## IMP — Impossibility and essence

- **IMP-01 (F)** — An entity whose essential properties jointly entail a contradiction cannot be instantiated under classical logic.
- **IMP-02 (F)** — Adding further propositions to an inconsistent set cannot restore consistency unless an existing proposition or inference rule is revised.
- **IMP-03 (F)** — Describing an impossible entity as *possible* does not eliminate the contradiction constituting its impossibility.
- **IMP-04 (F)** — Resolving a contradiction by altering an essential property changes the original conception being investigated.
- **IMP-05 (F)** — A single conception can contain multiple independent, minimal sets of contradictory properties.
- **IMP-06 (F)** — An inconsistent essence has no classical model satisfying all its essential properties.
- **IMP-07 (F)** — Logical impossibility, physical impossibility, and metaphysical impossibility need not have identical extensions.
- **IMP-08 (F)** — The absence of a discovered contradiction does not logically establish the absence of every contradiction.
- **IMP-09 (F)** — An impossibility proof can depend on substantive necessary truths in addition to purely logical laws.
- **IMP-10 (H)** — Every metaphysical impossibility ultimately derives from an incompatibility among essences or other necessary truths.

## MOD — Modal semantics and possible worlds

- **MOD-01 (F)** — Under standard modal semantics, possibility is equivalent to the negation of necessity of negation: \(\Diamond P\leftrightarrow\neg\Box\neg P\).
- **MOD-02 (F)** — The modal systems K, T, S4, B, and S5 permit different classes of accessibility structures.
- **MOD-03 (F)** — In the standard equivalence-frame interpretation of S5, accessibility is reflexive, symmetric, and transitive.
- **MOD-04 (F)** — Every equivalence class of an S5 accessibility graph forms a strongly connected component.
- **MOD-05 (F)** — An isolated empty world in an S5 frame satisfies the necessity of emptiness relative to its own singleton component.
- **MOD-06 (F)** — A world outside the actual world's accessible component is not a possible alternative relative to the actual world under that accessibility interpretation.
- **MOD-07 (H)** — Absolute metaphysical possibility is appropriately represented by one unrestricted S5 accessibility component.
- **MOD-08 (F)** — Modal accessibility does not, by itself, define temporal succession or a mechanism for moving between worlds.
- **MOD-09 (F)** — The validity of nested modal inferences can change when accessibility assumptions change.
- **MOD-10 (H)** — A complete, consistent collection of propositions is sufficient to represent a genuine metaphysical possibility, rather than merely a syntactically coherent candidate.

## NEC — Necessary individuals

- **NEC-01 (F)** — Necessarily having at least one existent individual does not entail the necessary existence of a particular individual.
- **NEC-02 (F)** — The contingency of every individual does not entail the possibility of a world containing no individuals.
- **NEC-03 (F)** — If a particular concrete entity necessarily exists and necessarily remains concrete, every possible world contains something concrete.
- **NEC-04 (F)** — Necessary existence alone does not entail necessary concreteness.
- **NEC-05 (F)** — A necessarily existing being can possess properties that differ between possible worlds.
- **NEC-06 (F)** — Necessary existence does not logically entail temporal eternity, timelessness, or immutability without additional assumptions.
- **NEC-07 (F)** — Necessary existence alone does not entail causal efficacy.
- **NEC-08 (F)** — Having causal powers does not entail necessary existence.
- **NEC-09 (F)** — A simple formal model can consistently describe an individual that exists concretely in every world and exercises causal powers.
- **NEC-10 (H)** — At least one concrete, causally efficacious being exists necessarily in metaphysical reality.

## EMP — Empty worlds

- **EMP-01 (F)** — A world without concrete entities is not necessarily a world without true propositions.
- **EMP-02 (F)** — A world that is empty throughout its history is distinct from a world containing an empty temporal state.
- **EMP-03 (F)** — A modal model can contain both an empty world and a populated world without contradiction.
- **EMP-04 (F)** — Having no concrete entities is distinct from having no entities whatsoever.
- **EMP-05 (F)** — The necessity of some concrete existence is incompatible with the possibility of a completely concrete-empty world.
- **EMP-06 (F)** — The existence of a necessarily concrete entity excludes a completely concrete-empty possible world.
- **EMP-07 (F)** — The possibility of removing each individual entity separately does not establish the possibility of removing all entities simultaneously.
- **EMP-08 (F)** — Every individual being contingent is consistent with every possible world containing at least one individual.
- **EMP-09 (F)** — A subtraction argument requires assumptions about the preservation of possibility under repeated removals.
- **EMP-10 (H)** — A world entirely devoid of concrete entities is metaphysically possible.

## STA — Empty states and transitions

- **STA-01 (F)** — An empty temporal state contains no concrete entity capable of exercising causal power.
- **STA-02 (F)** — An empty temporal state does not imply an empty world if concrete entities exist at other times.
- **STA-03 (F)** — If the past interval is entirely empty, a first concrete event cannot have a concrete cause located within that interval.
- **STA-04 (F)** — A model allowing uncaused events can represent concrete existence beginning after an empty interval without logical inconsistency.
- **STA-05 (F)** — A first event following an empty past is incompatible with the principle that every concrete event requires an earlier concrete cause.
- **STA-06 (F)** — The possibility of an event in another world does not itself provide a causal mechanism for producing that event in this world.
- **STA-07 (F)** — If the empty state is absorbing under a system's transition laws, no nonempty state is reachable from it.
- **STA-08 (F)** — A dynamical system with an appropriate source term can evolve from an empty state into a nonempty state; the mathematical model alone does not establish metaphysical possibility.
- **STA-09 (H)** — Time cannot exist without change, events, or concrete entities.
- **STA-10 (H)** — The beginning of concrete existence can be explained by an atemporal cause or metaphysical ground.

## TIM — Time and temporal beginnings

- **TIM-01 (F)** — A finite temporal duration does not entail the existence of a first instant.
- **TIM-02 (F)** — The existence of a first instant does not entail the existence of a first concrete event.
- **TIM-03 (F)** — The existence of a first event does not entail that time itself has a beginning.
- **TIM-04 (F)** — Infinitely many temporal instants do not entail infinitely many concrete events.
- **TIM-05 (F)** — Infinitely many distinct events can be assigned to a bounded temporal interval in a mathematical model.
- **TIM-06 (F)** — Temporal precedence and causal precedence are distinct relations; neither is formally identical to the other.
- **TIM-07 (F)** — A finite temporal past does not, by itself, entail finite causal ancestry.
- **TIM-08 (H)** — Temporal passage involves objective becoming, rather than merely relations between events.
- **TIM-09 (H)** — Every temporal event can be understood within an eternalist ontology without objective becoming.
- **TIM-10 (F)** — Branching-time semantics can represent histories sharing a common past while allowing different future continuations.

## CAU — Causal graph structure

- **CAU-01 (F)** — Every nonempty finite directed acyclic graph contains at least one vertex with no incoming edge.
- **CAU-02 (F)** — An infinite directed acyclic graph need not contain any vertex with no incoming edge.
- **CAU-03 (F)** — Weak connectivity of a causal graph does not imply the existence of a first cause.
- **CAU-04 (F)** — Strongly connected components identify causal cycles in a graph but do not, without further interpretation, establish temporal loops.
- **CAU-05 (F)** — A nonempty well-founded causal ordering contains a causally minimal element.
- **CAU-06 (F)** — Acyclicity alone does not entail well-foundedness.
- **CAU-07 (F)** — Having finitely many immediate causes does not entail having finitely many causal ancestors.
- **CAU-08 (F)** — The absence of infinite backward causal chains does not entail that every event has finitely many distinct causal ancestors.
  - Conditional repair and independent omission countermodels: [finite branching and existence-PSR syllogisms](causal-finite-branching-and-psr-syllogisms.md).
- **CAU-09 (F)** — A causal network may have infinite ancestry even when every event lies within a bounded temporal interval.
- **CAU-10 (H)** — No concrete event can possess an infinite causal ancestry.

## INF — Infinity and supertasks

- **INF-01 (F)** — An infinite series can converge to a finite mathematical value.
- **INF-02 (F)** — A divergent series need not possess a finite sum under ordinary real-series convergence.
- **INF-03 (F)** — An infinite sequence of distinct actions can be scheduled within a finite interval in an idealized mathematical model.
- **INF-04 (F)** — An infinite sequence indexed by \(\omega\) and one with reverse order type \(\omega^*\) have different ordering properties, relevant to beginningless histories and supertasks.
- **INF-05 (F)** — A binary state alternating indefinitely between zero and one does not converge to either state.
- **INF-06 (F)** — Some infinite sequences of states converge to uniquely determined limiting states.
- **INF-07 (F)** — A sequence of actions indexed by the natural numbers has no final action.
- **INF-08 (F)** — The actions of a supertask do not always determine its endpoint state without additional rules governing the limit.
- **INF-09 (F)** — The inconsistency of a particular infinite-action specification does not logically entail the inconsistency of every infinite-action specification.
- **INF-10 (H)** — Every physically or metaphysically realizable supertask must satisfy restrictions stronger than mathematical consistency.

## ACT — Actuality and causal powers

- **ACT-01 (F)** — Modal accessibility in ordinary Kripke semantics does not itself constitute a causal power.
- **ACT-02 (F)** — If every causal power belongs to a concrete entity, an entirely concrete-empty state contains no bearer of causal power.
- **ACT-03 (H)** — Every genuine causal power must have an actually existing bearer or foundation.
- **ACT-04 (H)** — An abstract law, considered independently of any concrete reality, cannot actualize concrete entities.
- **ACT-05 (H)** — Objective metaphysical possibilities are grounded in the potentialities of actual entities.
- **ACT-06 (H)** — Objective metaphysical possibilities can be grounded in essences independently of actual causal powers.
- **ACT-07 (H)** — Modal possibility is metaphysically primitive and need not be grounded in something more fundamental.
- **ACT-08 (H)** — A causal power can exist without being exercised.
- **ACT-09 (F)** — Necessary existence is formally compatible with the contingent exercise of causal powers.
- **ACT-10 (H)** — A metaphysical ground can explain the existence of something without temporally preceding it.

## EXP — Explanation and sufficient reason

- **EXP-01 (H)** — Every contingent concrete fact has a sufficient explanation.
- **EXP-02 (H)** — Every fact about existence, including necessary existence, is eligible for explanation.
- **EXP-03 (H)** — The existence of a necessary being can be explained through its essence without requiring a distinct external cause.
- **EXP-04 (H)** — Metaphysical explanations need not be causal explanations.
- **EXP-05 (F)** — Explaining each member of a collection does not, as a matter of logic alone, establish an explanation of the collection as a whole.
- **EXP-06 (F)** — An infinite dependency structure can provide every dependent element with a predecessor without possessing a foundational element.
- **EXP-07 (H)** — Every chain of metaphysical grounding must ultimately terminate in something ungrounded.
- **EXP-08 (H)** — A totality whose members possess only borrowed causal power cannot have sufficient explanatory power without a nonborrowed foundation.
- **EXP-09 (F)** — The impossibility of observing an observerless world does not establish the impossibility of such a world or explain why concrete reality exists.
- **EXP-10 (H)** — Certain strengthened formulations of the unrestricted PSR, combined with additional necessity principles, entail modal collapse.

## ONT — Ontological arguments and ultimate reality

- **ONT-01 (F)** — If \(G\) is possible and essential existence entails necessary existence, then \(G\) exists necessarily in S5.
- **ONT-02 (F)** — Under the stipulated necessity condition in S5, either \(G\) is necessary or \(G\) is impossible; contingent existence is excluded.
- **ONT-03 (F)** — Under the same conditions, if God's nonexistence is possible, God's nonexistence is necessary.
- **ONT-04 (F)** — Under these conditions, \(\Diamond G\) and \(\Diamond\neg G\) cannot both hold.
- **ONT-05 (F)** — Not having established God's impossibility is epistemically different from establishing God's metaphysical possibility.
- **ONT-06 (F)** — Necessarily existing concrete reality does not logically entail a particular necessarily existing concrete being.
- **ONT-07 (F)** — A necessarily existing concrete being excludes completely concrete-empty possible worlds.
- **ONT-08 (F)** — Necessary existence and concreteness alone do not entail omniscience, omnipotence, perfect goodness, or divine simplicity.
- **ONT-09 (H)** — Independent truths about essence, existence, and dependence can justify one side of the modal ontological argument's possibility dispute over the other.
- **ONT-10 (H)** — There exists exactly one ultimately foundational necessary concrete being from which contingent reality derives its existence.

## EPI — Epistemic and formal proof limits

- **EPI-01 (F)** — Failure to discover a contradiction does not entail metaphysical possibility.
- **EPI-02 (F)** — The existence of a formal model establishes satisfiability relative to its axioms and semantics, not automatically genuine metaphysical possibility.
- **EPI-03 (F)** — An unsuccessful proof attempt does not constitute a disproof.
- **EPI-04 (H)** — Conceivability is a reliable guide to metaphysical possibility under appropriately specified conditions.
- **EPI-05 (H)** — Inconceivability can provide reliable evidence of impossibility under appropriately specified conditions.
- **EPI-06 (F)** — Refuting an argument for a conclusion does not establish the negation of that conclusion.
- **EPI-07 (F)** — A countermodel refutes a proposed logical consequence relative to the formal assumptions under which the countermodel is valid.
- **EPI-08 (F)** — A formal proof's conclusion remains conditional on its definitions, axioms, and inferential rules.
- **EPI-09 (F)** — Mutually implying propositions form equivalence clusters in an implication graph, but their circular derivability does not by itself provide independent justification.
- **EPI-10 (H)** — Multiple genuinely independent explanatory and deductive arguments can establish stronger epistemic support for a metaphysical conclusion than any one argument alone.

## Precision audit before formalization

The original wording above is immutable **intake**, including where it is imprecise. A proof worker must not silently reinterpret it as an already-established theorem:

- **CAU-04** needs a nontrivial SCC or an actual self-loop for the stated cycle intuition: an isolated singleton is a strongly connected component under the usual zero-length-path convention but has no directed cycle.
- **CAU-05** needs the orientation of the well-founded relation fixed before translating 'minimal' into 'no incoming causal edge'.
- **MOD-05** asserts necessity **only relative to** its singleton accessibility component, not in all possible worlds across other components.
- **NEC-09 / ACT-09** must keep potential causal capacity, manifested event and actual exercise separate; a finite model is not evidence of metaphysical instantiation.
- **ONT-01–ONT-04** depend on a precise essential-necessity condition, the S5 frame and what the proposition `G` denotes; the possibility premise is still an independently open metaphysical question.
- **INF-03 / INF-08** separate scheduling an infinite sequence mathematically from establishing that infinitely many physical actions can occur and that an endpoint state is well-defined.

Keep the intake text intact while assigning any corrected reading its own meaning-audited canonical statement, linked as a refinement rather than pretending the original proposition was already proved.

## Research routes and next intake step

The first registered cross-world quantifier tests for **NEC-05**, **ACT-09**,
and the explanatory question near **EXP-03** are in
[Modal quantifier-shift models](modal-quantifier-shift-models.md). These are
certified *formal* configurations; the original intake statements and their
truth statuses are unchanged.

| Inventory groups | Existing work to reuse | Focused follow-ups |
| --- | --- | --- |
| IMP, MOD, ONT | #261–#267, #274, #437–#439 | #464, #471 |
| NEC, EMP, STA | #435–#436, merged #445/#456 | #462–#463, #466, #470 |
| TIM, CAU, INF | #318, #336–#339, #367, #440–#441 | #469 |
| ACT, EXP | #310–#312, #319–#320 | #462–#463, #465, #468 |
| EPI | #248, #342, #437–#438, #414 | #467, #471 |

Per entry, first search `corpus/statements/` and Lean for the **same meaning**. Link an existing statement where applicable, otherwise formulate a new canonical statement only after its semantics are fixed; then prove, exhibit a countermodel, or document a clearly open metaphysical premise. Source-derived claims require pinned and materialized witnesses. This preserves all 120 proposals while avoiding 120 potentially duplicate or unjustifiably 'proved' propositions.

## #1864: thirteen-slot profile schema and targeted modal admissibility (2026-11-23)

Follow-on to #1865 (merged), whose generic `MaximalProfile` it reuses; not a
reinterpretation of the original IMP/MOD/ONT intake labels. The formal
implementation is the Lean module
[DivineProfile](../TruthCore/Modal/DivineProfile.lean) (definitions, conditional
theorems and finite controls). No corpus argument or result is registered, and
no source is attributed: everything below is an **analyst reconstruction**.

Status (repair pass 1 after the independent semantic challenge of `c2009e30`):
the vocabulary moved out of `ActualistDomains` into its own module; the slots
are described as an unfixed schema; the nine-slot bridge is a distinct analyst
premise; the outer-E/inner-M reading is explicit; the necessity premise is
renamed; the frame condition is weakened to Euclidean and reflexive *at w*; and
omission and separation controls were added. Final-head CI is the verification
of record.

### What is encoded, and what is not

`ProfileSlots` is a **13-slot predicate schema; no sense is fixed**. Its
world-indexed slots carry the labels simple, perfect, good, one, infinite,
immutable, eternal, intellect, will, omnipotent, omniscient, morallyPerfect and
free, but the labels are mnemonic only. Every theorem quantifies over an
arbitrary schema, and all of them hold with every slot `True`
(`Control.noSenseFixed`). The claimed non-inferences between slots are checked
only as schema separations (`Control.separations`): good without morallyPerfect,
intellect without omniscient, will without free, and the nine StageTwo-order
slots without the full thirteen-slot excellence.

The slots are **not** StageTwo's typed senses (`IsSimple Composite`,
`IsPerfect InAct`, `IsSupremelyGood InAct GoodIn CausesIn esse`,
`IsTheOneGod σ.IsGod`, `IsImmutable InPotency`, …) and the omnipotence slot is
not `NamingVeracityBatch1.Power`'s `CanDo`. That typed vocabulary is not reused
directly for two reasons. It is world-invariant over `σ.Being`, while the modal
profile needs world-indexed slots. And `IsTheOneGod` and `GodIsOmnipotent` are
defined through `σ.IsGod`, which must stay out of every possible-world premise.
`NineAt` reuses only StageTwo's connective `NineClassicalAttributes` (the order
of the nine conjuncts), not its senses.

`ExcellenceAt p w x` asks all thirteen slots of the same `x` at the same `w`.
`GreatnessAt m p x v` adds existence of that `x` at `v` and existence plus full
excellence at every **M**-successor of `v` (M = `m.frame`).
`PossibleGreatness m p w` is M-possibility of such a bearer. Reading M as
metaphysical accessibility is OPEN.

**Two readings of described possibility.** `DescribedPossibleGreatness E m p w`
is **outer-E / inner-M**: some E-successor `v` of `w` at which `x` exists, is
excellent, and remains so at every *M*-successor of `v`. The E-premise is
therefore not purely descriptive: it already asserts M-necessity at an E-world,
and `greatness_at_origin` relies on that inner M. The purely descriptive sibling
`DescribedPossibleGreatnessInnerE` uses E inside as well. Passing from inner-E
to outer-E needs the extra bridge `InnerSuccessorsCovered` (every M-successor of
each E-successor of `w` is an E-successor of it; `describedInnerE_to_outerE`).
`Control.innerNotOuter` shows that inner-E can hold while outer-E and the bridge
both fail.

**Carrier interpretation (OPEN).** Where the case signature `σ` appears,
`σ.Being` is identified with the constant (possibilist) roster of an `Ontic`
model with world-relative existence, and the selected world `w` is read as
actuality. Both identifications go beyond the σ-sense disambiguation
`fe91cc1f` (intended interpretation of the case vocabulary) and are open
interpretive premises.

### Conditional theorems and their exact OPEN inputs

- `described_greatness_transfer` is a **near-transcription**: one application
  of `AdmitGreatnessWorlds` (E-successors of `w` that carry the complete
  greatness profile are M-successors of `w`) to the given witness. It is the
  singleton-predicate case of #438's `TransferLaws`, restricted to this profile.
  `Control.targetedNotGlobal` checks that the targeted condition can hold, with
  an M-witness, while universal `IncludedAt E M w` fails. `Control.eNotM` checks
  that an E-witness without the condition need not give an M-witness.
- `greatness_at_origin` uses `EuclideanAt m.frame w` and `ActualReflexive m w`,
  both only at `w`, not global S5. It uses the same algorithm as
  `ActualEuclidean.necessaryAtOrigin` (prior art); the new content is that the
  excellence conjunct travels with the same bearer. It factors through
  `greatness_at_origin_of_witness`: the witness-relative condition
  `M(v,w) ∧ ∀u, M(w,u) → M(v,u)` suffices without reflexivity at `w`.
  `Control.k5NoActual` shows that Euclideanness alone is insufficient (a
  globally Euclidean frame, not reflexive at `false`, with M-possible greatness
  and no bearer at `false`). It does **not** show that reflexivity is necessary:
  `Control.nonreflexiveReturn` is Euclidean at `false`, not reflexive there, and
  still returns the maximal profile.
- `actual_named_classical_god` and `actual_god_exists` consume the returned
  actual bearer through two separate OPEN bridges, both at the actual world
  only:
  1. `ProfileNineSuffice σ p w`, the nine opaque slots at `w` suffice for the
     primitive field `σ.HasClassicalAttributes`. This is a **distinct analyst
     bridge, not STMT-CLASSICAL-ATTRIBUTES-SUFFICE**: its own head constant keeps
     `bind-check` from matching the canonical statement, whose Lean instance uses
     the typed StageTwo senses. `profileNineSuffice_of_senseBridges` derives it
     from that canonical instance plus `ProfileToStageTwoSenses`, the sense
     bridges from each slot to its typed sense at `w`. The `one` slot is meant
     to be GOD-free, so that its bridge to `IsTheOneGod σ.IsGod` is the only
     place where `σ.IsGod` enters, and only at `w`. This is an instantiation
     rule the type does not enforce: a slot built from `σ.IsGod` would put
     GOD_4 into the possibility premise and trivialize the naming bridge, so
     any registration must check that no slot mentions `σ.IsGod`.
  2. `ActualDivineNaming σ m p w`, an existing bearer at `w` with all thirteen
     slots satisfies `σ.IsGod`. It is **not derived** from the other premises:
     `Control.namingOmission` satisfies every other premise of
     `actual_god_exists` in a signature with empty `IsGod`, where `GodExists`
     fails.

  The complete input bundle is: outer-E possibility, profile-relative
  M-admissibility, Euclidean and reflexive access at `w`, actual naming, and the
  nine-slot bridge. No member is established by this conjunction.
- `actual_necessary_bundle_greatness` shows that an actual excellent bearer plus
  `NecessaryExcellenceAt` (necessary existence and necessary excellence over
  M-successors of `w`; this is **not** essentiality) already yields the
  **actual** maximal profile with no frame condition at all.
  `actual_necessary_bundle_possible` adds the trivial step to M-possibility
  under reflexivity at `w`. The possibility detour therefore adds no independent
  support once these two premises are granted, and the possibility obtained is
  only M-possibility.
- `Control.noJointBearer`: omnipotence and omniscience slots each have a bearer
  but no bearer has both, so separate instantiation does not give a joint
  bearer.

### Philosophical assessment and live discriminators

**Positive warrant, provisional.** The existing actual-root/received-esse,
perfection-preexistence, nonlimiting-root and same-root-intellect/will research
gives cumulative grounds to investigate **one actual underived bearer** with
simplicity and at least intellectual capacity. Such grounds would bear on the
inputs of `actual_necessary_bundle_greatness` (an actual excellent bearer) once
the slots are given fixed senses; they do not yet supply power, full knowledge,
moral perfection or freedom in any fixed sense, nor the necessity premise. The
existing defeasible recombination policy in
[Kant's cosmological-inference study](kant-cosmological-inference.md)
supports testing jointly compatible qualities when no grounded exclusion has
been found, but non-discovery alone is not semantic consistency, and semantic
consistency is not metaphysical possibility. Present verdict: **conditional
modal connection over an unfixed schema verified; no slot sense fixed; full
metaphysical possibility not established; positive partial-profile warrant worth
further testing**.

**Best presently evidenced incompatibility pressure.** The
[simplicity/contingent-creation investigation](notes/simplicity-collapse-555.md)
has a verified inconsistent core if **the same** act is necessary, is strictly
sufficient for an effect, and that effect is contingent. The serious
application question is whether the alleged divine simplicity makes a
particular *freely selected act* essential and necessarily efficacious. If
divine freedom involves contingent effects, simply setting both
`p.simple w x` and `p.free w x` to true does not answer that question.
The original controls distinguish identity of bearer from identity/necessity
of the act, and necessity of the act from strict sufficiency. Rejecting
strict sufficiency or locating free variation in an extrinsic effect avoids the
stated inconsistent core, but incurs the specific explanatory or interpretation
obligation already discussed there. No full-profile contradiction follows
until the corresponding cross-vocabulary assumptions are supported.

**Exact cross-family consumers and obstacles.** The existing
[RootIntellectWill](../TruthCore/Causality/RootIntellectWill.lean)
conclusion preserves one actual necessary source with represented
essence/esse identity, simplicity, intellect and will. Its own documented
conclusion does **not** include omniscience, moral impeccability or free
selection, and it does not identify that bearer as `σ.IsGod`. The
[GodNamingSenses](../TruthCore/Causality/GodNamingSenses.lean)
`NoOtherPossibleGod` and `GodhoodEssentialToGod` conditionally connect
a world-varying description to the root's world-invariant God predicate;
they do **not** show that the thirteen slots, under any chosen senses, are a
sufficient description of the actual source. A future same-witness bridge must
import the same source and selected senses and justify its naming implication
rather than substitute an already asserted GOD_4 witness. On that route the
possibility premise is idle (`actual_necessary_bundle_greatness`: an actual
excellent bearer with necessary excellence already gives the actual profile),
so the actual-root support bears directly on the actual-bearer input, and only
partially, since the slot-sufficiency and naming bridges above stay open.

**Other explicit compatibility tests.** Under the existing
`NamingVeracityBatch1.Power` interpretation, `CanDo` a coherent task and
actually **doing** it are different relations. Impeccability construed as
never *choosing* evil need not contradict capacity to refrain or to choose;
impeccability construed as **incapacity** for every independently coherent evil
task can clash with an unrestricted `CanDo` reading. Either inference needs
a typed evil-task domain, a fixed sense of `Consistent`, and the precise
impeccability condition. This is a real conditional test, not a demonstrated
incompatibility of omnipotence and perfect goodness. Likewise, apparent
omniscience/future-freedom conflicts depend on which truth objects, temporal
facts, counterfactuals and freedom senses are jointly claimed; no
unconstrained universal knowledge predicate settles them.

**Symmetry.** On the same fixed proposition and frame the #437 K5 theorem
gives conditional consequences from `◇G` and `◇¬G`. The evidence
obligations are not discharged by a change of label: a reverse possibility
claim needs an M-accessible **same-profile** alternative or a supported
exclusion of that profile. An actual, justified incompatibility among
essential properties would support impossibility; an objection merely noting
that metaphysical accessibility is not yet proved does not provide a
counter-witness. A finite E/M filter only establishes non-entailment of
unrestricted transfer; it is not evidence that the divine profile is excluded
in reality.

**Next discriminating test.** Fix senses for the slots by typed actual-world
bridges from the same-root perfection/intellect/will source (preserving
power-as-capacity versus exercise and the same rigid bearer), starting with the
nine `ProfileToStageTwoSenses` conjuncts and a `Power`-based omnipotence bridge.
Then revisit the simplicity/contingent-creative-choice core under that profile,
and test `NecessaryExcellenceAt` slot by slot (particularly freedom and
omniscience). Preconditions for any registration against `STMT-GOD-EXISTS`:
DEF records for the new load-bearing terms (omnipotent, omniscient, morally
perfect, free, maximal greatness, M-admissible) with sense tags; a decision
between the outer-E and inner-E readings recorded as a disambiguation; a
warranted naming bridge and admissible-world reading; and binding the nine-slot
input to the canonical statement only through the explicit sense bridges above.


## #1864 continuation: fixed interpretations and two attribute-intersection discriminators (2026-11-23)

**Scope and destination.** Continuation of merged #1865 and #1876, without changing their generic modal implications or claiming that an admissible divine essence has been discovered. The existing `TruthCore.Modal.DivineProfile.Interpreted` section provides a *specific, GOD_4-free instance* of the old thirteen-slot schema. The graph destination remains `b19ffd92-01bd-5c0b-9643-e7407137ea5e` (actual de re necessary concrete bearer), followed by `STMT-GOD-EXISTS` only if the independently interpreted actual-world naming and StageTwo sense bridges hold. This is a conditional support family, not a newly registered result, and no root-premise closure is claimed.

### Fixed candidate profile, with precisely limited meaning

The new `fixedProfile` supplies all thirteen positions **for one identical bearer** using previously defined StageTwo and causal senses instead of arbitrary `True` slots:

| Slot(s) | Selected formal sense | Live philosophical content / unproved strengthening |
| --- | --- | --- |
| `simple` | `StageTwo.IsSimple Composite`: no composition | Whether essential distinction/intentional acts are constituents counted by `Composite` remains open |
| `perfect` | `StageTwo.IsPerfect q.InAct`: every actual perfection present formally or eminently | The global `InAct` dictionary and its applicability across modal alternatives remain open |
| `good` | `StageTwo.IsSupremelyGood`: goodness as being and causal transmission of perfections | This is ontological/causal goodness, **not** a definition of moral impeccability |
| `one` | `ActualRoot m v x` and uniqueness among selected roots at the *same* world | GOD-free; neither uniqueness of all necessary beings nor `IsTheOneGod σ.IsGod` follows |
| `infinite`, `eternal` | Existing `Infinite` and `Eternal` predicates of the StageTwo source route | Content is inherited from their fixed supplied definitions; the present constructor does not establish them |
| `immutable` | `StageTwo.IsImmutable InPotency`, no passive potentiality | Does not show that an extrinsic relationship or contingent effect is an intrinsic respect |
| `intellect`, `will` | Existing `HasIntellect` and `HasWill` predicates, same individual | These encode capacities, not self-understanding, omniscience, actual exercise or intentional selection |
| `omnipotent` | Existing `DeiFiliusAttributeField.IsAlmighty σ power`: can perform every `power.Consistent` task | Capability is not obligatory performance; consistency of a task is a separate typed classification |
| `omniscient` | `KnowsAllContentsAt S Knows v x`: knowledge iff truth, for every individuated content in the selected `C` | Requires real cognitive uptake, appropriate content coverage, reference to contingent truths and factivity; **not** unlimited omniscience merely because `C` is a type |
| `morallyPerfect` | `PermissibleChoicesAt`: every actually selected act is permitted | Only no-forbidden-choice impeccability. Does not yet provide reasons, charity, best possible action or maximal goodness |
| `free` | `NoncoercedChoiceAt`: some selected, capable, not externally imposed action | Weak free exercise only. Does not establish ability to do otherwise under fixed complete conditions, timeless free creation or contingent willing |

The extra `Knows`/`Chooses`/`Permitted`/`Capable`/`Imposed` relations are **explicitly primitive**, not definitions of intrinsically intentional understanding or agency. A model assigning these relations successfully is a model of these chosen formal meanings, not an interpretation certificate for real cognition, normativity or divine freedom. Only the last three new senses (KNOW for `omniscient`, MORALLY_PERFECT, FREE) are candidates, and their stronger traditional counterparts remain open. **These primitives and candidate senses have doc comments only and no `DEF-…` records; each needs a DEF record before any registration.** In particular, nothing in the type yet separates `Knows` as cognitive uptake from a truth oracle: the restored-commitment control below satisfies `KnowsAllContentsAt` with one.

**Rigidity by construction.** Nine slots of `fixedProfile` (simple, perfect, good, infinite, immutable, eternal, intellect, will, omnipotent) ignore the world argument and use world-free dictionaries, so they hold at every world once they hold at one, even at worlds where the bearer does not exist (`Interpreted.fixedProfile_rigid`, by definitional unfolding). This rigidity is an **encoded interpretive commitment of the selected interpretation, not a derived essentiality**, and it adds no evidence for M-necessary excellence; any later use of `fixedProfile` in `GreatnessAt` or `NecessaryExcellenceAt` would inherit the stipulated rigidity. Whether a real source has those properties essentially across metaphysically admissible alternatives still needs a substantive essentiality warrant that the encoding does not supply. The genuinely open cross-world gap *for this profile* is the four world-varying slots `one`, `omniscient`, `morallyPerfect` and `free`. There is **no instance of `σ.IsGod` in any of the 13 slot definitions**; the `IsTheOneGod` implication is postponed to an explicit actual-world bridge.

### Positive same-bearer support and its limit

`Interpreted.positiveCore_from_same_root` composes the **existing** `RootPositiveIntellectWill.NecessaryPositiveRootIntellectWillAt` witness with the fixed profile. Conditionally on all that prior route's premises, it selects **the same n**, actually existing and necessary relative to the original `m.ontic.frame`, with six interpreted attributes: simplicity, perfection, causal/ontological goodness, unique selected actual-root status, intellectual capacity and will-capacity. This does not prove all thirteen and does not insert the GOD_4 name. Five of the six (all except `one`) hold at every world by construction of the interpretation (`fixedProfile_rigid`); that is stipulated rigidity of the encoding, not a derivation that they are essential divine qualities across M. It is a genuine cross-family reuse/connection, not six independent arguments or a new proof that the starting root exists.

**Eight-slot extension using pre-existing philosophical bridges.** `positiveCore_with_infinite_power_from_same_root` retains that *exact same root* and adds `Infinite n` through the already documented Aquinas `SubsistentBeingIsInfiniteReading`, using the root's explicit `q.esseOf n = q.essenceOf n` conjunct. It then reuses the **registered** `Results.Causality.NamingVeracityBatch1.infinitePowerFromAct` theorem to derive `IsAlmighty σ power n`. This requires the three separate OPEN commitments `InfiniteIsUnlimitedAct`, `ActivePowerFollowsAct` and `ConsistentTaskRequiresOnlyPossiblePerfections`; a consistent task does not have to be selected/performed. The resulting **eight** candidate slots (simple, perfect, good, unique selected root, infinite, intellect, will, omnipotent) have a nonempty same-bearer conditional route. Immutability and eternity were missing at this stage and are supplied by the ten-slot extension below; complete knowledge, moral agency and free agency remain missing, and the typed source's identity with a real subsistent act still depends on the prior argument's interpretation. These are not eight unconditional statements about an existing God, nor a proof of profile-admissibility.

`Interpreted.fixed_to_stageTwo_senses` shows that the selected StageTwo instances are pointwise identical for eight of their nine old slots. The exception is deliberate: the GOD-free selected-root uniqueness must be related to `IsTheOneGod σ.IsGod` at the actual world by the explicitly OPEN `hRootNamesOne`. `ClassicalAttributesSuffice` and `ActualDivineNaming` remain independently OPEN, so the original `actual_named_classical_god` consumer does not become unconditional. In particular, `RootPositiveIntellectWill` does not already include an unrestricted omnipotence, complete cognitive knowledge, impeccable actual choice or free intentional exercise proof.

### Attribute intersection: knowledge, immutability and contingent truth

`invariant_knowledge_forces_truth_agreement` is a valid chain of three biconditionals that makes explicit that strict invariance of known contents is incompatible with complete factive knowledge of a content whose truth varies: if the same x knows **exactly** every true selected content at worlds w and v and **the set of contents known is invariant** (`∀c, Knows w x c ↔ Knows v x c`), then every covered content has the same truth value at both worlds. `varying_truth_excludes_invariant_knowledge` derives the corresponding incompatibility when one covered content is true at w and false at v.

This states the exact condition under which one strict version of the simplicity/omniscience tension bites, **not** a contradiction in the full divine profile. The added premise is *invariant known-content membership*, not merely identity of the cognizing being, pure actuality or an unchanging act of understanding. To apply it, a defender of collapse must justify why simplicity/immutability requires that stronger cross-world invariant extension; the reply must explain how one immutable intellectual act can have contingent truths as extrinsically varying objects, without reducing intentional knowledge to a true-output machine. Neither side obtains that substantive bridge just from the theorem.

### Attribute intersection: power, moral selection and freedom

`can_do_without_choosing_forbidden` uses the existing task-power vocabulary. Given a particular explicitly **consistent** task corresponding to a **forbidden** selection, complete power entails `CanDo` while impeccable selection entails `¬Chooses`. These are not contradictory: *ability* and *actual choice* are distinct relations. A substantive conflict would require an extra principle such as “moral goodness entails inability to perform this coherent task”, plus a justified mapping of forbidden acts to coherent tasks. Simply changing `power.Consistent` to mean “morally permitted” removes the formal test by changing the original meaning. Conversely, omnipotence never entails accomplishing a logically contradictory task under the existing `IsAlmighty` sense.

The harder divine-freedom question remains `#555` and `#1737`: if simplicity entails one **necessary** creative act, and that **same** act is strictly sufficient for one selected contingent effect, the existing rigid-act trilemma rules out that conjunction. Existing `SelectedEffectBridge` and `NecessaryVariableEffects` separate a necessary bearer and stable ability from same-act performance and stable selected output; they do **not** warrant a metaphysically free intrinsic will. A timeless free choice proposal must justify at least one of: contingent extrinsic output without strict same-act sufficiency, a nonnecessary selection/decree distinct in relevant respect, or a reason that permits multiple rationally acceptable outcomes without fixing one. Each option carries distinct explanatory obligations; no hypothetical secret contradiction is counted as evidence.

For perfect goodness versus free creation, the sourced comparison in `docs/notes/optimal-creation-choice.md` already distinguishes Leibniz's best-world rationale from Aquinas's rejection of a unique greatest producible creation; neither existing witness establishes a single mandatory creation. Interpreting goodness as requiring a unique optimal choice would be an **additional** premise, and a serious modal-collapse objection would need a defended uniqueness claim, not merely God's rational perfection.

### Five grades of possibility and the exact modal conditional

1. **Satisfiability:** some mathematical assignment instantiates the fixed vocabulary and its selected constraints together. A finite structural control establishes only this, relative to the stipulated semantics.
2. **Logical consistency:** no contradiction follows relative to a declared logic and theory; a finite witness need not justify that all the metaphysical meanings are faithfully encoded.
3. **Conceptual coherence:** the chosen definitions and essential-property descriptions can jointly describe one concept without equivocation; open causal/cognitive/moral readings are relevant here.
4. **Epistemic non-refutation:** no known contradiction is found. This is *weaker* than `¬□¬P` under a fixed modal semantics; it can supply only defeasible comparative support.
5. **Genuine metaphysical possibility:** there really is an M-accessible alternative from actuality realizing the **entire fixed profile of one bearer**, with the given essence/identity conditions. No theorem or model here establishes this.

The established formal route can be written as:

`DescribedPossibleGreatness E m (fixedProfile …) w`
+ profile-specific **OPEN** `AdmitGreatnessWorlds E m (fixedProfile …) w`
+ `EuclideanAt m.frame w` + `ActualReflexive m w`
→ `∃x, GreatnessAt m (fixedProfile …) x w`.

The stated E-premise is outer-E/**inner-M**: it already includes M-necessity at the E-witness. Purely E-internal description requires the separate OPEN `InnerSuccessorsCovered` to reach it. The weaker witness-relative return `M(v,w) ∧ ∀u, M(w,u) → M(v,u)` can replace the sufficient Euclidean-plus-reflexive package when independently justified. S5 is stronger than this return step requires. Only **after** that actual-world return can `ProfileNineSuffice` (via the StageTwo bridge) and `ActualDivineNaming` give the existing GOD_4 proposition, and those bridges are not established by definition or a Boolean control.

**Provisional metaphysical assessment.** The strongest current positive route is cumulative: necessary actual concrete source → perfection not limited by receptive composition → same-bearer intellect/will capacity → still OPEN actual understanding and knowledge of all contents → still OPEN rationally free good selection → full interpreted necessary excellence and **particular** M-admissibility. This provides specific, non-vacuous partial reasons to examine an actual source's attributes; it does **not** establish the genuine possibility of the maximal profile. The strongest justified negative pressure is the #555 strictly efficacious necessary-act conflict and the new invariant-known-truth-content restriction *if its stronger cross-world premise is defended*. A stable impersonal source and brute/admissibility-restricted modal ontology remain alternatives where they furnish substantive explanations, but mere assertion of an unidentified incompatibility is not a defeater.

**Next discriminating work.** Test whether purely actual subsistent wisdom entails *intrinsic* factive cognitive uptake (not merely cognitive effects); whether essential intellect/will carries invariant capacities but variable intentional objects; whether perfect goodness permits more than one rationally acceptable contingent creation; whether free will is necessarily exercised or only essentially available; whether the surviving source routes support each of the three missing slots (omniscient, morallyPerfect, free) *at that same n*; and whether a warranted interpretation of the actual metaphysical accessibility relation includes the **particular** full-profile realization. Cross-check all this against `#555` and the received-esse and actualist-identity analyses. Keep #1864 open: metaphysical admissibility, full traditional attribute senses and GOD_4 naming remain unresolved.


### Additional same-bearer route: ten selected actual-world slots (#1864; PR #1880 continuation)

The eight-slot result above is now extended to **ten of the thirteen precisely
selected candidate slots of one actual source**, WITHOUT claiming ten essential
attributes in every metaphysically accessible world or a real full divine essence.
The two extra slots are **immutability** and **eternity**, not knowledge,
morally perfect freedom, or knowledge of creative possibilities.

**Prior art.** The registered argument `379399d1`
(`NecessaryClassicalGodRootByComposition`) already derives, on the same
positive-root route, the root's pure actuality and eternity from simplicity,
the composition premise d8024a38 and the q.10 reading. Relative to it, the
ten-slot theorem adds only the GOD-free packaging into `fixedProfile` and
omnipotence (through the q.25 task-power bridges of the eight-slot route); its
immutability/eternity step is a reuse of the same reasoning, not new support.

The new Lean helpers reuse the registered weaker composition premise
`ActPriorityThetaEight.ActInBeingAndPotencyMakeComposite` (statement d8024a38,
the esse instance of `ActPriorityAtFirst.ActAndPotencyMakeComposite`
3d99779b; strength relation 4b6d0b59) and Aquinas's
`ImmutableIsEternalReading`, rather than silently equating firstness with pure
act. The exact positive argument is:

1. The SAME `NecessaryPositiveRootIntellectWillAt` witness n from the prior
   eight-slot proof has `IsSimple Composite n` and is actually in act in the
   designated esse-respect (`q.InAct n q.esse`, already included in
   `PerfectRootAt`'s `IsMaximumIn`).
2. If any subject in act in the esse respect and in passive potency in some
   respect is composite (`ActInBeingAndPotencyMakeComposite`, d8024a38; the
   unrestricted 3d99779b is not needed), then n's simplicity forbids every
   `InPotency n r`. This does **not** derive the act/potency composition
   principle from simplicity; its philosophical warrant remains OPEN. A weaker
   n-specific instance would suffice.
3. By the existing q.10 interpretation
   `ImmutableIsEternalReading InPotency Eternal`, n is eternal. This is the
   primitive StageTwo `Eternal` predicate under that conditional reading;
   no independent timeless-creation semantics has been supplied.
4. `positiveCore_with_ten_from_same_root` reuses the earlier q.7/q.25
   infinite-power proof and identifies its bearer with this exact n via
   `PerfectRootAt`'s **uniqueness among actual selected roots**. No
   independent existential witnesses are commuted or identified by name.

**Relative warrant.** The act-and-potency composition premise has a positive
metaphysical reading: a real unactualized passive determination of an existent
requires differentiation between its present act and its real capacity for a
distinct act. If such differentiation counts as composition in the *chosen*
SIMPLE_4 sense, a subsistent source whose actuality is nonreceived cannot
possess it. The opposing interpretation can deny that every modal difference,
especially a different **extrinsic relation to a creature**, constitutes an
intrinsic unrealized determination. That denial need not reject the no-passive-
potency inference; it restricts its application to proposed decrees and outputs.
Both sides must preserve the difference between `CanDo` (active capacity)
and `InPotency` (passive reception). The conditional proof establishes neither
an unrestricted divine psychological impossibility nor actual metaphysical
necessity of every creature. **Shared dependency:** the same `Composite`
parameter occurs in the composition premise and in the root's simplicity, which
comes through `CompositeHasAUnitingCauseReading`. The more inclusive the SIMPLE_4
reading of `Composite`, the easier the composition premise but the harder the
simplicity step: the uniting-cause premise must then hold for act/potency
composites too. The two premises do not gain independent support from one
broad reading of `Composite`.

**Most consequential collision remains the creation-act interpretation.**
#555 refutes the bundle of (i) the identical decree/act token performed
necessarily, (ii) strict sufficiency of that token for a particular effect,
and (iii) contingency of that effect. In the ten-slot theorem, n's
immutability is not, by itself, an identity thesis about the token of a
freely chosen creation; its eternity is not a principle of strict efficacy.
Consequently, that certified core cannot be applied without a further
contentful link from essence/simplicity to necessary *performance* of this
specific act and its stable output. The surviving positive account must give
a reason why a timeless, fully rational, immutably good act can have one of
several contingent effects without turning selection into a passive change.
This is an open explanatory task, not refuted merely by postulating a hidden
contradiction.

**A sharper power/goodness discriminator.** The earlier
`can_do_without_choosing_forbidden` concerns actual moral **non-selection**.
The new `IncapableOfForbiddenTasks` is a separate stronger sense: a subject is
unable to perform each mapped morally forbidden action. Under
`IsAlmighty` that reading forces **every** morally forbidden mapped task to
be logically *inconsistent* (`moral_incapacity_forces_task_inconsistency`).
If any corresponding forbidden task is independently judged
`power.Consistent`, those two strong attributes cannot coexist
(`coherent_forbidden_task_rules_out_moral_incapacity`). The test does NOT
establish that a sinful action, as an action of an essentially perfectly good
being, is itself a logically consistent task. Defining consistency as
morality instead would change the existing typed active-power sense and erase
the discriminating premise. The weaker impeccability-of-choice reading can
coexist with the active-power predicate, but it is not a full virtue/moral-
perfection explanation. Two limits of the formal test: (i) `Permitted` varies
by world but `taskOf`, `Consistent` and `CanDo` do not, so
`moral_incapacity_forces_task_inconsistency` turns a world-relative
prohibition into a world-free inconsistency, and the "exact price" is relative
to that indexing; (ii) `coherent_forbidden_task_rules_out_moral_incapacity`
needs the forbidden action to correspond to some task through `taskOf`, and the
classical reply that sin is a defect, not an exercise of power, rejects exactly
that mapping.

**Provisional current result:** ten actual selected attributes are connected
conditionally to ONE prior necessary source; three remain outside the
positive same-bearer derivation: **factive intentional omniscience,
morally perfect selection and genuine free willing**. Their exact stronger
senses and intrinsic intentional mechanism, universal content coverage,
and nonnecessitating contingent creation remain OPEN. Existing `#1866`/
`#1873`/`#1737` are the proper neighboring work; do not duplicate their
conditional cognitive/choice proofs or presume that source-level cognition
or free exercise has been established there. The complete profile's
**metaphysical admissibility from actuality** is a separate unsolved
commitment even if all thirteen candidate predicates were shown
mathematically jointly satisfiable. The actual-world GOD_4 naming,
rigid-identity interpretation and essentiality-throughout-M conditions
remain independently OPEN. Nine of the ten slots (all but `one`) already hold
at every world by construction of `fixedProfile` (`fixedProfile_rigid`); that
stipulated rigidity is not essentiality evidence, so the open cross-world gap
for this profile is `one`, `omniscient`, `morallyPerfect` and `free`, plus the
warrant for the encoding's rigidity itself.

**Next discriminating test:** Reuse the latest intrinsic-wisdom/
cognitive-uptake analysis to distinguish a source that *knows* contingent
contents from one producing a sound truth oracle; examine whether pure
actuality permits world-dependent intentional *objects* while retaining one
actual intellectual act. For creative choice, compare a timeless
agent's reasons that make multiple outcomes rationally permissible with
#555's strictly determining same-act condition; if only one adequate
outcome is possible, identify the defended optimality/necessitation
principle that makes it unique. Bind only reviewed, fixed-sense
premises to the cumulative GOD_4 route, and leave #1864 open otherwise.


### Restored-commitment control: source simplicity, knowledge and permissible different effects

`DivineProfile.Interpreted.CreationControl.Compatibility` is a deliberately
**structural**, non-metaphysical continuation of the existing
`NecessaryVariableEffects.alternatingEffects` (#462), not another unrelated
modal frame. Both worlds contain the SAME necessary individual `source = none`
(of type `Option Bool`), while a different composite, passively potent effect
exists and is caused in each world. At the designated actual world `false`,
the nonempty esse/act dictionary agrees **exactly** with its actual inventory.
The source is simple, devoid of passive potency and eternal, under
`ActAndPotencyMakeComposite` (the unrestricted form, which implies the
d8024a38 instance used by the ten-slot theorem) and `ImmutableIsEternalReading`; the actual first
effect is BOTH composite and potent, so the relevant composition predicates
are not globally empty.

The model further carries two opposed truth-contents (true at only one world),
content-complete and factive **extensional** knowledge at the same source,
and two different selected, noncoerced, permitted actions. The single
forbidden action `none` is never selected, but it is also outside `Capable`
and has no causal output, so the control instantiates nonselection by
incapacity, not "able but never chooses"; a permissible abstention is not
modelled. The selection-output correspondence
holds world by world, and #462's necessary source, contingent first effect,
and absence of ONE fixed effect remain true. Thus **the finite structural
formulas alone** do not force an invariant known-content set or a unique
chosen contingent effect from source necessity, absence of passive potency,
or thin moral non-selection. The control restores an actual nontrivial
composite/potent creature rather than making every predicate trivially True.

**Three explicit limitations:** the source's cognitive relation is assigned
extensionally from truth and is not *intrinsically grounded intentional
understanding*; the action-output match is only a correlation, not genuinely
reason-guided agency or a warrant for free willing; the `q.InAct` dictionary
is verified against the actual world's beings but not against the entire
world-indexed inventory. In particular, the control does not instantiate the
full StageTwo `fixedProfile`, provide an actual root in the selected grounding
relation, demonstrate a good-willed creative act, or show that such a world
really is metaphysically admissible. It is a counterexample to a proposed
**unbridged formal entailment**, not evidence for the truth of a rival divine
essence. #555's three-premise same-token collapse remains intact and would
need additional open interpretive bridges to apply to this source.

The philosophical research task is therefore sharpened: defend or reject
the bridge from an immutable source's immanent intellectual/volitional act
to **invariant object-content or strictly fixed effects**, versus an account
where one intrinsic perfection can be related to contingent objects without
itself becoming a passive changing state. The model makes clear which step
needs metaphysical explanation, not that either account has been won.


## C5 continuation: actual-source realization and its negation (2026-11-23)

This checkpoint follows merged #1865, #1876 and #1880. It tests C5 (a
genuinely metaphysically possible complete necessary divine essence) and
¬C5 (there is no such admissible bearer), not merely the evidential
fact that nobody has proved C5. The formal additions are in
[DivineProfile](../TruthCore/Modal/DivineProfile.lean). All are analyst
formulations without new Plantinga attribution.

### C1–C4 as a positive realizer route

Here C1 is the totality esse-cause commitment (#1882), C2 the
receptivity-or-prior-reception commitment (#1884), C3 weak concurrent
actualization (#1885/#1886; its statement `40a97664`, "whatever
has received esse is given being by something whenever it is
present"), and C4 the
eminence/noesis question (draft #1892).

The existing Interpreted.positiveCore_with_ten_from_same_root takes ONE
necessary actual source from RootPositiveIntellectWill's complete
conditional premise bundle, then uses the already identified q.7
infinity, q.25 coherent-task power, act/potency-composition and q.10
eternity premises. Its same-witness support concerns ten actual
candidate predicates, not ten independent arguments or a complete
metaphysically possible essence. It is a substantive point of contact
with the C1–C4 inquiries into an underived source, sustaining
actuality, causal perfection and intrinsic intellect; those
metaphysical commitments are not thereby unconditionally established.

The new candidate_greatness_from_ten_and_four theorem precisely
isolates the remaining conditional work:

1. The existing ten slots hold of the SAME actual necessary root n.
2. n additionally has actual omniscient, morallyPerfect and free slots.
3. At EVERY M-successor of actuality, this same n has the four
   world-sensitive slots one, omniscient, morallyPerfect and free.
   Reading choice: free is NoncoercedChoiceAt, a choice actually
   made, so requiring it at every M-successor takes the
   "necessarily exercised" branch of the open test "whether free
   will is necessarily exercised or only essentially available"
   (**Next discriminating work**, in the #1864 continuation above),
   not the weaker "essentially available" branch.

NecessaryAt from the ten-slot theorem provides continued existence.
Nine other predicates transport only because the particular GOD-free
fixedProfile constructor makes them world-invariant by DEFINITION,
not because their essentiality was proved. The proof explicitly
requires that fixed interpretation rather than allowing an arbitrary
opaque profile. The new candidate_possible_from_same_root combines
these conditions with the actual ten-slot source and actual
reflexivity. It derives M-possible full greatness and, as a separate
conjunct, that the same n with PositiveCoreAt (the selected unique
root at actuality) is maximally great at actuality, so the bearer is
pinned rather than existentially quantified away. It uses no
E-description-to-M transfer and no S5 condition beyond reflexivity.
In this route C5 is downstream of actual greatness: the possibility
conclusion is obtained from the actual maximally great bearer, so it
cannot serve as an independent ◇-premise for #437's inference to
actual existence (cf. actual_necessary_bundle_greatness, which already
shows that the possibility detour adds no independent support). It
does NOT prove that M is real metaphysical access,
that the nine stipulated rigidities hold of a real essence, or that
the three weak proxies capture traditional intrinsic omniscience,
moral perfection and free willing.

The companion Control.actualButNotEssential_holds is a two-world
S5 structural model on the generic ProfileSlots, whose slot names
are mnemonic only: one rigid bearer exists at both worlds, satisfies
all thirteen opaque slots at actuality, and is necessary in existence;
the opaque one slot (here v = false; not fixedProfile's ActualRoot
uniqueness) fails at the other world. Hence there is no M-possible
complete maximal-greatness profile from the origin. This proves an
essentiality gap at the schema level, not a metaphysical impossibility
of God. "Essential" here means de re modal possession of the slots at
every M-successor, not a Finean essence (cf. NecessaryExcellenceAt,
which is likewise not essentiality). The positive theorem deliberately
requires what this schema-level control omits; whether the
fixedProfile root premises entail one at M-successors is untested.

### The strongest worked case for ¬C5

The existing #555 SimplicityCollapse.rigid_core proves a genuine
contradiction from one rigid act token necessarily performed, its
strict sufficiency for one particular effect, and the contingency
of that effect, on the same ontology and frame. For the complete
divine profile to be genuinely impossible by this route, the
simplicity/free-will interpretation must *entail* that a specific
freely selected creative decree is necessary in performance AND
strictly suffices for its particular contingent effect. These are
contentful, currently OPEN bridges. Mere necessity of the bearer,
immutability or identity of the source's intrinsic act does not
already supply them; "mere" matters, because the C5 profile itself
contains the immutable slot, and a registered result already
connects immutability to this pressure.

The registered SIMPLICITY-ROOT-EXPOSURE result
(`SimplicityCollapse.rootExposure`, argument `df2b23c7`) is the
nearest conditional bridge from immutability to #555's conclusion.
Clause 1: IsImmutable plus the Metaphysics IX.6 potency reading
(PotencyIsUnactualizedCapacityReading) plus the open unattributed
ModalCapacity bridge (actuality in a respect at an accessible world
suffices for ability at this world) collapse the respects: no
respect true of the bearer at an accessible world is false of it
here. Clause 2: adding a decree that is one of the bearer's
respects, ExclusiveDecree (at most one decree here), a decree at
every accessible world and RespectSuffices (the decree suffices for
the effect at those worlds) gives ¬ContingentAt for the effect.
Clause 4 states the dilemma in the other direction: for a contingent
effect, some accessible world lacking it has no decree, or
ModalCapacity fails. In the general, world-indexed RootExposure, the
open inputs are ModalCapacity, a creative decree read as a respect of
the source, ExclusiveDecree, a decree at each accessible world and
RespectSuffices.

Mapping to the C5 encoding: fixedProfile's immutable slot uses StageTwo
IsImmutable over a world-free InPotency, and its perfect slot a
world-free q.InAct, whereas RootExposure's ReadingsAt and InAct are
world-indexed. The C5 encoding maps to RootExposure by the constant
families fun _ => InPotency and fun _ => q.InAct. Under the constant
family, decree-as-respect plus RespectSuffices alone collapses
contingency: if the decree d is a respect of the source, it holds at
every world, so RespectSuffices puts the effect at every accessible
world and ¬ContingentAt follows, with no ModalCapacity, IX.6 reading,
immutability, ExclusiveDecree or decree-at-each-world
(Interpreted.constant_respect_collapses_contingency, an unregistered
helper). So the C5 encoding can host a contingent effect only if
creative decrees are not InAct-respects of the source (RootExposure's
oneRespect exit, where no decree is a respect) or RespectSuffices
fails. A world-varying decree-as-respect would need InAct re-indexed
by world, and whether the source's acts may vary by world is exactly
the contested point. The world-free q.InAct is itself rigid by
construction, an encoding artifact like fixedProfile_rigid, and is
evidence for neither side. For the C5 source the concrete ¬C5 next
test is therefore the two live inputs decree-as-respect and
RespectSuffices. Neither RootExposure nor this note asserts the
readings, ModalCapacity, decree-as-respect, or that divine simplicity
entails them.

The rival account must explain how one
timeless rational source nonnecessitatingly produces one of
several permissible effects, not merely stipulate world-relative
outputs. The #462 and #1880 variable-output controls establish
non-entailment of fixed creation from thin structural premises,
not an adequate divine agency theory.

Other live restrictions are conditional on precise senses. Coherent
task power plus morally impeccable *nonselection* is not a
contradiction; adding the stronger thesis of incapacity for a
coherent forbidden mapped task gives the existing power/morality
incompatibility. Factive complete knowledge of changing truths
plus *identical known-content membership* fails, but simplicity,
immutability and a rigid intellect capacity do not imply the latter
(CreationControl); whether identity of one intellectual act does is
an open test (**Next discriminating work**, #1864 continuation
above). Perfect goodness versus permitted evil needs a further
defended obligation to prevent each permitted evil; the selected
proxy predicates contain no such obligation and so supply no
contradiction. Those are discriminating substantive tests rather
than hypothetical hidden impossibilities.

### Modal and epistemic scope; comparative assessment

Logical noncontradiction, a fixed joint formal model, conceptual
coherence, reasonable epistemic judgment, and M-accessible
same-bearer metaphysical realization are distinct grades. #438
shows that S5 for candidate E and metaphysical M relations does
not itself transfer descriptive satisfaction into M access.
Even targeted witness admission must be defended. Classical
absence-of-impossibility means ¬□¬P within ONE fixed modality;
it does not mean 'we have not yet derived a contradiction'.

The familiar #437 K5 positive and negative inferences remain
conditional on their own boxed premises; S5/reflexivity enables
actual-world return. The symmetrical necessary-nonexistence
argument owes an independently justified reverse possibility
premise concerning the SAME fixed G, world accessibility, rigid
identity and attributes. Mere failure to believe C5 is not
metaphysical proof of ¬C5. Conversely, a supported strict
incompatibility or admissibility restriction could justify
¬C5 without first finding a satisfying negative description.

**Provisional overall judgment:** the cumulative necessary
same-source work supplies informative, conditional positive
warrant for a substantial partial attribute profile. That is
stronger than unconstrained predicate recombination, but the
complete C5 premise is NOT established. The strongest actual
negative result, #555, is an exact conditional inconsistency;
its necessary-act/strict-efficacy reading remains disputed and
is not derived from the selected full profile. The registered
SIMPLICITY-ROOT-EXPOSURE bridge comes closest. In its general,
world-indexed form it derives ¬ContingentAt from immutability and
the IX.6 potency reading with open ModalCapacity, decree-as-respect,
ExclusiveDecree, decree-at-each-world and RespectSuffices inputs.
For the C5 source, whose world-free q.InAct is rigid by construction,
decree-as-respect plus RespectSuffices alone already collapse
contingency; these two are the live inputs there, and neither is
established. Thus ¬C5 is also NOT established. The positive route
warrants further work on its concrete missing predicates; the
negative route warrants a targeted test of whether a creative decree
is an InAct-respect of the source and whether it strictly suffices
for its effect. Neither
absence of contradiction nor lack of a full model decides the case.

**Next tests and revision conditions:** obtain intrinsic and
all-content cognitive uptake from #1866/#1873 rather than a
truth-oracle proxy; justify or refute #555's same-creative-act
bridge under #1737's contingent rational choice, concretely by
testing the two live inputs for the C5 source, decree-as-respect
(a creative decree as an InAct-respect of the source) and
RespectSuffices, keeping ModalCapacity, ExclusiveDecree and
decree-at-each-world for the general world-indexed RootExposure,
and whether re-indexing InAct by world is warranted; test whether the
fixedProfile root premises entail the one slot at M-successors;
establish
selected-root uniqueness across M without definitional
essentiality; justify M's metaphysical interpretation,
actualist/counterpart same-bearer identity, and the GOD_4
actual-world naming bridge. Add DEF/sense records for the
knowledge/choice primitives before binding a canonical argument.
A confirmed incompatibility or justified complete realizer would
revise this assessment. No registered result or computed
premise-frontier change is claimed for this helper-only delta.
