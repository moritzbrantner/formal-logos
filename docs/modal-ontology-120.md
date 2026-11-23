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
     bridges from each slot to its typed sense at `w`. The `one` slot is
     GOD-free; its bridge to `IsTheOneGod σ.IsGod` is the only place where
     `σ.IsGod` enters, and only at `w`.
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
rather than substitute an already asserted GOD_4 witness. This is why the
actual-root support currently reaches only a **partial** candidate for the
ontological possibility premise, notwithstanding the stronger structural modal
helper.

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
