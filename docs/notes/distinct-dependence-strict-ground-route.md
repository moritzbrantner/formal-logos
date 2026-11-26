# A scoped strict-grounding argument for nonmutual existential dependence

Date: 2026-11-13. This note elaborates **premise 2** of the nine shared
terminal-input combinations for God-existence support. The formal route is
recorded in `specs/existential-dependence-strict-ground.toml`; existing direct
acceptance of the premise remains available.

## The three different relations

Let `x` and `y` be **beings**, `Ex(x)` and `Ex(y)` their respective **existence
facts**, and `S` the assumptions of a Fine-style pure logic of ground (PLG).

1. `D(x,y)` is Truth Core's existing counterfactual **dependence for being**:
   without `y`, `x` would not be. This is stipulated as a relation on beings;
   its interpretation allows impossible counterfactual antecedents.
2. `StrictlyGrounds S Ex(y) Ex(x)` means that the existence fact of `y` is
   derivably a **strict partial ground** of the existence fact of `x` in Fine's
   PLG, relative to `S`. The calculus's consistency and derivability are
   syntactic, not automatically ontological.
3. `PriorSimply y x` is the project's selected **simple metaphysical
   priority**. It is neither counterfactual dependence nor strict grounding
   by definition. In particular, causal or temporal precedence and
   explanatory grounding should not be collapsed into one predicate.

The selected mapping is an **OPEN philosophical bridge**:

```text
For all distinct x,y: D(x,y) → StrictlyGrounds S Ex(y) Ex(x).
```

It is a directional implication, not an equivalence. It says nothing about
`D(x,x)`, which the counterfactual reading may make trivially true. The map
does not assert that different beings have different labels.

### What the Lean type actually encodes: a structural surrogate

In the theorem, `S` and `existenceFact : B → Atom` are arbitrary parameters,
and the atoms are uninterpreted (`DEF-FINE-PLG-STRICT-PARTIAL-GROUND`;
`DEF-FINE-PLG-DERIVABILITY`: "derivability says nothing about what actually
grounds what"). The formal content of the premise bundle is therefore
**structural**: distinct-step `D` embeds, under some labelling, into the strict
partial ground order of some consistent PLG theory. Nothing in the type says
that the atoms are existence facts, that the edges are actual or faithful
grounding, or which kind of ground is meant. Writing `Ex(x)` for
`existenceFact x` is the **intended reading**, an OPEN interpretation outside
the type. The labelling keeps beings and atoms as different types, but it does
not make the atoms existence facts.

The bundle is **stronger than the target**.
`mapForcesDistinctDependenceAcyclic`
(`TruthCore/Results/Causality/DependenceStrictGroundMapStrength/`) verifies
that consistency plus the map already force distinct-step `D` to have **no
finite cycle**, not only no 2-cycle. The formal warrant for the map is
therefore a warrant for the acyclicity of `D`, and any rival who denies
nonmutuality also denies acyclicity. The
[fixed-label and finite-ancestry tests](#what-does-a-consistent-representation-add)
below establish both the converse for identity labels on an inhabited domain
and a sufficient condition for well-foundedness using finitely many labels
over each effect.

### Which "ground": the selected sense and the open readings

Disambiguation `23dd6f32-b456-4963-adb3-7befbf0dc4fb`
(DEPENDENCE_FOR_BEING_VERSUS_STRICT_GROUND) records the senses each term takes:

- `D` takes sense 1, `DEF-DEPENDS-FOR-BEING`: efficient-causal counterfactual
  dependence of an effect on its agent cause (ST I q.44 a.1 ad 2). Its paradigm
  is "the light in the air depends on the shining sun".
- "Ground" takes sense 2 only: Fine's formal strict partial ground on
  uninterpreted atoms.
- The direct-assumption route crosses from sense 1 to sense 2 at the OPEN map
  premise `42756c07`. The strict-path route assumes the OPEN alignment
  `b6784d40` as its crossing premise and derives the map by PLG rules. Both leave
  the interpretation of the labels as existence facts open.
- The `controls` argument (missing map) shows that the two senses do not mix
  without that premise.

The theorem selects **no** metaphysical reading of the atoms. Two sibling
interpretations of the map remain open and untyped:

- **(a) Constitutive/metaphysical ground of existence facts.** This is Fine's
  non-causal metaphysical explanation, and it is the reading the rationale below
  appeals to. On it, whether the definition's own paradigm edge is covered is
  open (reassessed 2026-11-26, [negation tests](#negation-tests-on-the-same-labelled-edge-2026-11-26)):
  the illumination case supports a local direction of causal supply, but gives
  no warrant that the sun's existence fact partly grounds the light's. If it
  does not, the map would have to be restricted to a non-causal relation of
  receiving esse, not stated for the broad `D`.
- **(b) Natural/causal-production ground.** Here PLG is applied as the logic
  common to all grounding relations. On this reading the paradigm edge's local
  causal direction is supported, though applying the formal map still requires
  warranted steps between the selected labels, and the "constitutive
  explanatory direction" rationale does not apply. The map's warrant then reduces to the asymmetry of efficient causal
  dependence for being (compare `STMT-EFFICIENT-CAUSE-NOT-DEPENDENT-ON-EFFECT`),
  strengthened to acyclicity.

Neither reading is preferred by the formal result. A typed formalization of
either reading would need its own definition and Lean declaration: for (a), a
non-causal existence-fact grounding relation; for (b), a causal ordering of
existence facts. This is the precise next step for the interpretation.

## The positive argument, step by step

1. **Ground-theoretic order.** Fine's strict partial ground obeys transitivity
   in the formal PLG, and a PLG-consistent theory cannot derive a strict
   ground of an atom by itself. These are existing verified results in
   `TruthCore.Results.Modern.Fine.PlgDerivedRules` and
   `TruthCore.Results.Modern.Fine.StrictGroundAcyclic`.
2. **Existential interpretation.** For this selected family of existential
   dependence edges, the OPEN map above is assumed. Formally this is only the
   structural embedding. Its intended reading, that the edges are faithful
   grounds of existence facts, is a further OPEN interpretation. This is where
   real metaphysical argument must justify applying the ground relation,
   rather than merely importing its formal laws.
3. **Suppose a reversal.** Let `x ≠ y`, `D(x,y)`, and `D(y,x)`. The map gives
   `Ex(y) ≺ Ex(x)` and `Ex(x) ≺ Ex(y)`.
4. **Derive the contradiction.** PLG transitivity gives
   `Ex(x) ≺ Ex(x)`. With consistency, that is impossible. Thus
   `D(x,y) → ¬D(y,x)` for distinct beings.

This new proof composes the **existing Fine result** into the unchanged
proposition `STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT`; it supplies an
alternative conditional support, not a direct proof that all actual
counterfactual dependence is strict grounding. The **proof** uses no regress or
well-foundedness assumption. The **premise bundle**, however, commits to the
acyclicity of distinct-step `D` (see above). No new argument for God's
existence is asserted.

## Why this bridge is a philosophical claim, not a synonym

The strongest positive rationale, on reading (a) above, is **constitutive
explanatory direction**:
an existence fact genuinely receives its being from another fact, and the
source does not in turn receive that very existential actuality from the
effect. In that sense dependence marks an explanatory ordering rather than
mere correlation. Aquinas's *In V Metaphysicorum* lecture 13, nn. 15–18,
supplies source-backed conceptual support for priority's directional
dependence **when an order of prior and posterior is already given**. The
source does not establish that every counterfactual dependence pair falls
under such an order.

The gap is real. Ordinary necessity of co-existence does not orient an
explanation: two essentially inseparable but distinct constituents might
each be absent if the other were absent. On that broad counterfactual reading
`D(x,y)` and `D(y,x)` can both be true, while neither is a strict ground of
the other's existence. This is a **substantive scope alternative**, not a
merely conceivable unspecified objection. Any blanket identification of
counterfactual dependence with strict grounding would incorrectly rule it
out by definition. Likewise, explaining why a particular quality of a thing
obtains is not automatically explaining the existence of its entire bearer.

For the intended Thomistic explanatory sense the burden is now precise:

- Specify which existence facts actually receive esse from which sources,
  and in which respect. A separate same-respect source-dependent relation may
  be preferable to the current broad `D`.
- Defend the faithful **strict** interpretation. Weak grounding, correlation,
  essential co-instantiation and mere modal co-existence do not suffice.
- Show that the selected PLG assumptions are consistent and appropriate for
  actual existential facts, not just formally non-explosive.
- Transport the result to the selected `PriorSimply` only through a separate
  priority bridge. Neither this proof nor Aquinas's quoted order criterion
  defines that transport.

## Rivals to the map premise

Each rival names the target, the mechanism and its independent
justification. The two published rivals were supplied by the semantic
challenge on PR #1600. Their attribution is deferred: the cited texts have not
been materialized or read here, so they are recorded as navigation, not as
verified source claims.

| Rival | Target | Mechanism and justification | Price / standing |
|---|---|---|---|
| Modal co-existence (above) | Map on the broad counterfactual `D` | Essentially inseparable distinct constituents satisfy `D` both ways while neither strictly grounds the other's existence | The map must be restricted to oriented, source-dependent edges; still unresolved |
| Symmetric metaphysical dependence: E. Barnes, "Symmetric Dependence", in Bliss & Priest (eds.), *Reality and its Structure*, OUP 2018; N. Thompson, "Metaphysical Interdependence", in Jago (ed.), *Reality Making*, OUP 2016 | The map read as genuinely explanatory (reading (a)), and the strictness of grounding itself | Published positive arguments that some constitutive dependence is mutual (for example, positions in an ante rem structure). Such edges cannot be represented in any consistent strict-ground theory | If those cases are genuine dependence for being, the map fails on them. Defending the map requires either rejecting the cases or restricting `D` to a non-symmetric source relation. Unresolved; no refutation recorded |
| Vacuous counterpossibles (Lewis/Stalnaker semantics, defended by Williamson) | The map on `D` as `DEF-DEPENDS-FOR-BEING` defines it, "including where the antecedent cannot be realized" | On vacuist semantics, "if `y` were not, `x` would not be" is vacuously true whenever `y` exists necessarily. So any two distinct necessary beings mutually `D`-depend, and the map plus consistency then implies that `B` contains **at most one necessary being** | The map depends on a **non-vacuist counterpossible semantics** for `D`, or on a domain restriction (for example, excluding necessary abstracta from `B`). `DEF-DEPENDS-FOR-BEING` does not currently say which semantics it uses. This is a recorded dependency of the map, not a refutation |

No substantive objection to the formal validity of the derivation was
identified.

## Checked omission controls

The Lean `controls` theorem records two populated interpretations using the
distinct beings `true` and `false`:

1. **Without consistency:** `S = Set.univ` derives every ground sequent, so
   even wholly mutual `D` satisfies the formal dependence-to-ground map.
2. **Without the map:** the existing Fine infinite-descent construction
   supplies a consistent PLG theory while the unconstrained `D` is wholly
   mutual. The chosen theory simply does not interpret the relation.

These controls establish that the two inputs perform different work. They
do not prove either open input about metaphysical reality. They also prevent
the superficially attractive but invalid move of pointing to a partial-order
theorem and calling all ontological dependence a partial order.

**Nonvacuity.** `nonvacuity`
(`TruthCore/Results/Causality/DependenceStrictGroundMapStrength/`) gives one
joint formal model of the whole support bundle with a nonempty `D`:

- the consistent Fine infinite-descent theory over `Nat`, which derives `n+1 ≺ n`;
- the identity labelling;
- `D x y` iff `y = x + 1`, which has the distinct edge `0 → 1`.

So the bundle is not satisfied only by an empty `D`. This is a formal
interpretation only. It says nothing about real beings, and the model's
infinite descent is an incidental property of this witness.

## The infinite series at the efficient-cause consumer

Consider the cause of member 0. Member 1 supplies it, independently of 0,
and receives from member 2. At every later step the successor plays both
roles. Independence **of this effect** leaves room for dependence on a
further cause. What happens if this answer is available at every step?

Result `a01e0429-1544-453d-973b-779f186c1654`,
`strictGroundConsumerAllowsInfiniteCauses`, joins the earlier Fine descent
and Second Way omission models on one carrier. The beings and PLG atoms are
natural numbers with the identity labelling. There is one respect. Both the
efficient cause and the per se link of each `x` are its successor. Set
`D(x,y)` precisely when `x < y`. This includes indirect dependence on
**every** later member. PLG strict transitivity extends the successor sequents
to that entire relation. Thus the rival survives even when distinct-step
dependence is transitive and excludes finite cycles.

| Step in the existing argument | What holds in this model |
|---|---|
| Consistency and the distinct-edge map give P2 (`40b8313e`). | Every mapped edge is derivable in the same consistent theory. Here no number depends on itself. P2 itself leaves the diagonal open. |
| P8, no self-causation and P2 give cause independence (`972ed7e5`). | For `c = x+1`, `x < c` and `¬ c < x`. Yet `c < c+1`. |
| Effect dependence, cause independence and sufficiency of nonmutual dependence for priority give cause priority (`695c2113`). | Interpret `P(c,x)` by `x < c`. This makes the separate sufficiency bridge true for all pairs here. |
| The Second Way separately requires accessibility of its per se relation (`97f5850f`). | Its order, cause-priority, irreflexivity and middle-cause premises all hold. Every candidate first cause `f` has the incoming cause `f+1`, so there is no first efficient cause and accessibility fails. |

**Provisional judgment.** P2 has positive warrant wherever the source of a
bearer's very existence can be identified independently of the recipient in
that same respect. The light's dependence on the shining sun illustrates the
intended causal direction. Applying the strict-ground result globally still
requires a consistent theory and a defended assignment of existence facts to
all distinct dependence edges. The witness supplies arithmetic labels. It
specifies neither counterfactual truth conditions nor a metaphysics of
production. Its single respect also leaves the hand-and-stick objection to P8's
all-respects export intact. P2 remains available directly as the weaker
commitment.

As an explanation, the infinitist can take the entire organized series as
given and cite a specific upstream supplier for each member. The founded
account additionally explains supply by something whose own supply is
underived. At issue is whether the local answers and the organization suffice
to explain **why there is supply at all**. The borrowed-exercise comparison
shows how relay constraints can admit both an active and an inactive series.
Transferring that comparison to existence requires an account of admissible
alternatives for the very same bearers and respect. This model fixes the edges
and contains no such alternatives. A discriminating next test would show on
those common alternatives either that the organization accounts for actual
supply or that supply requires an underived source, with a reason independent
of assuming termination. [Borrowed exercise, “Three rivals”](borrowed-exercise-741.md#three-rivals)

## Effect on the God-existence support graph

The new proof creates another way to support one of the **nine inputs shared
by the terminal-only calculation**. Its premises are PLG consistency and the
structural strict-ground map. The map's reading as faithful grounding of
existence facts stays a further open interpretation. Neither premise is
disguised as a definition. It does
not replace the separate unrestricted independence-to-separability premise,
which faces the concrete necessary-being counterexample investigated in the
parallel replacement work. It does not automatically change the count of
premises that remain open or certify the theological conclusion.

**Next proposition:** `STMT-PRIORITY-REQUIRES-NONMUTUAL-DEPENDENCE`. In the two
root-facing consumers that only use `PriorSimply y x → D(x,y)`, first derive
and register a weaker sibling. Investigate whether actual causal/explanatory
priority suffices for that implication without the full reverse-dependence
negation; preserve the stronger original for the consumers that genuinely
need its other half. Next, examine the positive separation witness for the
existing independence premise only in the local context where it is used.

### Source and proof locators

- Fine, *The Pure Logic of Ground* (2012), §§2–3; formalized rules in
  `TruthCore/Modern/Fine/PureLogicOfGround.lean`; formal strict-ground results
  in `TruthCore/Results/Modern/Fine/StrictGroundAcyclic/Solution.lean`.
- Aquinas, *In V Metaphysicorum* lecture 13, nn. 15–18; consulted source and
  limits described in `docs/notes/priority-independence-logic-support-investigation.md`.
- Existing nine-premise research baseline:
  `docs/notes/nine-premise-support-investigation.md`.
- Current new formalization:
  `TruthCore/Results/Causality/DependenceStrictGroundMap/{Challenge,Solution}.lean`;
  strength and nonvacuity results in
  `TruthCore/Results/Causality/DependenceStrictGroundMapStrength/{Challenge,Solution}.lean`
  (spec `specs/existential-dependence-strict-ground-strength.toml`).
- Sense record: disambiguation `23dd6f32-b456-4963-adb3-7befbf0dc4fb`.
  Interpretation, rivals and next tests:
  attempt `1020b663-7fe1-42d2-8b0c-8a767607a1ce`.

## Self-dependence: reflexive requirement versus strict dependence (#1593)

Date: 2026-11-14. Batch spec `specs/reflexive-dependence-scope.toml`; Lean
vocabulary `TruthCore/Causality/ReflexiveDependenceScope.lean`; results in
`TruthCore/Results/Causality/ReflexiveDependenceScope/`. Attempt
[`a4d430a0-9711-4d04-b4a5-be385f92e757`](../../corpus/attempts/a4d430a0-9711-4d04-b4a5-be385f92e757.json).

### The conflict, made exact

`STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT` says nothing about `D(x,x)`;
`STMT-DEPENDENCE-FOR-BEING-ASYMMETRIC` excludes it. The two share the primitive
`DependsForBeing`, which has no built-in self-relation law, so the Lean corpus
contains **no contradiction**. They conflict only under a reflexive reading:

- **Checked:** if `D` is reflexive (new OPEN statement *Everything depends for
  its being on itself*, `56252cd8`), unrestricted asymmetry fails on every
  inhabited domain (`reflexiveRefutesAsymmetry`, result `bf6cb784`).
- **Checked separation:** with `D(x,y) := x = y` on two beings, `D` is reflexive
  and distinct-nonmutual but not asymmetric; the two-element order on `Bool`
  (`true` depends on `false`) is in addition transitive and has a distinct edge
  (`separationModels`, result `0ccf914c`). These models show only that the two
  premises differ in meaning on the diagonal. They say nothing about which real
  beings depend on themselves or on each other.
- **Lake-checked lemma** (`distinctNonmutual_iff_distinctEdge_asymmetric`):
  distinct nonmutuality is *exactly* asymmetry of the distinct-step part
  `DistinctEdge D` (reused from the strength module). So the strict reading of
  the asymmetric premise adds nothing over the distinct premise except the
  exclusion of self-edges.

Why reflexivity is a live reading rather than a manufactured objection: the
definition glosses `D(x,y)` as "`x` would not be if `y` were not", including
impossible antecedents, but "in the sense ST I q.44 a.1 ad 2 gives to an
effect's relation to its agent cause". On the bare counterfactual clause, apart
from that qualification, `D(x,x)` is "`x` would not be if `x` were not", an
instance of the counterfactual identity law (if A were the case, A would be the
case). The law holds in any selection semantics whose selected worlds satisfy
the antecedent, impossible-worlds semantics included, so the open question is
which clause `D` is, not whether the law holds. The agent-cause qualification
and its paradigm (light on sun) are strict. So the definition read whole
supports both readings on the diagonal, and neither is built into the Lean
parameter.

### Sense scope: no new TERM_n

| Reading | Self-relation | Existing representation |
|---|---|---|
| (a) non-strict counterfactual existence-requirement | `D(x,x)` holds | `DependsForBeing` plus the OPEN reflexivity statement `56252cd8` |
| (b) strict dependence | `D(x,x)` fails | for the self case only, `DistinctEdge D` (distinct-step part). Interpreted strict *explanatory* dependence is not separately represented: sense 2 of `23dd6f32` is Fine's formal strict ground on uninterpreted atoms, with no metaphysical reading, and the profile's `grounds` is a parameter joined to `D` only by OPEN bridges. No result here needs it |
| (c) modal existence entailment | holds; also transitive | `ModalRequiresExistence` (`d7f66ca4`, #1597). Any necessary `y` is required by every `x` (`modal_requirement_of_necessary`), so co-necessary beings require each other |

The self-relation question needs no new sense. On (a) the strict part is a
*defined* restriction of the same primitive, and the distinct premise is
already exactly its asymmetry. A genuinely *explanatory* strict relation
differs in orientation, not only on the diagonal. It is not separately
represented (the strict-ground sense is uninterpreted, and `grounds` is joined
to `D` only through OPEN bridges), and no result here uses it. (c) is reflexive and transitive but does not orient. No
bridge from `D` to (c) is asserted, and none of these relations is made a
synonym of another.

**Records corrected (paraphrase, note and doc comment only; no Lean type change).** The owning specs `specs/round2-perfection-primacy.toml` and `specs/round2-grounding.toml` carry the new paraphrases, and the doc comment of `DistinctBeingsNotMutuallyDependent` matches.
`STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT` no longer asserts as fact that
`D` holds trivially of a thing and itself. It now says the premise is neutral
on the diagonal. `STMT-DEPENDENCE-FOR-BEING-ASYMMETRIC` now records that it
presupposes the strict reading. `DEF-DEPENDS-FOR-BEING`'s note records the
self-relation fork.

### Order laws, tested separately

Each law is a separate premise, and each result uses only the laws it names:

- **Irreflexive priority** from `STMT-PRIORITY-REQUIRES-NONMUTUAL-DEPENDENCE`
  alone (`priorityIrreflexiveFromRequirement`, result `1ee45a81`). A
  self-priority would need both `D(x,x)` and `¬D(x,x)`. This works on reading
  (a) and on reading (b).
- **Transitive priority** from both OPEN priority bridges plus OPEN
  transitivity of `D` (new statement `09b88101`;
  `priorityTransitiveFromDependence`, result `938bfd7f`). Reflexivity and
  nonmutuality are not used.
- **Strict part** (lake-checked lemmas). Under the two bridges,
  `PriorSimply y x ↔ D(x,y) ∧ ¬D(y,x)` (`priority_iff_strictPart`). With
  reflexivity and distinct nonmutuality, that strict part is exactly
  `x ≠ y ∧ D(x,y)` (`strictPart_iff_distinctEdge`). So if `D` is reflexive,
  transitive and distinct-nonmutual, its inverse is a non-strict partial order
  and priority is its strict part. **This holds only under the two OPEN
  bridges.**
- **Controls** (`orderLawControls`, result `a79850a6`):
  - A reflexive direct-edge chain on `Fin 3` (2→1, 1→0, not 2→0) satisfies
    distinct nonmutuality and both bridges, but neither `D` nor the priority it
    induces is transitive. So transitivity of `D` cannot be dropped.
  - A reflexive, transitive reciprocal pair violates distinct nonmutuality and
    has an empty strict part.

**Transitivity is not granted by fiat.** `09b88101` is an OPEN claim about `D`
as DEF-DEPENDS-FOR-BEING defines it; no closure of `D` is typed or meant, and
all three premises of `938bfd7f` use that one `D`. Challenge: counterfactual
dependence is not transitive in general (Lewis's logic invalidates
counterfactual transitivity, which is why Lewis takes causation as the
ancestral of dependence). Candidate warrant: per se ordered composition, as in
the Second Way's "the first is the cause of the middle and the middle of the
last". If `x` has its being only as received through `y`'s own dependence on
`z`, then `x` depends on `z`. Neither is assessed further here.

### Root connection and #1590

- `STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT` keeps its Lean meaning and its
  availability on **both** readings. It is the self-relation-neutral premise,
  so the nine-input support formula is unaffected by the choice.
  `STMT-DEPENDENCE-FOR-BEING-ASYMMETRIC` is available only on reading (b).
- **Consumer of the asymmetric premise.** `ACTUAL-GROUNDING-ASYMMETRIC-VIA-DEPENDENCE`
  can instead use three premises: `STMT-ACTUAL-GROUNDING-IS-DEPENDENCE`, the
  distinct premise, and irreflexivity of the grounding relation itself
  (`actualGroundingAsymmetricViaDistinct`). This moves the self case from `D`
  to `grounds`. The theorem is Comparator-checked through result `d86e618b`'s
  configuration but **not registered as an argument**. Every new argument
  concluding `STMT-ACTUAL-GROUNDING-ASYMMETRIC` fails the sense-mixing check:
  that conclusion record itself links both `WELL_FOUNDEDNESS_AND_ANTI_BRUTE_ROOT_1`
  (`c86cc1d1`, `GroundAncestor`) and `_2` (`c57e2682`, `ActualRoot`), although
  neither occurs in its Lean type, and its existing arguments are allowlisted.
  Registering the sibling first needs that record's sense links corrected.
- **#1590's first bridge.** `STMT-ACTUAL-DEPENDENCE-IS-GROUNDING` has no
  distinctness condition. On reading (a) it makes every actual concretum ground
  itself (`reflexiveDependenceForcesSelfGrounding`, result `d86e618b`). With
  irreflexive actual grounding, or with `STMT-ACTUAL-GROUNDING-IS-SIMPLE-PRIORITY`
  plus irreflexive priority, that contradicts the existence of any actual
  concretum. The #1590 route `D → grounds → PriorSimply` therefore needs either
  reading (b) or the new distinct-relata sibling `a8298fbd`. That sibling is
  proved from the unrestricted bridge (result `cc7dd608`), and the `strengthens`
  relation records the order. `truth check` now warns that seven existing
  consumers of the unrestricted bridge do not record why they need the strong
  version. Several of them apply it only to distinct relata (for example via
  `EsseEffectDependsOnItsCause`, which has `c ≠ x`), and moving them to the weak
  sibling is a follow-up.

**Computed frontier delta** (`truth frontier-diff --base origin/main`):
- Open premises reaching the root stay at 476 (339 bare).
- `STMT-SIMPLE-PRIORITY-IS-TRANSITIVE` moves from bare to the conclusion of a
  verified argument from open premises. It is not established.
- The new bare transitivity premise `09b88101` takes its place.
- Verified support alternatives gain one (457 → 458 against merge base `692dfa9d`).
- No premise is established.

### Provisional judgment

The conflict was a scope ambiguity, not a refutation of either premise. The
distinct premise is the right shared input on both readings. The unrestricted
asymmetric premise is acceptable only as a strict-reading premise, and its one
root consumer can avoid it by moving the self case to grounding. What would
revise this:
- a semantics for `D` that rejects the counterfactual identity law for
  existence, which would remove the reflexive reading; or
- a consumer that needs irreflexive `D` itself and cannot move the self case
  to its own relation.

## What does a consistent representation add?

Fix the beings, their dependence steps and the labels proposed for their
existence facts. Project each distinct dependence step onto its labels in the
direction from supplier to dependent. On a populated atom type, **some**
consistent theory can realize these requirements exactly when the projected
steps have no finite cycle. The construction starts with just those steps
as strict sequents. Rank each label by the set of labels that reach it,
including itself. Every step strictly enlarges this set: its target belongs
to the later set, and membership in the earlier one would close a cycle.
The existing rank interpretation of PLG then excludes strict self-grounding.
Conversely any projected cycle would derive strict self-grounding in every
theory that realized those steps. [Fixed-label theorem](../../corpus/results/5ebdfbff-f984-43d0-a7d7-ddc19286f39f.json) [Assessment record](../../corpus/attempts/1020b663-7fe1-42d2-8b0c-8a767607a1ce.json)

When distinct-step dependence is acyclic and each bearer in an inhabited
domain supplies its own label, the generated theory derives **exactly** the reversed nonempty finite dependence paths as
strict partial grounds. Thus a successful retrospective fit gives exactly
the structural information already in distinct-step acyclicity. One can also
apply acyclicity directly to P2: two opposite dependence steps form a cycle.
An independently selected theory or an independently defended account of
which facts convey existence could still give evidence for the orientation
of a contested edge. The retrospective construction grants that edge in its
initial sequents. [Identity-label characterization](../../corpus/results/1acba9b6-c43f-46b5-9099-50a1b40230ed.json)
· [Direct support for P2](../../corpus/results/41877473-3868-4cb5-bc90-b44d9ac811a7.json)

**Why the choice of facts matters.** Take two independent pairs of bearers.
In the first pair the supplier is labelled blue and the recipient amber. In
the second the supplier is amber and the recipient blue. No bearer depends on
itself, no path has equal endpoint labels, and the two pairs never interact.
Yet the labels require both blue to strictly ground amber and amber to
strictly ground blue. Even keeping distinct labels on every actual chain
fails to ensure that combining the chains preserves strictness. The checked
example concerns these four bearers and two labels. It supplies a test for
any interpretation which identifies tokens across distinct cases by a shared
description. [Four-bearer control](../../corpus/results/b251e442-4373-4ef8-984d-5f5a9004be2e.json)

### When the labels can support the Second Way

Assume the selected PLG theory is consistent and every distinct dependence
step maps to a derivable strict ground under the supplied fact labels.
Keep this theory and labelling fixed. Two additional things suffice. First,
every per se efficient-cause link must supply the distinct dependence step in the specified respect. Second,
for each effect, there must be only finitely many labels among it and all
its upstream bearers. The set can differ from effect to effect. The number
of bearers sharing a label can be infinite. Strict ground on the finite set
of labels for one effect is transitive and irreflexive. Every upstream step
remains in that set and descends strictly. Induction on its labels now proves
accessibility for the **original cause relation** at this effect. Repeating
the argument for each effect yields the exact Second Way regress premise.
Its other premises still govern the inference to a first efficient cause.
[Formal connection and four premises](../../corpus/results/d09f6268-93bf-4a00-af60-c57fc2353825.json)

There is a concrete standard for what would warrant this kind of reasoning.
In a specified feed-forward logic circuit, the inspected connections and the
function of each gate can assign it a stage and establish that each selected
signal input comes from an earlier stage or a primary input. An output can
depend on many gates at the same stage. The finite stage argument explains
why tracing those **logical signal dependencies** reaches inputs. The presence
of two voltage levels alone would give no such explanation: a pair of
inverting stages can repeat a voltage. Structural evidence about the circuit
supplies the order that a mere count of states lacks. Its architecture
does not tell us how many levels of existential supply lead to a being.

**Provisional judgment.** The infinitist who accepts a consistent strict
interpretation and distinct per se supply at every step must give up finite
ancestral labels wherever a genuinely infinite upstream chain occurs. Along
such a chain recurrence of any one label would give a projected cycle. The
natural-number interpretation above does just what this requires. Its local
explanation by successive suppliers remains coherent. The founded account
can exclude it where a finite inventory of fact levels and strict passage
between them have independent warrant. Ordinary examples of recipient and
giver establish local direction much more readily than they establish such
an inventory. No preference for either account of **unrestricted** existential
supply follows from fitting the labels. Reopen the comparison on an
independently delimited set of existential roles for an effect, with an
argument that every further sustaining supplier belongs to the set and
moves between its roles in the required direction.

## Research attempts citing this note

- [Cluster reassessment of dependence, simple-priority and grounding leaves of the prima via (#1751)](../../corpus/attempts/9d71e28d-d492-4797-9221-45fa517a6e6b.json)

## Testing a supplied PLG theory

Date 2026-11-26. This test fixes the exact assumption set `S`, the bearer
relation `D` and the fact labelling. The existing representation result chooses
a theory to fit the projected dependence steps. The new results can inspect an
independently supplied theory without replacing any of its assumptions.
[Formal attempt](../../corpus/attempts/59b796b6-d240-43f1-b8c2-25c79e8a07b7.json)

Read a full sequent as contributing an arrow from **each** antecedent to its
consequent for this test. A partial sequent contributes its one arrow. Arrows
from strict sequents count as both strict and weak. An empty full antecedent
contributes no arrow. The two tests are:

1. **Consistency on a populated atom type.** No strict arrow may have a finite
   return path using arrows of any kind. A return of length zero counts. An
   all-weak cycle does not violate this test. For each atom, its rank is the set
   of atoms reaching it by zero or more weak steps. All members of `S` satisfy
   the rank interpretation: weak steps preserve inclusion and strict steps
   increase it properly because the target cannot reach back. Rank soundness
   covers every encoded PLG rule, so any strict self-sequent is underivable.
   A strict arrow with a return instead derives a strict self-sequent and
   hence every sequent. [Consistency criterion](../../corpus/results/00f2cd7c-c0a7-4eef-b57a-e59bde59b204.json)
2. **Dependence map.** Each distinct `D(x,y)` must have a finite path from
   `label(y)` to `label(x)` with at least one strict step. The path suffices
   by the PLG subsumption and transitivity rules. Consistency makes the
   condition necessary too: induction on derivations tracks which initial
   paths reach the consequent from each antecedent. Cut composes weak paths,
   reverse subsumption requires strict paths for each antecedent, and
   consistency rules out using explosion. [Strict derivability criterion](../../corpus/results/006f49e8-4c68-424d-9403-9f025185b555.json)

The consistency argument records population as a separate premise. An empty atom
type satisfies the no-return condition vacuously but has no sequent to witness
consistency. On the stated domain, the two tests give support options for `fea5942a` and `42756c07` in
the nonmutuality and Second Way consumers. On the same fixed `S`, the map
orients every distinct step, consistency excludes strict self-grounding,
and PLG composes successive strict grounds transitively. This need not make
`D` itself transitive: the target can derive composite grounds even if
`D` records only direct steps. The existing natural-number witness shows
that an infinite descent can satisfy the two conditions. On the diagonal,
mapping a self-dependence step would demand a strict self-sequent and
contradict consistency. The four-bearer control above shows why keeping
distinct labels on individual paths still allows collisions across paths.
[Consistency support](../../corpus/results/ac062be2-1f2b-4481-8f91-852dcdd33bb7.json)
· [Map support](../../corpus/results/945d3606-d6ac-4e5e-a9fd-d95d1dd508e1.json)

The two-label control holds `D(true,false)` and identity labelling fixed.
With just the weak full sequent `{false} ≤ true`, the theory is consistent
but cannot map that edge. With just `{false} < true` it is consistent and
does map the edge. Adding `{true} ≤ false` preserves the map and makes the
theory inconsistent. The third case cannot be detected by looking for cycles
among strict assumptions alone. These are results about the stated formal
presentations. [Boolean control](../../corpus/results/1ea2f628-a121-4e37-a21c-5f4af77f0321.json)

### Warrant at matching scope

For the same proposed supplier and effect in one respect, ask what explains
why the effect exists there and whether the supply runs in one direction.
The case for a strict reading is strongest when the effect's very existence
can be traced to the supplier's operation and the same account of the
supplier's existence does not refer back to the effect. The observed
light-supply example gives a local reason to look for an oriented relation.
This reason does not select constitutive grounding, a global theory of
existence facts, or a bound on its ancestry.

- **Modal existence requirement.** The positive account is preservation
  of the implication from the existence of the dependent to that of the
  required being across the selected worlds. The existing
  `ModalRequiresExistence` lemma shows that a necessary being is required
  by any bearer in that sense. Two distinct necessary bearers therefore
  require one another while strict PLG in a consistent theory cannot map
  the pair both ways. This challenges the map when the sole warrant for
  a strict step is modal co-instantiation. It leaves efficient-causal
  `D` distinct: using the result against that `D` would require a reason
  to identify the causal reading with the purely modal one. Modal
  implication captures constraints on co-existence and supplies no
  directional account of actual production in the light case.
- **Causal explanation without constitutive grounding.** In a sustaining
  illumination case, tracing the emitter's operation and the resulting
  light explains why that light is present. The supplier's existence
  by itself does not suffice for that causal account: the operation
  matters. A local grounding skeptic can accept this directional causal
  account and reject the claim that there is in addition a constitutive
  ground between bare existence facts. This targets the interpretation
  of the strict paths and their labels, even if the causal direction and
  the syntax are granted. It leaves open whether an interpretation in
  causal supply is adequate for the selected class of existence facts.
  The local account gives no explanation of why there is an entire
  upstream series of suppliers.

**Provisional assessment.** The exact test separates an omission of an
orientation in `S` from an incompatible combination of assumptions in
`S`. A separately motivated strict presentation could add support to
particular dependence edges. A presentation containing those edges by
construction transfers the burden to the input orientation and its warrant.
The repository has supplied examples of particular theories, but the root
argument takes an arbitrary `S` and no independently specified existence-fact
presentation is bound there. Both original claims remain available as direct
options. Apply the tests next to a specified effect and a theory whose fact
labels and assumptions are justified independently of the target dependence
edge, including any weak sequents that could return from the effect. A path
supported by actual same-respect supply would favor the causal reading.
Evidence for constitutive explanation at that same scope could change the
assessment of the stronger reading.

### Adjacent premises in the triage cluster

[Cluster attempt](../../corpus/attempts/473bd726-59d1-495f-9178-8efb6f33da8b.json)

| Premise | Finding and remaining condition |
|---|---|
| `adb951c1` | Per se alignment needs distinct endpoints and evidence that the effect's *being* depends on this supplier. The hand can move the stick through a per se instrumental series while the stick continues to exist when it is released. A reading restricted to per se causes of esse avoids that example, with alignment still to be supplied on that narrower relation. |
| `f10d5632` | Selecting the history relation to be the per se relation makes inclusion reflexive. Evidence of finite distinct ancestry and absence of loops must then concern that same selected history. An independently selected history needs a same-carrier inclusion check. |
| `2e248016` | The direction from world-local dependence to actual-concrete grounding requires a reason to export `D` to the profile's selected relation. The unrestricted statement also maps `D(x,x)`; with actual grounding irreflexive it excludes reflexive `D` on a populated actual-concrete domain. The existing distinct sibling `a8298fbd` avoids that diagonal commitment. |
| `0f5b53ef` | A quality-level explanation challenges the converse export only if the profile admits bearer-to-bearer grounding edges on that basis. For a profile restricted to existential grounds, the question is whether those grounds entail the selected dependence-for-being counterfactual. |
| `7a63a3fe` | The priority bridge targets the profile's world-local ground and `PRIOR_1`. A strict order on PLG labels yields no such bridge. The required calibration is actual grounding to priority in act in the relevant respect on the same bearers. |
| `2047d14b` | Self-grounding is excluded on a strict explanatory reading. In the world-local profile, any transfer from PLG would still need an explicit ground-to-PLG bridge **on the diagonal**, which the distinct map never supplies. The existing reflexive-requirement controls locate the competing reading. |

## Negation tests on the same labelled edge (2026-11-26)

Fix the supplier, recipient, their labels, and the entire assumption set before
asking what the dependence edge explains. The two branches of the per se route
use these inputs differently. Argument `4bd8457a` uses population and absence
of a strict return for consistency. Argument `ea09d50b` uses path coverage to
derive the map. The nonmutuality result requires consistency and the map on
the same presentation. These two arguments supply one way to obtain those
inputs; either input can also be assumed directly. The following judgments concern the baseline of PR #2025 and the
[compiled negation tests](../../TruthCore/Models/SelectedPlgNegations.lean).

**Population (`d1c47547`).** Strongly warranted in any application that
supplies both a bearer in the labelling domain and a total label function;
missing either input removes this proof of population and leaves it open. Applying the very same total label function to
that bearer supplies the atom (`populatedAtBearer`). A skeptic about reifying
existence facts can grant this mathematical witness and dispute its
interpretation. The strongest literal denial is an empty language.
`emptyPresentation` takes both carriers empty. Every path obligation and the
no-return condition hold, but there is no sequent at all to witness PLG
consistency. An empty target with a total labelling cannot retain the observed
bearer. No substantive objection to population survives those two inputs.
Reopen if the alleged witness and labelling belong to different domains or the
application has yet to exhibit a bearer.

**No strict return (`2bdf810f`).** Favor this condition for presentations of
one-way supply whose weak steps all preserve the same order. A strict step
then increases rank, so the reverse weak path cannot restore its starting
rank. A rival can instead preserve reciprocal constraints, for example the
co-existence requirements of two necessary bearers. Reciprocally weak edges
alone are compatible with the test. An infinite strict descent alone is also
compatible, as the earlier natural-number model shows. Denial requires a
strict step *and* a finite weak return. Keeping one direction strict while
admitting the return makes every sequent derivable in this calculus. That is
a specific conflict with the route's consistency premise. The positive
interdependence alternative (Thompson on holistic explanation; Bliss on
circles and regress) holds that some reciprocal links do constitutive
explanatory work. It challenges `42756c07` if both links belong to the
selected `D`; if both are represented in PLG with at least one strict
direction, the return violates `2bdf810f`. Acyclic infinite descent is a
separate alternative: it leaves `2bdf810f` intact and bears on a downstream
termination premise. Neither alternative supplies an example of the same
illumination effect sustaining its own supplier. For the unspecified root presentation the judgment
remains conditional. Inspect weak links as well as strict ones, or supply a
rank independently warranted for every initial sequent.

**Path coverage (`b6784d40`).** On a consistent presentation the exact price
of denying coverage is one distinct dependent and supplier with no strict-step
path in the required direction. The corresponding strict sequent is
underivable (`missingMapIffUncovered`). The prior weak-only control realizes
that denial while retaining the dependence edge. A causal investigator can
have a positive reason for precisely such restraint: the emitter's operation
explains the presence of light, while the proposed labels record just their
existences. Omitting a strict step is defensible when the evidence supports
the operation and the chosen presentation records no rule transferring it to
those facts. This favors withholding unrestricted coverage. It gives no
reason to deny a path whose initial steps already have that warrant. Reassess
on an independently specified presentation, checking each strict step and
both endpoint interpretations.

**Parent map (`42756c07`).** The directed supply in the illumination case
supports trying an oriented causal reading. The same evidence fits a local
account in terms of emission and reception (Wilson-style specific dependence
relations): emission and reception explain the specified light's presence
while the emitter operates, which supports withholding the export from causal
supply to a constitutive relation between bare existence facts, while leaving
formal path coverage and partial constitutive ground open. Such an account owes an explanation
of how the effect is sustained, but owes a *constitutive* ground only if there
is a further reason that this particular existence fact has one. Pointing out
that emission requires operation does not refute strict *partial* ground:
the proposed supplier fact need not suffice on its own. The current evidence
underdetermines that stronger interpretation. The Fine-style alternative
holds that source-indexed essence can distinguish directions that necessary
co-presence leaves symmetric. In the existing `directedNature` profile, modal
co-existence is mutual even though the essence assignment is directional; the
essence assignment is stipulated and the causal relation is empty, so the
theorem tests the modal relation alone. `modalControlExcludesMap` excludes the strict map
on that modal relation for **every** labelling and consistent presentation.
This rules out mere modal requirement as a general warrant. Applying that
result against the selected efficient-causal relation would require an
identification that the illumination case does not provide.

There is a second diagnostic for the parent. Keep the earlier Boolean edge
and identity labels and supply just a strict self-step at the supplier.
`loopMasksMissingPath` proves that the map holds while coverage and consistency
both fail. Every initial step stays at the supplier, yet explosion derives
the sequent about the recipient. Thus a successful derivation alone cannot
serve as the discriminating evidence. Reassess the parent on an independently
motivated consistent theory that explains why the supplier's *existence fact*
partly grounds the recipient's, at the very respect and time for which the
causal explanation is offered: once the supplier's operation, the time and the
respect are fixed, what explanatory contribution does the supplier's
*existence* still make? Until then the two bridges remain direct
assumption options. Neither the modal control nor the cyclic presentation
undermines a prerequisite of inquiry. Their conflicts are with identifiable
route commitments under the specified readings.
