# Cross-family interfaces: proof reuse and semantic boundaries

Continuation of [#1926](https://github.com/moritzbrantner/formal-logos/issues/1926), especially phases 1–2 and the owner-approved hybrid schema policy (2026-11-24). Evidence baseline: main `93e7ee882fba969b62df982486a1b8ec36217c57`. This is a selected declaration-level survey, not a complete inventory, a new tracker, or a verified theorem batch. The parent issue owns allocation and current handoff. Reuse [the prior schema machinery](../schemas.md), [restated premises](restated-premises.md) and [orphan graft map](orphan-graft-map.md); do not repeat their work.

Two proof bodies now have shared implementations. Five adapters reuse the fixed-point selection lemmas and five reuse the information-invariance lemmas. The independent review at `679faab15526c2ae89e3e432d3580b205691a0ac` compared the axiom footprints of 93 existing declarations on the base and the delivered sources. Each matched. The five new helpers are axiom-free. The frozen Challenges and registered conclusions retain their original hypotheses and senses. Sections describing proposals and local tool limitations record the stages before this verification. [Binding and premise comparison](https://github.com/moritzbrantner/formal-logos/actions/runs/45654738164/job/139348412985) · [Comparator and NanoDa verification](https://github.com/moritzbrantner/formal-logos/actions/runs/45654738164)

## 1. Information equivalence and discrimination

| Existing declaration | Structural role |
| --- | --- |
| `TruthCore/Logic/CorrectionCriterion.lean`: `FiberInvariant`, `AdmitsCriterion` | Equal observations imply equal correctness; exact classification iff fiber invariance. |
| `TruthCore/Explanation/HistorySelection.lean`: `SameEvidence`, `EvidenceOnly`, `Determines` | Agreement on an entire reason vector; informational dependence of a proposition; selection of the supplied complete presence history. |
| `TruthCore/Epistemology/InitialHistoryAuthenticity.lean`: `PositiveUniform`, `PositiveWitnesses`, `PositiveFibersTrue` | Restrict to admitted inputs and positive observations; uniform authenticity is not necessarily true authenticity. |
| `TruthCore/Logic/DarwinianEpistemicDebunking/BasisDefeat.lean`: `TruthSupervenesOn`, `VerdictStableOn` | Equal factor values imply equal correctness or verdict. |
| `TruthCore/Logic/ForeknowledgeDiscrimination.lean`: `TruthClass`, `Supervenes`, `Complete` | Agreement on selected contents; equality of intrinsic projections determines epistemic accessibility rows; completeness requires discrimination. |
| `TruthCore/Epistemology/FitnessTruthBoundary.lean`: `Successful`, `Truthful`, `Certificate` | Same successful behavior with opposite truth profiles; behavioral score cannot distinguish them. |

Candidate kernel: for data projection `observe : S → O` and predicate `P : S → Prop`, constancy on equal-observation fibers is equivalent to existence of a predicate on O representing P. For an equivalence relation rather than an observation function, express constancy directly or use an explicit quotient adapter only if compatible with the axiom policy. Restrict using an admitted-state subtype; do not silently enlarge domains. Reuse existing CorrectionCriterion proofs and Mathlib's function factorization where appropriate; a core-only lemma must not inherit Mathlib merely to reuse a convenience theorem.

A second reusable proof: on an admitted positive fiber, uniformity plus one authentic member yields authenticity of every member. Uniform falsity separates uniformity from soundness. No implication from extensional representation to computability, epistemic entitlement, probability, ontological identity or adequate metaphysical explanation.

Targets: F6 `f56b2ee7`, reliable inquiry, and contrastive adequacy against the brute-foundation and impersonal-source rivals. Missing application: actual inquiry or the full selected explanatory base must really preserve the specified information and admit the compared alternatives. Existing history selection does not itself justify metaphysical accessibility or the demand for entailing explanations.

## 2. Symmetry / fixed-point selection

| Existing declaration | Structural role |
| --- | --- |
| `TruthCore/Science/InductionSelection.lean`: `Equivariant`, `NoUniqueSelector`, `SymmetryConstraint` | Fixed evidence cannot have a moved unique hypothesis under neutral selection. |
| `TruthCore/Mereology/Fission1397.lean`: `Equivariant`, `no_choice` | Symmetric continuations cannot be deterministically selected under an output swap. |
| `TruthCore/Space/TranslationBoundary.lean`: `Covariant` | Relative displacements are unchanged by common translation; absolute output would have to translate. |
| `TruthCore/Explanation/PathRelocation.lean`: `InvariantUnder`, `UniqueSolution` | A transformation preserving the solution condition fixes its unique solution. |

The point-selector equation is `select (transform e) = move (select e)`. If `transform e = e`, the output is fixed. The relational form assumes closure of the accepted set under a transformation and a unique member; the unique member is fixed. These two forms are constructive, need no full group theory, and can be instantiated using permutations or arbitrary endomorphisms. The existing domain-specific notions remain unchanged.

Controls: an equivariant selector can return a fixed output; a set-valued response can return the whole orbit; an asymmetric input can distinguish the choices; a non-neutral selector can select one. A deterministic selector is not a law of all rational agency. A stochastic distribution may be symmetric even if a sampled outcome is not; no probabilistic or modal inference follows from the point-selector theorem.

Targets: `0266eac2` (WN), `66aecdd7` (will), contingent whole-order selection. The invariant nature of a necessary source is not yet the stronger claim that its entire productive setup is fixed under a transformation of alternatives, nor that the action is equivariant or single-valued. Preserve the chance and nonnecessitating impersonal rivals from [will versus chance](will-versus-chance.md). A symmetry obstruction can eliminate a specific deterministic mechanism; it cannot by itself distinguish personal from impersonal production.

## 3. Local versus uniform witnesses

The core contrast is `∀ i, scope i → ∃ x, R i x` versus `∃ x, ∀ i, scope i → R i x`.

- `TruthCore/Explanation/DisjunctionGround.lean`: `LocallyGrounded` and `UniformGround`.
- `TruthCore/Explanation/TruthmakerTheories.lean`: `LocalMaker` and `UniformMaker`.
- `TruthCore/Explanation/ExplanatoryAdequacy.lean`: `ContrastRelevant` and `UniformContrast` (also per explanandum).
- `TruthCore/Logic/QuantifierShift.lean`: `EachSometimeNotEntailsSometimeNothing` (transpose the witness roles).

The uniform form implies the pointwise form without classical choice. A common witness requires additional information: e.g. an inhabited scope, an anchor witness and transport of that witness to every admitted index. Pointwise uniqueness alone does not provide transport; the two-point diagonal relation has unique local witnesses but no common one. An empty index scope can satisfy the local form without any witness in an empty witness carrier.

Targets: the common-root interface `dc397705`, joint absence, worldwise necessary existence. Do not conflate a common ground, a rigid name, a common bearer and a necessarily present bearer. A common witness for a selected relation does not prove there is exactly one ultimate source.

## 4. Coverage, endpoint soundness and modal transmission

| Existing family | Existing ingredients |
| --- | --- |
| `TruthCore/Explanation/PSRStrength.lean` | `FactPSR`, `ContingentPSR`, `ExistencePSR`, `Factive`, `Necessitating` |
| `TruthCore/Explanation/BCCFDerivative.lean` | `CoveredOn`, `PFactive`, `PNecessitating`, `PContrast`, `PDistribution` |
| `TruthCore/Explanation/TruthmakerTheories.lean` | `Covers`, `TruthSound`, `WorldImmanent`, `MakerNecessitation` |
| `TruthCore/Epistemology/SourceEvidenceAdequacy.lean` | `Covered`, `RealizesPlans`, `AssertoricPlans`, transmission conditions |

A scoped coverage premise gives a witness for each target in its scope. Endpoint soundness says the selected witness relation implies separately supplied source and target predicates. Composition requires explicit intermediate identity; coverage alone does not guarantee truth. Actual soundness, cross-world sufficiency and reason-giving are separate obligations.

Test singleton reasons as a special case of plural reasons only through an explicit mapping; an arbitrary plural relation is not determined by its singleton fragment. Test modal transmission under the same accessibility relation and the same witness, not merely a similar name. Targets: existential PSR `608a262d`, explanatory completeness, and truthful evidence. Reuse `PSRStrength.Arena` rather than adding another semantic authority.

## 5. Performed occurrence and realization

- `TruthCore/Logic/SelfApplication.lean`: `Norm.selfApplication`, restriction and demarcation already supply reusable scope/acceptance machinery.
- `TruthCore/Logic/PerformedDenial.lean`: `AccuratePerformedDenial`.
- `TruthCore/Logic/AssertionRetorsion.lean`: `AssertionRealized`, `AssertionRealizationsExperienced`, `OccurringThoughtIsRepresentedAsExisting`.
- `TruthCore/Causality/Round3CogitoBase.lean`: `PerformedDoubtIsThought`, `PerformedDoubtOfThoughtSelfRefuting`.
- `TruthCore/Logic/KnowledgeRetorsion.lean`: `FactiveKnowledge`.
- `TruthCore/Logic/EpistemicReasons.lean`: `NihilismSelfUndermining`.

A performed token, together with a faithful realization bridge, witnesses an inhabited predicate extension. Negating that extension contradicts the witness. This is separate from a norm that fails its own acceptance standard; neither entails the existence of an actual performance from the mere description of a denial. Keep assertion, knowledge, sincerity, cognitive significance, phenomenal experience, epistemic reasons and truth distinct. An assertion of nihilism does not by itself establish that the assertion is warranted.

Targets: F1 `c425f0c5`, F6 `f56b2ee7`, observation/Cogito `fbc516c1`, `b45ca9db`, `1edfc1d1`. Reconcile #509, #515, #1007, #1989 and draft #1993; #1960 explicitly retained distinct occurrence premises. The common kernel is not an equivalence between the occurrence predicates.

## 6. Stable observation under intervention

- `TruthCore/Science/AdaptiveHistoryAccess.lean`: `Experiment`, `StableMatching`, `AdaptiveAgreement`.
- `TruthCore/Mereology/ArrangementDynamics.lean`: `Preserves` (Mathlib `Function.FactorsThrough`), `Realizes` (semiconjugacy), `run`.

The first compares two systems using a stable relation, including equal readout and related successors under every admitted action. The second is a functional coarse-graining instance: macro transitions commute with observation. The common induction preserves matching across a finite intervention trace. Equal transcript-dependent policies then choose the same next action. Preserve identical starting transcripts and the action alphabet, and do not extend finite deterministic histories to arbitrary stochastic or infinite runs.

Targets: authenticity of records, empirical underdetermination and reduction. The current blind/reveal historical controls and flip-left coarse-graining omission distinguish hidden differences from stable observational agreement. Observational equivalence does not entail ontological identity.

## Integration and verification

Use one small maintenance slice at a time; this note covers several independent candidate families, not a mandate to place every abstraction in one Lean module. Start with symmetry and information, then local/uniform witnesses, coverage, occurrence and interventions. Look for exact existing proof applications before adding a lemma. Do not build a generic framework where a Lean core or Mathlib theorem suffices. Register only real schema instances using `instance_of_schema` with checked instance and schema obligations as in [schemas](../schemas.md); do not create a parallel relation registry. Preserve the separate graph records and direct-assumption options.

Before implementation, in a prepared clone: use `truth related`, `context`, `dossier`, `semantics`, `brief` and `novelty` for exact statement IDs; use the issue brief and current PRs to avoid overlap; inspect existing Solutions and frozen Challenges; establish the minimal proof signature and axiom baseline. For changed proofs run the affected build, `truth check`, `truth bind-check --affected --base <merge-base>`, affected `scripts/verify-result.sh <RESULT-ID>`, Comparator/NanoDa and `truth frontier-diff --base <merge-base>`. Run the bundle audit if modifying argument bundles or pinned definitions. No premise change is intended for pure factoring; report computed comparison and exact affected result identities. Consequential graph bridges remain separate research work subject to independent semantic challenge.

This checkpoint uses GitHub read/write access only: no prepared clone or Lean/Rust verification tools are available in the current environment. The local retrieval and proof verification commands above have not run. The exact proof-body reuse, consumer reachability and novelty of candidate mathematical lemmas remain to be checked. Do not treat this note as certification.

## 7. Second checkpoint: concrete proof-body migration candidates

Inspection of the existing Solutions narrows the survey. The following is not a claim that the listed kernels are novel; check Lean core, Mathlib and the existing schema modules before naming another theorem. The snippets are **uncompiled candidate proof terms**, not registered consequences.

### 7.1 Fixed points: smallest useful vertical slice

The proof body of `TruthCore.Results.Science.InductionSelection.noUnique` is exactly the equality
`(hn e).symm.trans (congrArg select hf)`. In `TruthCore.Mereology.Fission1397.no_choice`, the equality is oriented the other way:
`(congrArg choose fixed).symm.trans (equiv d)`; its remaining proof is the case split over the admissible two alternatives. Neither proof needs invertibility. In `TruthCore.Results.Explanation.PathRelocation.symmetry_transfer`, uniqueness is applied to the transformed satisfying path. This is the set-valued form of the fixed-point constraint. The spatial proof `no_covariant_selector` first rewrites by `relative_shift`, then uses `fixed_iff`; it needs a body to exclude an empty absolute configuration.

Proposed two local lemmas if equivalent existing ones are not available:

```lean
theorem fixed_output {E H : Sort _} (s : E → H)
    (t : E → E) (u : H → H) (e : E)
    (fixed : t e = e) (commutes : s (t e) = u (s e)) :
    u (s e) = s e :=
  commutes.symm.trans (congrArg s fixed)

theorem unique_closed_fixed {H : Sort _} (P : H → Prop)
    (u : H → H) (h : H) (member : P h)
    (unique : ∀ x, P x → x = h) (closed : ∀ x, P x → P (u x)) :
    u h = h :=
  unique (u h) (closed h member)
```

| Existing proof to retain | Result ID and migration action |
| --- | --- |
| `InductionSelection.noUnique`, `symmetry` | `6cf4fc73-3265-5712-a0aa-c30a8cb3c299`; retain the recoding and neutrality premises; replace only the fixed-point step. |
| `Fission1397.no_choice` | `d03376f9-9c91-4dc4-b529-62039d7c1fc4`; retain admissibility, swap and distinctness; use fixed-output equality before cases. |
| `PathRelocation.symmetry_transfer` | `aaeed827-7dd7-5dc9-a199-52f68f131b74`; instantiate the closed-unique lemma with path precomposition. Preserve the time and arithmetic proof in its original module. |
| `TranslationBoundary.no_covariant_selector` | `4e27fddd-212c-5c09-a2df-c05f4e740340`; fixed-input rewrite and no-fixed-point argument, with the existing inhabitedness control. |

This small migration would demonstrate exact proof-body reuse, not introduce a universal selection profile or a new notion of symmetry. The mathematics is independent of whether a person, mechanism or law implements the selector. In particular, a unique result at the level of a **distribution** is not a unique realized outcome. For the impersonal-source investigation the precise next test is a fixed total determining setup, a substantive transformation of feasible outputs, and either an explicit covariance premise or a defended sufficient-reason standard implying it. Without these, the root-route application remains OPEN. Retain an asymmetric impersonal ranking and an invariant stochastic generator as separate cases.

### 7.2 Information: reuse the existing connections first

The audit initially treated several families as independent, but they already have meaningful reuse:

- `TruthCore.Results.Science.AdaptiveHistoryAccess.historyControls` invokes `TruthCore.Results.Logic.CorrectionCriterion.characterization.1` directly with the transcript as observation and `PastOccurred` as the predicate. Keep that connection; the general `adaptiveAgreement` result is `83edc309-1c34-402d-9394-4d095218244a`.
- `TruthCore.Results.Epistemology.InitialHistoryAuthenticity.observation_evidence` proves equality of observation iff `HistorySelection.SameEvidence` on equality tests. Its `evidenceOnly_iff_uniform` already restricts to admitted inputs with a subtype and uses this lemma. Do not replace it with an invented second evidence relation. `sound_iff_uniform_witnesses` supplies the separate authenticity witness per inhabited positive fiber.
- `HistorySelection.characterization` constructs the predicate `fun w => SameEvidence truth basis w a` and proves constancy by reflexivity, symmetry and transitivity. Its `no_selection` is a direct use of that characterization. Result `4b8f07db-2a50-5826-ac09-083f0e088d64`.
- `ForeknowledgeDiscrimination.core` uses selected truth agreement and factivity, not unrestricted knowledge. Result `067b5373-8169-42a6-8f80-cf7874761eb9`. Retain reflexivity when using agreement of epistemic rows; an empty accessibility row is complete in the thin semantics without providing factivity.

The genuinely additional reuse target is the passage between equivalence-invariant predicates and exact determination for different projections, not another proof of the already-shared historical criterion. Prefer a proposition-valued construction (avoids demanding function extensionality or propositional extensionality to encode an entire truth vector as an equality). One useful constructive adapter signature is:

```lean
theorem matched_data_no_exact_classifier {S O : Sort _}
    (observe : S → O) (P : S → Prop) (s t : S)
    (same : observe s = observe t) (hs : P s) (ht : ¬ P t) :
    ¬ ∃ C : O → Prop, ∀ x, C (observe x) ↔ P x := by
  rintro ⟨C, exactC⟩
  exact ht ((exactC t).mp (same ▸ (exactC s).mpr hs))
```

This is a consequence of the already-proved CorrectionCriterion characterization; use that theorem if its carrier and axiom boundaries fit, rather than registering this as a new philosophical result. The pure algebraic statement works with supplied equality and truth at the two states. The fact that a target is not determined by an observation alone does not prove the target unknowable given further evidence.

### 7.3 Stable dynamics: relational matching versus coarse-graining

`TruthCore.Results.Mereology.ArrangementDynamics.realization_iff` uses Mathlib's `Function.extend` to build a macro transition from `Function.FactorsThrough`. Its `histories` proves semiconjugacy along a finite word by list induction. `AdaptiveHistoryAccess.runAgreement` uses Nat induction with a shared policy, equal transcript, and matching successor states. These are related but not identical: the latter permits distinct state carriers and a general relation, and must additionally preserve observations and equal transcript-dependent actions.

A safe adapter relates a micro-state `s` to a macro-state `m` exactly when `observe s = m`; each macro step agrees by the existing semiconjugacy hypothesis. If the macro readout is the identity, the resulting experiment matches the micro experiment's readout. Apply the existing adaptive theorem, rather than add a duplicate induction. Whether this gives an already-registered or useful new graph instance is not yet checked. No use of macro dynamics in the ontology follows merely from observational simulation. Preserve the current finite-history, deterministic-transition scope.

## 8. Additional patterns found during Solution inspection

### 8.1 Modal transmission and transport of failures

`TruthCore.Results.Explanation.PSRStrength.necessitating_reason_contingent` takes an actual true reason, a contingent fact and a necessitation bridge; its proof carries the fact's accessible failure world back to failure of the reason. `bccf_contingent` uses the same move with the aggregate-to-conjunct bridge. `TruthCore.Results.Modal.SimplicityCollapse.rigid_core` takes the same act at every accessible world and strict efficacy, and uses the same contrapositive to exclude a contingent selected effect. The existing modal K-closure work in #1926 is the natural place to reuse this, not a new modality.

Local schematic implication (uncompiled, constructive):

```lean
theorem failure_transport {W : Sort _} (R : W → W → Prop)
    (a : W) (P Q : W → Prop)
    (bridge : ∀ v, R a v → P v → Q v)
    (actualP : P a) (failure : ∃ v, R a v ∧ ¬ Q v) :
    P a ∧ ∃ v, R a v ∧ ¬ P v := by
  obtain ⟨v, hv, hn⟩ := failure
  exact ⟨actualP, v, hv, fun hp => hn (bridge v hv hp)⟩
```

This isolates the modal failure witness without introducing excluded middle or a reflexivity assumption. The forward necessity theorem needs the same accessible domain and implication at each accessible world; it is not enough that the reason happens to explain the actual fact. For `holder_necessary` in HolderRootIdentification, the move from not-contingent to necessary uses an explicit excluded-middle input and actual existence; do not erase that dependency. The source's necessary existence is also not the necessary performance of its particular act.

Candidate applications: PSR-collapse, source-to-effect necessity, aggregate contingency, truthmaker necessitation and joint-absence holder identification. Coordinate existing #1941/#1942/#1947 and the necessary-source investigation; the common theorem transfers no philosophical warrant between their bridge premises.

### 8.2 Same-witness property transfer and root-role inclusion

The current `TruthCore.Results.Causality.HolderRootIdentification` contains an exact repeated proof family: `holdersHaveIntellectFromCommonRoot` and `holdersAreGodFromCommonRoot` extract the identical root witness, rewrite with `root_eq_commonRoot`, then apply its respective predicate. `atMostOneHolderFromAtMostOneRoot` uses predicate inclusion; `godHasWillFromWilledHolder` transfers will across equality derived from uniqueness.

The following two proof shapes are candidates for reuse (prefer an existing lemma or direct equality elimination when shorter):

- If every H-bearer is an R-bearer and R is at-most-one, H is at-most-one. This requires **no existence**; keep it separate from unique existence.
- If a selected witness `n` has property `P` and every H-bearer is equal to `n`, then every H-bearer has `P`. Nothing follows about existence of an H-bearer. If `P` is one element of a conjunction, all projections still refer to the same witness.

Candidate next migration: abstract just the repeated role-to-selected-root step if it reduces real repetition. Compare `TruthCore.Logic.Strength.UniqueExistence.AtMostOne` and `ExactDelta` for already-registered uniqueness machinery; reuse #1926's common-root interface and phase-3 uniqueness work. Preserve the existing `root_eq_commonRoot` proof's **direct** actual concrete ground relation. A transitive-ancestry version requires a separate premise. A root is not identified by being necessary or having one attribute. In particular, existence of an intellect-bearing source and a will-bearing source does not establish one source with both properties without a common-witness premise.

These patterns are close to the user's current intellect/will investigation, but should not generate a fresh God-identification route merely by abstracting predicates. New sense-specific instances must bind to existing root-role claims with explicit application evidence.

## 9. Executed finite diagnostic controls

A local Python standard-library enumeration was run during this survey. It checks the small mathematical profiles only, independently of Lean and the corpus. It does not certify the candidate proof terms or prove any actual-world application.

```python
from itertools import product
B = (0, 1)
maps = list(product(B, repeat=2))
n = 0
for tr, mv, sel, e in product(maps, maps, maps, B):
    if tr[e] == e and sel[tr[e]] == mv[sel[e]]:
        assert mv[sel[e]] == sel[e]
        n += 1
assert n == 32
n = 0
for mv, p, h in product(maps, maps, B):
    if (p[h] and all(not p[x] or x == h for x in B)
            and all(not p[x] or p[mv[x]] for x in B)):
        assert mv[h] == h
        n += 1
assert n == 4
bad = 0
for obs, p in product(maps, maps):
    invariant = all(obs[s] != obs[t] or p[s] == p[t]
                    for s, t in product(B, repeat=2))
    factors = any(all(c[obs[s]] == p[s] for s in B) for c in maps)
    assert invariant == factors
    bad += not invariant
assert bad == 4  # of 16 profiles
gap = 0
for r in product(B, repeat=4):
    R = lambda i, x: r[2*i+x]
    local = all(any(R(i, x) for x in B) for i in B)
    uniform = any(all(R(i, x) for i in B) for x in B)
    assert not uniform or local
    gap += local and not uniform
assert gap == 2  # of 16 relations: diagonal and antidiagonal
n = 0
for allowed, obs, pos, truth in product(maps, maps, maps,
                                        product(B, repeat=4)):
    I = [i for i in B if allowed[i] and pos[obs[i]]]
    holds = lambda i: bool(truth[2*obs[i]+i])
    sound = all(holds(i) for i in I)
    uniform = all(obs[i] != obs[j] or holds(i) == holds(j)
                  for i, j in product(I, repeat=2))
    witnesses = all(any(obs[i] == obs[j] and holds(j) for j in I) for i in I)
    assert sound == (uniform and witnesses)
    n += 1
assert n == 1024  # includes empty scopes; vacuity explicitly retained
gap = 0
for a, b in product(maps, maps):
    factive = a[0] and b[0]
    sufficient = all(not a[v] or b[v] for v in B)
    if all(a) and sufficient:
        assert all(b)
    gap += factive and not sufficient
assert gap == 1  # actual factivity alone permits failure of modal sufficiency
```

The actual run reported 32 fixed-selector antecedent instances, four closed-unique instances, 16 factorization profiles (four failures of factorability), 16 witness relations (two local-without-uniform cases), 1,024 restricted positive-fiber profiles, and one case of actual factivity without modal sufficiency. The finite witness and factorization failures are not philosophical counterexamples to the existence of a necessary source; they discriminate the proposed logical transitions. No broader closure computation has run.

## 10. Handoff for first implementation

Prioritize the precise §7.1 migration as a small independent maintenance slice if the novelty/context checks confirm it is not already covered. Use the existing four result IDs as inputs to `truth context`, inspect their frozen Challenges and Comparator configurations, and record the baseline axiom lists before moving proof bodies. Keep domain-specific lemmas and imports where they own genuine application work. The second slice should reuse the already-existing historical evidence adapter and target the outstanding relational/functional invariance boundary in §7.2–7.3. The modal and witness patterns in §8 should be handled through the corresponding existing #1926 work rather than duplicate it.

The draft is a documentation checkpoint. A prepared repository checkout, installed conventions in the local toolchain, Lean elaboration, exact theorem binding/axiom comparisons and independent semantic review of consequential applications remain pending. No new corpus relation is written, no record is deleted, no proof body or frozen Challenge changes, and no premise change is intended. No claim of mechanically checked equivalence or new root support is made.

## 11. Implementation checkpoint: shared fixed-point selection

Owner approved this style of abstraction on 2026-11-25. The draft now
implements the small maintenance slice identified in §7.1. Earlier sections
describe the earlier documentation-only checkpoints.

`TruthCore/Logic/FixedPointSelection.lean` has two prelude-only helper theorems:
`fixed_output` and `unique_closed_fixed`. The former uses equal inputs
`e' = e` and a pointwise transformation equation, instead of requiring a
global input endomorphism; this is weak enough for the spatial observation
projection. The latter applies uniqueness to a transformed member of a closed
predicate. Neither is a new corpus proposition.

- Induction: the singleton clause of `symmetry` uses the unique-closed lemma;
  `noUnique` uses fixed-output equality.
- Fission: `no_choice` uses the same fixed-output equality, with its original
  case split, admissibility, distinctness and swap premises.
- Space: `no_covariant_selector` supplies `relative_shift` and its original
  covariance equation; it retains the nonempty body and nonzero-shift proof.
- Time: `symmetry_transfer` supplies precomposition by the original reindexing,
  the invariant condition and the unique solution. The stationarity and
  arithmetic arguments are unchanged.

All five affected proof bodies keep their original theorem types and four
existing certificate/result identities. Frozen Challenges, comparator
configurations, vocabulary definitions, corpus records and semantic obligations
are unchanged. The fission certificate permits no axioms; the other three
permit the existing Mathlib axiom set. The two helpers use only equality
transport and function application; the actual axiom lists still need
mechanical confirmation.

The affected Logic aggregator was generated from the complete pinned Git tree
using the repository generator's sorted module-name/render algorithm, after
reproducing the exact existing aggregator byte-for-byte. A full local
`scripts/root-imports.sh --write`/check remains pending with the prepared clone.
The connector-only environment has no Lean, no working repository clone and
no network access from its local shell. Check the final revision with the
commands in §10 and the four affected certificate IDs in §7.1; do not merge
until those checks pass. No philosophical application or graph bridge is
registered here; independent semantic review remains pending for such
applications. Proof-body consolidation is not additional support for the case.

## 12. Implementation checkpoint: information invariance

The fixed-point checkpoint (head `276205beeffd832362d948a16347108d2c2f82f2`) passed [CI run 45647306508](https://github.com/moritzbrantner/formal-logos/actions/runs/45647306508).
The next maintenance slice introduces prelude-only `TruthCore.Logic.InformationInvariance`:
- `factor_iff`: move the existing CorrectionCriterion proof to a generic proposition-valued classification lemma, without changing its exported philosophical vocabulary.
- `class_agreement`: symmetry and transitivity of a supplied relation give agreement on membership in an anchored class. Reflexivity is not needed for this transfer.
- `of_representative`: transport truth from a related representative through invariance of the specified predicate; no universal coverage or equivalence-relation assumption is introduced.

Five existing Solution bodies now use these:
| Proof | Reuse and retained boundary |
| --- | --- |
| `CorrectionCriterion.characterization` | Exact classification iff fiber invariance; its finite controls and declaration are unchanged. |
| `HistorySelection.characterization` | Invariance of the actual world's evidence class, with the old evidence relation and its existing symmetry/transitivity; result `4b8f07db-2a50-5826-ac09-083f0e088d64`. |
| `InitialHistoryAuthenticity.sound_iff_uniform_witnesses` | Authenticity is transported from an admitted representative of the same positive observation; the relation explicitly retains admittedness. Existing authenticity result `84562a64-8e16-4fe0-92d2-6bd860b8b538` and identity bridge `3a404de1-a186-4700-89ec-afee90edcd1f` consume the original theorem. |
| `DarwinianEpistemicDebunking.BasisDefeat.calibratedSupervenience` | Transfer correct calibration from a representative of the same factor value. Truth supervenience, verdict stability, panel coverage and panel accuracy are all retained. |
| `ForeknowledgeDiscrimination.canonicalCertificate` | Related worlds agree on accessibility rows in the canonical selected-truth relation; the converse, factivity, and completeness conditions stay unchanged. |

The exact existing `observation_evidence` and `evidenceOnly_iff_uniform` adapters remain in InitialHistoryAuthenticity. AdaptiveHistoryAccess continues to use the old CorrectionCriterion result rather than bypassing it.

Executed finite diagnostics in the connector JavaScript runtime over two-element carriers: 16 observation/predicate profiles for factorization; 16 instances with a symmetric/transitive relation and related pair for class agreement; 32 cases satisfying the invariance/true-representative antecedents. All checks passed. These test only the finite logical patterns, not Lean or a metaphysical application. The Logic aggregator was regenerated from the complete pinned Git tree using the repository's exact render rule after byte-identical reproduction of the previous aggregate. No changed theorem types, corpus records, frozen Challenges, permitted axiom lists or new philosophical conclusions; verification of the new proof bodies and actual axiom lists is pending CI. Exact premise comparison remains pending at the new head.

## 13. Additional patterns for the next maintenance/research slices

The following are candidate interfaces based on inspected declaration bodies, not a claim of new certified results. Some extend earlier patterns rather than justify another library module.

### 13.1 Local compatibility versus global amalgamation

- `Logic/CollectivePossibilityRouteBoundary.lean`: `LocalShift`, `AllIndividuallyPossible`, `JointAbsenceImpossible`. A particular restricted shift can hold even when the unrestricted inference is invalid.
- `Modal/FiniteHitting/Vocabulary.lean`: `FiniteOmission`, `Hitting`, `Survivor`; finite joint absences and global absence differ. Compactness and rigid roster policy are independent.
- `Causality/GrimReaperPatchwork.lean`: `AdjacentPiecesCoPossible`, `ArrangementPossible`. Each pair of patches can coexist at some world without one world realizing the entire indexed arrangement.
- `Explanation/JointContingencyLocalization.lean`: `Equivalence` on an existing fixed conjunction; classical localization of failure is not arbitrary recombination.

The structural object is a family of subsets of one admitted witness space: individual, finite, adjacent and total intersections. Test implications with the same witness carrier, accessibility and all constraints. A finite witness space with constraints `x = 0` and `x = 1` has individually nonempty sets but empty intersection. The cofinite sets of Nat show finite intersection without global intersection. For finite-family or compactness conclusions use the existing mathematical lemmas, not a fresh metaphysical compactness axiom. Root destinations: the Third Way and the joint-absence power principle; distinct temporal, modal and causal admissibility premises stay open. This is a strengthening of the local/uniform witness survey, not a competing quantifier library.

### 13.2 Conservative expansion and invariance under forgetting structure

- `Explanation/ConservativeReasonExpansion.lean`: `canonical`, `CoverageAndGuardedStability`, `Certificate`; extend an arbitrary Ontic profile while keeping that profile unchanged.
- `Explanation/TargetCopyExpansion.lean`: `copied`, `EntailingCoverage`, `Certificate`; explanatory-token truth can be copied from the very target it ostensibly explains, preserving the original dependence profile.
- `Explanation/GroundingBaseline/Reduct.lean`: `GeneralInvariant`; queries on the shared modal reduct agree despite changes to omitted grounding relations.

Common proof scheme: a projection from enriched profiles to base profiles; a lift witnessing that each base model has an admissible enrichment; invariance of the target under that projection. An expansion condition that every base profile admits cannot exclude any base profile on its own. This is about **expressed formal conditions**: it does not show that all real explanations are merely labels or circular. Reuse the existing expansion certificates rather than introduce a second ontology. A substantive productive or explanatory bridge must constrain the lift. This is a useful test for the existential PSR `608a262d` and the claimed adequacy of impersonal sources.

### 13.3 All-premise production and closure traps

- `Causality/DerivativeJointPower.lean`: `Supply` (intrinsic or an admitted rule whose entire contributor set is supplied), `Trap`, `Escape`, `LocalPower`.
- `Logic/RegressDomains.lean`: `GeneratedWarrant`, inferential rule data and noninferential foundation; shares the inductive all-premise structure already identified in #1926.
- `Explanation/ExplanatoryClosure.lean`: `Accounted`, `Closed`, `FullSupply`; `allMembers` explicitly moves enablers into the demanded contributors.
- `Explanation/ActualExerciseExplanation.lean`: `OutputFounded`, `ProductiveCut`; tests when an adopted role and its product are both trapped.

A general rule package can carry a conclusion, an entire prerequisite predicate and a permitted-rule flag. Preserve inductive versus locally closed/coinductive readings: a cycle can satisfy local equations while failing inductive generation. Preserve contributor versus enabler roles; an existential predecessor is not sufficient for all-premise support. Existing `Supply` is already reused by the explanatory closure module. First inspect adapters before abstracting constructors; do not introduce a third fixed-point implementation. Root destinations: supplier-complete foundations and rational warrant; a shared graph shape does not by itself justify transferring the foundational standard between domains.

### 13.4 Scope transport and the actual-context index

- `Modal/DesignatedValidity.lean`: `DiagonalValid`, `NecessitatedValid`, `SuccessorClosed`, `ContentTransport`. Truth at admissible designations is not automatically necessary with a fixed designated context.
- `Logic/KnowledgeAdmissibility.lean`: `SupervenesAt`, `PhenomenalTwin`, `AdmissibilityLaw`. The existing Solution imports `PossibilityTransfer.box_transfer_iff` and uses frame inclusion; this is established implementation reuse, not a new proposed theorem.
- `Logic/ScopedEmpiricalProofBarrier.lean`: `ObservationBarrier`, `DomainCalibration`, multiple domain classifications.
- `Logic/NaturalTheologySemanticScope.lean`: `Meets` selects consequence, warrant or finite observation; `ConsequenceWarrantBridge` is explicitly open.

Common distinction: restriction of the quantified domain can weaken a universal test, but transfer to a new domain or evaluation context requires inclusion and, for index-dependent content, a transport law. No automatic transfer from formal validity to warrant or from failed empirical verification to meaninglessness. Reuse the existing modal transfer lemmas. Root destinations: modal ontological reasoning, natural-theology applicability, F1/F6 inquiry standards. This complements information invariance; changing the admissible alternatives is not the same as observing equal information.

### 13.5 Bearer, capacity, manifestation and effect

- `Causality/PowerExistenceBoundary.lean`: `UnborrowedPowerAt`, `ExternallySupportedAt`, `Coherent`; exercised power and existential support are different typed relations.
- `Modal/BearerExercise.lean`: `ManifestationRule`, `necessaryExercise`; necessity of capacity transfers to necessary exercise only by an explicit manifestation rule.
- `Explanation/JointCooperation.lean`: `Compatible`, `Coordinated`, `NecessaryIn`, `MutualFit`; scenario covariation, actual cooperation and modal necessity are distinct.
- `Explanation/ExistentialInheritance.lean`: `AbsenceInheritance`, `ActualResources`, `RulesPreserveTruth`; transfer of contingent failure through a fixed required bearer and truth-preservation under all group members.

This extends the existing modal transmission and witness identity patterns with a useful role separation: availability, possession, actual exercise, realized effect, and supporting existence. Use existing shared frames and explicit cross-role maps; no new universal power ontology. Necessary possession does not entail a necessarily performed act, and necessary exercise of some power does not entail a rigid necessary effect. Root destinations: the impersonal-source, causal perfection and will arguments. Compare exact omission controls before proposing any new bridges.

These five candidates overlap the original eight. Two conservative-expansion arguments share a proof step. Both `onticPropertyConservative` and the second conjunct of `TargetCopyExpansion.checks` instantiate a universal hypothesis at an admissible lift and project to its base. Each construction still needs its own coverage proof. A future maintenance slice can test `Function.Surjective.forall` on that projection. `GroundingBaseline.Reduct.invariant` instead uses extensionality on the retained fields.

Amalgamation remains a comparison across applications. The temporal result requires a local shift, finite hitting fixes a component and roster, the Reaper argument follows overlap down an indexed descent, and the contingency application begins with a supplied failure world. Extracting another shared lemma would become useful once two proofs use the same step under matching witness and admissibility conditions. The broader survey in #1926 remains open.
