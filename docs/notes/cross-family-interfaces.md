# Cross-family interfaces: proof reuse and semantic boundaries

Continuation of [#1926](https://github.com/moritzbrantner/formal-logos/issues/1926), especially phases 1–2 and the owner-approved hybrid schema policy (2026-11-24). Evidence baseline: main `93e7ee882fba969b62df982486a1b8ec36217c57`. This is a selected declaration-level survey, not a complete inventory, a new tracker, or a verified theorem batch. The parent issue owns allocation and current handoff. Reuse [the prior schema machinery](../schemas.md), [restated premises](restated-premises.md) and [orphan graft map](orphan-graft-map.md); do not repeat their work.

**Outcome:** candidate factoring only. No Lean, corpus, sense, claim, proof-binding or frontier-rule changes. No new philosophical premise is established. The intended subsequent maintenance slices keep the exact existing theorem types, all UUIDs, all senses including unused senses, and the same axiom footprint. Any new graph bridge needs its own application warrant and independent semantic challenge.

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
