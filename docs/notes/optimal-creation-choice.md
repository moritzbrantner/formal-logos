# Fixed optimal choice and selected effects

This bounded investigation advances the selected-effect bridge, not a new
free-agency theory. Reuse: `SelectedEffectBridge.OutputProfile`, unchanged
`varying` / `NecessaryVariableEffects.alternatingEffects`, and
`Results.Modal.SelectedEffectBridge.selectedEffectNecessary`. The related search
and dossier for `STMT-SELECTED-EFFECT-BRIDGE-CERTIFICATE` were inspected before
new vocabulary; choice-context controls already distinguish fixed conditions
from local functionality. The additional discrimination here concerns the
internal structure of the choice rule: unique optimal option, tied best values,
and absence of an achieved best value.

## Verified source readings

`LEIBNIZ-MONADOLOGY-53-55` was materialized from the existing Latta (1898)
web-snapshot edition (`corpus/passages/leibniz-monadology-en.json`), extending its
selector to anchors 53 through before 56. Read all three sections together:
§53 invokes infinitely many possible universes, only one actual, and sufficient
reason for the choice; §54 locates the reason in fitness/degrees of perfection;
§55 assigns knowledge of the best to wisdom, choice to goodness and production
to power. This is a substantive best-world rationale. These sections do **not**
prove that there is exactly one candidate achieving greatest quality, encode a
numerical metric, or settle the modal status of the rule, alternatives or order.
The definite singular wording does not by itself supply a theorem excluding ties.
No attributed formal claim or uniqueness premise was manufactured from it.

`AQUINAS-ST-I-Q25-A6-EN` was materialized from the complete 1920 Dominican
translation article, including objections and all replies
(`corpus/passages/aquinas-st-i-q25-a6-en.json`). The corpus source `AQUINAS-ST`
already exists. The body distinguishes essential goodness, where making this
thing essentially better changes which thing it is, from goodness beyond essence.
Reply 1 distinguishes the better product from a better manner of divine making;
it denies that God makes from greater wisdom/goodness while permitting better
products. Reply 3 grants optimal ordering with the present creation supposed,
but permits different/additional things yielding another better universe.
Reply 4 limits a blanket improvement reading through the special dignity of
Christ's humanity, beatitude and Mary. The article therefore resists identifying
perfect making with maximizing this creation over unrestricted alternatives.
It does **not** establish `∀ admissible option, ∃ strictly better admissible option`:
that quantifier-strengthening is deliberately rejected. Nor does it establish
that tied optima explain divine choice. These are independently stipulated
logical rivals, not attributed Thomistic teachings.

Both commands succeeded before these readings were written:

```
python3 scripts/source_evidence.py materialize LEIBNIZ-MONADOLOGY-53-55
python3 scripts/source_evidence.py materialize AQUINAS-ST-I-Q25-A6-EN
```

The manifests preserve exact page hashes, selectors and selected-text hashes.
The passages contain the evidence; no long source translations are copied here.
The Theodicy references in Monadology were not independently read, and no
Theodicy claim is made. q19 and Spinoza were not re-audited.

## What the types establish

`Optimal feasible quality x` requires admissibility and Mathlib
`IsGreatest (quality '' feasible) (quality x)`. Quality has a `PartialOrder`, not
a numerical or linear assumption. The set and map are literally fixed across
the modal alternatives; their metaphysical necessity is not established.

`OptimalOutputs` says every output at the selected/accessibly indexed worlds is
optimal, and each performance has some output. This positive-output totality is
separate from at-most-one output. The no-creation alternative to divine creation
is outside this bounded output model. No absent creation is represented by an
existent effect; `none` in the original ontology remains the source.

The general proof takes an actual output `x`, obtains some output `y` at each
accessible performance using totality, proves both optimal, identifies them by
the separate candidate-uniqueness hypothesis, and transports the output fact.
This derives `StableActOutput` rather than assuming its equivalent under a
new name. Existing `selectedEffectNecessary` then adds ubiquitous same-act
performance, causal realization and sound causal endpoints to infer necessity
of that particular actual output. It adds no premise of source necessity and
makes no universal propositional-collapse claim. Actual selected output alone
supplies no all-world output existence.

Any two optimal candidates have equal greatest quality by antisymmetry. The
constant-Nat-quality overlay makes the two original `some false` / `some true`
candidates distinct optima. `varying` and its existence/causal tables are
unchanged; the old soundness, necessary-source, same-act and causal-realization
facts remain reusable. The new certificate explicitly retains local uniqueness,
failed stability and contingency of `firstEffect`. The fixed feasible set
contains both candidates even though one is absent at each selected world;
feasible does not mean simultaneously existent.

Strict improvement of every admissible candidate contradicts an actual optimum,
as the improving candidate cannot lie above a greatest value. `Nat`, all
candidates admissible, and identity quality witness this regime. This does not
prove such a regime metaphysically admissible or attribute it to Aquinas.
Empty feasible sets also satisfy strict improvability vacuously; they likewise
have no optimal candidate. No completeness or exclusivity theorem for these
regimes is claimed: tied best and no-best are controls, not an exhaustive
philosophical dilemma. Perfect agency need not maximize remains an independent
rival outside the selected maximizing hypothesis.

## Verification and premise comparison

The combined full-content source elaborated with no diagnostics through the
coordinator service, workspace `/home/brantner/privat/truth-core-sprint-proof`,
session `causal-harvest`, preview HEAD
`210ab594fb5a1b2af75a6f0af684299937065238`, Scratch path
`Scratch/optimal_creation_choice/Combined.lean`, content SHA256
`a1f5e51cf2861746934e1e8a63250a5eed681621a40fb17d85c889ebed89bbd8`.
This is interactive evidence only. Canonical CI must still build the exact
modules, bind-check and run Comparator/NanoDa. Reproduction of focused proof
checks uses the canonical Solution and its registered result config.

Claim/type self-sweep: no new source claim, inference premise or root route is
introduced. The certificate universally quantifies its conditional backgrounds;
its no-premise argument certifies those conditional consequences and the explicit
controls, not those backgrounds. Its prose preserves fixed feasibility/quality,
positive-output totality, optimal-candidate uniqueness, and all causal hypotheses.
The tied control witnesses the particular finite interpretation only; it is not
a metaphysical possibility or agency proof. Definition/disambiguation records
separate best value, best option and perfect manner of making. Root-premise
comparison intended and actual: none added, removed or discharged. All adoption,
maximizing-rule, uniqueness, positive-output and metaphysical-adequacy questions
remain open.


## Same-source knowledge–choice–creation integration (#1737; 2026-11-23)

**Status: proposed checkpoint, pending delivered-head Lean/CI and independent
semantic challenge.** The additional theorems in
\`Results.Modal.OptimalCreationChoice.Solution\` use the same
\`SelectedEffectBridge.OutputProfile\` and \`NecessaryVariableEffects.EffectBeing\`
as the established certificates. No previously registered result, frozen
Challenge, claim, sense, root-route argument or computed premise status changes.
This addresses the outstanding unverified omission assignment in #1737's
2026-11-18 comment; the older \`varying\` and \`fixedEffects\` certificates
are reused rather than reproved.

### End-to-end graph: precise status at each arrow

\`\`\`text
[Existing necessary-source / actual-esse routes] --same bearer n-->
    E(n) and N(n)
       |  [OPEN transfer into one modal Ontic/OutputProfile and Causes field]
       v
[Existing GodHasIntellect and GodHasWill routes: capacities of that n]
       |  [OPEN intrinsic intentional apprehension; PR #1866 is a draft,
       |   not an available proof of actual understanding or willing]
       v
[Knowledge of candidate effects and their actual-world truth conditions]
       |  [OPEN content coverage, reference, factivity and actual judgment;
       |   ForeknowledgeDiscrimination #1380 only tests selected profiles]
       v
[Practical reason ranks/permits options + actual adoption by SAME n]
       |  [OPEN reason-grounded intention, selection without external
       |   determinant, complete intentional specification, rational policy]
       v
[Contingent choice/omission by n, with explicit productive exercise]
       |  [OPEN intention-to-effect efficacy, production/esse mapping
       |   to the actual root, causal-exemplar explanation and mode]
       v
[Selected world/order is produced and purposefully explained by n]
       |  [OPEN adequacy of why this order rather than another or none;
       |   explanatory adequacy is not necessitation]
       v
[Contingent creation compatible with necessary n]
       |  [FORMAL finite compatibility only: the controls below;
       |   no proved metaphysical admissibility or divine applicability]
       v
[God-existence / perfect intellect, will, knowledge and goodness consumers]
    only after the missing SAME-WITNESS, sense and causal bridges
\`\`\`

This graph is **not** a new implemented inference into GOD_4. The roots already
import capacity-level \`StageTwo.GodHasIntellect\` and \`GodHasWill\`, while the
logic of \`CommonKnowerScopes\` forbids distributing multiple content knowers
to one common bearer. The \`ForeknowledgeDiscrimination\` selected-content
result does not establish divine universal truth-complete knowledge.
\`DivineLoveRoute\` and the veracity study retain separate recipient-good,
moral-policy, factual-assent and permission burdens. No change to them is
silently inferred from a modal example. The actual creation nexus sought here
would use the *same* necessary being and the *same* grounding/production
relation as the existent-world argument, not a newly nominated object whose
name happens to be "God".

### Two checked finite model targets and what each discriminates

1. **Three mutually accessible worlds: A, B and no creation.**
   \`threeWorldCreation\` has \`W = Option Bool\`: at \`some false\`,
   \`firstEffect\` exists and is caused by one rigid \`source\`; at \`some true\`,
   \`secondEffect\` exists and is caused by the same \`source\`; at \`none\`,
   \`source\` exists but there is no creature, productive performance or causal
   edge. The source is necessary and the two effects separately contingent;
   each created output is causally sound, locally unique and optimal under the
   existing fixed tied-candidate ordering. Neither contingent effect becomes
   necessary. The predicates for intellect/will are only fixed unary
   **capacities**, and recognition covers just the two *possible options*;
   they are not intrinsic thought, free choice, omniscience or goodness.
   \`TracksSelectedCreation\` checks all-world output/selection correspondence,
   but the selection table still reads the world label: **even global fidelity
   is not an intentional explanation**.

2. **Same single best created candidate, creation versus omission.**
   \`alwaysPerformedOmission\` and \`optionallyPerformedOmission\` share exactly
   the ontology, rigid source, causal edges and outputs. Both have a unique
   admissible created effect at the actual creation world. In the optional case,
   the selected productive act is *not* performed at the omission world:
   \`OptimalOutputs\` and \`StableActOutput\` hold, while
   \`SameActEverywhere\` fails. In the universal-performance case,
   \`SameActEverywhere\` holds and every **actual** output is optimal, yet the
   omission world has no output at all: **positive-output totality** and
   \`StableActOutput\` fail. Both retain the same contingent particular effect.
   Thus the extra totality premise in \`uniqueOptimalStable\` is not a harmless
   restatement of perfect rationality or uniqueness. Here universal
   performance denotes one rigid act token, *not* a defended identity of
   intrinsic divine willing across worlds.

The actual-world \`coincidentalTag\` agrees with production of
\`firstEffect\`, but fails \`TracksSelectedCreation\` at the different
creation world. It models a fixed tag accompanying one actual event, not a
decision that governs all accessible effects. Conversely, passing the latter
relation only proves extensional alignment; a world-driven lookup table is
not an independent intentional *source*. Genuine intentional selection needs
further reference, practical adoption, counterfactual guidance and a
source-level explanation of specification rather than merely an isomorphic
copy of outputs. These remain **OPEN**.

### Necessary cause, rational determination and positive rival accounts

- **Necessary emanation (Spinoza-type).** Reuse
  \`NecessaryVariableEffects.fixedEffects\` / \`fixedSameNecessaryEffect\` and
  the \`SimplicityCollapse\` rigid-act core. A complete necessary
  nature/act plus a strict invariant production principle determines its
  effects: this gives a clear world-invariant sufficient determination, but
  denies the *metaphysical* contingency of that output. Spinoza's freedom as
  self-determined nonexternal action is compatible with his necessitarian
  account; the disagreement is about contingent objects. If a contingent
  creature exists in the relevant sense, necessitarian production must deny
  that contingency or one of the strict premises. The stronger Spinozist
  objection remains: a varied complete decree might change the intrinsic
  intellect, will and essence of a simple being (Ethics I proposition 33,
  note II; previously inspected and pinned in
  \`selected-effect-bridge-462.md\`). No finite table answers this.

- **Timeless, self-determining free choice (Aquinas-type).**
  The existing pinned ST I q.19 a.3, a.5, a.8 readings distinguish necessary
  willing of goodness, nonnecessary creaturely objects, rational order among
  things willed and efficacious willing of their contingent *mode*.
  This offers purposive/nonexternal explanation without treating each complete
  rational reason as a necessitating antecedent. But complete intentional
  specification still requires an account compatible with simplicity, pure
  actuality and a *single* intrinsic act: merely naming the choice "extrinsic"
  or "timeless" does not supply it. The structural controls refute no
  articulated Spinozist application.

- **Unique-best deterministic rational selection (Leibniz-type).**
  The established \`uniqueOptimalStable\` plus
  \`selectedEffectNecessary\` already entails one particular necessary
  output **conditional on** fixed candidates/qualities, a unique best
  created candidate, positive output at every performance, ubiquitous
  performance of the selected act, sound causal endpoints and stable output.
  Different admissible created optima do not logically force a unique
  choice. Even uniqueness *among creations* does not settle whether creating
  anything is required: the omission control isolates that gap. A policy
  maximizing over \`creation ∪ {refrain}\` requires a new typed *decision*
  comparison, rather than treating \`EffectBeing.none\` (the source) as an
  effect or slipping refraining into \`soleCreatedCandidate\`.

- **Brute world selection or brute contingent source activity.**
  The tabulated model supplies a causal antecedent, but if a world label or
  primitive brute act selects the effect, it gives only a local actual causal
  history, not an intelligible reason why that particular history rather
  than its accessible rivals. The \`coincidentalTag\` test blocks an
  especially weak actual-match proxy. A brute rival may reject contrastive
  explanatory closure while retaining reliable actual production; it is
  structurally coherent here and is not defeated by a theorem requiring
  closure it denies. The intentional rival still owes a positive reason
  why its own nonnecessitating choice has greater explanatory content than
  this world-label surrogate. This is the discriminating target, not a
  declaration that every brute fact is impossible.

### Explanation versus necessitation and provisional assessment

**Conditional results:** a necessary source with stable candidate-recognition
and capacities can have different *world-local* effects or omit producing any
effect; source necessity alone does not transfer to effect necessity.
\`SelectedEffectBridge.selectedEffectNecessary\` remains the controlling
conditional **necessitation** rule. Neither \`RealizedOutputs\` nor a
\`TracksSelectedCreation\` match qualifies as *metaphysically adequate
explanation*. Strictly sufficient reasons are one possible explanatory
demand, not the definition of explanation used by every rival. The #750/#555
reason-closure results keep their exact distinct scope.

**Overall provisional assessment (to be challenged independently):**
the non-necessitation distinction is well motivated and the same-bearer
finite examples clarify which assumptions do real logical work. The existing
capacity, goodness and intentional-purpose argument families offer positive
reasons to investigate personal creation over impersonal emanation or bare
selection. They have **not yet** established an actual, intrinsic,
nonnecessitating and rationally explanatory selection by the GOD_4 bearer.
Consequently the divine free-creation synthesis remains **underdetermined**,
not dismissed and not declared proved. Even maximal rationality may be
interpreted as (i) strictly uniquely determining the world or (ii) licensing
several nondefective outcomes; the finite models support distinguishing these
policies, not deciding their metaphysical truth.

**Revision tests:** (a) independently map complete intentional content to
the same simple source and explain how it varies without an added intrinsic
contingent determinant; (b) compare a defended permissive-rational-choice
policy with genuinely unique complete reasons, including refraining as a
typed decision; (c) demonstrate an intention-to-production causal/esse
bridge at the fixed root instead of an output-copying table; (d) give a
knowledge-of-actual-contingents account consistent with the #1380 factivity/
intrinsic-supervenience boundary; (e) compare the resulting complete personal
account with the strongest impersonal necessary emanation and brute-selection
answers to the *same world-order explanandum*. If no such positive account
is supplied, retained contingency may be a bare specification rather than an
improvement in explanatory adequacy.

**Self-sweep and verification boundary:** the rigid \`source\` is a single
\`EffectBeing\` value across all accessible worlds; created beings are
distinct \`some b\` values. World \`none\` is an index and is not an
existent effect; omission is an absence of outputs and causal edges. The
three-world case distinguishes capacity, option recognition, performed act,
selection and produced effect, without equating any with actual intentional
understanding, free will, moral goodness, world-choice or all-truth knowledge.
The two-world case varies just the performance predicate while preserving
ontology/output and demonstrates separate failure of totality. The new
theorems have no registered argument/result or frozen Challenge; Comparator,
NanoDa and \`truth frontier-diff\` therefore have **no new route to certify**,
and the computed premise delta is expected to be **none**. Focused Lean
elaboration, full CI, corpus/binding/axiom checks and independent semantic
challenge must be evaluated on the delivered PR head; until then the model
certificates and assessment here are **proposed, not verified or reviewed**.
