# Fixed optimal choice and selected effects

This bounded investigation advances the selected-effect bridge, not a new
free-agency theory. Reuse: `SelectedEffectBridge.OutputProfile`, unchanged
`varying` / `NecessaryVariableEffects.alternatingEffects`, and
`Results.Modal.SelectedEffectBridge.selectedEffectNecessary`. The related search
and dossier for `STMT-SELECTED-EFFECT-BRIDGE-CERTIFICATE` were inspected before
new vocabulary; choice-context controls already distinguish fixed conditions
from local functionality. The additional discrimination here concerns the
internal structure of the choice rule: unique optimal option, tied best values,
and absence of an achieved best value. [Research record](../../corpus/attempts/optimal-creation-choice.json)

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

**Status: checkpoint in PR #1875.** CI passed on the first delivered head
(d23a5d3); an independent semantic challenge then found overstated prose and
unacknowledged reuse, repaired here (repair pass 1). The additional theorems in
`Results.Modal.OptimalCreationChoice.Solution` use the same
`SelectedEffectBridge.OutputProfile` and `NecessaryVariableEffects.EffectBeing`
as the established certificates. They are unregistered: no argument, result,
frozen Challenge or Comparator config. No previously registered result, frozen
Challenge, claim, sense, root-route argument or computed premise status changes.
This addresses the outstanding unverified omission assignment in #1737's
2026-11-18 comment; the older `varying` and `fixedEffects` certificates
are reused rather than reproved.

**Reuse and what is new.** That a necessary source can have varying or absent
activity is already certified by
`NecessaryContingentActivity.necessaryWithContingentActivity` (#435) and
`NecessaryVariableEffects.necessarySourceVariableEffects` (#462). The two-world
creation/omission profiles are #555's `SimplicityCollapse.optionalAct` and
`SimplicityCollapse.inefficaciousAct` on `noCreation`, whose `Core` already
certifies their necessary source, (non-)ubiquitous performance, strict efficacy
facts and contingent effect; failed stability of `inefficaciousAct` is composed
here from `Core` clause 2 and its denial of strict efficacy. The new content is
the **optimality layer** over these profiles (`soleCreatedUnique`,
`optionalOmissionOptimal`, `universalOmissionOutputOptimal`,
`universalOmissionNotTotal`): a unique optimum plus optimality of every output
does not yield `StableActOutput` without positive-output totality. The
three-world model adds the omission world and the selection-table tests
(`TracksSelectedCreation`, `coincidentalTag`) to one profile.

### End-to-end graph: precise status at each arrow

```text
[Existing necessary-source / actual-esse routes] --same bearer n-->
    E(n) and N(n)
       |  [OPEN transfer into one modal Ontic/OutputProfile and Causes field]
       v
[Existing GodHasIntellect and GodHasWill routes: capacities of that n;
 NOT formalized in the controls below, which model no intellect or will]
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
```

This graph is **not** a new implemented inference into GOD_4. The roots already
import capacity-level `StageTwo.GodHasIntellect` and `GodHasWill`, while
`CommonKnowerScopes` shows per-content knowers do not entail one common
knower (`noWitnessExchange`). The `ForeknowledgeDiscrimination` selected-content
result does not establish divine universal truth-complete knowledge.
`DivineLoveRoute` and the veracity study retain separate recipient-good,
moral-policy, factual-assent and permission burdens. No change to them is
silently inferred from a modal example. The actual creation nexus sought here
would use the *same* necessary being and the *same* grounding/production
relation as the existent-world argument, not a newly nominated object whose
name happens to be "God".

### Two checked finite model targets and what each discriminates

1. **Three mutually accessible worlds: A, B and no creation.**
   `threeWorldCreation` has `W = Option Bool`: at `some false`,
   `firstEffect` exists and is caused by one rigid `source`; at `some true`,
   `secondEffect` exists and is caused by the same `source`; at `none`,
   `source` exists but there is no creature, productive performance or causal
   edge. The source is necessary and the two effects separately contingent;
   each created output is causally sound, locally unique and optimal under the
   existing fixed tied-candidate ordering. Neither contingent effect becomes
   necessary. The model contains **no** intellect, will or option-recognition
   predicate: an earlier draft carried constant labels for these
   (`x = source`, `True`) that were connected to nothing and could not fail,
   so they added no logical content and were removed. The necessary source
   with varying or absent activity is the #435/#462 result reapplied, not new.
   `TracksSelectedCreation` checks all-world output/selection correspondence,
   but the selection table still reads the world label: **even global fidelity
   is not an intentional explanation**. Each created effect is its own world
   label (`x = w`), so "selected effect" and "selected world" coincide; the
   world is a surrogate for the selected effect.

2. **Same single best created candidate, creation versus omission.**
   These are #555's `SimplicityCollapse.optionalAct` and
   `SimplicityCollapse.inefficaciousAct` on `noCreation` (creation world
   `false`, omission world `true`), reused, not new models. They share the
   ontology, rigid source, causal edges and outputs. Both have a unique
   admissible created effect at the creation world. In the optional case,
   the selected productive act is *not* performed at the omission world:
   `OptimalOutputs` and `StableActOutput` hold, while
   `SameActEverywhere` fails. In the universal-performance case,
   `SameActEverywhere` holds and every **actual** output is optimal, yet the
   omission world has no output at all: **positive-output totality** and
   `StableActOutput` fail (the latter already follows from #555 `Core`
   clause 2 with the failure of strict efficacy). Both retain the same
   contingent particular effect. The new content is the optimality layer:
   the extra totality premise in `uniqueOptimalStable` is not entailed by
   uniqueness of the created optimum plus optimality of all actual outputs;
   whether a create-or-refrain rationality principle supplies it is **OPEN**.
   Here universal performance denotes one rigid act token, *not* a defended
   identity of intrinsic divine willing across worlds.

**What the controls do not model: the simplicity-restored application.**
Under #555's `BeingCarriesAct` reading (the token is performed wherever its
bearer exists) with a necessary source, `Core` yields `SameActEverywhere`.
`beingCarriesActApplication` checks that `threeWorldCreation` and
`optionalAct` fail `BeingCarriesAct` and `inefficaciousAct` satisfies it. So
under that reading the three-world model and the optional profile are
excluded, and `threeWorldOptimalOutputs` holds only because performance is
withheld at `none`. Only the always-performed profile survives; there the
difference between creating and omitting is carried by the world label
alone. That is #555's inefficacious, extrinsic branch, structurally the same
as the brute-selection rival below.

The actual-world `coincidentalTag` agrees with production of
`firstEffect`, but fails `TracksSelectedCreation` at the different
creation world. It models a fixed tag accompanying one actual event, not a
decision that governs all accessible effects. Conversely, passing the latter
relation only proves extensional alignment; a world-driven lookup table is
not an independent intentional *source*. Genuine intentional selection needs
further reference, practical adoption, counterfactual guidance and a
source-level explanation of specification rather than merely an isomorphic
copy of outputs. These remain **OPEN**.

### Necessary cause, rational determination and positive rival accounts

- **Necessary emanation (Spinoza-type).** Reuse
  `NecessaryVariableEffects.fixedEffects` / `fixedSameNecessaryEffect` and
  the `SimplicityCollapse` rigid-act core. A complete necessary
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
  `selected-effect-bridge-462.md`). No finite table answers this.

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
  The established `uniqueOptimalStable` plus
  `selectedEffectNecessary` already entails one particular necessary
  output **conditional on** fixed candidates/qualities, a unique best
  created candidate, positive output at every performance, ubiquitous
  performance of the selected act, sound causal endpoints, outputs realized
  as source causal edges (`RealizedOutputs`) and an actual output; stability
  is derived, not assumed.
  Different admissible created optima do not logically force a unique
  choice. Even uniqueness *among creations* does not settle whether creating
  anything is required: the omission control isolates that gap. A policy
  maximizing over `creation ∪ {refrain}` requires a new typed *decision*
  comparison, rather than treating `EffectBeing.none` (the source) as an
  effect or slipping refraining into `soleCreatedCandidate`.

- **Brute world selection or brute contingent source activity.**
  The tabulated model supplies a causal antecedent, but if a world label or
  primitive brute act selects the effect, it gives only a local actual causal
  history, not an intelligible reason why that particular history rather
  than its accessible rivals. The `coincidentalTag` test blocks an
  especially weak actual-match proxy. A brute rival may reject contrastive
  explanatory closure while retaining reliable actual production; it is
  structurally coherent here and is not defeated by a theorem requiring
  closure it denies. The intentional rival still owes a positive reason
  why its own nonnecessitating choice has greater explanatory content than
  this world-label surrogate. This is the discriminating target, not a
  declaration that every brute fact is impossible.

### Explanation versus necessitation and provisional assessment

**Conditional results:** a necessary source can have different *world-local*
effects or omit producing any effect (already #435/#462); source necessity
alone does not transfer to effect necessity.
`SelectedEffectBridge.selectedEffectNecessary` remains the controlling
conditional **necessitation** rule. Neither `RealizedOutputs` nor a
`TracksSelectedCreation` match qualifies as *metaphysically adequate
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

**Self-sweep and verification boundary:** the rigid `source` is a single
`EffectBeing` value across all accessible worlds; created beings are
distinct `some b` values. World `none` is an index and is not an
existent effect; omission is an absence of outputs and causal edges. The
three-world case distinguishes performed act, selection table and produced
effect; it models no capacity, option recognition, intentional understanding,
free will, moral goodness, world-choice or all-truth knowledge. The two-world
(#555) case varies just the performance predicate while preserving
ontology/output and demonstrates separate failure of totality. The new
theorems are unregistered: no argument/result, frozen Challenge, Comparator
config or binding, so Comparator and `bind-check` have nothing new to certify
and the computed `frontier-diff` premise delta is **none**. CI's NanoDa
no-`sorry` check does cover the affected Solution module. CI passed on
d23a5d3; the independent semantic challenge of that head and its repair are
recorded in PR #1875. The assessment above remains a provisional judgment.


## Rational authorship versus brute selection (2026-11-23)

Scope: #1737, #735/#750, #1875, #1887. Evidence baseline
`8083301a037428574d0e46b1064d8f6d858da377`; related open work #1901,
#1909, #1910 and #1904 is background to the original draft. Fix the same actual source
n, the same actual complete creaturely order H (including its history and
laws), and candidate alternatives H' and refraining. No assumption that all
described alternatives are metaphysically possible. Here an explanation of
the order is not a demand for a separate aggregate entity, and n's own
existence is not the explanandum H. These are analyst arguments; no new
source-attributed claim, formal declaration, or certified model.

### 1. A symmetric three-level demand

Ask of every source (personal or impersonal): (i) what explains the
existence and actual productive exercise of the source, (ii) what explains
its producing an order of this kind, and (iii) what explains its producing
this complete order rather than each rival? These are not interchangeable.
A productive account can explain the occurrence of a particular outcome. A
partial contrastive explanation excludes some alternatives. An exhaustive
determining explanation for the third question requires that the total grounds
exclude every admitted incompatible alternative. Distinguish a reason for the source's existence
from a reason for the occurrence of a volition, from the volition's
intentional object, from a causal reason for the effect.

Use #545, #742's base-fixed net selection core and #555, not another modal
collapse theorem. Necessity of n does not make all of its relations or
effects necessary. Conversely, a necessary complete determining ground
would make its strictly necessitated effect necessary. If selection is
itself a contingent fact and the demand for a complete determining reason
extends to it, a strict reason for H obtained by citing that selection has
merely moved the explanatory debt. The fact-level closure demand is stronger
than a PSR restricted to actual concrete existence; neither automatically
settles how to account for volitions or extrinsic relations. No special
exemption for personal choice, no deduction of unlimited recombination
from rejecting this demand. An impersonal probabilistic or dispositional
producer must receive the same credit for actual production as a personal
one when the same causal and nonnecessitating standard is met.

### 2. A positive authorship proposal, not a personal-stop predicate

Consider an engineer who intends a bridge to allow safe passage, deliberates
between two sound designs, settles on one and realizes it. Assume the
designer understands the designs, the goal actually figures in the choice,
the designer controls which design is implemented, and the implementation
is causally governed by the intention. Contrast a random draw from the
same two designs followed by implementation; contrast also a passive
observer who correctly predicts the drawn design. The goal explains
excluding unsafe designs in both the rational and the intentionally
restricted lottery cases. The actual rational intention can additionally
explain the particular implementation in a different respect: the chosen
design is the object for the sake of which the implementation occurs, not
merely the output of a draw or a description attached afterwards. Neither
the reason for choosing a sound design nor the mere fact that the engineer
chose A explains why A rather than B was endorsed if every differentiating
consideration is absent. If the engineer deliberately selects by lottery,
the intention explains use of the lottery, not direct authorship of its
particular draw.

This motivates **practical authorship** as a candidate explanatory reading
(not a proposed corpus predicate): an existing source recognizes an end and
feasible means, adopts a particular object for a genuine reason, and its
own directed exercise produces that object. Reasons must have content
assessable without simply consulting which object occurred; they must
figure in the actual practical operation, not just license it afterward.
An intentional account answers why the effect exists as a realization of
an intelligible purpose and why the agent, rather than an autonomous
chance selector, is responsible for implementing it. It does not promise
a necessitating reason for the agent's very endorsement.

A discriminating test concerns *direction* rather than modal coextension.
A reason-copying table that maps H to "intends H" fails to identify a
directed exercise producing H. A producer whose mechanism is actually
guided by an intention and a spectator who perfectly represents its output
can share all truth-valued intention/output pairs; the latter has no
productive authority over it. A randomizer controlled as a policy but not
in its individual result supplies a further omission. The intended
difference is the causal/exemplar dependence of implementation on an
apprehended and adopted end, not the frequency of success or a flag
saying "personal". For ordinary agency the difference is investigated
through purposive correction of a failed implementation, the role of
reasons in actual decision, and the means/end organization of production.
A merely successful fixed table could imitate each observed correction;
an actual reason-using mechanism or constitutive intentional account,
rather than behavioral matching alone, is still required. A deterministic
agent can satisfy this reading, so it does not establish libertarian
freedom. An impersonal system with genuine purpose-relative productive
organization may satisfy part of the proposed standard, and a functionalist
who establishes genuine cognition and agency would satisfy the authorship
reading rather than being excluded by stipulation.

The proposal goes beyond #742's tested marks only at the philosophical
level: cognition of an end, adoption *for* a reason, and actual
intention-directed production. It is not a new inference from pro tanto
favoring, world-tracking or merely interposing an act. Its positive warrant
is the difference between using a reason to realize a design and
post-hoc rationalization, plus the ordinary practice of explaining actions
as actions for ends. The generalization from mediated human action to a
simple nonpassive ultimate source is OPEN. The strongest rival accepts
productive explanation and fixed rational/causal constraints but treats
the residual selection as primitive, whether in an agent or an impersonal
producer. The account may then have greater purposive explanatory content
without resolving the residual exact-world contrast. Do not call the rival
contradictory or the personal stop fully adequate merely because one is
intentional. A defender of universal determining explanation will still
charge that residual debt to both.

### 3. A constructive simple-source reading and its unresolved cost

A candidate classical account: the necessary source's intrinsic actuality
includes intellectual apprehension of its own goodness and the range of
creatable finite goods, and active productive power. Finite realizations
need not exhaust or complete that goodness. Essential reasons could
determine which ends and means are fitting without uniquely specifying
every finite good, law, parameter or history. Creative freedom is then
choice among admissible realizations (possibly no creation, if no duty
requires it), not freedom to violate necessary truth or goodness. A
necessary impersonal nature could also impose constraints, so the
existence of a boundary is not the personal discriminator. Neither the
necessary constraints nor a permissive policy are inferred from a
necessary bearer alone. "Good" cannot mean merely "what this source
chooses": that would leave the restriction vacuous. Reasons must be
normatively substantive and not constituted merely by the chosen output.

The strongest nonpassive reading takes creative direction to be timeless:
the source is not informed by its effects; the effects are dependent on
its active specifying causality. The creative act need not be a new
intrinsic accident, an unrealized passive potency, or a temporal choice
episode. The proposed relation to H is genuinely productive, not a
Cambridge description of H's independently obtaining. But applying this
reading is precisely the hard part. #555 `BeingCarriesAct` plus necessary
bearer yields `SameActEverywhere`; with strict efficacy of the same rigid
act for H the contingent-effect package is inconsistent. A world-relative
description that changes denotation does not provide this rigid act. In
#1875 the surviving always-performed model is structurally output-varying;
it does not give intrinsic intention. A varying intrinsic decree requires
a simplicity/identity interpretation that permits it. An extrinsic
intentional determination needs an account of why the effect depends on
the determination rather than the determination being fixed by the effect,
without reintroducing a contingent intrinsic modifier. Neither is yet
provided by the constructive sketch. Divine foreknowledge needs its own
content/reference and discrimination bridge (#1380): knowledge rows can
differ under a fixed rule, but an intrinsic-state supervenience reading
does not permit different rows for the same intrinsic state. Accurate
world-indexed relations by themselves are not apprehension.

This is compatible with the aim of the latest C2 work, not a solution to
it. The possibility that a distinct dependent effect is absent is not the
possible absence of the underived n. Active power to produce or refrain
need not be a power over n's own esse; the application to real powers and
non-being must use the existing C2 senses. If C2 is won, it could supply a
necessary bearer, not the intrinsic-explanation, intellect, will or choice
bridges. Conversely, an agency model cannot rescue C2 by assuming the
necessary bearer that C2 is meant to establish. #1909's determining
demand, #1910's E/D distinction and #1901's G0/G1/G2 split are live
comparators, not verified new supports from those open branches.

### 4. Epistemic agency as a positive end, not an assertion shortcut

A different consequence of the authorship reading concerns the epistemic
quality of the world. Suppose this same source accurately understands both
H and the evidential role of a created faculty or trace mechanism; freely
intends creatures to exercise genuine epistemic agency in a specified
domain D; and is good in the substantive sense of not gratuitously
frustrating that very end. Specify the normal use/environment of a
mechanism independently of whether its verdict is true (e.g., ordinary
undisturbed acquisition, storage and retrieval of traces of events, with
specified error conditions). Then deliberately arranging all normally
available evidence in D to support a false history, with no ordinary way
to correct it, frustrates the proposed epistemic end in D. This is a
reason against global counterfeit creation, not a deduction from bare
intellect, power, goodness or absence of false divine assertions.

The candidate normative premise: where an agent intentionally confers a
truth-directed capacity for a domain, deliberately rendering its ordinary
exercise systematically misleading, without an overriding justification,
is contrary to faithfully realizing that good. Its warrant is the
means/end mismatch: a capacity for access to truths cannot fulfill that
specific end merely by reliably producing the appearance of access.
Epistemic agency also matters as a good for the creatures, not only as a
means to useful behavior. One could consistently intend limited cognitive
access, allow local mistakes for other goods, or give a faculty a practical
rather than historical purpose. Distinguish actual authoring of systematic
misleading evidence from permitting secondary causes, honest ignorance,
fiction, miracles, error, or deceptive creatures. The premise does not
exclude all such possibilities. A genuine overriding reason, a different
intended domain or a corrective route weakens the argument; universal
hidden-reasons defenses that license any apparently misleading evidence
also weaken the proposed positive entitlement. Not every false trace is a
divine assertion, so `GodAssertsOnlyTruth` (5a035a1e) cannot be silently
extended to evidence by #1410's assembled branches. Nor does know-how to
produce a faculty entail accurate actual cognition of H.

An application to a normally functioning radiometric record would require
a trace-producing process linked to the actual event, preserved causal
provenance, a reliable faculty/instrument and warranted applicability of
the intended-domain interpretation. Historical calibration can supply
defeasible warrant, not a noncircular deductive guarantee against a
perfect coordinated counterfeit of the calibration itself. A five-minute
apparent-age order is not ruled out merely by a necessary cause; on the
proposed epistemic-end and no-gratuitous-frustration account such an
unqualified global counterfeit is opposed by a specific reason. To exclude
it categorically requires a sufficiently strong actual normative
constraint, a scoped intended end and absence of overriding justification.
Even an ontic guarantee requires a further account of human access or an
appropriate externalist warrant condition. No equal priors, skepticism
from bare contingency, or induction theorem follows. Reuse #737 and
#1734; #1904 owns the history-evidence comparison. The distinctive addition
is the possible *positive intentional ground* for normally truth-connected
evidence, not a duplicate present-evidence-only non-entailment.

### 5. Matching-scope rival assessment and next tests

- Brute contingent foundation: may have stable natures, reliable causal
  trace mechanisms and warranted ordinary scientific practices; leaves
  foundation actuality primitive and may also leave the complete selection
  primitive. No unrestricted replacement follows without further modal
  premises.
- Necessary impersonal producer: may have genuine intrinsic existential
  explanation, lawlike or probabilistic production, substantive essential
  limits and truth-tracking secondary mechanisms. Under productive
  nonnecessitating sufficiency it earns the corresponding explanation
  credit; no inherent guarantee of purposive authorship or epistemic
  goodness. A positive impersonal teleological account would reduce the
  comparative advantage, not be excluded by label.
- Necessitarian source: a warranted unique complete order could satisfy
  the determination demand even without creative choice, although
  mathematical uniqueness and actuality of the structure differ; no
  metaphysical contingency at the tested scope. Must explain apparent
  contingency and how finite agents have access to the necessary order.
- Necessary free personal source: can potentially explain source existence,
  intelligible ends, actual purposive production, scope restrictions and
  epistemic goods together. Same unresolved exact selection if full
  determining contrast is demanded. Adds burdens of genuine cognition,
  agency/efficacy, goodness, nondeceptive intent and a simplicity-compatible
  account of their contingent terminations.

**Proposed assessment, not a reviewed standing change.** A nonnecessitating
productive explanation can be genuinely explanatory; the purposive
authorship distinction offers a positive comparative reason to investigate
personal sourcehood beyond bare modal or causal tables. Relative to a
purely brute account of H, an actually instantiated, reason-guided,
productive and faithful source would supply explanatory content the
brute account lacks. Relative to the strongest constrained impersonal
producer, its added advantage is conditional and concerns intelligible
ends and intentional epistemic care, not the bare fact of contingency or
the closure of every contrast. On universal determining sufficiency the
same objection remains against both nonnecessitating sources; on weaker
productive sufficiency both may succeed. Maintain the existing
underdetermined judgment about the complete classical synthesis. There
is substantive warrant for the ordinary authorship distinction, not yet
for its full simple-source application or for an exceptionless epistemic
constraint. The cases are not exhaustive and no rival is defeated.

Graph destination: the existing #1737 targets
2757f6a3-2d14-5033-9740-2c36a678ce73 and
1822b59d-1040-57e4-8991-f7862db26355; #1730 intrinsic reason
a7bbd2fd-242c-5097-a9a3-581d25835890; C2 necessary-concrete endpoint
b19ffd92; God-existence destination 8626f8a5-9531-5da7-9ebd-f901e74b1129.
All connections from same-source necessary actuality through intrinsic
intentional understanding, will, purposeful actual exercise and normative
epistemic-end interpretation remain OPEN; do not exchange witnesses or
identify `m.grounds` with `m.ontic.Causes` (#555 applicability).
5a035a1e is assertion-only, not a new historical-reliability consumer.
No new graph edge or premise discharge. Expected premise delta none;
the computed frontier comparison and validation evidence are recorded in PR #1911.

Next discriminators: (a) a constitutive/exemplar account giving productive
intentional direction rather than output-conditioned relation while retaining
the exact #555 simplicity commitments; compare it with actual reason-using
impersonal mechanisms, rather than further output tables; (b) identify
which moral reasons are side constraints on the creative end as opposed
to permissive rankings, test unique/tied/incomparable goods and refraining
without assuming an optimum; (c) defend or reject the no-gratuitous-
frustration premise for one independently specified evidence channel,
apply it to the same source, and test a justified misleading-evidence
exception and an equally reliable impersonal rival. Strengthen the
assessment if these bridges are supplied and survive restored-commitment
tests; weaken it if genuine authorship reduces to the same uncontrolled
selector or the epistemic norm has no discriminatory application.
Independent final semantic challenge required. Connector-only
author-side self-sweep: no new Lean/proof/type, source claim, sense,
statement or result; exact modal and knowledge controls retained, no
claim that the conceptual authorship sketch models full divine simplicity
or that an epistemic end entails every historical belief. Canonical
related/dossier/novelty and full checks unavailable in this session.
Attempt [7d015c02](../../corpus/attempts/7d015c02-2e23-4b2e-a418-e23c943c3a5a.json) records the proposed checkpoint.


## Can direct intentional production be extrinsic without becoming brute? (2026-11-23)

Continuation of the preceding #1737 checkpoint, same witness n and complete
creaturely order H. Reuse the checked #555 rigid-token and #462 output-profile
results, #1875 omission controls, #742 reason-selection boundary and #1380
content discrimination. The [#462 literature investigation](https://github.com/moritzbrantner/formal-logos/issues/462#issuecomment-6827802194)
already records O'Connor's direct agent-causal proposal and Huneeus's
extrinsic volition; the existence of these proposals is not a new result.
The new discriminating question is how to retain independently specified
intentional content and genuine efficacy when the particular exercise is
not a new intrinsic state. No separate issue, new modal framework or
change to #555's completed certificate. Baseline main 8083301a037428574d0e46b1064d8f6d858da377;
continuing draft #1911, prior head f4392e11aed1d4a2bda2546d546996eb5a13f151.

### 6. One-act rationality: the reason for an order is not a cause of the will

Selected source readings for philosophical orientation (not new pinned
attribution records):

- [ST I q.19 a.2–5, especially a.5 co. and ad 1–3](https://www.newadvent.org/summa/1019.htm):
  in a single act an end and its means can be willed in their order,
  without the act of willing the end being a distinct cause of willing
  the means. Aquinas denies a cause of the divine will; his account of
  its rationality rests on the ordering of things willed, not on a
  causal transition within the will. A.3 co./ad 5 distinguishes the
  necessary primary good and the nonnecessary relation of the will
  to finite goods. A.4 ad 4 treats directing knowledge, commanding will
  and executing power as one in God. A.6 ad 1 distinguishes qualified
  willing from what God wills simply; a.8 addresses efficacy and the
  contingent or necessary mode of effects.
- [ST I q.45 a.3 co./ad 1–3](https://www.newadvent.org/summa/1045.htm)
  and [q.13 a.7 co.](https://www.newadvent.org/summa/1013.htm):
  active creation signifies the divine action with a creature-relative
  description, while the real creation relation is in the creature.
  The real relation of the creature presupposes its subject in being;
  the passage does not install a contingent selector in God. Creation
  in this sense concerns beginning; do not infer a conservation thesis
  from the duration qualification in q.45 a.3 ad 3.
- [ST I q.14 a.8–9, a.11](https://www.newadvent.org/summa/1014.htm):
  intelligible forms alone do not explain determinate production;
  practical direction requires will. Possible and actual contents are
  distinguished. A.8 ad 1 explicitly distinguishes consequence from
  causal dependence in knowledge. A.11 proposes an extension to singulars
  on the basis of the scope of divine causality.
- Huneeus, *Divine Simplicity and the Theory of Action*, online-first
  text (2024), [§§2–4, printed pp. 7–15](https://philarchive.org/archive/HUNDSA-4),
  DOI 10.14428/thl.v9i1.82053 (subsequently published 2025).
  Previously inspected and summarized in #462. The accessible extracted
  text in this pass was read at pp. 7–15; page-image fetch was blocked.
  §3's key-press example distinguishes an intrinsic end from the more
  specific action performed. §4 recognizes that nonobservational
  productive knowledge of the exact details is the harder question.
  This reading is used for orientation, not a new source-claim binding.

The first distinction gives a positive interpretation not requiring
reasons to act as efficient causes of new intrinsic divine states.
For example, if n creates an order with rational creatures and wills
their genuine epistemic access, it can will reliable means of inquiry
in their relation to that end. The means/end content is assessable
independently of the bare fact that the order obtains: systematically
unreliable means would not fulfill that specified purpose. The
productive act could embody that rational structure without containing
a temporal deliberative succession or being a cause of itself.

This proposes an explanation of why specified features are ordered
together in H: the order is apprehended and intentionally realized
as an order. It is stronger than finding a good which the actual
effect happens to instantiate. It is not an inference from teleological
fit alone to intention. An impersonal mechanism with actual causal
constraints could generate the same order and would explain its
structure in a nonintentional way; it is not ruled out here. Nor does
an explanation of the means/end relation tell us why this particular
end-relative whole was actualized. Do not convert the source's denial
of a cause of the one will into a denial of all rational explanation,
or convert the ordering of willed things into a determining cause of
the selection of H. Those would be opposite scope mistakes.

The one-act view also clarifies the no-mediator test. Suppose every
specific voluntary exercise must be caused by an already distinct
specific voluntary exercise selecting that very outcome. The demand
reapplies to the proposed selector; without a base case there is
another regress rather than an explanation. This is conditional on
the repeated demand for a *separate* voluntary mediator. A rival
may instead identify the base case with a causally necessitated
executive state, an indeterministic event-causal choice, or direct
agent-causal production. The regress does not prove that the direct
case is metaphysically possible, free or rationally adequate.
It shows why simply demanding another prior volition cannot be the
universal test of intentionality. Explanatory priority here is not
temporal priority, especially for a timeless source.

### 7. The granularity and efficacy tests

Fix two incompatible complete candidate orders H and J, each realizing
a genuine primary good P; optionally include omission. They are
descriptions of candidate realizations, not additional actual concrete
beings or certified metaphysically possible worlds. Let D be a
specific positive feature separating H from J. The issue is not
whether the source knows both candidates, but how the very production
of H is intentional under the description containing D.

Consider three different claims at the actual exercise:

1. n intends P and successfully realizes it in H.
2. n intentionally produces H under an independently understood
   description that includes D.
3. n knows every actual detail of H and intends, rather than merely
   foresees or permits, each such detail.

The first does not entail the second. An agent who intentionally
presses a key may make contact at an exact point without acting for
the sake of that point. An agent who authorizes a lottery can intend
a valid selection but not direct which number wins. These cases may
still involve genuine authorship of the coarse action. Claim 2
does not require a separate volition for each feature, nor does it
entail that every consequence of realizing that description is
intended under all its descriptions. Claim 3 is a stronger
particularity demand; permission of secondary agents must remain
distinct from directly decreeing every event. Reuse the
foreseen-collateral rival in #1459/#1458 (recipient-good application);
do not count this scope distinction alone as a new solution.

A new diagnostic is to separate **success-defined production** from
**antecedently meaningful content** in the proposed extrinsic account.
Here 'antecedently' refers to explanatory specification, not a
pre-creation moment. A predicate 'n successfully produced H for P'
cannot hold in an H-absent situation by its very success condition.
Its factive implication to H, or a theorem that all its actual
instances realize H, is no evidence of nontrivial perfect efficacy.
In ordinary actions, adoption of a description and success are
distinguishable: trying to realize D can fail. A perfect source
could have a genuine impossibility of failure without there being
an actual failing divine intention. But the content of the
intention, and the difference between successful and unsuccessful
realization of it, must be intelligible apart from defining the
intention by the observed success. This is a semantic requirement
on the proposed explanatory interpretation, not a claim that a
divine failure is metaphysically admissible.

Apply this to #555's exact `StrictEfficacy p w a x` (wherever the
rigid a is performed at an accessible world, x exists). `BeingCarriesAct`
makes performance necessary given the bearer's necessity. It cannot
be supplied for a description which merely names the source's actual
world-relative success. In particular, an invariant act of willing
a general good need not strictly necessitate a particular H merely
by being perfectly efficacious with respect to its general object.
If it is instead the same necessary act with H as its specifically
determined object and strict efficacy for that object, the old
`Core` excludes a contingent H-effect, provided the description
has a faithful rigid x interpretation. No formal extension of
the effect-being type to complete orders is claimed.

Thus perfect efficacy need not mean that all options licensed by
a general end become actual. Nor is it a license to call all
result variation intentional. The positive candidate must distinguish
selecting this D from merely selecting a policy under which either
D or its absence may occur. This is a useful check on the proposed
nondeception argument: general goodness plus actual production
is weaker than an intended truth-access policy, which is weaker
than the claim that the source specifically wills every evidence
record as accurate. The weaker policy can be the appropriate
normative target; no unrestricted reliability conclusion follows.

### 8. A concrete two-reading extrinsic fork

The direct-production proposal can be given two different explanatory
readings. Neither is a new registered disambiguation; these are proposed
interpretations to test with the existing rigid-act, reference and
causal dictionaries.

**A. Intentional exercise is the productive transaction itself.**
The source understands candidate realizations, necessarily wills a
primary good and freely causes H in the light of that good. The
particular act of creating H is individuated by the very directed
causal transaction, not by an additional intrinsic executive event.
Its truth includes H's actually being caused; H is not an antecedent
independent parameter needed to trigger the cause. This is the strongest
positive direct-agent reading. In creation ex nihilo there need not be
an earlier receiver, already existing H, or a chooser independent of
n. A primitive causal exercise can in principle distinguish production
from mere coexistence without a further causal event that produces the
exercise. No circular self-production of H is asserted.

The ontic explanation 'H exists through n's exercise' is not the
same as the semantic explanation 'the proposition that n created H
is true because this productive transaction obtains'. Factivity,
existential dependence of a relation on its relata, and productive
direction do not coincide. If someone instead explains H by a
distinct selection fact wholly explanatorily grounded in H, they
owe a defense against circularity under their accepted grounding
standard. If the obtaining transaction is primitive, the model
does not give a complete determining reason for that contingent
fact. It may satisfy nonnecessitating concrete existential
coverage if n actually produces H; it does not by that alone
satisfy complete reason closure over all contingent facts including
the transaction (e.g. a BCCF). No redefinition of 'fact' or
automatic exemption for nonconcrete relations. An impersonal
necessary producer can offer the same transaction-level concrete
existential account. The distinct personal benefit, if warranted,
is genuine apprehension and purposive direction of its exercise.

**B. A specific content-adoption relation is explanatorily prior
to realization.** Consider n knowingly adopting a candidate
specification D as a content, not relating to an already existent
creature. A candidate's intelligibility as a possible object need
not entail its actuality; no ontology of independently existing
abstract plans is presupposed. If adoption is independently
characterized and causally/volitionally relevant, the productive
act can be strictly efficacious for D without equating adoption
with successful production. This avoids the circular target-copy
reading. If n's intrinsic actuality is wholly invariant, however,
the varying adoption is either an externally individuated exercise
of n or requires a varying condition. No appeal to a pre-existing
created selector is available for the entire first-created order.
If the relation is a distinct contingent real determination in n,
the strong intrinsic simplicity reading has not been retained.
If the relation is a contingent fact concerning n and an
intelligible content, but is not an intrinsic determination,
the account owes its positive metaphysics (including the status
of such a relation when all proposed intrinsic grounds are fixed).
If it is merely a description whose entire differentiating
truthmaker is H's already obtaining, it has not supplied an
explanatorily prior specification. Aquinas's q.45 a.3 denies a
real creature-related determination in God; reading B therefore
cannot simply be ascribed to him by citing that passage. A
non-intrinsic action relation is not automatically a real accident
in either relatum, nor is every such relation admissible under
the strict account of simplicity. This distinction is the live
interpretation question, not a new proof of an accident-free
relational ontology.

**Difference-principle test.** The weak claim 'a distinct outcome
means there is some difference in the total productive situation'
is compatible with reading A: the particular causal transaction
differs. The strong claim 'any difference in actual output must
be grounded by a difference in the cause's intrinsic actuality'
would exclude both readings with invariant intrinsic actuality,
unless it were restricted or a varying independent condition
introduced. Ordinary causal explanation motivates a dependence on
real causal activity, but does not by definition establish the
strong intrinsic-supervenience premise. Human examples of a shared
intent producing differing movements often vary intrinsic states,
bodily circumstances or external conditions; they cannot establish
its negation at the ultimate-source scope. The mere fact that a
cause receives no perfection from an effect also fails to prove
that its particular exercise is not intrinsically individuated.
No passive change and no intrinsic modal variation are different
commitments. The first-cause/privation and active-power senses
from C2/C3 do not supply the latter on their own.

These readings need not exhaust interpretations. A contingent
intrinsic executive volition is a further option if strict
intrinsic simplicity is relaxed; necessitarianism is another if
contingency is denied. A nonnecessitating impersonal causation
account survives the same weak difference-principle and fact-level
closure tests. A legitimate application of A or B must say which
facts it treats as primitive, which are grounded and why there is
no extra independent causal contributor. No differential
probability or deterministic preference is imposed as the
criterion of actual directed agency.

### 9. Productive knowledge and causal direction

The intended description in reading B, or the description under
which reading A's action is genuinely performed, can be known
without being actual. Knowledge of the possible contents does not
therefore select one. Actual self-knowledge of n's exercise could
give a different ground of knowledge of H than observation of H.
This is a serious positive productive-knowledge proposal: a
composer intentionally playing a specified sequence may know
the notes through performing them, rather than through hearing
them after performance. It is not guaranteed to extend to every
detail of an agent's effects. If n's intentional object only
specifies P, knowing P through the act does not differentiate
H from J. A perfectly successful producer of P and a perfect
predictor of all details are not thereby a knower of every
detail through deliberate production. Huneeus §4 already
recognizes this difficulty; #1380 supplies the formal
discrimination and reference constraints, not a new route to
cognition.

One cannot infer cognitive scope from efficient-causal scope
alone without the actual intentional-understanding bridge.
The positive q.14 a.8/a.11 proposal combines intelligible
exemplarity and will, not just undirected causal power. If
reading A's precisely directed transaction is the basis of
nonpassive productive knowledge, self-knowledge must include the
extrinsically individuated exercise, rather than only a fixed
intrinsic projection. If reading B is adopted, actual knowledge
of which content is adopted must be grounded in the adopting
exercise, not inferred from an output label. In either case the
actual reference/apprehension and truth-discrimination interface
stays open. Do not let naming a transaction as intentional
prove the #1380 bridge.

### 10. Provisional judgment, constraints and next discriminating work

The substantive advance is a narrower separation of one-act
rational order, exact-outcome intentionality, content-specific
efficacy and the source's own exercise fact. The first has a
positive explanatory reading without a sequence of intrinsic
causes. Nonnecessitating direct production is a serious
philosophical account, not a refuted impossibility; it can
distinguish dependence of a created effect on a source from
brute concrete actuality. But reading A does not by itself
supply an independently content-specific decree or a complete
determining reason for its actual exercise; reading B makes
that explanatory role explicit and bears a stronger
simplicity/intentional-ontology burden. The strict intrinsic
difference principle is not established by the available
examples, and neither is its negation at the divine case.
Retain suspension about the complete classical-theistic
synthesis, with a positive conditional preference for a real
reason-directed producer over a source that merely labels
its output. This is not a winner against an equally productive
impersonal account on concrete-existence adequacy alone.

The next narrow task should test the truth conditions for
'intentionally produces x for R' when there is no additional
intrinsic executive act: is independently intelligible
content plus direct source-level agency enough for a true
de re specification, or must the particular content fix
an intrinsic difference? Test the strongest version of the
direct-production proposal under explicit scope of intended
descriptions, causal direction, nonfailure and reason relevance.
If a distinct content-adoption fact is required, assess whether
its reality can be only effect-side under the q.45 relation
reading without target-copying, or whether strict simplicity
must be weakened. Horizontal continuation: apply the result
to #1459's particular existence-good willing and #1380
productive knowledge, not the assumption that goodness or
capacity already entails either. Reassess if the stronger
difference principle can be defended for intentional acts
without circularly requiring deterministic causation; or if
an account shows why a determinate productive relation can
constitutively direct its effect without an intrinsic
selection-state or independent contingent condition.

Connection unchanged: #1737 targets 2757f6a3-2d14-5033-9740-2c36a678ce73
and 1822b59d-1040-57e4-8991-f7862db26355, #1730 target
a7bbd2fd-242c-5097-a9a3-581d25835890. Actual intentional
exercise, identity with the same source's causal-esse
production, and reference/knowledge remain OPEN. Existing
`GodHasIntellect` and `GodHasWill` capacities do not supply
these. No change to C2, #1459, #1380 or historical-trace
files. No new registered theorem, statement, claim, sense
or root edge. Canonical CLI/Lean and independent semantic
challenger unavailable here; author-side scope sweep only.
Expected premise change none (not a computed delta).
The existing 7d015c02 attempt is supplemented with this
narrower research finding; the earlier checkpoint remains
intact. Independent final semantic review must challenge
the distinction between the obtaining causal transaction
and an independently meaningful intention, the conditional
no-mediator regress, the granularity claims and the q.45
interpretation. The review and disposition are recorded in PR #1911.


## Exemplar as practical measure: can specificity belong to the exercise? (2026-11-23)

Continuation of §§6–10, prior head eec73ea4bf32706f814d53ff5ef300849598f012.
Main at dispatch f93b376f390bbd480b9a7705404c001622bdb553 (C2 note and
attempt advanced; no overlap). Fix the same actual n and two candidate
complete creaturely specifications D and E, each independently intelligible
and not merely the descriptions "whichever world obtains" and "another
world". Their incompatibility as specifications is stipulated for this
comparison; their metaphysical admissibility is not established. Distinguish
a specification from its actual concrete realization x. The following is
a proposed philosophical application of #1380's reference-ground and
error-norm test and #555/#462's same-token scope, not a new formal model.

### 11. Fixed exemplars, variable practical role

Selected readings, no new pinned attribution or source claim:

- Aquinas, [ST I q.15 a.1–3](https://www.newadvent.org/summa/1015.htm).
  A.2 co. and ad 1–4 distinguish the intelligible principle by which
  God understands from the many things understood; the latter need not
  be multiple actualizing forms in God. The multiplicity of ideas is
  understood in relation to possible creaturely likenesses of the one
  divine essence, not supplied by actual creatures. The responses
  distinguish understood relations from real relations in God. A.3
  distinguishes ideas as principles of making and knowing. This is
  evidence for a positive *availability of determinate exemplar content*
  account under simplicity, not a proof of the modal possibility of
  every proposed description or of variable selected content.
- [ST I q.14 a.8–9, a.15 ad 1–2, a.16](https://www.newadvent.org/summa/1014.htm).
  Knowing an operable form as such does not by itself determine
  production; the a.8 account adds will. A.16 distinguishes knowledge
  practical by its end from knowledge of what can be made but is not
  made; a.9 distinguishes simple intelligence and vision. A.15 ad 1
  distinguishes knowledge from predicates such as creator that concern
  creatures as they are in themselves. This last qualification prevents
  simply treating actual singular cognition as another extrinsic
  creator-label. The text does not give a possible-world semantics for
  the variable role of a particular exemplar.
- [ST I q.19 a.2 ad 1, ad 4; a.3 ad 5–6](https://www.newadvent.org/summa/1019.htm)
  connects the simple will to many willed objects through the primary
  divine good; it expressly distinguishes the necessary will in itself
  from nonnecessary willing of finite things.
- [SEP, *Action*, §4 Practical Knowledge](https://plato.stanford.edu/entries/action/#PraKno)
  and [*Intention*, §3–4](https://plato.stanford.edu/entries/intention/)
  (secondary navigation and interpretation, not a direct Anscombe
  witness). The practical-knowledge account presents the agent's
  understanding under an action description as specifying the action,
  not necessarily an additional efficient cause. The intention supplies
  a standard for performance; theoretical knowledge instead answers
  to its object. The literature disputes the relevant efficient-causal
  interpretation and whether practical self-knowledge extends to actual
  effects. This motivates the proposed test; no divine conclusion is
  attributed to Anscombe.

The q.15 distinction is a more specific response to the claim that
distinct intentional *objects* require distinct intrinsic actualizing
forms. It is not yet a response to the claim that distinctly *adopting*
objects requires a distinct intrinsic actuality. Hold both D and E
understood, in the same act of understanding in both candidate worlds,
and hold n's primary end and power fixed. There remain two different
roles for a content: being intelligible as something n could produce,
and being the measure under which n actually produces. The former
can be fixed while the latter varies on the proposed account.
Necessity of the intelligible form repertoire supplies neither
practical adoption nor the actuality of any of its members.

### 12. The practical-measure test: a stronger candidate than output matching

Compare a finite artist producing a figure under the independently
understood specification "equilateral triangle" with an artist
intentionally generating any triangle by a random procedure whose
result happens to be equilateral. Also compare an artist who intended
a scalene triangle but whose execution error yields an equilateral
one. Each can know the two specifications, value geometric beauty
and genuinely cause the actual equilateral figure. Yet the standard
by which success as an intentional action is assessed differs: an
equilateral figure fulfills the first specific intention, fulfills
the second coarse intention without being specifically required by
it, and fails the third specific intention. A bystander who knows
the resulting figure perfectly is a fourth, nonproductive comparison.
The cases do not have equal intrinsic human states; they are a test
of intentional specification, not counterexamples to divine
intrinsic-supervenience. Neither is a model of ex nihilo creation.

This supplies a candidate positive interpretation of the "for R"
in §§2 and 7: an intelligible specification D must be operative as
a measure of the particular productive exercise, so that conformity
to D is a success condition for that exercise **under the description
D**. D itself can be evaluated without first consulting the output.
The action's rational structure makes the intended object a standard
of production rather than merely a true description of the result.
This goes beyond `TracksSelectedCreation`: a world-label table
cannot by its match establish which norm governs production.

This is not an extensional definition of intentionality or a
sufficient condition consisting of any norm plus output. A programmed
machine can have a success standard set by someone else; a lottery
policy can be intentionally chosen while a specific draw is not; an
artificial system could genuinely implement intentional guidance on
some accounts. The nondeviant *actual operation of the source's own
apprehended specification* is essential. Impersonal norm-like
production is not excluded by calling a standard "practical".
A genuine functionalist account of cognition/agency would be credited
if it satisfies the same demands. The ordinary comparisons motivate
the distinction without establishing its realization at a simple
source.

The divine nonfailure test can now be expressed without imagining
an admissible world in which God wills D and fails. D and E have
different fulfillment conditions as specifications; if E excludes D,
E would not fulfill a D-specific intention. This is an evaluation
of contents, not a counterfactual asserting a metaphysically possible
failed divine exercise. If a separate efficacious D-directed act is
given and performed, the existing `StrictEfficacy` pattern can
apply to an appropriately interpreted rigid effect x. If the
exercise is individuated as the actual successful production of x,
its implication to x is constitutive and does not supply strict
efficacy of the antecedently specified intention by itself. No
extension of the effect-being type to a complete description is
silently made.

### 13. What the nonintrinsic thesis must assert, and what could defeat it

Distinguish the intrinsic identity of the actualizing operation
from the practical content specifying a productive exercise.
The strongest direct-source account takes the operation to be
the source itself, with no received executive form, and the
specific exercise to be n's actual production in the light of
one of its understood exemplars. The form under which the
effect is produced is a constitutive specification of the
exercise, not a new efficient cause standing between n and x.
This is the positive hypothesis, not a consequence of the
q.15 source. The object as understood need not be an
independent concrete object causing n, nor an already produced
x. An independently intelligible D is not itself a contingent
external causal selector.

The rival grants the entire fixed repertoire and the one
intrinsic act of apprehending it, but holds that whether D or E
is the measure actually adopted must be determined by how the
agent's immanent willing is intrinsically actual. This is stronger
than insisting that the *action* be actually specific. It asserts
that the adopted practical role of a fixed content cannot vary
while intrinsic actuality is fixed. Positive warrant: an agent
who understands both D and E yet actually intends D rather than
E differs in practical orientation, and the usual examples make
that orientation attributable to the agent, not just the world.
An independently specific intention to D could remain true
when ordinary execution fails, so the intentional role does not
generally consist in the actual object being produced. These
considerations motivate the stronger thesis but do not establish
that attribution to the agent means intrinsic determination
rather than a real exercise relationally specified.

A precise dispute for the same n, w and admitted alternative v:
with identical complete intrinsic actualities, fixed intelligible
D and E, and no varying independent creative enabler, must the
actual practical role of D be identical at w and v? The intrinsic
account affirms. The extrinsic account denies in at least one
such genuine pair while keeping the practical role explanatorily
substantive. This is a dispute about the actual intentional
role, not about a mere `W → B` world function, bare reference,
the existence of the source or the plurality of represented
objects. One-sided failure to establish the universal thesis is
not evidence of the real alternative needed for its negation.

If the intrinsic thesis holds, a fixed necessary immanent
operation plus independently fixed repertoire cannot vary its
D-specific adoption without a varying enabler. With a genuinely
D-specific strictly efficacious rigid act everywhere the #555
core applies. Without intrinsic invariance, a contingent
executive state remains a serious nonclassically-simple personal
option; without strict efficacy or contingent H, other existing
branches survive. If the extrinsic thesis holds, the varying
exercise can be a candidate nonnecessitating concrete-existence
explanation without such a state. But why the particular
exercise obtains remains open under complete determining
fact-level closure. No special stop for n if the same demand
is imposed on impersonal production.

The strongest reply to the rival is that distinct practical
specification might be formally constitutive of a directed
source-level activity, rather than a new intrinsic antecedent.
An account of intentional action as an activity, rather than
an executive mental occurrence plus event it causes, makes
this a serious proposal. Yet if the only explanation offered
for the actual adoption of D is the fact that x realizes D,
the proposal fails its own practical-measure test: the third
artist and lottery controls pass result-conformity too.
An ordinary action can be known under a particular description
through its exercise. For n, however, the hypothesis that its
own activity is *already* practically D-directed must receive
substantive warrant; formal-causal language by itself supplies
none. The q.15 account of multiple understood ideas is not
an account of the obtaining of the productive relation. This
is the remaining exact distinction, not another label for it.

### 14. Two downstream consumers and assessment

For #1459's `CausalExistenceWilling`: if the existence of
a particular recipient x is genuinely part of D as the
operative intentional measure of n's production of x, the
particularity objection is weakened. One still must establish
the recipient-directed good rather than just instrumental
ordering, identity with the same `CausesIn n x esse`, and
actual goodness/intention premises. Foreseen collateral
production remains distinct; a perfect means/end fit or
knowledge of x does not imply the relevant willing. No
`CausalExistenceWilling` proof is claimed. For #1380's
productive-knowledge route: if actual practical knowledge
includes the adopted measure and n knows its own effective
exercise, the content of that knowledge can explain a
particular effect's being known without passive reception,
conditional on fidelity, reference and factivity. Knowing
all possible measures, or reading an effect as correctly
matching a measure, does not provide the actual knowledge
premise; the fixed-intrinsic epistemic-row supervenience
objection remains. Nor does an operative coarse measure
give knowledge of every secondary contingent effect.

Provisional assessment: q.15 gives positive warrant within
the classical account for distinguishing intentional content
from intrinsic cognitive multiplicity. The practical-measure
proposal sharpens an actual difference between purposive
production and lucky conformity without defining success as
the mere observed effect. This makes a content-specific direct
exercise a more intelligible candidate; it does not establish
its compatibility with strict simplicity. The strongest
intrinsic-orientation rival can accept the same action norm
while requiring it to be intrinsically realized. Maintain
the existing underdetermination judgment at that exact
realization bridge. Do not claim a metaphysical countermodel,
a new formal result, a root support alternative or a defeat
of an impersonal producer.

Next discriminating test: compare rival ontologies of
*exercise of active power* (an immanent event necessarily
requiring intrinsic determination versus a transitive
productive activity individuated by its intentional object).
Ask whether direct actuality of a particular exercise can
be primitive without being an additional intrinsic perfection,
and whether a genuinely operative practical norm can be
constitutive of that exercise without a separate real
determination in the agent. Reuse the causal-activity senses,
the #555 strict-act reading and the #1731 immanent-intellect
interface; not another table of matching world labels.
If the action account is viable, apply it to #1459 under a
fixed recipient and #1380 under a fixed determinate content.
If it is not, identify the weakest defended intrinsic-state
or content-supervenience commitment that forces revision of
the simplicity package. Reassess also if a substantive
impersonal norm-guided account meets the same explanatory
standard.

Self-sweep: no new registered statement, formal consequence,
definition, result, claim, source binding or root edge.
The distinctions are analyst tests. The source reading
concerns multiplicity of understood objects, not varying
world-indexed adoption. Existing #1380/#555 scopes are
unchanged; #1459 recipient-directed and esse bridges remain
open. Same attempt 7d015c02, existing note only. No new
verified result or computed frontier delta. Canonical CLI,
Lean and independent challenger unavailable in this session;
author-side scope check only. Independent semantic review
must challenge §§11–14, especially the proposed practical
measure's actual explanatory role, the precise scope of
q.15, and the unresolved strong intrinsic-orientation
principle.


## Active power, immanent operation and the essential object of an act (2026-11-23)

Continuation of §§11–14, prior head e5e728d280a0d01a666b37f51d7c2046790b7a73;
main f93b376f390bbd480b9a7705404c001622bdb553 at dispatch. #1912 owns the
separate many-receivers C2 problem; no changes to its paths. Fix n, the actual
distinct effect x, the candidate specification D, and a genuine alternative
in which x is absent, **if warranted**. Do not infer such an alternative
from merely describing it. Question: can a particular exercise of n's
active power be intentional without being another intrinsic actuality?

### 15. Actualizing another is not the same as being actualized

Selected source readings (orientation, not newly pinned claim bindings):

- Aristotle, *Physics* III.3, 202a13–202b22, [Hardie/Gaye translation](https://classics.mit.edu/Aristotle/physics.3.iii.html).
  The actualization in the movable is shared in the relevant sense with the
  mover's acting, without identity of the accounts of doing and undergoing.
  Reuse the existing `MotionLocatedInMovableReading`,
  `MoverMovedShareOneActualityReading`, and
  `TeachingLearningSameMotionDifferentAccountReading` in
  `TruthCore/Greek/Aristotle/Physics.lean`. The shared motion does not
  establish that the mover has no other intrinsic changes or dispositions;
  III.2 explicitly discusses reciprocity by contact.
- Aquinas, [*De potentia* q.1 a.1 co., ad 1, 5–6, 15–18;
  q.3 a.15 co., fourth argument and ad 14–20; q.7 a.10 co., ad 1–2](https://isidore.co/misc/Res%20pro%20Deo/Aquinas/Bilingual/english/QDdePotentia.htm).
  Q.1 distinguishes operation, first act and active power, and distinguishes
  power as a principle of an effect from a principle of an operation that
  is identical to the divine essence. Crucially q.3 a.15 does **not** simply
  extend the transitive-action analysis to divine action: it locates the
  divine action on the immanent intellect/will side of the distinction.
  Q.7 a.10 denies an intermediary action and a creature-related real
  determination in God, contrasting the natural agent's situation.
- [ST I q.25 a.1 co./ad 1–4, a.5 co./ad 1](https://www.newadvent.org/summa/1025.htm)
  distinguishes active from passive power and identifies the divine
  operation and power with the essence; the one wisdom/will/power is
  conceived under different explanatory aspects. A.5 argues that finite
  orders do not exhaust the divine end, hence wisdom and justice do not
  restrict divine power to the actual order. [Q.45 a.2 ad 2, a.3 co./ad 1–3](https://www.newadvent.org/summa/1045.htm)
  distinguishes creation from a change of a pre-existing subject and
  distinguishes active creation from the creature-side real relation.
- W. Matthews Grant and Mark K. Spencer, *Activity, Identity, and God:
  A Tension in Aquinas and his Interpreters*, Studia Neoaristotelica 12(2)
  (2015), [author text](https://philarchive.org/archive/GRAAIA-4), pp. 12–15
  (object essentialism and five positions), 40–42 (contrastive explanation),
  53–56 (primary object and dependence-based restrictions).
  Extracted text of the specified sections inspected; page-image fetch
  returned HTTP 403, so no image verification or new pinned attribution.
  The authors distinguish identity claims about divine actions from
  essentiality of their objects; they do not agree on a single winner.

A motion being actual in the patient can be the mover's acting under a
different account; it does not follow that the motion must be a second
alteration in the mover. This undercuts the inference from an actual
causal transaction to an additional passive actualization in the source
*merely by virtue of being the cause*. It does not prove the negation of
intrinsic state variation for ordinary agents with differing outputs.
Nor can the motion reading be substituted for `CausesIn n x esse`:
creation has no pre-existing patient undergoing motion. The q.45
creature-side dependence is the relevant extension, with applicability
to the selected source still open.

The stronger classical proposal is not an activity issuing from n,
an intermediary which subsequently creates x, or an accident n must
receive. The source's immanent operation is itself the active causal
principle; x's being-from-n is real without contributing an additional
perfection to n. It is possible to grant this account of **where
actualization is realized** while denying its account of **which
intention the operation realizes**. Pure actuality need not be
restricted to inert actuality, but absence of passive reception does
not entail modal invariance of all specific intentional facts.
The distinction has genuine positive source support; the specific
intentional bridge remains substantive.

### 16. The essential-object test, not another collapse theorem

Fix an intrinsic operation a, the same rigid bearer n, and the actual
specific willing of x (not a name for whichever output happens to occur).
Three independent claims in ordinary language:

- **Identity:** a is n's own necessary intrinsic actuality; the
  performance of this rigid operation follows wherever n exists.
- **Secondary-object essentiality:** wherever this very operation is
  performed in the admitted alternatives, it is specifically directed
  to x under the relevant intentional description.
- **Efficacy:** wherever n specifically wills x in that sense, x exists
  (unconditional creative decree, not bare approbation or permission).

With necessary n, the first supplies `SameActEverywhere` through
`BeingCarriesAct`, and the latter two jointly supply `StrictEfficacy`
on the same rigid x, if their intended interpretation fits the existing
profile. The #555 core then excludes an accessible absence of x.
No new proof or type is needed. Merely locating the productive effect
in the creature does not escape this application if the immanent
creative willing is itself necessary and x-essential. Conversely,
necessary a need not be a necessary specifically-x-directed exercise
unless the object-essentiality bridge is warranted. The negation
relevant here is a genuine accessible case with a performed and not
specifically-x-directed, not the observation that a could be described
generically. Such a case would have to preserve n, a, primary good
and the actual intentional interpretation; the existing output-label
controls do not establish it metaphysically.

The strongest objection to object nonessentiality is that intentional
actions are not indifferent to their objects: someone choosing a
particular means, rather than another, seems to perform a different
choice. Species of action, individual operation, complete description
of a transaction and intrinsic actuality of its agent are nevertheless
not interchangeable. An act's practical kind can be specified by an
object without proving that every secondary object is essential to the
numerical identity of its underlying operation. The converse is also
not automatic: one primary end can organize many different genuinely
specific choices. Grant and Spencer's primary-object proposal therefore
requires an additional individuation principle; their own pp. 53–54
acknowledge the limitation.

Compare four relevant packages without claiming exhaustiveness:

1. All specific immanent creative objects essential to the identical
   necessary act: conditional collapse above, even if the actualizing
   relation is on the creature side. A necessitarian accepts that cost;
   special identity logic or weaker essentiality is a further defense,
   not assumed here.
2. Only the primary good essential to the immanent act; its contingent
   secondary term belongs to a substantive directed exercise. This
   preserves classical identity, avoids the essential-object premise
   of the core and can preserve genuine intentionality if its practical
   measure is operative. It owes the latter interpretation.
3. All particular creature-directed acts essentially have their objects,
   but those fully individuated acts are not identical to the substance
   (an extrinsically individuated whole/transaction); the intrinsic
   principle is n. This avoids the identity premise for the whole
   creative act but must address the source texts' immanent-act identity
   and ensure genuine apprehension/will rather than mere productive
   power. It cannot label all creature-directed cognition extrinsic
   and infer the existing intrinsic-noesis bridge from that label.
4. A contingent distinct intrinsic executive state: the familiar
   personal-source alternative; preserves content-specific efficacy
   without requiring object nonessentiality, but revises the strong
   simplicity/intrinsic-invariance package. It does not settle why its
   contingent state obtains.

These distinctions are adapted to the existing #555 token semantics;
the four packages are not a reproduction of Grant and Spencer's
five-position taxonomy. In particular their separation of immanent
and transitive act identities is not the same as the fourth package
above.

### 17. A substantive comparison: purpose, selection and the real relation

The positive reason for restricting object essentiality is not merely
the inconvenience of collapse. For receptive cognition or desire,
an object can contribute to specifying the agent's operation; a
nonreceptive productive source has the opposite causal direction.
Its own known primary goodness can supply the constitutive intrinsic
principle, while secondary goods are dependent finite expressions of it.
Q.25 a.5 gives a substantive reason that no finite expression exhausts
that goodness. But nonexhaustion of an end does not logically exclude
a uniquely mandated finite option: an ordering rule could select one
option without that option exhausting the end. Nor does every admissible
description automatically become a live alternative for a particular
act. The positive case for nonessentiality is therefore cumulative
with active-power, real-possibility and normative-policy commitments,
not an inference from infinity alone. The impersonal rival can also
distinguish a fixed active nature from variable outputs; the specific
purposive role remains the difference at issue.

Now test the creature-side relation interpretation with two proposed
readings of the SAME actual n producing x. Both retain actual
productive dependence, full availability of D as an understood
exemplar, and conformity of x to D:

- the intrinsic operation is actually exercised for D as practical
  measure of x's production;
- n exercises a coarse policy or a blind productive power, with x
  conforming to D only as a result (the #1459 foreseen-collateral case
  is another version, not identical to blind production).

The thin actual `CausesIn n x esse`, the modal causal edge, and
conformity cannot distinguish these descriptions. This is an
interpretation comparison, not a claim of two admissible worlds
with every real relation identical. If the creature-side relation
is merely existence-from-n with no intentional structure, and the
only additional information is x's conformity to D, it cannot
supply the proposed practical-measure criterion. If the productive
dependence itself is an intrinsically directed **kind of exercise
by the agent** (not an independently operating created thing),
the exercise has content beyond its thin causal encoding. This
stronger interpretation must be defended, but does not require
an additional efficient cause or a separate real accident in n by
definition. To call its actual obtaining a primitive fact is a
possible metaphysical commitment; it is not a reason for an
arbitrary exception to a determining PSR.

The relevant positive claim is thus about what the relation is,
not simply where it is. A real effect-side relation can be
constitutive of x's being-from-n without causing n to be or to
acquire an operation. Its converse denomination need not denote
a second entity. This avoids a circular demand that x cause its
own existence: the explanatory fact is x's being *produced by n*,
not x's bare existing, and n's operation is causally prior, not
temporally prior. The direction of causation does not itself
ground the particular fact that this operation is practically
D-directed. If that fact is reduced to success-conformity alone,
the lottery and error comparisons (§12) still apply. If it is
accepted as genuinely directed and nonnecessitating, it supplies
a positive explanation of actual x without a separate intrinsic
executive state; it does not supply exhaustive determining
contrast at the level of the exercise itself. Apply the same
test to an impersonal producer's primitive exercise.

### 18. Assessment and reuse

Prefer, **conditionally within strict classical simplicity**,
the distinction of one necessary immanent operation with a
primary essential object and nonnecessary creature-directed
terminations over a proposal requiring a separate transitive
divine operation as an intermediary. The preference is supported
by q.3 a.15, q.7 a.10 and q.25 a.5, not a general philosophical
refutation of other source ontologies. Positive advance:
there is no valid move from active power as such or the effect's
actualization to another intrinsic passive actuality of n; and
even the stronger immanent-operation identity needs specific
object essentiality and efficacy to generate the collapse
objection. The proposed nonessentiality restriction has a
positive rationale in nonreceptive production, nonexhaustion
of the divine good, and the distinction of causal principle
from concrete transaction. None supplies the actual particular
practical-role bridge unconditionally. Remain underdetermined
about the jointly instantiated classical synthesis and a
genuine alternative to x; do not weaken the already reviewed
C2 judgments or infer possible absence of n from active power.

For #1731/C4 reuse `IntentionalExemplarExtension.EffectExemplarCoverage`,
`CognitivelyTakesUpExemplar`, and the `ImmanentSelfPresence` scope:
the existing conditional content and actual-uptake predicates are
not the same as choosing a specification. The module's
`RootToEsseCauseAt` remains open; no new bridge from virtual
production to intrinsic understanding. For #1459, distinguish
intending x's existence-good under a specific practical object
from causing x under a coarse policy; recipient-directed good
remains additional. For #1380, actual singular knowledge
requires apprehension of the varying term, not another source
intrinsic species by assumption. A primary-object argument
does not prove the claim that all actual-contingent contents
are truly known. The n-to-a-to-x interpretation and fact-level
closure seams remain shared with #1730 and #735/#750.

The next material discriminator is no longer another account of
the location of action. Test **restricted object essentiality**
directly: whether the necessary primary intentional actuality
can be intrinsically complete without its specific contingent
practical term being part of its identity. Compare the
same-agent, same-primary-end, different-means cases with the
nonreceptive analogue, and distinguish an independently
specified intention as a real exercise from the merely
world-relative denomination. A substantive constitutive
account would have to meet the practical-measure and
nonaccident tests simultaneously; otherwise determine which
explicit simplicity, efficacy or contingency premise must
be revised. Horizontal support from real powers/essence and
actual intentional cognition is needed rather than repeatedly
relabelling the selection relation. This is a precise
remaining warrant problem, not exhaustion of the research.

Self-sweep: all new arguments are analyst applications, not
Lean-certified results or new corpus statements. Existing
Physics readings are motion-scoped, and #555's rigid x is
not an entire description. No identity of `m.grounds`,
`CausesIn` and `Ontic.Causes` asserted. Sources consulted
in the stated scope, no new attribution claim. Same attempt
7d015c02, no new graph edge, expected premise delta none;
canonical CLI and independent semantic challenger unavailable.
Review must challenge the immanent/transitive distinction,
the modal object-essentiality scope and the alleged thick
effect-side intentional relation. CI and actual computed
premise comparison outstanding.


## Restricted object essentiality: the two relations and particularity of the recipient (2026-11-23)

Continuation of §§15–18 on prior head f13c6c03b68d7f50cec90de7e80ada8d9eb93d48.
Current main at dispatch f9c1f2ef6bcc56f341c95a70f3815834827595dc.
#1912 is now merged; reuse its same-giver/individual-identity distinction
without reopening C2. #1913 owns the independent brute-contingency propagation
question. Fix the same source n, intrinsic operation a, actual distinct effect
x, and an intelligible description D of its production. No genuine alternative
is established by stipulating a model or description.

### 19. Direct source warrant for the distinction at issue

New selected reading: Aquinas, *De veritate* q.23 a.4 co., ad 2–3, 6–8,
11–16, and a.5 co./ad 1–3, [Latin](https://www.corpusthomisticum.org/qdv23.html)
and [English](https://isidore.co/aquinas/english/QDdeVer23.htm). Particularly
[56440–56441] (a.4 ad 15–16). This is a source reading for research
orientation, not a new pinned attribution or mechanically verified premise.
The Latin was checked against the English, particularly the scope of
the reply about the two relations.

A.4 ad 15 explicitly distinguishes the will's relation to its object
as willed from its relation to that object as to be made actual. The
latter presupposes the former in the order in which we understand
voluntary production. Aquinas denies absolute necessity of the first
relation, while affirming the efficacy conditional for the embracing
will (*voluntas beneplaciti*). Ad 16 rejects the need to interpose a
contingent middle cause between the two orders to avoid absolute
necessity. Ad 13 locates the nonnecessity in the reference to producing
the thing in its own nature, not in an additional actuality inhering
in God. Ad 6–8, 12–14 distinguish this from a temporal change of will.
The a.4 body includes the possibility of another creature representing
the divine goodness equally nobly, and denies the need for the whole
creation for God's own goodness. A.5 co./ad 1 makes the intended mode
of the effect relevant: efficacy of a will is fulfillment of the
specification, not transfer of the causal source's own mode of being
to the effect. Do not infer that the actual effect could fail while
the identical specific efficacious decree holds at an alternative.
The separate scope of the effect's contingent causal mode and the
modal status of the decree must remain visible.

This reading supplies unusually direct textual warrant for the
two-relations architecture proposed in §8B, subject to a crucial
qualification: the text explicitly speaks of an order of understanding.
It does not supply an independently existing contingent executive
event or a modern hyperintensional grounding theory. It is not an
argument that the first relation is a temporal antecedent, or an
extra real intrinsic determination in n. Nor does it automatically
settle what makes the first relation obtain. It is stronger evidence
for Aquinas's intended account than merely reusing q.19 a.3's
nonexhaustion analogy. It counts against a reading that treats
specific willing as nothing but a retrospective description of the
actual product and then claims to have explained the product by
that description.

Reuse #555's Core and #462's SelectedEffectBridge, not a new
certificate: distinguish necessary intrinsic a, actual adoption of
D, and effective realization of D. At an appropriately interpreted
rigid effect x, if the necessary a essentially has the specific
object and specific creative willing entails x's existence in every
accessible world, the old strict-efficacy contradiction follows
with x's actual contingency. Aquinas's proposed denial concerns
the first relation's absolute necessity, not the second conditional's
validity. The substantive question is whether the first relation can
be actual and genuinely directive without constituting a further
intrinsic actuality. A.4 ad 15 gives evidence that this is the
intended explanation, not a deduction of its metaphysical success.

### 20. An expressive end differs from an acquired end

The ordinary analogy of selecting means to happiness is incomplete.
Aquinas's positive reason in a.4 co. is that divine goodness is
already perfect, rather than a perfection realized by producing
creatures. Compare two uses of the same recognized good:

- An agent who needs to reach a destination may be bound to take
  the only available route. The means supplies an actuality the
  agent lacks; if the means changes, the agent's satisfaction can
  depend on that change.
- An agent who already possesses a good can intend to share it.
  A particular gift can realize the recipient's good without
  constituting or completing the giver's intrinsic perfection.
  The particular recipient and gift can nevertheless matter to
  what the agent intentionally does.

The positive reason for restricting secondary-object essentiality is
that a dependent, expressive termination need not supply the
formal actuality by which the giver acts. This does not apply just
because an agent is called divine or foundational. The giver must
already possess the good, the effect must be genuinely produced
rather than be an independent recipient supplying the needed
perfection, and the productive direction must be shown. The ordinary
gift example is not a witness of same-intrinsic-state varying
choices. It explains why the necessity of a primary end need not
be transmitted via *dependence on the means*, not why this particular
exercise is metaphysically possible.

Two further premises are not interchangeable: (i) D is not
constitutively necessary to the source's own goodness; (ii) the
source's essential rational policy does not require D. A giver
who lacks nothing might nonetheless be bound by a unique moral
requirement to make a particular gift. Even a genuine equally
noble individual alternative does not establish substitutability
within a complete order: changing a creature could affect other
goods, recipient obligations and the compatibility of the history
as a whole. The a.4 equal-nobility claim is positive source
support for the alternative, not an all-orders admissibility
proof. Reuse #1875's unique/tied optimum and omission controls.
A policy can require some realization while not requiring any one
particular realization; whether omission is admissible remains
a separate question. The same constraints apply to an impersonal
necessary producer with an essential normative/teleological
policy if such a policy is defended.

### 21. A narrower, constructive particularity argument

Do not make the entire problem depend on the controversial claim
that every created individual must be picked out by a separately
individuating intrinsic intention. Distinguish intending that
an entity of a determinate kind be produced, intending an actual
entity's production under an adopted description, specifying its
numerical identity antecedently, and intentionally specifying
every fact about it. Those have different burdens.

Consider a potter intentionally making two cups for two people.
The cups may be qualitatively indistinguishable as cups. The
potter's practical plan deliberately specifies two instances and
their respective recipient roles, rather than an intrinsically
individual name or primitive thisness for each cup. Once the plan
is nondeviantly executed, each cup is deliberately made, not
merely a fortuitous byproduct. The maker need not have identified
an already existent cup before making it. A bystander may describe
each cup equally accurately; a kiln accident producing a third
cup does not make the third a deliberately made gift. A generic
aim to make at least one cup does not intentionally adopt all
further cups merely because they satisfy that aim. The adopted
distributive scope and the actual production as its fulfillment
matter. These are ordinary finite agency examples with intrinsic
processes and pre-existing materials, not same-state or ex nihilo
models.

This suggests a specific sufficient-account candidate for intentional
production of x without a separate pre-production singular
identification of x: a genuine adopted content independently
specifies a productive role or a distributive range, the source's
exercise nondeviantly produces x *as an instance covered by that
role*, and x's actual concrete identity is supplied by the
productive realization and its individuating principles. The plan's
coverage must not be defined as whatever the source happens to
produce. A creator can in principle intend individuals through
their originating productive role, rather than an intrinsic
representation already containing their existence. No inference
is made from a description to actual referential success or from
origin to all essential properties. In particular, the same ultimate
giver alone cannot fix the identity of x: the two-oak result and
comparison in #1912 explicitly exclude this shortcut. The candidate
needs the actual individualized effect, not the common source as
an identity key. In another admitted alternative, the very same adopted
content could be fulfilled by a different eligible product y. Intentionally
producing actual x under that content does not supply prior selection of
rigid x, or the strict efficacy for x used in #555.

For #1459 the candidate reduces a *possible* application burden:
willing this recipient's good need not require a separate
individuating executive decision per recipient if a genuinely
adopted distributive content includes that recipient's existence
as a good for it, and the same source actualizes it as such.
Neither mere knowledge of the whole nor production of every member
entails the distributive intention. The foreseen-collateral rival
still stands, and actual recipient-directedness, coextension,
causal-esse and intent-to-effect bridges are still required.
Use the existing a94c5dfc / c691e3d0 route and its restricted
47c6da1b consumer, not a new route asserted to bypass the premise.
A comparable account of de re practical knowledge for #1380 needs
actual apprehension of the individualized product through the
exercise; quantificational intention and its fulfillment do not
entail complete singular knowledge.

The result is narrower than the original complete-order question.
A source might purposefully create each creature under relevant
descriptions without selecting every individuating detail of the
whole history, particularly if it intends secondary agents to
exercise real powers. Even genuinely intentional particular
production in this sense does not explain choosing an entire
specific world rather than every rival. Keep the complete-order
contrast and the actual obtaining of the volitional relation open.

### 22. Assessment and revision

The new source evidence favors the two-relations interpretation
as Aquinas's positive proposal; compare Grant–Spencer (2015),
*Activity, Identity, and God*, pp.54–56, including n.103 (a primary
end does not individuate finite acts) and n.104 (different effects under
their positions 4 and 5 do not make God's literal act different). The latter
leaves a challenge for a distinct practical exercise. [Text](https://philarchive.org/archive/GRAAIA-4)
read in extraction; page images again inaccessible (HTTP 403).
ST I–II q.18 a.6 co./ad 3 distinguishes the species of internal
and external human acts, not numerical identity across worlds.
Neither textual account proves restricted object essentiality.
The exemplar account makes fulfillment conditions independently
intelligible. Ordinary distributive agency gives a reason to distinguish
intentional production under a role from antecedent singular selection.
Applying this account to actual adoption by a simple creator remains open.

Moderate confidence in the explanatory relevance of expressive
rather than acquisitive ends and the ordinary distributive
intention distinction; retain suspension on actual contingent
termination compatible with strict intrinsic invariance. The
strongest rival agrees that a complete intrinsic principle need
not be perfected by its effect and that distributive intention
is possible, but holds that **actual adoption**, as opposed to
available content, must be intrinsically determinate in a
genuine intentional subject. It is not answered by appealing to
the independence of the intrinsic principle from its objects.
If it is right and the actual adoption differs across worlds,
one must revise strict intrinsic invariance or the contingent
effect/efficacy package with differing adoption. Variable individualized
outputs under the very same efficacious role specification remain open. If actual adoption can be a substantive
nonintrinsic exercise, the weaker concrete-existence PSR may be
met, but the complete determining fact-level demand remains
unsatisfied unless further reasons are supplied. Same test for
an impersonal nonnecessitating exercise.

Next meaningful test, not another object-essentiality paraphrase:
apply the two-relations account to a fixed actual recipient and
an explicitly adopted distributive specification. Ask what makes
the source's adoption operative independent of the successful
output, and which grounding/intentionality theory can meet that
test with the strong simplicity commitment restored. Compare
the stronger objection that the first relation cannot be
explanatorily prior if it is wholly grounded in the effect, with
the limited reply that an actual productive exercise is not
grounded in *bare* existence of its product. The distinction
between semantic dependence and metaphysical explanatory priority
must be defended, not attributed to a.4 ad 15 as an already
proved theory. As a horizontal next test, use #1731 actual
self-understanding and #1380's reference/actual-knowledge
requirements. Avoid reopening #1459's separately scoped research
without coordination.

No new registered statement, claim, sense, theorem, result or
root edge. Existing note and attempt 7d015c02 only. Checked
source locators, same-source witness, modal versus temporal and
thin versus recipient-directed scope at author level. No new
pinned source claim. Independent semantic challenge and
canonical CLI/CI remain required; no verified premise delta
claimed.

## Research attempts citing this note

- [Issue 1737 same-source contingent creation, omission, and selection adequacy](../../corpus/attempts/divine-knowledge-choice-creation-1737.json)
