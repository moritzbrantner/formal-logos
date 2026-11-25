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


## Actual direction by an invariant good (#1953; 2026-11-24)

This continuation investigates the actual-application test in §22. The new question
is what warrants the passage from **an intellectual productive source** to
**production in virtue of its apprehended good**. The distinction between
available content and actual practical use was already established in
§§9–14; another assertion of that distinction would not advance the question.
The baseline is main `a55e21b51aae73115c95a998e32b4a6686eaa968`.
The comparison fixes one actual source n, one actual distinct recipient x,
its production at the selected world, and one intelligible productive
specification D. D is not the name of whatever happens. It may specify a
recipient role fulfilled by different individuals, as in §21. Neither a
complete alternative world nor a particular divine intention is assumed
merely because it can be described.

### 23. Reuse and the claim actually being tested

The issue's elementary two-level identity distinguishes exclusions shared by
all admitted specifications from exclusions supplied only by the actual
specification. With its fixed target map, `T0 \ T_a` is the disjoint union of
`T0 \ U` and `U \ T_a`, where `U` is the union of the specifications' target
images. An excluded target requires exclusion of its whole fiber. These
identities apply to arbitrary admitted families; no free recombination is
needed. They concern target coverage. They do not make the restricting rule
an actual cause, an apprehended reason, or a sufficient account of adoption.
A probability difference could also matter without any support-set exclusion.
The present source and warrant question is not answered by registering these
set identities. Their elementary proof and diagnostic remain in
[#1953](https://github.com/moritzbrantner/formal-logos/issues/1953); no new
Lean certificate or rerun of its finite counts is claimed here.

Reuse is substantive rather than merely bibliographic:

- [ExplanatorySymmetry](../../TruthCore/Explanation/ExplanatorySymmetry.lean)
  keeps favouring, actual explanation, net selection and the outcome-defined
  `settled` relation distinct. Its structural marks do not certify authorship.
- [ReasonGuidedWholeExercise](../../TruthCore/Explanation/WholeSeriesReason.lean)
  and the #1297 comparison allow a necessary bearer with a contingent
  reason-guided exercise. Their optimality/choice conditions do not decide
  whether a reason actually guides the production.
- [The selected-effect and optimal-choice results](#what-the-types-establish)
  already govern rigid-object efficacy, ties and positive-output totality.
  No new necessity result is needed for an invariant end.
- Merged #1941's `oneIntellectualPowerGivesWilledGiving` (`b5b84276`) and
  `actualAbsenceHolderGivesByWill` (`963e9689`) concern actual giving by a
  rational power of the same holder. `Rational` has no further formal content
  in that overlay. Merged #1949's
  [good-sensitive propensity comparison](will-versus-chance.md#would-selection-that-tracks-a-good-identify-an-intellectual-and-willing-source)
  prevents promoting equivalent output profiles into equivalent mental
  activity or into evidence uniquely favouring mentality.

The narrow proposal is positive: n's understanding of D and the relevant
good is the actual formative principle under which n produces x; n's
appetite endorses realizing that good through this exercise; and x results
through that direction. The reason can explain production under D without
settling every difference between x and another eligible realization.
"Formative" here means that the understood specification supplies the
standard and organization of this performance, not merely information
available to its producer. "Nondeviant" means that realization proceeds
through that practical direction, rather than through an unrelated causal
route that happens to produce a conforming result. These are the ordinary
roles being investigated, not new predicates that certify their own use.

### 24. The positive argument in q.19 a.4, and what it adds

Read the third argument of [ST I q.19 a.4 co. and ad 2–4](https://www.newadvent.org/summa/1019.htm#article4)
as an argument about the mode of actual production. Effects pre-exist
according to the cause's mode; divine being is understanding; effects
therefore proceed intellectually, with appetite toward realization.
Ad 4 identifies directing knowledge, commanding will and executing power
in the same cause. The first two arguments instead appeal to intellectual
priority over natural finality and to the determinate operation of a
natural form. Those are further disputed commitments, not independent
proofs that a nonnecessitating impersonal propensity is impossible.
The complete Latin article was materialized and read, including objections
and replies, at passage `74e86e1a-2d6e-592b-95b3-10c3a725ea2e`. The argument
is God-indexed. Applying it to the neutrally specified n requires its
same-source and actual-intellect premises, rather than supplying a new
proof that n is God.

The third argument's strongest reconstruction has four steps. This is an
analyst reconstruction of its philosophical work, not a newly registered
inference.

1. **Fix the actual productive principle.** The source does not merely
   have a description of x. Its own actual power supplies x's production.
   The effect's relevant form must therefore be accounted for in that
   productive principle, rather than being borrowed from an independent
   creator of the form. This is the causal precontainment commitment.
2. **Identify the mode of that principle.** On the strong intellectual
   reading, the source's intrinsic actuality is actual understanding,
   not just a power capable of producing an understanding creature.
   Its effect-content is apprehended intelligibly in that actual
   understanding. Productive containment alone would not supply this step.
3. **Carry the formative content into the exercise.** The effect proceeds
   through the mode in which its form is actively present in the cause.
   Here the content apprehended in step 2 is what actually organizes the
   production, not a parallel representation of what another operating
   principle will produce. This is the load-bearing claim about the
   relevance of the intellectual form.
4. **Interpret the actual inclination and execution together.** The
   source's actual orientation to realizing that understood good is
   intellectual appetite, and the productive exercise implements it.
   Distinct directing, endorsing and executing roles need not be three
   entities or three successive events. The recipient is then produced
   for an apprehended reason under the operative description.

The move from step 2 to step 3 is stronger than substitution of identicals.
If the source's esse really is its understanding, one may substitute the
same subject in the statement that it produces x. This warrants predicating
production of that very understanding. It does not by itself warrant the
further explanatory claim that x is produced **in virtue of the apprehended
D**. A fact about the identity of a cause does not settle every respect in
which it is causally relevant. The source's precontainment-to-procession
principle carries that additional work. Keeping this work explicit gives
the argument a serious positive interpretation; silently treating the two
claims as the same would remove its central premise.

The existing [IntentionalExemplarExtension](../../TruthCore/Causality/IntentionalExemplarExtension.lean)
locates the corresponding distinctions. `EffectExemplarCoverage` supplies
true effect-content, while `CognitivelyTakesUpExemplar` supplies actual
apprehension. `ImmanentSelfPresence` starts from actual understanding in its
selected sense; it does not infer it from virtual productive possession.
Even actual uptake is not yet adopting D as the form governing production.
Conversely, if the full actual intellectual-appetite interpretation is
warranted, one need not demand a further act of adopting that adoption.
That would add a requirement the argument neither needs nor claims to meet.

### 25. Where the formative relevance premise has positive warrant

The premise has a clear ordinary application. A craftsperson produces a
specified object by understanding its form, taking that form as the plan
of the work, and organizing the execution accordingly. Reasons about the
form explain the sequence of operations and its corrections; the same
maker's mere knowledge of another possible design does not explain its
production. Familiar practical knowledge, deliberate performance and
means–end organization give direct, defeasible grounds for treating
apprehended content as active in such cases. The account does not earn
this warrant merely from its successful output. These ordinary cases have
complex agents and changing conditions; they are evidence for the
explanatory relation, not witnesses of strict divine invariance.

The primary action sources sharpen, rather than replace, that warrant.
Aristotle, [Nicomachean Ethics VI.2, 1139a17–b5](https://classics.mit.edu/Aristotle/nicomachaen.6.vi.html),
connects practical thought and desire to the same object and locates the
origin of action in their end-directed conjunction. In
[De anima III.9–10, especially 432b26–433a26](https://classics.mit.edu/Aristotle/soul.3.iii.html),
medical knowledge without healing, and apprehension without action,
prevent an inference from understanding alone. His distinction between
actual and apparent good also prevents identifying intentional action
with objectively good action. These texts concern finite agency.
[Metaphysics Θ.5, 1048a1–24](https://classics.mit.edu/Aristotle/metaphysics.9.ix.html)
adds appetite or choice to rational capacities for opposites under its
stated agent–patient conditions. It supplies no independent theorem that
every possible impersonal ultimate power is deterministic.

For the simple-source application, the strongest positive warrant is
**cumulative and constitutive**. An independently warranted actual
intellectual source; effect-forms understood in that source; and its
productive power exercised through its own intrinsic actuality jointly
make active intellectual formation a natural unified account of the
production. On this account the plan is not an externally supplied
blueprint and the will is not an additional event that activates the
source. The source's own apprehension, appetite and power
are the activity's mutually intelligible aspects. The proposal explains
how a reason can be operative without causing a change in the source,
and why a reason's contribution can be the order realized in the effect
rather than a necessitating antecedent of the will itself. That is genuine
explanatory content, conditional on the stated interpretation.

This cumulative case draws its support from the actual-intellect,
causal-form and direct-exercise commitments together. It need not produce
a disconnected proof of every member. One may also accept actual
intellectual appetite or direct reason-guided agency as a primitive with
this content and its defeaters. Calling the exercise primitive does not
erase the explanation of its recipient: what it produces, through what
power, and for what apprehended good can remain informative. It also does
not resolve a further demand for a determining reason why this exercise
obtains. The same permission to start with an actual productive nature
and direct exercise belongs to the impersonal account.

The cumulative warrant has a precise limit. **Removing a separately
existing form, executive event or blind subsystem does not establish the
relevance of one explanatory aspect of the remaining actuality.** A rival
can maintain one power while distinguishing its being cognitively
self-present from its selectively producing effects. Numerical simplicity
is not, without a further account, a rule that every effect is produced
under every true description of its cause. It would be question-begging
to call this distinction composition merely because the personal account
would prefer all production to be practical. A real-composition objection
must identify the allegedly distinct constituents and defend that
classification. No such demonstration is supplied by the one-power
certificate.

Accordingly, q.19 a.4 gives more than an assertion that God wills: it
provides the formative rationale and its unity condition. It does not
supply independent additional support for the actual-intellect premise
from which its third argument starts. Nor may causal precontainment be
read first as virtual power, then as apprehended content, and finally as
practically governing content without carrying the changed requirements.
The [source/production distinctions](causal-perfection-transfer.md#what-can-the-complete-performance-of-a-product-tell-us-about-its-producer)
already prohibit the first promotion; the present analysis isolates the
second. Reusing the same text through both routes is not two independent
pieces of evidence.

### 26. Actual application of an invariant purpose

A fixed content can guide an actual performance without selecting its
complete individual detail. Take D to specify a productive role and an
intelligible good for its intended recipient: for example, making a usable
vessel as a gift to its recipient, rather than producing any vessel-like
object. Actual x can be deliberately made as that gift without having
been an independently existing singular object of prior acquaintance.
The realization supplies the individual instance; the independently
specified role supplies the relevant standard. Reuse §21, including the
need to distinguish an intended second gift from an accidental third cup.
This is a finite analogy for the roles, not a divine creation example.

At the proposed n, the least sufficient personal advantage can likewise
be purpose at this role's scope. It need not be a distinct intrinsic
intention determining every feature of the complete world. If the same
understood good and role genuinely govern the actual exercise, variation
between eligible realizations need not be variation in that purpose.
This does not establish that the relevant alternatives are possible, or
that this role is actually intended by n. It identifies which stronger
problem may be left aside without losing the narrower explanatory claim:
complete-world selection and prior selection of the rigid individual are
not requirements for every intentional production under a role.

There are two important limits on an invariant policy. First, a standing
permission or the conditional constraint “if producing, produce within D”
does not itself initiate production. Actual supply and actual practical
use remain needed. If a categorical intention requires some production
and is necessarily operative and efficacious in that respect, omission
cannot be retained just by calling the end nonnecessitating. Secondly,
if “good” means only the being or actuality shared by every candidate
product, a policy to communicate good may exclude no candidate at that
target. This need not empty an actually operative motive of all purposive
content; it does prevent claiming extra target-set discrimination. A
more restrictive norm needs its own content and warrant.

[ST I q.19 a.2 co./ad 2–4, a.3 co./ad 5, and a.5 co./ad 1, 3](https://www.newadvent.org/summa/1019.htm)
supply the positive background: communication of possessed goodness,
nonnecessary creaturely objects, and an order among the things willed
without a cause producing the one will. The actual production is a
contingent expression on that account, not the acquisition of a missing
intrinsic perfection. This motivates purposeful giving; it does not
settle every permissible complete decision. The separate effect/act/source
superiority and creation/omission comparison remains the scope of
#1955 and draft #1956.

### 27. The strongest rivals on the same explanatory questions

The important middle comparison grants actual intellectual content to n
while withholding its operative role. The source understands D and all
other admitted specifications, but its actual production proceeds through
a good-sensitive disposition; its knowing D is not what guides that
production. This challenges step 3, not the possibility of knowledge or
the reality of production. Knowledge without action and the distinction
between an active form and an unused plan give the failure mechanism
positive ordinary motivation. They do **not** establish a metaphysically
possible simple source with all the intended commitments. Here the
proposal is a serious challenge to the inference, not a certified
countermodel to the complete classical account.

The strongest response is that active exemplarity is part of the source's
actual productive nature, not a speculative representation next to an
independently operating blind power. Where that nature is independently
warranted, the response meets the challenge: its actual exercise is
intellectual in the explanatory respect at issue. Where it is supported
only by saying that the producer also understands D, the response repeats
the disputed step. The question is not whether an additional substance
selects the output, but whether the apprehended form actually supplies
its productive direction.

| Same test | Intellectual formation | Good-sensitive impersonal production | Intellectual content without formative governance |
| --- | --- | --- | --- |
| Actual existential supply | Actual productive exercise is required. | Receives the same credit for the same actual productive exercise. | Can retain actual production. |
| Independently meaningful good and permitted class | Can restrict the exercise without uniquely fixing its result. | Can instantiate the same restriction or propensity; no inferiority follows from that match. | Can know the same good and have the same permitted class. |
| Why the effect is produced for that apprehended good | Explains this respect when the understood form and appetite govern the exercise. | Offers natural finality or a disposition, without apprehension as its own reason. | Does not gain this explanation merely from possessing the content. |
| What warrants the actual mode | Practical agency directly in ordinary cases; a cumulative actual-intellect and formative-causality account for n. | Ordinary noncognitive productive organization motivates the kind; the ultimate nature/application is a further commitment. | Ordinary unused knowledge motivates the distinction; full simple-source realization is unproved. |
| Primitive actual exercise and residual exact contrast | May take a direct exercise as a stopping point; exact contrast can remain unresolved. | The same stopping standard is available. | Knowing the contrast does not itself explain its selection. |

Two controls prevent an artificial advantage. If n knowingly adopts and
executes a lottery **as a way of realizing D**, there is already purposeful
control at the policy's scope. The random draw is not thereby deliberately
selected in its complete detail. If a functional account establishes that
the supposedly impersonal process really apprehends D as a reason and
acts through that apprehension, it qualifies for the same purposive
explanation. It cannot be excluded by its label. In the opposite direction,
a foreseen collateral effect, an accidentally conforming outcome and an
external spectator's perfect prediction do not become adopted realizations
just because n knows the resulting facts.

This comparison separates a positive explanatory difference from evidence
that the difference is instantiated. A complete account of actual
intellectual formation would explain a respect left out of a purely
noncognitive account. Identical target coverage is not evidence that the
two accounts explain the same respects. It is also not evidence that the
personal account is true of n. Ordinary productive structure is credited
symmetrically; neither side receives a presumption of ultimate applicability
from its familiar examples alone.

### 28. Independence of the source and the operative-role question

The accepted #1957 study is external pending evidence in
[PR #1961 at fcd9be242c6068356fff720baf5f37e7f9e5deb7](https://github.com/moritzbrantner/formal-logos/blob/fcd9be242c6068356fff720baf5f37e7f9e5deb7/docs/notes/psr-self-application-756.md#source-specification-and-existential-grounding-1957-2026-11-24),
not a patch or premise imported into this main-based branch. Its identity
argument is retained: dependence of the very intrinsic actuality transfers
under literal identity and the same dependence relation; connecting that
dependence to a bearer's esse in a different typed representation needs
its stated calibration. A product-dependent relational fact is not simply
the existence of its subject.

That result removes a false dilemma for the present proposal. Actual
production under D need not be either a separate intrinsic executive item
or a description whose whole explanation is x's bare existence. A source's
directed activity can be the primitive productive explanation, while the
completed description “produces x under D” has x as its term. Truth of that
completed description requiring x does not show that x supplies the
source's intrinsic actuality. It does not, however, establish the activity's
claimed direction by D. The #1957 identity argument and the present
formative relevance question concern different inferences.

The relevant source architecture was checked in full in existing pinned
passages: [ST I q.45 a.3 co./ad 1–3](https://www.newadvent.org/summa/1045.htm#article3),
`fb7bd7bb-c007-43fa-9147-a017d0ae1f01`, and
[q.13 a.7 co./ad 1, 3–6](https://www.newadvent.org/summa/1013.htm#article7),
`12d8ecc5-37c5-4309-870a-f9273a43669e`. The real creation relation is in
the creature, with the divine action signified relatively. Q.13 a.7 ad 3
separates immanent intellect/will from names following external effects.
Thus a temporal Creator-denomination is not itself evidence of operative
intention. These passages make the no-reverse-grounding response substantive;
they do not let an output-dependent success description do the work of
actual practical governance.

The already recorded [q.14 a.8 co./ad 1, 3 and a.16 co./ad 1](https://www.newadvent.org/summa/1014.htm)
were reread in the primary English translation for this pressure test.
Intelligible form needs appetite to be productive; knowing how a work
could be made is not yet knowledge practical by its end. The text's
actual-versus-virtual causality distinction relies on its positive
productive account. Reading “whatever is made is practically known” as
an independent shortcut from output to formative adoption would therefore
reuse the very conclusion at issue. No new pinned q.14 claim is added.

If x instead constitutes the very intrinsic practical actuality identical
with n's esse, the #1957 obstruction applies under its actual-grounding
calibration; calling that actuality a relation does not evade it. If the
only product-dependence established concerns the successful relation, that
obstruction is not established. In neither case may the mode of production
be inferred just from the location of a relation. Strict efficacy for the
same rigid x still has the #555 consequences when its entire premise
bundle is present. Intentional production of an instance under a role is
weaker than that rigid-object commitment.

### 29. Provisional judgment, exact root connection and reopening condition

**Overall assessment.** Actual intellectual formation has positive direct
warrant in ordinary agency and a substantive cumulative interpretation at
a simple intellectual source. The source's own apprehended content can be
the actual principle of its work without a prior executive event. This
constitutive account is stronger than an output label and is a defensible
direct option, not a commitment that loses all warrant because it stops
at an actual exercise. Q.19 a.4 makes its crucial formative rationale
explicit. This supports the intelligibility and conditional explanatory
force of the proposal; it is not a proof that the proposed simple source
is possible or that the actual ultimate producer has that nature.

The precise result of the comparison is that neither actual intellect plus
numerical identity nor selective production by itself settles **which
explanatory aspect governs the production**. The inspected source argument
stops discriminating once its intellectual precontainment is read only as
available or actual cognition rather than active exemplarity. Its stronger
reading discriminates, with the warrant just stated, but cannot be counted
as a new independent derivation of that operative role from the thinner
premises. The necessary good-sensitive impersonal producer remains a
standing rival, and the intellectual-but-nonoperative challenge has not
been excluded at strict-simple-source scope. The overall actual
classical-creation synthesis remains underdetermined. This is a withheld
universal/application conclusion, not a refutation of the formative
principle or a full rival countermodel.

The exact graph destinations and retained obligations are:

- Existential PSR `608a262d-08fe-4dfd-9413-67e2ecf35b84`, with BX1
  `6c6191dc-082d-4417-b675-b32d4fab4573` and BX2
  `0e44041e-4591-4aad-857a-f6748032f142`, reaches B2
  `8a8d00e9-12b6-4cf0-b662-431cc4addd49` by result
  `7bf9cb77-0418-4363-9298-266eac105edd`. Actual purposeful production could
  support an interpretation of adequate existential supply, but a selected
  recipient does not establish that PSR over its full domain or either
  bridge. Adequacy, domain and causal-mode application remain visible.
- The issue's old no-consumer wording for `fdd2b1cf` is superseded on main.
  Merged #1944's `godHasWillFromWilledHolder`, result
  `834ddcfa-8631-4bbc-8afc-6ae04ccc55d0`, consumes `fdd2b1cf`, GOD_4-holder
  `0050b6ed`, at most one holder `5f93d4f0` and rational-power-to-will
  `65e0179f` to give `66aecdd7-ea4e-55c6-9377-10db08893854`.
  [Holder/root identification](holder-root-identification.md#3-results)
  has its own premises. This supplies a root connection for the existing
  willed-giving route; it does not silently enrich its rational-power
  primitive with the formative content investigated here.
- The particular-recipient consumer `a94c5dfc` additionally requires the
  recipient's own existence-good as willed for it, not only a coarse
  productive end. `RootToEsseCauseAt`, `GivesAt`, `CausesIn` and grounding
  are not identified. The [C2 necessity route](contingency-receptivity-c2.md)
  (`e5d49f99`) retains its same-bearer receptivity/prior-cause obligations.
  The assumed necessary n in this comparison cannot establish them.

**Concrete remaining blocker.** No supplied account demonstrates that the
source's *actual* productive specification is intellectual in the formative
sense, rather than intellectually represented while production has a
noncognitive selective character. The ordinary evidence licenses this
relation for agents whose production can be traced through their practical
activity. At n, an argument from an exclusively intellectual productive
nature can license it; identity, one power and effect conformity alone do
not establish that interpretation. The blocker is this application, not a
missing additional selecting event, a failure to prove every primitive,
or another set-theoretic result.

**Next discriminating test.** Reopen this slice with a positive account of
the *same n's productive principle* that connects its intrinsic cognitive
content to the form of its actual exercise. In particular, test whether a
blind selective character in that very principle would require a real
constituent distinct from its intellectual actuality, using a defended
composition criterion rather than counting descriptions. A demonstration
would strengthen the formative route. A positively justified single-power
account that retains actual self-understanding while its production is
not governed by any apprehended content would strengthen the rival. Both
must preserve the specified recipient, actual supply, content and strict
simplicity assumptions; neither a second possible-world table nor the
absence of an objection supplies either result. Independent same-source
intellect evidence remains useful cumulative support, but a capacity label
or the output's own intelligence is not that evidence. Until such evidence
is supplied, further readings merely repeating precontainment or the
practical/speculative distinction would rerun the identified premise.

### 30. Evidence and verification boundary

This is a source-grounding and warrant assessment in the existing note and
attempt `7d015c02-2e23-4b2e-a418-e23c943c3a5a`. It adds no Lean declaration,
registered claim, definition, proof or graph edge. The six q.19/q.13/q.45
articles above were materialized from existing hash-checked SCTA raw caches
at revision `f9065dc8ce7bc790b8c972e49ee19d661f028be6` and read in full.
Their article locators and passage identities remain unchanged. Aristotle
and q.14 were read at the linked primary translations; they are research
readings, not newly pinned claim bindings. Existing selected-effect,
ExplanatorySymmetry, appetite and will results retain their own formal
scope. At the §§23–30 baseline, #1933 `ActualExerciseExplanation` at
`e5dd8243c5690f5d9255a509da00111cbdc36c8e` was external branch evidence;
its output-bypass control supplied no new premise in that assessment.

The current CLI was used for related, dossier, context, brief and novelty
before drafting, including the supplied #1953/#1737 issue snapshot. Novelty
retrieval identified this attempt and the causal-perfection work as prior
substantial treatments; absence of an exact text match is not a novelty
claim. The same CLI's semantics audit covered the current will target and
the complete PSR and holder-to-will bundles, including the latter's
registered power and will sense bridges. Local `truth check`, the offline
attribution check against the stated baseline, and new local-link checks
passed. No new or changed stating claim requires attribution review.
The author sweep retained all
seven recurring checks: no metaphysical reading of structural controls;
matched burdens; exact source scope; no prose extension of the types;
explicit encoding limits; scoped C2/PSR labels; and external publication
status. The initial draft left independent review of the complete assessment
and publication description pending; the subsequent accepted review is
recorded below. Its scope is §§23–30 and that proposed outcome, not later
continuations. Delivered-head validation belongs to the coordinator's
publication record.

**Review and publication.** Independent reviewer `/root/final_operative_review`
accepted the complete §§23–30 assessment, the full attempt delta and the actual
proposed PR body at `1dfc852338fa18197cb0f00f6ae09c9d5c34cba7`, with
qualifications and no substantiated defect. The reviewer checked the primary
formative argument and action passages, exact PSR and holder-to-will consumers
and sense bridges, and the positive warrant, rival and application boundaries.
This is semantic acceptance of the provisional assessment, not a formal
certificate or establishment of actual ultimate applicability.

The [published review snapshot](https://github.com/moritzbrantner/formal-logos/commit/85e20946be520d64ae568523d9025bdb2abd2369)
has the identical Git tree as the reviewed local snapshot. Current corpus,
complete semantic bundles, offline attribution, new local links and whitespace
checks passed; the computed frontier comparison has no change. The
[publication branch](https://github.com/moritzbrantner/formal-logos/tree/agent/specification-coverage)
is not merged; its PR owns the delivered-head CI disposition.

## Effect superiority, practical excellence and intrinsic source perfection (#1955; 2026-11-24)

This comparison continues
[#1953](https://github.com/moritzbrantner/formal-logos/issues/1953) and #1737.
Baseline: `61acfd5629cab58221fe148b034340c7af9278ff`. No new statement,
source claim, definition, sense, Lean theorem, argument or result is registered.
The existing optimal-output and selected-effect results remain unchanged.

### 31. Fix the comparison before asking about superiority

An effect can be a more valuable created product without its production being
a better exercise of the producer's power. Conversely, flawless execution of
a specification is compatible with a morally defective choice of specification.
Distinguish four comparisons:

- **E:** objective value of the resulting created order, holding the relevant
  value criterion fixed. Comparing isolated products does not establish a
  comparison of complete orders.
- **F:** fidelity/excellence of execution relative to an independently
  intelligible and adopted end, including appropriate means. No inference from
  output matching alone to adoption or practical direction.
- **A:** all-things-considered quality of the complete decision, including
  selection of its end, obligations, opportunity costs and permissible
  omission. This is not identical to F.
- **P:** intrinsic perfection of the producer, including relevant power,
  knowledge and intrinsic goodness. A further possible evaluation **R** of the
  producer includes relational or historical excellences (which actual
  decisions the producer makes). Do not identify P and R without argument.

Use the same source, relevant background and feasible decision comparison
throughout. A comparison between distinct sources, or a claim that another
possible source would make a better choice, needs an additional bridge into
the chosen scope. No actual alternative world is established by the comparisons.

The earlier materialization of `AQUINAS-ST-I-Q25-A6-EN`, recorded above,
already motivates the difference between a better thing and better making;
reply 3 compares the present order considered as a whole with another order,
not just an isolated improvement. The complete reply 1 distinguishes the
wisdom/goodness of the maker from the manner of the thing made. In the
public [ST I q25 a2 ad 2 and a6 ad 1–3](https://www.newadvent.org/summa/1025.htm)
reading inspected for this checkpoint, a2 ad 2 also distinguishes power
whose effect is its end from the divine power's relation to its effect.
This is source orientation, not a newly bound claim; the prior pinned reading
remains the authority for the corpus. The stronger contemporary objection
is the action-to-agent surpassability step discussed in
[SEP, Divine Freedom, section 2.2](https://plato.stanford.edu/entries/divine-freedom/#FreeGood):
even permission to choose a less valuable creation need not establish the
possibility of unsurpassable agency. The encyclopedia discussion was inspected;
Rowe's full book and Adams's original paper were not materialized or read for
this checkpoint. Do not attribute the following analyst model to them.

### 32. Exact reflection obstruction

For a nonempty comparison domain S, let E, A and P be ordinal maps into
strictly ordered codomains (only their strict comparisons are used).
Write E(i)>E(j) for a strict improvement of the represented outcome from j
to i, and analogously for A and P. Consider the following four hypotheses:

1. Some E comparison is strict.
2. For every i,j, E(i)>E(j) implies A(i)>A(j).
3. For every i,j, A(i)>A(j) implies P(i)>P(j).
4. P is invariant across S.

These are jointly inconsistent: instantiate 2 and 3 at the witness of 1;
the resulting strict P comparison contradicts 4. In particular, under 4
and 3, no strict A comparison is possible, even if there is strict E
variation. Under 4 and 2, strict E variation forces a failure of 3 at
some pair. Under 4 and 3, strict E variation forces a failure of 2.
Neither of the reflection rules is a consequence of the definitions.
Replacing A by F tests whether a better product requires better execution relative to the adopted end. Each reflection rule needs its own warrant.
If P is replaced by R, invariance needs fresh warrant.

The following matched controls use three labeled comparison situations.
The tuple entries are grades, not quantities of being or moral utility.
Each control negates precisely the indicated hypothesis of the four and
retains the other three:

| Omitted hypothesis | E | A | P |
| --- | --- | --- | --- |
| 1: strict effect variation | (0,0,0) | (0,0,0) | (0,0,0) |
| 2: effect-to-act reflection | (0,0,1) | (0,0,0) | (0,0,0) |
| 3: act-to-intrinsic-source reflection | (0,0,1) | (0,0,1) | (0,0,0) |
| 4: invariant intrinsic perfection | (0,0,1) | (0,0,1) | (0,0,1) |

The last control is not a model of a simple immutable being. The third
control can rank an external decision outcome without ranking its producer's
intrinsic state; it does not establish that its varying decisions are
compatible with divine simplicity. The second stipulates equal A, not
merely equal execution quality F, and therefore does not settle whether a
lower-valued complete decision actually has equal merit.

Reproduced exhaustive diagnostic (JavaScript; 27 ordinal maps per axis,
19,683 triples). This is a nonmodal finite test of the four claims, not a
count of admissible worlds, a probability, or evidence of metaphysical truth.

```js
const maps = [];
for (let a=0;a<3;a++)
  for (let b=0;b<3;b++)
    for (let c=0;c<3;c++) maps.push([a,b,c]);
const pairs = Array.from({length:9},(_,k)=>[Math.floor(k/3),k%3]);
const gt = (f,i,j)=>f[i]>f[j];
let total=0, full=0, deletions=[0,0,0,0];
let invariantAndVariable=0, invariantAndVariableAndEA=0;
for (const e of maps) for (const a of maps) for (const p of maps) {
  const flags = [
    pairs.some(([i,j])=>gt(e,i,j)),
    pairs.every(([i,j])=>!gt(e,i,j)||gt(a,i,j)),
    pairs.every(([i,j])=>!gt(a,i,j)||gt(p,i,j)),
    p.every(v=>v===p[0])
  ];
  total++;
  if (flags.every(Boolean)) full++;
  for (let k=0;k<4;k++)
    if (!flags[k]&&flags.every((x,i)=>i===k||x)) deletions[k]++;
  if (flags[0]&&flags[3]) {
    invariantAndVariable++;
    if (flags[1]) invariantAndVariableAndEA++;
  }
}
console.log({total,full,deletions,invariantAndVariable,
  invariantAndVariableAndEA});
```

Observed: `total=19683`, `full=0`, `deletions=[27,216,288,312]`,
`invariantAndVariable=1944`, `invariantAndVariableAndEA=288`.
The universal proof is the two strict implications above, not induction
from this enumeration. Under the appropriate strict-implication
interpretation the same proof works on arbitrary comparison domains.
This is a simple incompatibility diagnostic; do not register an open
reflection premise or a transcription as an independently supported result.

### 33. A positive nonexhaustion argument, and its limit

Suppose a productive source has the power to actualize each of two
specified ends. In each case the adopted end is fully and competently
realized, but the realized ends differ in value or extent. For example,
a capable maker can successfully execute either of two independently
specified gifts. The smaller gift is not a failure to make the larger
one if it was never part of the operative specification. Having the
capacity to produce the greater gift is already a condition of its
feasibility; the smaller effect therefore does not show a lack of that
capacity. In an ordering solely by available productive capabilities,
identical capability sets cannot be strictly ordered by inclusion.
This establishes a limit of the proposed *inference from product
to productive power*, not the equal moral quality of the decisions.

A defect-of-execution test requires an intended or due end, a capacity
to realize it and a shortfall relevant to its realization. Merely
identifying another possible better product establishes none of these
jointly. An intrinsic actuality need not gain a new perfection from
communicating an already possessed good. These considerations supply
positive warrant for rejecting a general E-to-F implication and for
distinguishing F from P. They also fit the earlier expressive/acquisitive
distinction in section 20. They do not entail rejection of E-to-A or
A-to-R; an agent can exercise excellent technique for a wrong end, and
the choice may itself exhibit deficient generosity, justice or rationality.

The strongest maximization objection should grant this whole account of
productive execution and attack the choice of specification:

- If another complete feasible decision realizes a strictly greater
  all-things-considered good with no relevant countervailing reason, and
  a perfect chooser necessarily selects an undominated decision, then
  the inferior decision is excluded. These are substantive premises.
  Product superiority alone, a partial ordering, and a finite example
  cannot establish them for the entire creative decision.
- If all choices are strictly improvable in that complete decision
  ordering, the same policy has no admissible choice. Reuse #689/#1953's
  no-best and omission distinctions. This is not a proof that there is
  no best possible world, or that a perfect chooser is impossible
  independent of the policy premise.
- If an agent has no unmet obligation to an actual beneficiary and does
  not acquire an intrinsic good by producing the effect, some familiar
  grounds for obligatory production are removed. A norm of impersonal
  promotion or a norm of surpassability of the actual chooser may still
  impose a stronger requirement. No-rights-violation is not a proof of
  complete permissibility, equal A, or equal R.

Conversely, if a defensible account of source perfection exhausts the
relevant excellence in intrinsic actuality, and the creative exercise
introduces no additional intrinsic completion, then a difference in
external product cannot *by itself* introduce a difference in that
excellence. The open metaphysical application is whether all the
relevant goodness and excellence of choice really is intrinsic in
that sense, and whether two distinct directed exercises can be actual
without a difference of intrinsic actuality. Relationally individuated
acts and the actual operative content must be defended, not stipulated
away by assigning a constant P map. Ordinary productive agents are not
witnesses of the strong simplicity claim.

### 34. Symmetric assessment and root-facing consequences

| Account or control | Execution | Complete decision / source burden |
| --- | --- | --- |
| Personal producer with optional expressive end | Can successfully realize distinct adopted ends | Warrant of permissible adoption, nondeviant guidance and sameness of intrinsic perfection is still needed |
| Impersonal producer with nonnecessitating good-sensitive propensity | Can match the same product and policy ranks | Must warrant the same complete-decision constraints if claimed; extensional parity does not establish or defeat intentional explanation |
| Producer with insufficient ability | Can fail a due or adopted specification | The failure may discriminate capability when alternatives and actual exercise are independently known; a less valuable result alone does not |
| Producer knowingly executing a wrongful end flawlessly | High F is consistent with inferior A | A theory of perfection must address actual practical goodness, not identify it with technical success |

The comparison is not an independent argument for the root's intellect
or will. It can remove an overstrong maximization assumption from a
*proposed* account of rational creation. It cannot alone give positive
warrant for the actual same-source practical guidance. The existing
#1941 route `b5b84276` / `963e9689` and target `66aecdd7` require
their stated same-bearer bridges. The possibility of producing a
greater external good is also not the converse of causal preexistence
of perfections (`64498e7e`), existential transfer (`f8ba2429`) or
actuality-goodness (`00e962ae`). Those principles compare different
respects and relations; none currently supplies E-to-A or A-to-P.
Retain all existing existential and simplicity-route obligations.

Provisional assessment: the distinction between a better product and
better execution has positive ordinary-agency and conceptual warrant.
The claim that a complete decision's value need not alter intrinsic
source perfection is credible under an intrinsic/extrinsic distinction
but remains conditional on its metaphysical application. The stronger
all-things-considered maximization and moral-person-surpassability
objections are standing. An impersonal producer can retain parity on
the extensional criterion. The next discriminating question is whether
the act's choice of end is itself positively excellent without
maximizing total produced good, and how a genuine operative intention
can belong to the same source without adding intrinsic completion.
A proved dominance or an intrinsic-choice essentiality premise would
weaken the permissive proposal; a defensible criterion of due versus
freely communicable good and an independently warranted actual
practical-content bridge would strengthen it.

### 35. What can make the choice of a smaller gift good?

Consider a printer who has undertaken to make a single accessible edition
for a particular reader by Friday. On the last available press shift she can
honor that undertaking, print several standard copies for other readers,
or leave the press idle. Assume that the standard copies yield more total
reading benefit, that the accessible edition meets an actual need, and
that the other readers have no comparable claim on this shift. All three
options include the forgone uses of the shift. A wholly competent
execution is possible for either printing option.

The reader's claim gives the printer a positive reason to choose the
accessible edition. It also explains why choosing this end can exhibit
fidelity even if it yields less total benefit. If the reader releases the
claim beforehand, the benefit ranking and printing ability stay fixed
while that particular reason falls away. Serving the reader's need can
still be generous. To rank that generosity above using the shift for the
other readers requires a judgment about their competing goods. Likewise,
a rule that tracks valid claims can select the same edition. Attributing
fidelity as a motive requires evidence that the printer acted on her
understanding of what she owed. [Earlier waiver comparison](moral-governance-intellect-will.md)

For a proposed creator, a prior promise to an existing reader cannot justify
creating that very reader in the first place. The comparison shows what a
reason concerning this recipient can contribute when its basis is available.
A case for freely communicating a good still needs a reason applicable
before the proposed gift, an account of permission across the complete
alternatives including omission, and evidence that the same giver acted
for that reason. A source that necessarily understands the end but produces
through an independently operative disposition still fits the output.
The invariant-good comparison in #1962 and the policy test in #1971 locate
those remaining questions. [Policy and end requirement](will-versus-chance.md#end-requirement-policy-requirement-and-productive-fixity-2026-11-25)

### 36. Which account of goodness requires choosing the greatest feasible good? (#1955)

Grant one producer four feasible complete decisions. Hold fixed what
counts as care due to each created beneficiary and the ranking of
created benefit among the outcomes in which all receive that care.

| Decision | Outcome | Satisfies every actual beneficiary’s due claim | Also maximizes created benefit among the eligible options |
| --- | --- | --- | --- |
| O | Create no beneficiary | Yes | No |
| A | Create one and provide due care | Yes | No |
| B | Create two and provide due care to both | Yes | Yes |
| C | Create two and withhold due care from one | No | No |

The stipulated ranking is O < A < B. C is ineligible before the
maximization comparison. A rule requiring due care for every actual
beneficiary permits O, A and B on that criterion. Adding the obligation
to select a greatest eligible outcome selects B. Withholding care in C
has an existing patient. Including the interests of possible beneficiaries
or imposing impersonal beneficence could change the comparison, given
an argument for that wider standard. The table answers no question about
the actual distribution of suffering.

Now vary the proposed ground of goodness while preserving those four
decisions, the ranking, and the due-care judgments. Someone who takes
evaluative truths as necessary and primitive can endorse either policy.
A proponent of divine-nature goodness likewise needs a reason why
expressing that nature requires maximizing created value, or a reason
why a nonmaximal expression can be wise and generous. Learning a
beneficiary’s needs without theology concerns access to the good.
Holding that a decree cannot make deprivation good concerns independence
from voluntary choice. Either thesis can be held while attributing the
good’s being to divine nature. Ontic independence from that nature is a
third, substantive thesis. A necessary normative truth could constrain
what counts as permissible without removing the producer’s capacity
to perform the act. [Normative standing and the origin of a claim](moral-governance-intellect-will.md)

The immanent due-good account has a concrete advantage in explaining
what counts as a defect in C through the good of that recipient. A
natural-kind account can use the same explanation of flourishing and
still owes a reason why another agent must secure it. A realist about
necessary norms can supply that practical requirement as a basic
truth. Its primitiveness alone gives no argument against it. An account
in terms of ideal attitudes owes a well-defined, nonempty class of
competent assessors and grounds for trusting their verdicts here.
Distinguishing preexisting goodness from command-grounded obligation
also allows a theist to deny that arbitrary commands set the value
ranking. The participation proposal can relate the good of the patient
to the source of its being, conditional on the transfer premises.
Coextension with actuality alone does not establish identity or moral
benevolence. The same tests of scope and explanatory adequacy apply to
each primitive commitment. [Finite goods and their source](wielenberg-making-account.md) · [Owner’s matched comparison](https://github.com/moritzbrantner/formal-logos/issues/1955#issuecomment-7143785792)

The strongest remaining objection asks whether an unsurpassably good
chooser could actually select A when B dominates it as a complete
decision. Both accounts exclude A if they also grant that a perfect
chooser must avoid dominated decisions. Showing B yields more created
benefit establishes only the first ranking in the table. The next
test is what about the source’s own end could make communicating good to
this recipient positively excellent while permitting omission or a
different gift. An independently warranted obligation of impersonal
beneficence applying to those very alternatives would count against
the permission. Identifying an actual operative reason for this giver
is the further application pursued in #1953.

## Can objective finality explain a contingent order without apprehension? (2026-11-25)

This continuation assesses the strengthened impersonal rival on the same
explanatory task as rational authorship. Baseline
`30a9820018644fe98d92b9f10874c3382340a9ee` incorporates main
`a9819b148bd4a7c089cff9dc07f95c209452511e`. The three continuations merged in
[#1971](https://github.com/moritzbrantner/formal-logos/pull/1971) are substantive
reuse: [end requirement versus policy requirement](will-versus-chance.md#end-requirement-policy-requirement-and-productive-fixity-2026-11-25),
[rational classification versus formative exercise](will-versus-chance.md#can-the-same-intrinsic-actuality-understand-and-produce-blindly-2026-11-25),
and [actual form-specific supply](will-versus-chance.md#from-universal-existential-supply-to-proper-formative-causation-2026-11-25).
The [dispatch comparison from #1978](explanatory-symmetry-742.md#did-the-reason-guide-production-of-this-order-1570)
and [Glen Roy application from #1981](explanatory-symmetry-742.md#why-did-darwin-give-up-the-marine-explanation-of-the-parallel-roads)
already distinguish reasons available, reasons actually used, and the source
of a reason-using subject. Their findings are retained, not presented as new
tests. No new formal primitive, model or graph edge is introduced here.

The dependency refresh also retains the related
[source-specific manifestation comparison](causal-perfection-transfer.md#source-specific-manifestation-versus-intrinsic-understanding-2026-11-25-provisional),
[personal-capacity and operative-purpose distinction](moral-governance-intellect-will.md#personal-and-impersonal-source-original-authority-institution-and-operative-purpose-2026-11-25-draft),
and the adjacent [complete-decision comparison](#effect-superiority-practical-excellence-and-intrinsic-source-perfection-1955-2026-11-24).
Their separate source-apprehension, actual-guidance and decision-quality
obligations retain their stated scopes.

### 37. Meanings and one matched candidate construction

Fix the proposed necessary source n, its actual productive exercise, and the
same actual contingent order H, including one actual rational recipient x.
The shared explanandum is H's existence, intelligible organization, objective
goods and the genuine rational activity of its creatures. It does not yet
include n's having intended H. Objective purposiveness must not silently
become intentional authorship in the statement of what needs explaining.

| Term in this comparison | Selected meaning and boundary |
| --- | --- |
| Objective good-directedness | A real productive nature is directed toward independently assessable goods or success conditions. A pattern retrospectively called good is insufficient; apprehension is not included. |
| Objective reason | A fact counting in favor of an end or exercise under a stated evaluative standard. Its existence alone neither causes the exercise nor makes it the source's motive. |
| Apprehending a good as good | The source actually understands the relevant content in its evaluative bearing. A correct specification, capacity to produce thinkers, or merely available content is insufficient. Tacit understanding is allowed. |
| Motivating reason | An apprehended consideration actually figures in the source's practical exercise under the relevant description. Neither explicit deliberation nor a separate executive event is required. |
| Rational authorship | The source's own apprehension and inclination supply the formative measure of its productive exercise, and realization proceeds through that direction. This is stronger than ownership of a power classified as rational. |
| Primitive exercise | An actual exercise taken as an explanatory stopping point, with its power and direction still specified. This does not mean uncaused product, unstructured production or complete explanation of the exercise's obtaining. |
| Intrinsic invariance | The source has the same intrinsic actuality across the admitted modal alternatives. This is a cross-world claim, not merely absence of temporal change, and does not by itself fix every effect-directed relation. |
| Adequacy | Adequacy for a specified question: productive dependence, kind-level organization, actual intentional direction, or exhaustive particular selection. Success at one is not automatically success at all four. |

For a common candidate, let D specify an order enabling a finite knower to
understand evidence and correct errors through its own activity. D is fixed
by those fulfillment conditions, not by the name H. A history systematically
depriving its supposed knowers of understanding or access to correction would
not fulfill that description merely because their answers were accurate.
Different complete histories could meet D if their metaphysical possibility
is independently admitted. No such possibility follows from describing them.
In the actual comparison x realizes the recipient role; D alone does not
select x's rigid identity or every feature of H.

The **impersonal candidate** has an underived, invariant concrete productive
nature whose nonnecessitating power is genuinely directed toward D and other
admitted goods. Its actual exercise supplies H's existence and form, including
x's real cognitive powers. It is not a bare rule awaiting an external
implementer, and an abstract value is not asked to instantiate itself. The
source's concrete nature bears the directed power. The account must defend
that nature and its efficacy; it does not obtain them by stipulating a
successful output.

The **personal candidate** supplies the same H and x. The source actually
apprehends D as good, and this content is its adopted formative measure in
the very exercise that produces H. The power, apprehension and inclination
are proposed as aspects of one actuality, not successive internal events.
The good can be expressed in a recipient without completing a deficiency in
n. This is the positive direct-exercise account of §§24–26, with actual
formative relevance included rather than inferred from a matching effect.
Producing x under D need not mean willing x's own good to x in every respect;
the recipient-specific bridge `a94c5dfc` remains separate.

The **contemplative candidate** adds actual self-understanding and knowledge
of D to the productive nature while denying that this knowledge supplies
the practical measure of creation. One nature explains the agreement between
what is known and what is produced. It need not postulate a second source or
an independently existing blind subsystem. This is the hybrid examined in
#1971, not a model established by assigning a cognition flag. All three
constructions are substantive proposals with open ultimate application, not
certified models of the full simplicity and contingency commitments.

### 38. Can a reason explain the particular exercise without being apprehended?

An objective fact can enter an explanation without being known by the
producer. On the impersonal candidate, the productive nature's real relation
to a good explains why its exercise has the corresponding organization.
The fact that D is good does not alone do this work: the proposed nature must
make that good relevant to its actual production. This supplies a positive
noncognitive account of finality rather than an inference from desirability
to existence. Whether such underived normative efficacy is actual remains
an open commitment.

Under the selected meaning, a motivating reason cannot explain this exercise
*as the source's reason for acting* unless the source apprehends the
consideration and acts through that apprehension. That is a distinction
between explanatory relations, not a demonstration that all adequate
production must have the second relation. Saying that n produced H
"because D is good" must identify which relation is asserted. A personal
explanation adds practical uptake; an objective teleological explanation
adds a real good-directed productive nature. Neither follows from the value
judgment alone.

A particular exercise can be explained under a description that another
exercise would also satisfy. If n's actually apprehended D governs its
giving to x, the account explains this giving as realizing D even if D
does not distinguish x from every alternative recipient. That is genuine
token application of a reason, not exhaustive token selection. The same
distinction credits an actual manifestation of a good-directed impersonal
power while withholding a further explanation of every difference between
H and another eligible history.

The #1978 dispatch test already separates practical use from an accurate
report and from a proxy. It also retains the direct impersonal selector that
tracks the relevant condition itself. #1981 then gives grounds for actual
reason use in the recipient's correction without inferring that the ultimate
source used that reason. These results advance the comparison: a recipient's
apprehension is part of the shared explanandum, while the source's uptake
is the further claim to warrant. No general epistemic defeat follows from
the source's being noncognitive when the recipient's real understanding and
reason-sensitive activity are retained.

### 39. Contingent selection and the same stopping criterion

An invariant propensity can be a source of contingent effects without being
indifferent to their character. Intrinsic invariance fixes the proposed power
and its direction, not a uniquely necessitated manifestation. This is the
stronger rival already admitted in #1971. Its actual exercise cannot be
supplied merely by stating the range of its power or the goodness of D.
The candidate posits actual production and takes the residual exercise as
primitive where no further explanation is offered.

In that sense the account avoids an unproduced or wholly unstructured H;
it does not automatically avoid unexplained particular selection. An
apprehended reason and an efficacious intention can likewise explain the
character and implementation of H while leaving why this intention was
exercised unsettled. A reason favoring H over H' can supply a partial contrast
without necessitating H. A correspondingly grounded impersonal tendency
deserves the same partial credit. If no relevant differentiating consideration
is supplied, calling the actual token a choice does not complete the contrast.

The stopping alternatives are consequently explicit. Under a standard
accepting actual nonnecessitating production with an independently meaningful
direction, either account may stop at a primitive exercise without losing
all its explanation of the product. Under an exhaustive determining standard,
both owe the residual differentiator. Citing a contingent endorsement or
selector moves that obligation to the endorsement or selector if the standard
also covers it. One need not demand an endless series of adoptions to accept
actual practical agency; one may not demand that series only of its rival.

Reuse [#742's exact core](explanatory-symmetry-742.md#the-incompatible-core):
agreement on every member of the supplied base, base-fixed favoring,
selection at both compared histories, and the stated outcome-field conditions cannot all be
retained with the opposed outcomes. Its controls concern that encoding.
They neither refute nonnecessitating explanation nor give personal choice
an exemption. They also do not demonstrate a metaphysically possible
impersonal first source. The current question concerns the warrant and scope
of the stopping standard, not a missing additional selection table.

### 40. What rational authorship adds, and the hybrid's limited equivalence

Rational authorship adds the source's own apprehension and practical use of
the good. An actual exercise under D answers, in that respect, what the
source produced H *for*, not only which valuable organization its power
realizes. Ordinary nondeviant practical production gives this form of explanation direct,
defeasible warrant. The communication of an understood good gives the
personal candidate a substantive motive, and §§24–25 give a cumulative
one-actuality account of how apprehension, inclination and execution can
belong together. A primitive directed exercise can retain that positive
content without a separately caused act of choosing it.

This difference is not an automatic advantage on the neutral explanandum.
If actual intentional provision for x were independently warranted, a
wholly noncognitive account of that very act would omit something real.
If only x's benefit and H's ordered character are warranted, adding
"intended provision" to the explanandum would assume the contested fact.
The personal account may offer an informative explanation of those common
facts through intentionality; its additional relation must still have
positive warrant at n. Conversely, a merely possible nonintentional route
does not defeat an intentional relation established as actually operative.

The contemplative candidate can be treated as equivalent to the impersonal
candidate **for the selected productive explanation** when the same good-directed
nature and exercise do the same formative work, and the added knowledge
contributes no practical governance in that scope. Their complete ontologies
are then still different: one includes actual cognition. Equal outputs alone
do not establish this limited explanatory equivalence. Nor does residual
indeterminacy establish nonoperative cognition: an actually intended D can
govern production while another tendency concerns only which D-realization
occurs.

The hybrid is not thereby an instance of formal `CHANCE_3`. The existing
`oneIntellectualPowerGivesWilledGiving` result `b5b84276` obtains and identifies
an owned rational power using its intellect/will and exercise premises. It
does not encode an apprehended D governing the particular giving. #1971
already preserves this distinction between rational classification and
exercise *qua* intellectual inclination. The latter, when warranted, excludes
a wholly blind explanation of that same exercise in that respect; relabeling
the former does not establish the latter. A genuine constitutive explanation
of formative use would strengthen the personal account even if observable
outputs remained matched.

### 41. Necessary rational source, contingent effects and exact incompatibilities

Necessity of n does not itself entail necessity of H. Temporal immutability
also differs from modal invariance: absence of change within a history does
not assert identical intrinsic character in every possible history. The
current stronger comparison grants intrinsic invariance. It must therefore
locate any variable effect-directed determination without silently giving
n a contingent intrinsic perfection.

The [#555 rigid-act result](simplicity-collapse-555.md) fixes one act token a
and one recipient x. `SameActEverywhere p w a`, `StrictEfficacy p w a x`,
and contingency of x are incompatible. Source necessity together with
`BeingCarriesAct p a` is one sufficient route to the first premise, not its
only possible basis. That bridge must concern the same a whose strict
efficacy concerns x. A description meaning "whatever n does"
does not establish rigidity of a content-specific act. An invariant
good or permissive policy does not establish strict efficacy for this x.
The `optionalAct` and `inefficaciousAct` deletion controls exhibit the exact
structural alternatives, not complete rational or impersonal metaphysics.

The personal candidate can accordingly retain a necessary intrinsic
actuality while proposing a contingent relation to a particular recipient,
or deny that the same invariant act necessitates that recipient. It must
give a positive intentional account of that relation rather than read
the intention from the realized output. The impersonal candidate has the
analogous obligation for its manifestation. Neither may retain all the
incompatible #555 premises by changing the act or recipient between steps.
The candidate account thus avoids an immediate inference from necessary
source to necessary effect; it is not a demonstrated solution to every
simplicity or complete-explanation demand.

Actual knowledge of contingent contents adds the separate
[#1380 constraint](foreknowledge-discrimination-1380.md#exact-mathematical-result).
Within its selected epistemic semantics, factivity, completeness for the
selected family, differing truth profiles, and equality of epistemic rows
cannot coexist. The `Supervenes` bridge makes equal intrinsic projections
give equal rows. A fixed rule with varying rows is not a fixed row, and
temporal immutability supplies no such supervenience. Denying that bridge
may leave a relational account available, but a matching relation is not
yet genuine apprehension. This is an additional obligation for a source
claimed to know actual contingent contents, not a theorem that a necessary
source cannot have intellect. A merely contemplative source with only
necessary self-content is not assigned contingent knowledge without this
further commitment.

### 42. Operative intentionality, unity and change

The strongest personal account treats actual production through apprehended
D as one actuality described intellectually, appetitively and productively.
It need not posit three internal constituents or a transition from dormant
capacity to acquired determination. A role-relative good can be expressed
without an increase in the source's perfection. This gives a positive
constitutive proposal rather than an unexplained sequence of inner selectors.
Its ultimate application remains open: absence of a separately named
constituent is not proof that the account realizes strict simplicity.

Apply the same criterion to the rival. A real distinction between knowing
a principle and that principle's production does not follow from their
having different explanations, or from being distinguishable in ordinary
composite agents. If the rival posits genuinely distinct intrinsic
constituents, the accepted simplicity constraint applies to those constituents.
If it proposes one actuality with different explanatory aspects, a further
composition argument is needed. Numerical identity of power and intellect
likewise does not establish that every exercise proceeds *in virtue of*
intellectual apprehension.

The companion [practical-inactivity analysis](will-versus-chance.md#does-practical-inactivity-divide-the-source-2026-11-25)
tests this specific inference and its positive one-actuality alternative.
Its finite-power source control permits practical-role differences within
one power without thereby demonstrating a strictly simple hybrid. Complete
self-knowledge also leaves the actual practical measure to be identified.
This refines §29's earlier composition reopening condition; it must not be
replaced by a fresh demand to infer real parts from descriptions. The
remaining issue is whether an independently warranted constitutive account
makes the understood form the measure of the actual exercise, or instead
grounds nonoperative cognition and good-directed production together.
Hypothetically switching off a necessary intrinsic feature of n while
holding that very source fixed is not an available intervention.

### 43. Three kinds of matching and positive discrimination

**Actual-output matching** means that the candidates explain or accommodate
the same observed H. It leaves their productive pathways, possible responses,
and further commitments unsettled. #1978's inspected routes show why a proxy
and a direct tracker can agree on an outcome and differ on another relevant
case. The direct tracker survives the proxy test. One successful imitation
does not establish complete equivalence.

**Profile matching** means agreement across a specified evidential scope,
including whatever dispositions or propensities are relevant to that
comparison. Equal possibility sets alone are weaker than that condition.
When the candidates genuinely match the admitted profile, those matching
features provide no basis by themselves for preferring rational authorship.
This is not a probability assignment over worldviews, equal-prior assumption,
or judgment that their total warrant is equal. Constitutive explanation,
source evidence or independently supported theoretical constraints could
still discriminate. Accommodating every observation by an unconstrained
post-hoc productive rule is a weakness; unrestricted appeals to unknown
intentions deserve the same criticism.

**Constitutive matching** concerns what actually realizes apprehension and
practical governance. If a defended account of cognition is satisfied by
the purportedly impersonal system's actual semantic and productive roles,
that system qualifies for cognition under the same account. Its label must
not exclude it. If apprehension includes further irreducible conditions,
matching a productive profile leaves those conditions unresolved. Neither
conclusion follows from sophistication alone. Behavioral equivalence does
not establish absence of cognition, and a merely mental label does not
establish cognition's operative role.

The available discriminators are therefore concrete. Evidence for actual
apprehension in this n, joined to evidence that the apprehended good measures
this giving, would support personal authorship. A defended constitutive
principle excluding the rival's proposed productive nature under the shared
simplicity assumptions could also discriminate. A constrained account that
successfully explains independently specified features that its strongest
rival fails to explain would gain relative warrant. Each test must preserve
the same source, actual exercise and recipient. Evidence for a creature's
reason use, an outside interpreter's correct description, or a power's
capacity label does not by itself satisfy any of these tests.

### 44. Cumulative judgment, precise limits and revision conditions

| Candidate | Positive warrant and explanatory contribution | Exact commitments still needed at n | What would change its relative standing |
| --- | --- | --- | --- |
| Actual rational authorship | Ordinary practical production warrants apprehension-directed explanation; communicating an understood good supplies a substantive motive. The constitutive proposal integrates understanding, inclination and production without requiring a further executive event. | Actual same-source cognition; formative relevance in this exercise; a defensible account of contingent termination under intrinsic invariance; recipient-specific scope where claimed. | Strengthens with a warranted account locating the actual formative measure in n's understanding. Weakens if that knowledge is shown to be nonoperative, or if its proposed intrinsic constitution violates the retained simplicity/efficacy bundle. |
| Good-directed impersonal production | Noncognitive productive organization motivates the explanatory form; an intrinsically directed concrete power can account for goods and form rather than merely license them. Primitive production has the same stopping permission as personal exercise. | Reality and efficacy of the proposed ultimate good-directed nature; its unitary constitution; the claimed production of genuine rational subjects; actual manifestation rather than a bare range of possibilities. | Strengthens with a positive constitution account that explains the independently specified organization. Weakens if a required power contradicts the same accepted constraints, or if actual practical cognition of n is warranted and this very exercise is shown to be governed by it. |
| One-actuality contemplative source | Knowledge without practical employment motivates the distinction, and a common nature can explain agreement between cognition and production without a second selector. It preserves more of an independent intellect case than the wholly noncognitive rival. | Joint compatibility of actual intellect, nonoperative production and the proposed simple actuality; a positive account of the productive aspect rather than a flag or two unacknowledged constituents. | Strengthens with that constitutive account. Weakens if the source's actual productive nature is independently identified as an intellectual inclination in exercise, or if real distinct constituents are demonstrated under the accepted criterion. |

**Overall provisional assessment.** For the neutral explanandum, the
strengthened impersonal proposal remains a substantive explanatory rival,
not merely an unrefuted label. Its direct form-specific production and
objective finality answer questions that an indifferent or merely permissive
source leaves unanswered. Their ultimate realization is not established.
The personal account retains positive direct and cumulative warrant for
its richer explanatory form; its further intentional relation is neither
empty nor automatically instantiated by the ordered product. Current
evidence does not warrant an unconditional ranking between these strongest
ultimate-source accounts. The hybrid sharpens, rather than resolves, the
gap between cognition and actual formative use.

Genuine relative inadequacy arises when one candidate fails an independently
warranted requirement on this same exercise that the other meets: actual
productive form, actual source apprehension and governance where evidenced,
or a shared constitutive constraint. It does not arise merely because one
omits a feature posited only by the other, leaves the same residual contrast
primitive, or has more descriptive clauses. Limited equivalence is warranted
only for the explanatory relations or evidential profile actually matched;
it is not identity of ontology or explanation in every respect.

This reconciles rather than displaces the earlier results. #1971's
end/policy distinction prevents inferring obligatory creation or omission
from a good alone; its formative analysis prevents inferring practical use
from the classification of a power. #1978 and #1981 establish discriminating
local basing questions and retain the impersonal account of the same
reason-using recipient. They do not promote the recipient's reason to the
source's motive. §§37–44 sharpen the assessment of the strengthened rival
and supersede a generic instruction to repeat these completed tests. The
unresolved classical-creation application in §29 remains unresolved.

The next useful evidence is a defended constitution and application of the
actual productive principle: cognition operating as its measure, or a
unitary noncognitive replacement on the same conditions. Independent
same-source intellect evidence can contribute without being counted twice
as evidence of practical exercise. The root connections remain exactly
those in §29: `29818edd` concerns intellect; `b5b84276` classifies the
owned exercised power under its complete premises; `834ddcfa`, with
`fdd2b1cf`, `0050b6ed`, `5f93d4f0` and `65e0179f`, reaches will `66aecdd7`.
No prose step here supplies their open premises, enriches their frozen
conclusions, or establishes the actual practical interpretation, the full
existential PSR, or recipient-specific willing.

**Evidence and review boundary.** This is an analyst synthesis in the
existing note. The earlier source readings and reviewed consequences are
reused within their stated scopes. The #555 and #1380 declarations and
the #1941 solution were inspected for the exact bundles above; no new
formal result or metaphysical possibility is certified. The source-specific
simplicity continuation has its own evidence boundary. The author sweep
checks matched stopping rules, neutral explanandum, same witnesses, full
joint premises, scoped senses, and the separation of output matching from
cognition and actual formative governance. Independent reviewer `/root/semantic_review` accepted the complete
integrated continuation, companion analysis, both current attempts,
canonical A/B record changes and actual PR body with qualifications at
`ecd99e9fab1ffd743c35a5829b57405f04377184`. The sufficient-bridge repair is
resolved, with no unresolved substantiated findings. The later upstream
merge preserved the reviewed files verbatim; subsequent changes reconcile
review/publication bookkeeping only. Current corpus, generation, bundle,
attribution, link and whitespace checks pass, with no computed premise
change. Draft PR #1962 owns exact delivered-head CI; no new local full
Lean/Comparator/NanoDa run is claimed. This review accepts the conditional
comparison, not actual ultimate application or full metaphysical
realization. The earlier §§23–30 review retains its original scope. The
[published reviewed snapshot](https://github.com/moritzbrantner/formal-logos/commit/ebe7aca0e20702feafd79c9273a8e1d43c41c130)
has exactly the same Git tree (`2dee7e703e85ac1daebffad008042770c82e07dd`)
as that local review revision.

## What gives a material thing its end? (2026-11-25)

Continuation of §§37–44, prompted by the question why an impersonal source
would give things finality and why material things would have purposes.
The earlier comparison granted objective finality. This continuation
investigates its positive grounding; it does not withdraw the grant by
defining every end as an intention. The supporting investigations are
[intrinsic finality and its source](teleology-first-mover.md#intrinsic-finality-and-the-source-of-its-order-2026-11-25)
and [material function and source finality](goodness-form-end-definitions.md#from-material-function-to-source-finality-2026-11-25).
They extend, rather than repeat, the existing first-source recognition audit
and the organizational-function investigation of PR #1646.

### 45. Three explanations that must stay apart

Fix the same source n and recipient x, with a specified capacity and
completion e. Three questions are different:

1. What makes e a completion or good **for x**, rather than just an outcome
   an observer happens to prefer?
2. How does n produce and sustain a nature in x whose operations are
   genuinely directed toward e?
3. Does n produce x **because n apprehends that good**, making it a reason
   that actually governs this productive exercise?

The first concerns the recipient's standard; the second its productive
ground; the third the source's practical reason. A producer can give a
recipient a real capacity without exercising that capacity itself. Conversely,
calling a capacity good does not explain its production. Neither transition
is settled by the word “purpose.” The intellectual account has a substantive
answer to the third question when actual governance is warranted, but cannot
acquire that warrant merely from answers to the first two.

| Selected sense | What must be explained | What that alone does not supply |
| --- | --- | --- |
| Causal directedness | Why this power has characteristic manifestations and operating conditions. | A standard distinguishing proper performance from another lawful outcome. |
| Proper function or biological good-for | Why a contribution belongs to this bearer's organization or selected history, and how a token can fail at it. | Optimality in every respect, a moral obligation, or the producer's apprehension. |
| Intrinsic finality | Why the recipient's form or activity is ordered to a characteristic completion, including impeded cases. | That this ordering must ultimately be possessed as known. |
| Intentional purpose | Why an agent's apprehended end actually organizes the relevant exercise. | That the intention is good, that it determines every detail, or that this agent is the ultimate source. |

These distinctions identify explanatory tasks; they do not declare mutually
exclusive ontologies. A material organism may also be a hylomorphic whole,
and a material realization does not establish exhaustive physicalism.
Likewise an impersonal necessary source need not be matter or a composite
biological mechanism. An objection to one of those narrower proposals must
identify the bridge that makes it relevant to the strongest impersonal rival.

### 46. What the material account now explains

The repository already contains a positive account stronger than “the
system tends to survive.” In the
[organizational-function investigation](goodness-form-end-definitions.md#organism-organization-as-a-candidate-due-standard-2026-11-14),
different structures replenish resources, preserve a boundary and renew one
another. Capacity, current exercise, outside support and delayed compensation
remain separate. Loss of a native capacity can leave actual survival intact
while removing resilience to specified challenges. Conversely a competent
capacity can be inactive because support makes its exercise unnecessary.
Changing an incidental emission has no return path in the selected model.
These differences are fixed by causal relations and interventions, not by
adding a `Good` label to the successful trajectory.

That investigation also preserves the selected-effect account's positive
explanation of proper function, including defective tokens and present
mechanisms. Current organizational contribution and historical selection can
support different but overlapping claims; neither is merely “chance.” The
finite recurrence is an analyst model with numerical checks, not an empirical
organism or a newly Lean-certified theorem. The cited biological studies
support particular distinctions between supported growth, photosynthetic
competence and lower current output. They do not validate every model input
or identify a metaphysical bearer.

The evaluative step remains substantive: maintaining or restoring an
appropriate capacity is a good **for this bearer in this respect**. It has
positive warrant in the connection between loss of the capacity and loss of
the bearer's characteristic activity. It is not an arbitrary preference, but
neither is that warrant a proof that every persisting organization is good,
that maximum persistence is its highest end, or that the selected reference
class is correct. The existing `DueActualityThesis` keeps `GoodIn` independent
of the supplied form/end and possession relations precisely so this claim
can fail. No new definition erases that open application.

Conflict makes indexing essential. A process may sustain one organization
while damaging another. That does not make both causal descriptions false
or all biological evaluation subjective; it blocks inferring one
all-things-considered ordering from their separate local goods. Similarly,
a contribution to an organism's maintenance is not automatically the
Fifth Way's `Best x e`. Its registered reading concerns what is best **for
the same x**. Changing x from an organ to the organism, its lineage, or the
ultimate source changes the premise. No optimality or bearer switch is
licensed by the observed benefit.

The result is positive and limited: material organization supplies a
substantive way in which nonknowing parts can have functions and fail at
them. It challenges an argument that such functions are unintelligible
unless the part apprehends its end. It does not establish that the
organization has no intellectual cause, or that every kind of finality
reduces to maintenance or selection.

### 47. The strongest intellectual challenge and the exact impersonal reply

An unrealized end need not act backward from the future. Present powers,
form and organization can explain a directed process before its completion.
The source reading in the teleology companion grants that positive
intrinsic role. The stronger intellectual challenge is therefore about the
**origin of the order**, not the temporal location of its later result:
what makes heterogeneous means count as fitting for an independently
specified completion, and makes impeded realization a failure?

Apprehension supplies a positive answer. An agent can understand the
recipient's good and the relevance of means, and make that understanding
the productive measure. The same end can organize different means, and
the measure need not be copied from the eventual outcome. Where this
practical relation is evidenced, it explains more than a list of efficient
transitions. At the ultimate-source scope, an understood recipient good
also provides a reason for communication without a need in the producer.
This is the strongest personal contribution, continuous with §§24–26.

The proposed exclusion of the rival needs a further premise: every
noncognitive instance of such ordering is received or executive, so
underived original ordering must be intellectual. The natural-form rival
targets that premise. Its generative power is intrinsically specified by
the kinds of capacities and completions it produces; it does not first
produce an indifferent object and then attach a purpose. A creature's
failure under interference can follow from those same capacities and
conditions. Its good-for standard belongs to the creature's nature,
while that nature depends productively on n. This is a positive proposal
for questions 1 and 2, with the ultimate application still to be warranted.
It does not answer question 3 affirmatively, and cannot be credited with
an apprehended reason by renaming its orientation.

The biological mechanism cannot simply be promoted into this ultimate
account. Its functional loop depends on parts maintaining a bearer that
in turn maintains those parts. The retained underived, necessary and
intrinsically invariant source does not depend on its contingent recipients
to keep it in existence. This uses the underived-source commitment and
the specified productive relation; necessity alone does not establish
causal independence. Hence
recipient-maintenance is not source-maintenance, and the latter cannot
explain the source's production here. This is a specific failure of
transfer, not a refutation of the local explanation. The strongest rival
instead proposes that n's own productive nature gives recipients their
forms and appropriate powers. Its recipient-directed profile is an
additional metaphysical commitment, with local organization offering
an intelligible explanatory analogy rather than an ultimate instance.

Both candidates must therefore identify the **actual relevance** of
recipient-good to n's production. A power characterized only as “whatever
produced the observed good result” does not explain that relevance. A
mind credited only with knowing all possible goods does not explain it
either. The stronger proposals specify, respectively, a generative nature
or an operative practical measure whose identity constrains the account
of production, including possible deviations, independently of merely
copying the actual outcome. Such constraints need not uniquely determine
one total order: the same nonnecessitating causal scope is retained.

The original-ordering principle remains available as a direct or
cumulative intellectual commitment. Its conditional force is not erased
because its ultimate application is contested. But the archer analogy,
nonexistence of a future effect, local malfunction and lack of a need in n
do not independently show that all intrinsic noncognitive specification
is borrowed. Nor does a refusal of further explanation establish the
impersonal account. Each ultimate stopping point must be assessed for
its actual content, coherence and explanatory work, under the same rule.

### 48. Revised comparison and the remaining discriminator

The finality investigation improves the account of what each candidate
must supply. It supports real local function without apprehension by the
functional part, while denying that a local self-maintenance explanation
automatically covers an underived source's production for others. It
also strengthens the positive intellectual case by identifying what
apprehended completion contributes as an operative measure. It does
not establish the exclusivity of that ultimate grounding.

| Proposed account or inference | Assessment on the tested requirement |
| --- | --- |
| Actual recurrence or persistence alone establishes proper purpose | Inadequate: it conflates functioning, compensated defect and supported inactivity, and does not fix the relevant bearer or good. |
| Selected history plus current organization explains a specified biological function | Positively supported within its historical, causal and reference-class scope. It need not deny intellectual governance elsewhere. |
| The same maintenance loop explains the necessary source's orientation toward recipient goods | Inapplicable as stated: the producer is not maintained by those recipients. The stronger generative-nature proposal must be assessed instead. |
| Intellect understands the good, therefore it actually produces for that good | Inadequate: the nonoperative-intellect case still separates apprehension from formative governance. |
| The recipient's independently specified good actually governs n's exercise as apprehended | A substantive personal explanation when warranted; it neither entails exhaustive determining contrast nor follows from a good output. |
| An intrinsic noncognitive generative nature actually supplies the recipient's directed powers | A substantive ultimate rival, with its constitutive and application commitments explicit. The present tests do not defeat this strengthened proposal. |

**Overall provisional judgment:** the argument that purely nonknowing
material activity cannot sustain any real function is not supported by
the inspected causal and biological evidence. The stronger claim that
all original final ordering ultimately requires intellect remains
positively motivated by practical intelligibility and the communication
of understood good, but not established against the granted intrinsic
generative rival. Neither the absence of an ultimate cognitive exclusion
nor the positive local mechanisms proves that the two complete source
explanations are equivalent. The prior ultimate-source underdetermination
is retained with a more precise division of explanatory work.

Upward revision for the intellectual case requires warrant that this
source's productive specification is actually possessed and used as
understood, or a defended original-ordering principle excluding the
positive intrinsic rival at the shared scope. Upward revision for the
impersonal case requires a constitution and application of its own
generative orientation that explains the same recipient-relative
standards and their failure conditions while retaining the necessary,
invariant and nonnecessitating source. A contradiction with a shared
constraint would count against either. A change in the independently
justified bearer, due standard or relevant conditions can revise a local
function attribution without deciding source cognition.

The exact existing root bridge remains `65c409cc` together with
`46326b43` and `4c79298d`, through `11628966`, to intellect `29818edd`.
Local directedness does not supply the bundle's knowing director,
same-end reduction to an intellectual unmoved director, or identity
conditions. Actual practical direction remains additional even if that
intellect conclusion is supplied. The existing teleonomy countermodels
are scoped logical controls, and the due-goodness results are conditional
on their full supplied standards. No new Lean result, source claim,
definition, support edge or premise discharge is introduced here.

This complete continuation and the updated existing attempts are proposed
for independent semantic review. The previously accepted §§37–44 and
their modal/simplicity controls retain their own review scope; their
acceptance does not automatically cover this new finality assessment.

## Research attempts citing this note

- [Issue 1737 same-source contingent creation, omission, and selection adequacy](../../corpus/attempts/divine-knowledge-choice-creation-1737.json)
