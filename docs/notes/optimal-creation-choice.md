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


## Rational authorship versus brute selection (2026-11-23; proposed, unreviewed)

Scope: #1737, #735/#750, #1875, #1887. Evidence baseline
`8083301a037428574d0e46b1064d8f6d858da377`; related open work #1901,
#1909, #1910 and #1904 is not assumed as merged. Fix the same actual source
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
The third admits a partial contrast answer (some alternatives excluded), a
productive answer for an individual outcome, or an exhaustive determining
answer. Only the last demands that the total grounds exclude every admitted
incompatible alternative. Distinguish a reason for the source's existence
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
computed frontier-diff and offline corpus validation remain pending.

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
Attempt 7d015c02 records the proposed checkpoint.
