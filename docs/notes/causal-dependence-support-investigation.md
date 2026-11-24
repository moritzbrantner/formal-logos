# Causal dependence: support for three common terminal premises

Date: 2026-11-13. Frozen comparison: `03d97b48a86d4b7d7bbedcb4441398ce3a9dadef`.
Context: [God-existence support formula](god-existence-support-formula.md).

This investigation preserves the existing premises and asks what could warrant
them. It identifies a useful connection to an existing strict-grounding result,
specifies a sufficient modal bridge, and separates an esse-specific causal route
from the broader efficient-cause premise. The proposed bridges below are draft
specifications for review, not registered propositions or newly verified
theorems. No definition, source claim, Lean declaration, or proof status changes.

## 1. Targets and present assessment

Write `D x y` for the frozen `DependsForBeing x y`, `W x y` for
`CanBeWithout x y`, and `E c x r` for `EfficientlyCausesIn c x r`.

| Common premise | Exact existing content | Provisional warrant and best next route |
|---|---|---|
| P1, `000e1f65-6e74-5519-bbf3-300d5f61ada8` | `∀ x y, D x y → ¬ W x y` | Strong prima facie warrant for an essential, source-specific existential prerequisite. The frozen counterfactual sense still needs a bridge to the full admitted possibility range. Section 4 specifies one through persistence of dependence and centering. |
| P2, `0f49d71e-09e6-5a9c-b7e7-e0e9b8fe769c` | `∀ x y, x ≠ y → D x y → ¬ D y x` | Strong motivation for strict explanatory dependence; numerical distinctness and existential coimplication alone do not supply strictness. Section 5 connects an explicit strict-grounding interpretation to an existing PLG nonreversal result, without assuming well-foundedness. |
| P8, `c0d99549-799c-5a01-9b59-75fe88550b26` | `∀ c x r, E c x r → D x c` | The received-esse/conservation reading supplies a substantive conditional rationale. The frozen quantifier covers every respect of causing the same bearer, so esse-specific support does not discharge it. Section 6 gives the narrower existing route and the exact additional export needed for P8. |

All three remain open, supported analyst premises. That status does not make
their direct warrant worthless, and developing a derivation does not replace
the option of accepting a premise directly after considering its meaning and
grounds. Conversely, a plausible narrower interpretation cannot establish the
unchanged broader proposition. No requirement of independent or disjoint
support trees is imposed.

## 2. Semantic contract and evidence reviewed

The controlling definitions are:

- `bf26b9b2-41ed-55b0-9557-dae90ab9b81f`, dependence for being: x would not be if
  y were not, including the q.44 impossible-antecedent application. Its Lean
  parameter is a supplied binary relation. Neither asymmetry nor transitivity
  is built in. Self-dependence is compatible with this counterfactual reading.
- `d0b06beb-e8cb-5cb8-af2f-bc7f8cc004b2`, being-without: a real possibility of
  x being while y is not. It is a separate supplied relation.
- `69c0b23e-54c7-57a1-871f-839c6e5514c6`, `EFFICIENT_CAUSING_2`: c here and now
  efficiently causes **x's being r**. It does not stipulate that every such c
  causes the existence of x. The relation is also distinct from `CausesIn`.
- `56989bd0-a232-56ea-9093-c89350effff4`, direct per-se conservation of esse:
  the source account includes continuing productive dependence. The later
  typed `SustainsBeing` candidate deliberately omits that dependence clause.
  Its name or time indexing cannot supply the missing implication.

The `related` and `dossier` CLI reports were inspected for every target before
proposals. The relevant arguments, result records, and Solution bodies were
then read. The two first targets had no attempts in this baseline; P8 already
had an extensive investigation. The filtered orphan report identified the PLG
results as presently disconnected from root paths; the connection proposed
here is not yet a new graph edge.

### Primary sources actually read

Selected existing witnesses were materialized successfully and their complete
selected text read: `AQUINAS-ST-I-Q44-A1` (Latin article),
`AQUINAS-ST-I-Q104-A1-EN` (English article), and `AQUINAS-IN-METAPH-V-L13`
(Latin lecture, including paragraphs 15–18). These remain the existing source
records. The following source summaries specify their scope.

| Reading and existing evidence | What the passage contributes; limits |
|---|---|
| [ST I q.44 a.1](https://www.newadvent.org/summa/1044.htm), ad 2; claim `3ed36bec-27f4-5c77-93d5-3b6724d65204`, source statement `7673ebac-f30c-5960-8a4a-d779db4b14e1` | Aquinas gives a dependence rationale for efficient causality even for a necessary effect, explicitly allowing impossible conditional terms. The main article's participated-being argument presupposes earlier divine simplicity and unity claims. This is neither an independent proof of God here nor a vacuous material-implication argument. It does not supply every semantic dictionary from cause to modal or ground relations. The materialized Latin controls the reading; the linked English is corroboration/navigation. |
| [ST I q.104 a.1](https://www.newadvent.org/summa/1104.htm), body and replies; claims `40aefb2e-c9b3-5bb1-8802-96bbc4e2ed83` and `da9c82ed-e886-5335-81c3-cebad9b27345` | Dependence follows the respect in which the agent causes. Causing becoming differs from causing being; the builder and retained heat illustrate the distinction. Direct conservation continues the giving of esse, without repeated creation by motion or time. This positively motivates esse-specific dependence. The article supplies neither a general transfer from a determination to its bearer's existence nor a neutral experimental adjudication between conservation and existential inertia. |
| *In Metaphysicam* V, lect.13, especially n.18; claim `95f41960-baf4-58ad-ba7f-b11b2f439f7c`, statement `489711d5-3589-5e33-997a-4ba8bce1f492` | The argument concerns pairs already ordered as prior and posterior; its being-without qualification is “in some way,” with generation/corruption examples. The passage motivates a directed dependence account of priority. It neither quantifies over every pair of distinct beings nor identifies its dependence with the frozen counterfactual relation. |

Two further primary texts were read from the author's public uploads. They
are current research readings, not new pinned corpus claims:

- Fine, [*Essence and Modality*](https://www.academia.edu/8908669/essence_and_modality),
  author draft headed June 1992/revised February 1993, opening discussion and
  singleton example: an essential existential condition implies corresponding
  necessity, while mere necessary coexistence does not determine the direction
  or source of an essential connection. The Socrates/singleton comparison
  explicitly separates these questions. Draft section incipits, not assumed
  journal pagination, locate this reading.
- Fine, [*The Pure Logic of Ground*](https://www.academia.edu/8908730/the_pure_logic_of_ground),
  §§1–2, printed pp.3–7: strict ground excludes the relevant weak reversal;
  weak ground can represent explanatory equivalence. The paper distinguishes
  **strict partial** from **partial strict** ground; they are not interchangeable
  in the mixed transitivity rule. The reading corroborates the existing
  `FINE-PLG-1-2` bibliographic passage and claim
  `092c0769-d552-5860-889e-6bcf7b0f4aa6`. It does not upgrade that record to a
  hash-pinned witness. The canonical NYU PDF fetch failed; no unread PDF is
  attributed here.

### What is new relative to the earlier causal investigation

[Causal transitivity 1399](causal-transitivity-1399.md), attempt
`56ae2547-ae69-46f4-93b5-4c8ee786ed13`, already investigated received actuality,
the becoming/being distinction, existential inertia, impossible absence,
same-bearer identity, and the all-respects scope problem. The present source
reading corroborates those findings. It is not a new discovery that a heater's
causing heat does not by that fact explain the bearer's esse.

The additional work here is: (i) an exact sufficient P1 package that exposes
where essentiality must enter; (ii) a concrete connection from P2 to the
existing PLG nonreversal theorem, with its consistency and interpretation
requirements; and (iii) an explicit export package showing what the already
available esse-specific route would need to conclude the unchanged P8.

## 3. Reusable results and their full premise packages

These are existing registered results whose records and relevant Lean bodies
were inspected. No fresh Comparator or Lean execution is claimed.

| Result | Complete premises relevant here | What it actually concludes |
|---|---|---|
| `972ed7e5-098f-5ca6-9685-98d2cee48db8`, `Round2PerfectionPrimacy.efficientCauseNotDependent` | P8; `NothingIsEfficientCauseOfItselfReading` (`8b2561cd-3743-536d-a110-3352fdb0c6b9`); P2 | An efficient cause does not existentially depend on its effect. It consumes P2 and P8; it cannot establish them without circularity. |
| `47957c28-218a-58e4-94e4-5220a0c45795`, `Round2PerfectionPrimacy.nonmutualDependenceSuffices` | P1; independence allows being-without (`8ab3d114-d6e2-5f6d-805b-ae901f56d39b`); priority by being-without (`97fa3a0b-eb23-5fb1-9741-c1f09fb72206`) | Nonmutual dependence suffices for simple priority. No proof of P1 is supplied. |
| `695c2113-50b7-5b6c-ab51-e3cc02526d99`, `CausalMapsBatch1.efficientCausePrior` | P8; efficient cause independent of effect (`47b151ca-f500-5a7c-80d4-33bb90247ee3`); nonmutual dependence sufficient for priority (`bf93f259-29b4-53df-ae5b-ac7f522ea33d`) | Efficient causes are simply prior. It cannot be used backwards to justify its own dependence premises. |
| `db9175af-5a90-5cb2-b3e0-b8e25537be88`, `Round2Grounding.esseCauseGroundViaDependence` | Esse causes exist at the selected world (`c99f9d23-3f05-5c3c-9279-44a59e445a14`); esse causes are concrete (`82eeeb3c-b96d-5483-b1ac-f6059ff02211`); a distinct esse cause is depended on (`2068f91c-1eeb-5dbb-a71a-f7b6a12bb495`); actual concrete dependence is grounding (`2e248016-f8bf-5d8a-931e-7f9ebbb13e42`) | For actual concrete x, a distinct cause c of x's esse is actual, concrete, and a ground of x. All four premises remain explicit. Neither `CausesIn`/`EfficientlyCausesIn` identity nor an all-r extension follows. |
| `92c24bb5-763e-55d0-90b1-ef53d0bd0ab6`, `Modern.Fine.StrictGroundAcyclic.consistentStrictGroundAcyclic` | The corpus argument has no external premise statements because the conclusion itself universally quantifies the sequent theory S and **assumes `Consistent S`**. | No derivable finite strict cycle; no strict ground with its weak reversal; well-foundedness only if the atom type is finite. The theorem does not prove a selected S consistent or interpret actual dependence as ground. |

The fourth row is a useful existing route around an unnecessarily broad causal
interface, not a proof of P8. Its second registered variant,
`9783ec19-a74e-4198-8217-cc4d7175709f`, replaces the unscoped concreteness
premise with a separately derived existence/concreteness calibration; it also
does not discharge the esse-dependence premise.

The PLG theorem's finite-cardinality part is unnecessary for P2. Result
`fbc592d0-8fc4-5ac9-97f3-9302f3241d57`, statement
`73707346-9ddf-5c21-92d7-952739a9dc2b`, supplies an existing consistent PLG
infinite-descent example. Thus using nonreversal here does not silently import
termination or a first ground.

Other tempting shortcuts fail on scope. `Round2Grounding.asymmetricFromWF`
concerns a supplied grounding relation among actual concreta; it is not the
global P2. `asymmetricViaDependence` assumes dependence asymmetry, rather than
proving it. The global `DependenceForBeingAsymmetric` statement
`da8e6b60-4dab-5858-9c8d-f6e84c821970` even excludes self-dependence; it cannot
replace the deliberately distinct-only target without a sense change.

## 4. P1: from counterfactual dependence to essential absence exclusion

### Positive rationale

For a source that is an essential prerequisite of this very being, retaining
the being while removing that source violates the account of what the being
is. This is a substantive reason to accept a scoped P1: it connects an
independently specified identity or essence condition with real possibility.
It is stronger than the observation that the source usually accompanies the
effect, and differs from saying that any source of the same kind would do.

An illustrative package is a singleton under an ontology in which its
particular member belongs to its essence and an existing set's members exist.
Those identity and existence principles yield the relevant inability to exist
without that member. This is a conditional illustration of how the bridge
could be warranted, not a proof about every concrete effect or evidence that
set ontology is obligatory. It also does not prove that the singleton's
ordinary counterfactual relation has the exact frozen q.44 interpretation.

The needed distinction is between an identity-preserving possibility in which
x survives without **this y**, and a different individual or a different kind
of source satisfying a generic description. “Every received act has some
source” alone leaves substitution possible. Historical origin dependence also
does not immediately settle present coexistence with the originator.

### Draft sufficient package P1-A

Fix one reference situation, one domain of bearers, one interpretation of
cross-situation identity, one time/aspect convention, and one admitted
possibility predicate `A v`. Let `Exists v x` mean existence in that same
comparison, and let `Dv v x y` be a world-indexed extension of the intended
counterfactual dependence. The draft obligations are:

```text
Possibility witness:
  ∀ x y, W x y → ∃ v, A v ∧ Exists v x ∧ ¬ Exists v y

Persistence of the dependency when its bearer exists:
  ∀ x y, D x y → ∀ v, A v → Exists v x → Dv v x y

Centering at an admitted situation where the source is absent:
  ∀ v x y, A v → ¬ Exists v y → Dv v x y → ¬ Exists v x
```

The proof plan is short: a witness to `W x y` supplies an admitted v with x
and without y; persistence supplies `Dv v x y`; centering supplies nonexistence
of x there. These conflict. Only the displayed direction of the possibility
representation is needed. Agreement of `Dv` with the frozen D in the reference
situation is part of interpreting it as an extension, even though that
agreement is not an additional logical step in this proof sketch.

The main substantive input is persistence. Its best candidate warrant is an
independently supported **essential existential requirement on this source**,
plus the claim that admitted possibilities preserve that essence. If
persistence is introduced merely because P1 is desired, this package explains
the logical gap but does not supply new warrant. Centering is also an explicit
rule of the chosen counterfactual semantics, not a property already registered
for the primitive D.

A nearest-situation counterfactual may hold at the reference situation even
though a more remote, identity-preserving possibility has a replacement
source. That is a concrete reason to distinguish the two questions. It is not
by itself evidence that such a replacement exists for the metaphysical source
at issue. A freely assigned finite model would only diagnose non-entailment.

For necessarily existing sources, absence has no ordinary possible witness.
The modal exclusion may then be immediate, while the q.44 dependence question
still asks for a meaningful nonvacuous counterpossible account. P1-A does not
construct that account or infer productive dependence from the absence of
possible absence worlds.

### Assessment and next test

The strongest positive route is essential source dependence, with direct
prima facie acceptance available in a clearly stated local domain. The exact
universal P1 remains unresolved because the frozen D does not already certify
that every one of its links persists across all admitted possibilities.

The next discriminating test is to take a defended instance of D and specify
its identity conditions and source role before evaluating absence. Does the
same bearer admit a different source while retaining those conditions? If
not, give the independent essentiality argument; if so, determine whether the
original D was contextual or historical. Neither conclusion should be selected
by changing the comparison domain after seeing the answer.

## 5. P2: a new connection to strict grounding without well-foundedness

### Positive rationale and exact reusable theorem

An explanation in which y supplies the very existential actuality derived by
x is naturally directed: using x's receipt of that actuality to account for
y's supplying it threatens to leave the receipt unaccounted for. This gives
prima facie motivation for strict existential explanation. To turn that
motivation into P2, the work is to justify that D expresses this kind of
derivation, not merely co-presence, reciprocal constraints, or explanatory
equivalence. Numerical distinctness alone does not perform that work.

The existing PLG result offers a precise conditional consequence. In the
repository vocabulary:

```text
StrictlyGrounds S A B := Derivable S (strictPartial A B)
Consistent S := ∃ s, ¬ Derivable S s

For every Atom and S, if Consistent S, then:
  ∀ A B, StrictlyGrounds S A B →
    ¬ Derivable S (weakPartial B A)
```

This is the second conjunct of statement
`307261a0-1fcf-5920-a3cd-ebfe29a7617e`, proved by the existing result above.
Its Solution combines `Derivable.transStrictWeak` with noncircularity and
consistency. `Derivable.subsumptionStrictPartial` converts a reverse strict
edge into the prohibited reverse weak edge. This identifies actual reusable
inference machinery, rather than appealing generally to “grounding theory.”

### Draft sufficient package P2-A

Choose atoms that faithfully represent existence facts for the same beings in
one fixed situation, with mapping `e : B → Atom`. Require:

```text
Consistency:
  Consistent S

Dependence-to-strict-ground interpretation:
  ∀ x y, x ≠ y → D x y → StrictlyGrounds S (e y) (e x)
```

Given distinct x and y with both dependence directions, the interpretation
supplies two opposite strict edges. Subsumption makes the second a weak
reversal of the first; the existing nonreversal theorem excludes it. This is
a proposed composition, not a newly executed Lean proof. It needs neither a
finite universe nor well-foundedness, a first cause, or a general sufficient
reason principle.

The mapping is oriented cause/source fact first, dependent existence fact
second. Injectivity of `e` is not needed by the displayed syntactic argument,
but honest individuation, actuality, and the interpretation of the atoms are
still essential to applying it to the intended beings. If one can justify the
mapping only for actual concreta or a selected class of essential dependencies,
the result is that restricted P2. A further coverage premise is needed for the
frozen unqualified quantifier.

### What the package gains, and what it does not

The PLG theorem is independently reusable and currently has no root-path
consumer. It avoids deriving P2 through efficient-cause priority results that
already consume P2. It also separates noncircularity from the stronger issue of
infinite regress.

The substantial new bridge remains open. In the intended strict-partial sense,
nonreversibility belongs to the interpretation of strictness. An argument that
simply labels every D link “strict” has moved the disputed content into the
dictionary. To improve warrant, the dictionary needs an independent account
of why existence is supplied/constituted on one side and received on the other.
Consistency of the selected S also needs warrant; the universally quantified
PLG theorem cannot establish that S.

The genuine scope alternative is weak explanatory dependence or reciprocal
constraints. Fine's weak/strict distinction provides positive vocabulary for
that alternative, but examples of equivalent truths are not automatically
examples of distinct beings mutually dependent for esse. The present reading
therefore does not record a metaphysical refutation of P2. It identifies what
a proposed counterinstance would have to preserve: distinct bearers, the same
existential respect and situation, both links in the **frozen** D sense, and
grounds for treating them as more than an arbitrary relation assignment.

Ordinary feedback across successive times or different respects is likewise
not a reciprocal same-respect existential derivation. It can challenge a
careless unqualified causal slogan without settling the typed premise.

### Assessment and next test

P2 has a strong conditional route under strict explanatory dependence. The
existing source support motivates that direction for already ordered
prior/posterior pairs; it does not independently quantify over all D pairs.
The key next task is an existence-fact bridge for a substantive dependency
instance, together with an independently motivated consistent theory of its
grounds. A successful local bridge should be tested for extension of scope
before registering the global premise. No termination assumption is needed.

### Registration and infinite-series test (2026-11-24)

P2-A subsequently landed. Result `40b8313e` takes consistency
(`fea5942a`) and the distinct-edge interpretation map (`42756c07`) to P2
(`0f49d71e`). Result `972ed7e5` consumes that exact P2, together with P8
and no self-causation, to conclude that a cause is independent of its effect
(`47b151ca`). Result `a01e0429` realizes the full package on a single series
in which every member has a further cause. This locates the outstanding
termination question at the per se regress premise (`97f5850f`).
[Model, scope and warrant](distinct-dependence-strict-ground-route.md#the-infinite-series-at-the-efficient-cause-consumer)

## 6. P8: received esse, same-respect effects, and export to the bearer

### Positive conservation argument, with its premises exposed

The strongest candidate is a received-act argument, already developed in the
earlier note. It can be expressed without building the desired dependence into
the name of a causal relation:

1. The present esse of this very bearer is received and currently derivative,
   rather than merely having been received at its origin.
2. Such a current derivative actuality requires a concurrent productive
   actualization; a historical production plus a persistence law does not
   exhaust its explanation.
3. The identified agent's relevant contribution supplies that esse and is
   indispensable in the counterfactual comparison, with the same bearer,
   time/aspect, causal role, and background conditions retained.
4. Withdrawal of that contribution is appropriately represented by the frozen
   dependence counterfactual, including an explicit account when source absence
   is impossible.

These are proposed metaphysical and semantic premises, not new attributions to
a source. They make clear why the conservation interpretation can support
existential dependence: present being is received through an indispensable
present act. They also make clear why origin-receipt, essence/esse nonidentity,
or a field named `givingEsse` alone is insufficient. Premises 2–4 still need
defense for the selected case.

The global divine-conservation conclusion in q.104 already presupposes God.
Importing that conclusion into a proof of God's existence would beg the
question. What is reusable here is the general analysis of becoming, being,
and continuing source contribution, conditional on an independently supported
instance. Neither the source nor this package supplies a new God-existence
premise without those independent grounds.

The existing narrower sibling is already available:

```text
2068f91c-1eeb-5dbb-a71a-f7b6a12bb495
EsseEffectDependsOnItsCause:
  ∀ c x, c ≠ x → CausesIn c x esse → D x c
```

It is an open analyst premise, not a closed result. Its four-premise route to
actual concrete grounding is listed in section 3. It supplies a useful
destination for a well-supported received-esse account without requiring all
efficient causality to have the same scope.

### Draft sufficient package P8-A for the unchanged target

To derive the frozen all-r P8 from that sibling, one sufficient package is:

```text
EsseEffectDependsOnItsCause CausesIn esse D

NothingIsEfficientCauseOfItselfReading E
  (∀ x r, ¬ E x x r)

Same-bearer esse export:
  ∀ c x r, E c x r → CausesIn c x esse
```

For an E edge, the second premise gives distinctness; the third supplies an
esse-causing edge with the SAME c and x; the first supplies D. This specifies
the missing universal transfer. The no-self premise must be justified by a
route that does not already rely on the P8 being derived; using
`CausalMapsBatch1.nothingEfficientCauseOfItself` for it would be circular here.

The export is not present in the definition of E and is not supplied by the
source scope reviewed. Even a universal conserver of all bearers would not
show that every distinct agent producing an accidental determination is that
bearer's conserver. Replacing x with the temperature, illumination, or event
that c produces changes the endpoint and does not establish P8 for x.

A same-respect alternative would introduce dependence of **x's being r** on c,
then prove a separate transfer to the existence of x when r is esse or
independently shown essential to x. That is a new typed sibling/bridge project,
not a reinterpretation of the current target. When reusing the existing
esse-specific sibling, the separate `EfficientlyCausesIn` to `CausesIn`
dictionary must also be explicit.

### Evidence, alternatives, and limits of illustrations

The builder/house and retained-heat examples support the need to distinguish
causal roles; they do not discriminate a conserver's absence because they
remove a producing activity of a different kind. Likewise, the historical
illumination analogy should not be promoted to a present-day physical
measurement of instantaneous dependence. A controlled interruption could
provide evidence for a particular maintained process; identifying that process
with the esse of its bearer needs a further argument.

The serious alternative examined in the earlier note is historical production
plus a stable persistence law: a presently actual bearer persists unless an
independently specified destructive condition occurs. To carry an existential
conclusion, the law must explain why every existential loss is covered by those
conditions. “No change” cannot simply abbreviate survival, and mere qualitative
constancy is not that coverage. Conversely, rejecting this alternative requires
an argument that only concurrent efficient actualization explains received
esse. Neither side is established merely by restating its adequacy requirement.

An intrinsic power that produces its own bearer's existence may raise the
priority circularity treated by the existing self-actualization results. That
does not automatically exclude an extrinsic historical or law-based account,
nor does it exclude a being maintaining some already present determination.
The same identity, respect, and time must survive the comparison.

### Assessment and next test

The received-esse route retains substantive positive warrant; the exact
strengthening to every respect remains poorly supported by the sources and
interfaces inspected. This is a reason to pursue the narrower route in
parallel, not to delete the old premise or declare a metaphysical falsity from
a mathematical omission model.

The next discriminating investigation needs an independently described
productive contribution to the existence of one and the same bearer, followed
by a reasoned comparison with the historical-law account. A new Boolean loss
flag, a predicate named “adequate explanation,” or a repeated appeal to origin
does not resolve the remaining issue. For the unchanged P8, an additional
same-bearer argument covering every causal respect would still be required.

## 7. Joint constraints, outcome, and reopening conditions

These three premises should not be assessed under shifting senses of D. If P1
is combined with the separate independence-allows-being-without premise and
classical contraposition, the resulting draft equivalence is `D x y ↔ ¬ W x y`.
Under a full modal interpretation of W, P2 then rules out reciprocal necessary
coexistence of distinct beings. This is a conditional interaction to inspect,
not an observed metaphysical counterexample or a newly verified corpus result.
Necessary backgrounds and essential coexistence must be handled explicitly
before a global modal collapse is adopted.

The most useful new connection is **P2-A**: the existing PLG nonreversal result
can be composed with a separately defended dependence-to-strict-ground bridge.
Its exact open obligations are consistency of the selected sequent theory,
faithful existence-fact interpretation, and coverage of the frozen D domain.
The most direct source-supported causal continuation is the existing
esse-specific sibling; its received-act rationale and historical-law rival
remain explicit. P1-A gives a concrete way to identify and investigate the
essentiality premise needed by a modal continuation.

No root premise is discharged and no support edge is registered by this note.
The work preserves both direct acceptance and conditional derived options.
Reopening is warranted by a materially better essential-source argument, an
actual dependence/strict-ground interpretation with a consistent theory, a
productive account of the same bearer's present esse, or an independent
existential persistence/destruction-coverage argument. Further diagrams or
arbitrary relation assignments alone would not settle these questions.

## 8. Validation boundary

The current work adds this research note and three attempt records only.
`truth check` passed, reporting 545 attempts and the existing corpus warnings.
`source_evidence.py check` passed for 512 passages and 2,048 formalized claims;
its one bibliographic and one permanently unavailable witness remain explicitly
not byte-verified. `docs_index.py`, staged `git diff --check`, and
`attribution-check --base 03d97b48a86d4b7d7bbedcb4441398ce3a9dadef` passed;
the attribution check found no new or changed stating claim.

Computed `frontier-diff` against that baseline reports `changed: false` for
both the default Catholicism root and `STMT-GOD-EXISTS`, with no added/removed
support bundles or route changes. The God target retains 314 support bundles
and 396 open premises (276 bare, 40 stated, 80 supported). These are ordinary
CLI frontier counts, not a new recomputation of the terminal BDD family.

The configured verifier toolchain is unavailable in this worker environment.
No fresh Lean, Comparator, or NanoDa success is claimed; unchanged registered
formal results are reused as existing evidence.

## Current cluster assessment under the substantive objection standard (2026-11-18)

**Scope and boundary.** Issue #1751, walk of the GOD_4 prima via route until
its premises bottom out, lane B: existential dependence, simple priority and
grounding. Drafted on main `df4909cb025d2e53fee6071a32defe9cf2721284`. The root
is GOD_4 exists `8626f8a5`; its cheapest route is the prima via argument
`ed7c588a`. Expanding each open premise of that argument through its cheapest
verified support ends in 93 open leaves. This section assesses sixteen of them.
At this baseline `truth currentness` for the GOD_4 root reports 423 open
premises (84 current, 158 legacy-only, 181 none); of the sixteen, nine are
legacy-only (`c0d99549`, `42756c07`, `000e1f65`, `97fa3a0b`, `47aff057`,
`09b88101`, `f10d5632`, `2e248016`, `402cf70f`) and seven have no attempt
(`fea5942a`, `d85de8e1`, `3ef67739`, `71454b27`, `d6e558d0`, `57c5ed67`,
`5dacb0db`). Attempt `9d71e28d-d492-4797-9221-45fa517a6e6b` carries the
compact current assessment.

This note is the owner because it already holds the semantic contract for `D`,
`W` and `E` and the evaluations of three of the sixteen: P1 `000e1f65`, P8
`c0d99549` and the strict-ground package P2-A, whose two inputs are `fea5942a`
and `42756c07`. The narrower priority note
([priority-independence-logic-support-investigation.md](priority-independence-logic-support-investigation.md))
and the strict-ground note
([distinct-dependence-strict-ground-route.md](distinct-dependence-strict-ground-route.md))
are reused, not repeated. `8ab3d114` is current in attempt `dd24400b` and is
used here, not reassessed. Lane A owns the motion and causal-chain core
(`6b9fedc2`, `57552dce`, `a594d8c4` and others); where a premise here shares a
dependency with that core, the dependency is named and not assessed.

Earlier sections stay unchanged under their own dates. This section changes no
theorem, Challenge, claim, statement, definition, relation, closure or formal
status. Observations marked "analyst observation" are unregistered and not
Lean-checked.

### (a) Fixed meanings

- **Dependence for being** `D x y` (`DependsForBeing`, definition `bf26b9b2`):
  x would not be if y were not, in the sense ST I q.44 a.1 ad 2 gives to an
  effect's relation to its agent cause, impossible antecedents included. A Lean
  parameter with no structural property. Two forks stay open: the diagonal
  (reading (a) reflexive, reading (b) strict; attempt `a4d430a0`), and
  originating versus sustaining dependence (#1626, open; the time-indexed split
  exists only for *cause of being*, disambiguation `88a8fba7`).
- **Being able to be without** `W y x` (`CanBeWithout`, definition `d0b06beb`):
  y can be while x is not, "can" as real possibility. A separate parameter.
  Analyst observation used below: by the definition's own words nothing can be
  while it is not, so `¬W(x,x)` is a meaning postulate of the selected sense.
  It is not registered.
- **Simple priority** `P y x` (`PriorSimply`, SIMPLY_PRIOR_1, definition
  `1d9aa4d9`): prior by nature, not in time; glossed by act and potency
  (whatever is in potency in a respect presupposes a being in act in that
  respect). A primitive with no respect argument and no world argument.
  Disambiguation `be54be36` separates it from temporal priority only.
- **Efficient causing** `E c x r` (`EfficientlyCausesIn`, definition `69c0b23e`):
  c is here and now an efficient cause of x's being r, for any respect r.
- **Cause of being** `CausesIn c x esse` (definition `211a6432`): tenseless,
  mode-unspecified, with no world argument.
- **Profile vocabulary**: `ActualConcrete m w x` is `m.concrete x ∧ ExistsAt w x`;
  `m.grounds w` is the world-local selected relation, whose causal or
  constitutive reading is open (#1626); `ContingentAt` is definition
  `97f37f5c`; concrete means having esse in re (definition `008cb21a`).
- **Causing necessity** `CausesNecessityOf c x` (tertia via vocabulary, with
  `NECESSARY_PER_SE_2`, definition `2282c0ee`): c causes the necessity of x.
  No record separates causes of necessity among beings from demonstrative
  causes of necessity.
- **Ground**: Fine's PLG rules only, with no semantics (#349). `Consistent S`
  means some sequent is not derivable; `StrictlyGrounds S A C` means `A ≺ C` is
  derivable (disambiguation `23dd6f32`, sense 2).
- **Per se link** `CausesAsCaused` (definition `4a101a4c`); `cause` is the
  studied causal-history relation; `PerSeLinksIncluded` is definition `6c9be385`.

### (b) Where the sixteen enter the prima via

The cheapest expansion reaches them through three spines. Each line gives a
conclusion, the argument and its premises.

- **Spine I, no infinite per se regress, for `c1b68c21`** (through `675b71d2`,
  `226c38f6` and `f1ef9206`). `97f5850f` ← `b58472dd` (`e529c42f`, `37e9e7a0`,
  `f10d5632`). `e529c42f` ← `1bca81ef` (`a896d2b5`, `42890b45`). `42890b45` ←
  `e229bb2c` (`57552dce` of lane A, `e078f07b`, `d85de8e1`). `e078f07b` ←
  `8c629064` (`c0d99549`, `47b151ca`, `bf93f259`). `47b151ca` ← `1ffd6090`
  (`c0d99549`, `8b2561cd`, `0f49d71e`). `0f49d71e` ← `139070d5` (`fea5942a`,
  `42756c07`). `bf93f259` ← `75f11492` (`000e1f65`, `8ab3d114`, `97fa3a0b`).
  `37e9e7a0` ← `113c01ef` (`57552dce`, `e078f07b`, `7ad36aca`, `32d77f18`).
  `7ad36aca` ← `6009e16f` (`bf93f259`, `47aff057`, `09b88101`).
- **Spine II, at most one first mover via the maximum in being, for
  `c27dce66`** (through `697b7dc4`, `957a71fe`, `3e86eea5`, then `eaa4c679` ←
  `f53dd124`). `c71c068c` ← `dd7ee4b9` (`3ef67739`, `2e248016`). `d29cebca` ←
  `eddef85a` (`71454b27`, `d6e558d0`, `2e248016`). `86efed1a` ← `931319ea`
  (`47aff057`, `57c5ed67`, `2e248016`). `82cfaf26` ← `f9c69ee8` (`d96105fb`,
  `c18faab2`); `d96105fb` ← `4c43a8ec` (`406f0cbe`) ← `815d22c8` (`d5a94eb1`,
  `402cf70f`).
- **Spine III, pure act, for `6c18d52b`** (through `3e2366b5`: `74eb9113`,
  `a4d3261a`, `c6d6379b`). `74eb9113` ← `f8992ef7` (with `70e98bb5` among its
  premises); `70e98bb5` ← `1cb656a0` (`47aff057`, `5dacb0db`).

`47aff057` occurs in all three spines and `2e248016` three times in spine II.
`c71c068c` has two further registered supports (`9b14e6d7` via local causes,
`2162ca9d` via participation), so `3ef67739` and `2e248016` are one support
option there, not the only one.

### (c) End state of each premise

Lean content first, then the end state. "Derivable" names a short derivation
that is proposed for the formal owner and not certified.

| Premise and Lean content | End state | Strongest positive warrant, or reason | Conditions and shared dependencies |
| --- | --- | --- | --- |
| `c0d99549` `∀ c x r, E c x r → D x c` | **Open, blocked by a kept counterexample** (row 1 of (e)). Judgment revised; see the supersession paragraph in (g). | Esse instance only: the received-esse argument of section 6 supports the sibling `2068f91c` (`c ≠ x`, `CausesIn c x esse`). Claim `3ed36bec` supports, and does not state, the all-respects form. | Analyst observation: `c0d99549` follows from `e078f07b` taken on its own claim `3ed048c0` and the first half of `47aff057` (`E c x r → P c x → D x c`). So the counterexample also bears on that pair; see (d) 4. On the route it enters only through `8c629064` and `1ffd6090`, both under `e078f07b`. |
| `fea5942a` `Consistent S` | **Reducible:** with `42756c07`, for the selected `S` built from distinct-step `D`, it is equivalent to the open `702dc502` (distinct-step dependence has no finite cycle). One direction is `e86849cf`; the converse is proposed. | Analyst observation: for any relation R on atoms whose transitive closure is irreflexive, the set of strict sequents `a ≺ b` for `R a b` is PLG-consistent (interpret strict partial ground by the transitive closure of R and weak ground by its reflexive closure; every PLG rule is sound, and `a ≺ a` is never derivable). Take S to be that set for the distinct-step part of `D`, with the identity labelling; then `42756c07` holds by the assumption rule. | Hence, for some S and labelling, `fea5942a` with `42756c07` holds exactly when distinct-step `D` has no finite cycle: one direction is verified (result `e86849cf`, `mapForcesDistinctDependenceAcyclic`), the other is this proposal. An independently specified existence-fact theory would need its own soundness under Fine's semantics, which is not formalized. Off the route when `e078f07b` is taken directly ((d) 2). |
| `42756c07` `∀ x y, x ≠ y → D x y → StrictlyGrounds S (e y) (e x)` | **Trivial under the selection of `fea5942a`'s row; for an independently specified existence-fact theory, open, blocked by an unfixed sense.** | Directed existential explanation: what supplies existence is not in turn supplied by its recipient (section 5). With `fea5942a` its formal content is acyclicity of distinct-step `D`, which is more than the nonmutuality `0f49d71e` it is used for (attempt `1020b663`). | The atoms are uninterpreted (disambiguation `23dd6f32`); the causal reading reduces to efficient-causal asymmetry, and the constitutive reading does not cover the sun and light paradigm. Rivals: rows 5–7. The direct option `0f49d71e` is weaker and needs no ground theory. Off the route when `e078f07b` is taken directly. |
| `000e1f65` `∀ x y, D x y → ¬W x y` | **Open, blocked by the originating/sustaining fork (#1626).** | On the sustaining or essential reading: strong prima facie (section 4, P1-A). Claims `95f41960` (n. 18) and `da9c82ed` (q.104 a.1) support it. | On the originating reading the living-parent case is a kept counterexample (row 2): the child would not be if the parent had not been, and the child can be while the parent is not. The section 4 standing for the sustaining scope is unchanged. With `8ab3d114` and excluded middle it gives `D ↔ ¬W` (section 7). Off the route when `e078f07b` is taken directly and `97f5850f` is bypassed ((d) 2). |
| `97fa3a0b` `∀ y x, W y x → ¬W x y → P y x` | **Defended direct option, on concrete relata.** | Claim `ab5ec574` (In V Metaph. lect. 13 n. 15) supports the criterion for priority by nature in being (source statement `fa759767`); the transport to `P` is the open step (attempt `5cf65146`). | Scope condition, analyst observation, row 11: on a carrier with non-concrete candidates whose being is modally fixed, the criterion makes a non-concretum a `P`-relatum, which `57c5ed67` forbids. Restricting it to concrete relata, as in the n. 15 generation examples, removes the clash. No substantive objection to its sufficiency on concreta. Off the route when `e078f07b` is taken directly and `97f5850f` is bypassed. |
| `d85de8e1` `WellFounded P` | **Open, blocked; the substantive load-bearer of spine I as expanded, failing jointly with all-respects `e078f07b` on either reading of `P` ((f)).** | The instrumental-causation reasoning for no infinite per se series (moved movers move only as moved, `1e47e6db`, lane A; [borrowed-exercise-741.md](borrowed-exercise-741.md)). | Its support for `97f5850f` adds no discriminating warrant: the per se regress premise is its restriction to per se links, and whoever admits an infinite per se series denies both for the same reason (the statement says so). Its extra content, well-foundedness of all simple priority, has no separate warrant on file. Standing rival: row 4; joined with all-respects `e078f07b` on the causing reading, the kept counterexample of row 21. |
| `47aff057` `∀ y x, P y x → D x y ∧ ¬D y x` | **Open, blocked by the respect fork in `P`** ((d) 4). | On priority in being: claim `95f41960` (n. 18) supports the direction, and the 2026-11-13 judgment ("good conceptual and textual support" for the directional principle, transport open) is unchanged. | The forward half suffices for `931319ea` and `1cb656a0`; both halves are used only in `6009e16f`, which (d) 2 removes from the route. Joined with `e078f07b` on one `P`, it implies `c0d99549` and inherits row 1. |
| `09b88101` `∀ x y z, D x y → D y z → D x z` | **Open, and dispensable on this route.** | On the per se received-being reading: if x has its being only as received through y's own dependence on z, x depends on z (Second Way order). | Used only through `6009e16f` → `7ad36aca` → `113c01ef` → `37e9e7a0`, which (d) 2 bypasses. Row 8: Lewis's non-transitivity is kept only against the bare counterfactual clause. |
| `f10d5632` `∀ y x, perSe y x → cause y x` | **Derivable by selection.** | The studied relation is a parameter: choosing it as the per se efficient-cause relation, or any relation containing it, makes the premise reflexive inclusion. | The content then moves to `57552dce` (lane A): every per se link is an efficient causing in some respect, which definition `4a101a4c` glosses ("c efficiently causes x only insofar as …"). Row 16: it is substantive only if the studied relation is an event network (disambiguation `bedfab81`). |
| `3ef67739` `∀ x, AC x → ContingentAt x → ∃ y, AC y ∧ D x y` | **Open, blocked by the diagonal fork and by existential inertia.** | Supporting claim `7cd6850f` (CC100 #4, presentation): dependent beings depend on something. On the strict sustaining reading, a dependence principle for contingent concreta. | On reading (a) it holds trivially with `y = x`, and `dd7ee4b9` then grounds each contingent concretum in itself, which well-founded or distinct grounding excludes ((d) 3). On reading (b) it is substantive, and existential inertia is the standing rival (row 3). Repair: a distinct-relata sibling, used with `a8298fbd`. |
| `2e248016` `∀ c x, AC x → AC c → D x c → grounds w c x` | **Open; avoidable by its distinct-relata sibling.** | On the causal reading of `grounds`, the sun and light paradigm (attempt `040e3b4e`). | `eddef85a` and `931319ea` apply it only to distinct relata (their conclusions have `c ≠ x`, `y ≠ x`), so `a8298fbd` suffices there (registered strength order, result `cc7dd608`). Only `dd7ee4b9` needs the unrestricted form, because `3ef67739` lacks distinctness. Row 2 (originating `D`) and the open causal/constitutive fork (#1626). Member of the inconsistent package in (d) 3. |
| `71454b27` `∀ c x, CausesNecessityOf c x → D x c` | **Defended direct option.** | Claims `3ed36bec` and `bd3767d3` (q.44 a.1 ad 2): a necessary effect has an efficient cause and would not be without it. Derivable alternative (analyst observation): from `8c8b1986` (a cause of necessity causes esse), `2068f91c`, and distinctness of a cause of necessity "from elsewhere" (aliunde). | No substantive objection to its truth identified. On a vacuist counterpossible semantics it holds trivially and carries no dependence information; the q.44 reading presupposes non-vacuous dependence counterfactuals. |
| `d6e558d0` `∀ c x, CausesNecessityOf c x → AC c ∧ AC x` | **Defended primitive (domain stipulation).** | For the tertia via's causes of necessity among beings, only actual beings cause or are caused. Supporting claim `573a8ba8` (CC100 #10, presentation). | Row 12: q.44 a.1 ad 2 itself cites principles of demonstration causing the necessity of conclusions (claim `bd3767d3`), which are not concreta. The stipulation holds for the ontic sense only, and no record separates the two senses. |
| `57c5ed67` `∀ y x, P y x → AC y ∧ AC x` | **Defended primitive (domain stipulation).** | The case's simple priority relates actual beings: only actual things are in act. | Price: the world-free `P` is tied to the reading world. Coherence conditions: `a4d3261a` (act prior to potency) then needs every bearer of a potency to be an actual concretum, and `97fa3a0b` needs the concrete restriction above. No substantive objection identified. |
| `5dacb0db` `∀ x y, D x y → CausesIn y x esse` | **Defended direct option; close to a meaning postulate of `D` read with its agent-cause clause.** | What x's being depends on, as an effect on its agent, is a cause of x's being. | Row 13: on the bare counterfactual clause, constitutive dependence (a singleton on its member) is a `D`-instance with no cause of being. On reading (a) it makes everything a cause of its own esse. Both conditions point to the strict agent-cause reading. |
| `402cf70f` `∀ v a b, concrete a → concrete b → ExistsAt v a → grounds v a b → a ≠ b ∧ CausesIn a b esse` | **Open; likely too strong; avoidable.** | Principal sustaining of being: what sustains another's being is a cause of it and does not sustain itself (definition `32606882`). | Row 14: since `CausesIn` has no world argument, support at a merely possible world makes the supporter a cause of being simpliciter. The selected-world sibling `98efaa9e` suffices for `d96105fb` (result `8155fcf5`, `groundMoreInEsseOfCause`); no strength order between them is registered. Row 15 (instrumental or compositional grounds). |

Tally: derivable 1 (`f10d5632`); reducible 1 (`fea5942a`); defended primitive or direct
option 5 (`97fa3a0b`, `71454b27`, `d6e558d0`, `57c5ed67`, `5dacb0db`); open
with a named blocker 9 (`c0d99549`, `42756c07`, `000e1f65`, `d85de8e1`,
`47aff057`, `09b88101`, `3ef67739`, `2e248016`, `402cf70f`).

### (d) Structural findings

1. **No meaning postulates in the records, but the bridges collapse three
   relations into one.** `D`, `W` and `P` are Lean parameters, and the three
   definitions say that no structural property is built in. None of
   `000e1f65`, `8ab3d114`, `97fa3a0b`, `47aff057` or `09b88101` is a meaning
   postulate of the records. Irreflexivity of `W` is one (unregistered). Taken
   together the bridges give `W = ¬D` (`000e1f65`, `8ab3d114`, excluded
   middle) and make `P` the strict part of `D` (`bf93f259` from the three
   premises of `75f11492`, with `47aff057`; lake-checked lemma
   `priority_iff_strictPart`, attempt `a4d430a0`). The open questions are then
   about one relation: its sense (strict or reflexive, sustaining or
   originating, being or any respect) and well-foundedness. `d85de8e1` is the
   single substantive load-bearer of spine I as expanded, not of the cluster,
   and on either single reading of `P` it fails jointly with all-respects
   `e078f07b` (6 and (f)). Spine II
   rests on `3ef67739`, `2e248016`, `402cf70f` and the source-only `c18faab2`,
   spine III on `5dacb0db` and `47aff057`.
2. **Bypasses (analyst observations, for the formal owner).**
   - `97f5850f` follows from `42890b45` and `f10d5632` alone: a subrelation of
     a well-founded relation is well-founded, and `NoInfinitePerSeEfficientCauseSeriesReading`
     is `∀ x, Acc perSe x`. This removes `e529c42f`, `37e9e7a0`, `a896d2b5`,
     `7ad36aca`, `09b88101` and one use of `47aff057` from spine I. Finite
     ancestry is a stronger finitist conclusion than the regress premise needs.
   - `e078f07b` has a stating source claim (`3ed048c0`, q.2 a.3: "quia sic
     esset prius seipso", read as simple priority). Taken as a direct option,
     it removes `c0d99549`, `fea5942a` and `42756c07`. Together with the
     `97f5850f` bypass, which removes `6009e16f`, it also removes `000e1f65`,
     `97fa3a0b` and `8ab3d114`, because `bf93f259` (from `75f11492`) also
     feeds `6009e16f` → `7ad36aca` → `113c01ef` → `37e9e7a0` → `b58472dd`.
     The derivation through `8c629064` stays a conditional support option.
   - With both, spine I as expanded rests on `d85de8e1`, `f10d5632`,
     `57552dce` and the direct option `e078f07b`. On either single reading of
     `P` that bundle faces an established counterexample ((f)), so the
     surviving form binds spine I to `97f5850f` directly, on its q.2 a.3
     claims, or to an `e078f07b` restricted to per se ordered causing.
3. **An inconsistent package in this expansion.** Analyst observation:
   take any actual concretum x. `8ab3d114` with irreflexivity of `W` gives
   `¬¬D(x,x)`. If `D(x,x)`, then `2e248016` at `c = x` gives `grounds w x x`,
   and `402cf70f` at `v = w` (or its sibling `98efaa9e`) gives `x ≠ x`; so
   `¬D(x,x)`. Contradiction, without excluded middle. So these premises with any
   actual concretum (`InhabitedAt m w`, which the case asserts elsewhere, for
   example `56f68b40`) are jointly inconsistent. This holds under the route's
   single interpretation of `D`, `W`, `m` and `w`, with the reading world
   identified with the `w₀` of `56f68b40`: spine I's `D` is that of
   `75f11492`, and spine II's `D`, `m` and `w` are those of `dd7ee4b9` and
   `815d22c8`. All three open premises lie in this one expansion: `8ab3d114`
   in spine I, `2e248016` and `402cf70f` in spine II (they meet at
   `f53dd124`). It differs from `9150bd9c` (`56252cd8`, `2e248016`,
   `7a63a3fe`, `47aff057`) by deriving reflexivity from `8ab3d114` and closing
   with `402cf70f` instead of `7a63a3fe` and `47aff057`. `dd24400b` proposed
   composing the diagonal with `9150bd9c`. Repairs, any one of which
   suffices:
   - take `e078f07b` directly and apply the `97f5850f` bypass (2);
   - restrict `8ab3d114` to distinct pairs, which suffices for `75f11492`
     because the antecedent `D(x,y) ∧ ¬D(y,x)` forces `x ≠ y`;
   - replace `2e248016` by `a8298fbd` in all three of `dd7ee4b9`, `eddef85a`
     and `931319ea`, with a distinct-relata sibling of `3ef67739` in
     `dd7ee4b9`.

   The third keeps the expansion neutral on the diagonal, as `a4d430a0`
   recommends.
4. **The respect fork in simple priority.** `P` has no respect argument but
   is used with two meanings on this route:
   - *priority in act in a respect* ("priority in causing" for short), the gloss of definition `1d9aa4d9`,
     carried by `a4d3261a`. `e078f07b` uses this sense, as its Lean type's
     all-respects quantifier and the hand-and-stick gloss in claim
     `3ed048c0`'s interpretation require (per se causes acting together).
     In V Metaph. lect. 13 nn. 7–8 give the mover, the generator and
     command as causal cases of priority and call the generator a principle
     "simply and by nature" (as recorded in
     [power-existence-scope-boundary.md](../power-existence-scope-boundary.md),
     section "In Metaphysicam V lect.13: priority senses and the shared-Prior
     obligation", 2026-10-31);
   - *priority in being*: nn. 15–18 (claims `ab5ec574`, `95f41960`).
     `47aff057`, `97fa3a0b`, and `5dacb0db` through `70e98bb5` use this
     sense. They are the uses that depart from the definition's gloss.

   The hand and the stick separate them: the hand is prior to the stick in
   act in the respect of moving, and the stick's being does not depend on the
   hand in either the originating or the sustaining sense. With one `P`,
   `e078f07b` and the forward half of `47aff057` therefore imply the false
   `c0d99549`.
   - Spine I needs the respect sense, because its edges are causings in some
     respect (`57552dce`).
   - Spine II needs the being sense (`47aff057` in `931319ea`).
   - Spine III joins the two: `3e2366b5` uses `a4d3261a` (respect sense)
     with `74eb9113`, whose derivation runs through `1cb656a0`, which uses
     `47aff057` and `5dacb0db` (being sense).

   Splitting `P` is therefore forced. `3e2366b5` then needs an explicit
   bridge, for example that nothing other than the first being is prior to
   it in act in any respect. That bridge is outside this lane.
5. **Duplicates and flags.** `402cf70f` and `98efaa9e` are a strong and weak
   pair with no strength order registered. `2e248016` and `a8298fbd` are such
   a pair, registered (result `cc7dd608`). `c0d99549` and `2068f91c` are an
   all-respects and esse pair; no strength order is registered and none
   should be, since the strong one is false (row 1). `d85de8e1` (`P`) and
   `c18faab2` (`MoreIn esse` among actual concreta) are parallel
   well-foundedness commitments for different relations, not duplicates. The
   currentness flag `consumer_on_sense_index_allowlist` on `2e248016`,
   `3ef67739`, `47aff057`, `57c5ed67`, `71454b27` and `d6e558d0` comes from the
   over-linked WELL_FOUNDEDNESS_AND_ANTI_BRUTE_ROOT senses on the conclusions of
   `dd7ee4b9`, `eddef85a` and `931319ea` (attempts `a4d430a0`, `7b8e8975`),
   whose types use neither sense. On `f10d5632` it comes from `b58472dd`,
   which uses four senses of one disambiguation by design. No equivocation was
   found in these flags. No premise of the sixteen has transcription-only
   support. The `truth semantics` preflight on the thirteen route arguments
   that consume the sixteen (`8c629064`, `1ffd6090`, `139070d5`, `75f11492`,
   `6009e16f`, `113c01ef`, `e229bb2c`, `b58472dd`, `dd7ee4b9`, `eddef85a`,
   `931319ea`, `815d22c8`, `1cb656a0`) reports no unbridged mixing. It reports
   the allowlisted legacy mixings just named on `b58472dd`, `dd7ee4b9`,
   `eddef85a` and `931319ea`. Through their ancestry, `1ffd6090`, `b58472dd`,
   `815d22c8`, `8c629064`, `113c01ef` and `e229bb2c` reach allowlisted
   mixings in arguments outside this cluster. These include CAUSE and
   UNITING_CAUSE (for example `0f804637`, `7c6127b9`, `29851dcb`), MOTION
   and POTENCY_CAPACITY. Those ancestry mixings are not assessed here. The
   preflight reports SIMPLY_PRIOR_1 as a single sense everywhere, so the
   respect fork of 4 is invisible to the sense rules until it is registered.
   Record defect noted, not repaired: definition `c86cc1d1` describes
   `ActualConcreteGround` but names `GroundAncestor` as its Lean declaration.
6. **Lane A's reciprocity claim, checked against the Lean declarations.**
   The claim: two beings that each move or efficiently cause the other in
   different respects (each tells the other something new) come out simply
   prior to each other, which contradicts transitivity and irreflexivity of
   priority (`7ad36aca`, `32d77f18`). It matches the registered `0566122f`
   (`NoMutualEfficientCausation`: if c efficiently causes x in some respect, x
   efficiently causes c in no respect). Check:
   - `PriorSimply : B → B → Prop` has no respect argument.
   - `e078f07b` is `∀ c x r, E c x r → P c x`, and `6ca87431`
     (`ActualMoverIsSimplyPriorReading`) gives priority from moving in any
     respect.
   - `SimplePriorityTransitiveReading` and `NothingPriorToItselfReading` are
     respect-free too.

   So the derivation is formally valid. With `47aff057` it does not even need
   transitivity: `P a b` and `P b a` give both `D(b,a) ∧ ¬D(a,b)` and
   `D(a,b) ∧ ¬D(b,a)`. Cross-respect causing gives only respect-relative
   dependence (the hearer's knowing depends on the speaker, not the hearer's
   being), which is the hand and stick point of 4.

   Finding: **the derivation is valid.** Which premise it refutes depends on
   the reading of `P`:
   - On the priority-in-causing reading, it refutes the respect-free order
     laws (`7ad36aca` with `32d77f18`, or `d85de8e1`) joined with
     all-respects `e078f07b`. The cases are established, not hypothetical:
     mutual informing, colliding balls.
   - On the priority-in-being reading, it refutes all-respects `e078f07b`
     itself, as row 1 does.

   Either way the fault lies in respect-free `P` combined with `e078f07b`'s
   quantifier over every respect. It is the same fault as 4, seen from the
   asymmetry side. In this cluster it bears on `d85de8e1` (a well-founded `P`
   is irreflexive and acyclic), on `47aff057` (joined with `e078f07b`), and on
   `09b88101` only through `7ad36aca`, which (d) 2 bypasses.

### (e) Recorded objections and rivals, classified

| # | Record | Classification under the substantive standard |
| --- | --- | --- |
| 1 | Accidental-respect causing without existential dependence: the hand moving the stick; a heater heating water (section 6; [causal-transitivity-1399.md](causal-transitivity-1399.md), "Same endpoint test") | **Kept, newly as a counterexample.** *Target:* `c0d99549`'s quantifier over every r. *Mechanism:* c is here and now an efficient cause of x's being r, and x would still be if c were not. *Justification:* ordinary established cases; q.104 a.1 distinguishes causing becoming from causing being (claims `40aefb2e`, `da9c82ed`); claim `3ed048c0` itself names hand and stick as per se causes. *Relevance:* the premise is on the route and states the all-respects form. An established counterexample, not a hypothetical. It transfers to the pair `e078f07b` and the forward half of `47aff057` on one `P` ((d) 4). |
| 2 | Origin dependence: a living parent and an adult child (attempt `040e3b4e`) | **Kept, conditional on the originating reading of `D` (#1626).** Against `2e248016` and `a8298fbd` as recorded, and classified here also against `000e1f65`: the child depends on the parent by origin and can be while the parent is not. No target on the sustaining reading. |
| 3 | Existential inertia (attempts `56ae2547`, `a739dad6`, `05bc2722`; #1616) | **Kept** as the standing rival to `3ef67739` on the strict sustaining reading. *Mechanism:* a contingent concretum persists without any concurrent supplier of its existence, explained by its origin and the absence of destroyers. *Independent justification:* observed persistence of ordinary things in the absence of destroying conditions, and the practice of explaining persistence by conservation laws without positing a concurrent supplier (recorded in [causal-transitivity-1399.md](causal-transitivity-1399.md)). *Price:* it owes coverage of every existential loss by its destroying conditions (section 6). The premise owes that present received esse needs a concurrent actualizer. Neither burden is discharged. |
| 4 | Source-free global structure, the strongest infinitist reply ([borrowed-exercise-741.md](borrowed-exercise-741.md), "Three rivals") | **Kept** against `d85de8e1` and the per se regress premise. *Mechanism:* a beginningless network of instruments, each powered by its predecessor and lawfully organized, is the whole explanation. *Independent justification:* the witnesses in borrowed-exercise-741 are coherent, jointly sufficient and locally powered, and demanding a source of supply begs the question against the reply. *Price:* it owes why the exercise occurs rather than the allowed all-off scenario. Unchanged. |
| 5 | Modal co-existence of essentially inseparable constituents (attempt `1020b663`) | **Kept as a scope boundary** on `42756c07`: it restricts the map to oriented, source-dependent edges and has no target on the agent-cause reading. |
| 6 | Symmetric metaphysical dependence (Barnes 2018, Thompson 2016; challenger-cited, attribution deferred) | **Restated.** The texts are unread here, and relevance to the selected efficient-causal sense of `D` is not shown; the cited cases are constitutive. No weight against `42756c07` on its selected sense. |
| 7 | Vacuous counterpossibles (attempt `1020b663`) | **Boundary retained** as a semantic dependency of `42756c07` and `71454b27`, not an objection. The q.44 a.1 ad 2 reading of `D` (claims `3ed36bec`, `bd3767d3`) presupposes non-vacuous dependence counterfactuals. |
| 8 | Lewis's non-transitivity of counterfactual dependence (statement `09b88101`; attempt `a4d430a0`) | **Kept** only against `09b88101` read by the bare counterfactual clause. No substantive objection identified against the per se received-being reading. |
| 9 | A nearest-situation counterfactual with a remote replacement source (section 4; attempt `f798617c`) | **Restated** as the missing persistence and centering bridge of P1-A. Section 4 already says it is "not by itself evidence" of a replacement. No weight. |
| 10 | Categories 12: causal priority with reciprocal implication (attempt `5cf65146`) | **No substantive objection identified** to `97fa3a0b`. The case bears on whether separability is necessary for priority, not on its sufficiency. |
| 11 | Non-concrete candidates of fixed being status (this section, analyst observation) | **Scope condition** on the joint use of `97fa3a0b` and `57c5ed67`, not an objection to either alone. |
| 12 | Demonstrative causes of necessity (claim `bd3767d3`) | **Kept as a scope boundary** on `d6e558d0`, conditional on reading `CausesNecessityOf` to include demonstrative causes. The tertia via's causes of necessity among beings are untouched. |
| 13 | Constitutive dependence: a singleton and its member (Fine, *Essence and Modality*, read for section 2) | **Kept as a scope boundary** on `5dacb0db`, conditional on the bare counterfactual reading of `D`. No target under the agent-cause clause. |
| 14 | Cross-world export through the world-free `CausesIn` (this section, analyst observation; the statement's own paraphrase records the feature) | **Kept, conditional on reading the world-free `CausesIn` as actual causing** (definition `211a6432` calls it mode-unspecified). *Target:* `402cf70f`'s quantifier over every world v. *Mechanism:* if a grounds b only at a merely possible world, a becomes a cause of b's being simpliciter. *Justification:* the two types and the ordinary point that supporting at a possible world is not causing actually. *Relevance:* the strong version is the route's premise; `98efaa9e` avoids it. |
| 15 | Instrumental or compositional grounds; control `DescendingGrade` (attempt `7b8e8975`) | **Kept as a scope condition** on `402cf70f` and `98efaa9e`: both hold only if the selected relation is principal sustaining of being. `DescendingGrade` is restated as a fact about one interpretation. |
| 16 | Event versus being carriers (attempt `pruss-koons-finite-history-reading`; disambiguation `bedfab81`) | **Boundary retained.** Bears on `f10d5632` only if the studied relation is Koons's event network. The global-compatibility rival in that attempt targets countable patchwork, not a premise here. |
| 17 | Papineau and Hume (attempt `rival-sourcing-papineau-hume-512`) | **No substantive objection identified**: both are recorded as silent on `f10d5632`. |
| 18 | The reflexive and strict readings of the diagonal (attempt `a4d430a0`) | **Boundary retained** as a sense fork, not an objection. It is now load-bearing through (d) 3. |
| 19 | Rejected map edges (attempts `causal-maps-batch1-rejected-edges`, `round2-grounding-rejected-edges`) | **Not objections.** They record support gaps: the q.44 statement has no Lean declaration, and CC100 #10 is about causes, not priority. |
| 20 | Formal controls: `needsNoLoops`, `needsFiniteAncestry`, `needsInclusion` (result `a4558f9c`); `separationModels` and `orderLawControls` (results `0ccf914c`, `a79850a6`); the strict-ground controls and nonvacuity model; the consistent infinite descent `fbc592d0`; the two-being table (attempt `a739dad6`); `DescendingGrade`, `OffWorldAscent`, `NoGradeForRivals` (attempt `7b8e8975`) | **Restated** as facts about single stated interpretations. Each shows that a premise is needed in that interpretation or that two premises differ in meaning. None is evidence that a premise is false. |
| 21 | Reciprocity: two beings that cause each other in different respects (lane A, 2026-11-18; the case is excluded by `0566122f`) | **Kept; the derivation is valid, and its target depends on the reading of `P`** ((d) 6). *Target on the priority-in-causing reading:* the respect-free order laws (`7ad36aca` with `32d77f18`, or `d85de8e1`) joined with all-respects `e078f07b` (and `6ca87431`); with `47aff057`, no transitivity is needed. *Target on the priority-in-being reading:* `e078f07b`'s all-respects quantifier. *Mechanism:* each is prior to the other. *Justification:* mutual informing and colliding balls are established cases. |

Counts:
- kept 11 (rows 1–5, 8, 12–15 and 21);
- restated 3 (rows 6, 9, 20);
- boundaries retained 3 (rows 7, 16, 18);
- one scope condition (row 11);
- one row of non-objections (row 19);
- no substantive objection identified 2 (rows 10, 17).

No substantive objection is identified against `fea5942a`, against `71454b27`
as to its truth, against `57c5ed67` beyond its coherence conditions, or
against `97fa3a0b` on concrete relata.

### (f) Overall provisional judgment

The dependence and priority spine of the prima via is a positively motivated
conditional structure. As recorded now, with one `D` and one `P`, its expanded
leaf set is not jointly tenable:

- the hand and the stick refute `c0d99549`, and with it the joint use of
  `e078f07b` and `47aff057` on one `P`;
- `8ab3d114`, `2e248016` and `402cf70f` (or `98efaa9e`) exclude every actual
  concretum, given the meaning of `W`.

Both faults are faults of sense, not of the underlying ideas. They are repaired
by fixing `D` as strict, sustaining dependence in being, and by splitting
simple priority into priority in causing and priority in being with an
explicit bridge where both are used. On that reading:

- the bridges `000e1f65`, `47aff057`, `97fa3a0b` and `5dacb0db` have strong
  prima facie support from In V Metaph. lect. 13 nn. 15–18, q.44 a.1 ad 2 and
  q.104 a.1;
- `fea5942a`, `f10d5632` and `09b88101` drop out or reduce to bookkeeping;
- `71454b27`, `d6e558d0` and `57c5ed67` are defensible domain commitments.

The philosophical load then sits on three contested points, none of them
defeated. The first is the per se regress premise `97f5850f`, taken directly
on its q.2 a.3 claims, against the infinitist rival (row 4).

On either single reading of `P`, `d85de8e1` with all-respects `e078f07b` faces
an established counterexample:
- on priority in being, row 1 against `e078f07b`;
- on priority in causing, row 21 against `d85de8e1`.

So `e229bb2c` is not a surviving support for `42890b45` unless `e078f07b` is
restricted to per se ordered causing, in which case `d85de8e1` reduces to the
regress premise.

The other two points are the dependence principle for contingent concreta
(`3ef67739`, against existential inertia) and the transport of priority in
being to spine III. Nothing here is established, defeated or closed.

Later derivation (#1926, 2026-11-24; [one-dependence-order.md](one-dependence-order.md),
attempt `b2cf0e2e`): `d85de8e1` is now derived from `82cfaf26` (well-founded
actual grounding), `86efed1a` and `32d77f18` (result
`simplePriorityWFOfActualGroundingWF`), so it is formally closed from open
premises rather than a bare leaf. This does not revise the judgment above: the
derivation binds the unsplit PRIOR_1, `86efed1a` is supported only on priority
in being and meets row 1's case on priority in causing, and the route to `42890b45`
through `e229bb2c` still needs `e078f07b`. The "open with a named blocker"
standing in (c) is unchanged as a warrant judgment; only its formal status
moved.

### (g) Revision conditions and next tests

This judgment would change with:

- a defended reading of `P` on which per se priority in causing carries
  existential dependence of the moved bearer (restores the single-`P` route);
- an independent argument for well-foundedness of all simple priority beyond
  the per se regress reasons (would give `d85de8e1` discriminating support);
- an existential-inertia account with independent loss coverage (would defeat
  `3ef67739` on the sustaining reading);
- a semantics for `D` that rejects the identity law on the diagonal (removes
  reading (a) and package (d) 3 with it).

**Most discriminating next test:** bind spine I to `97f5850f` directly, or to
an `e078f07b` restricted to per se ordered causing, and not to respect-free
`d85de8e1`. This decides whether spine I has a surviving support at all
((f)).

**Second test:** register the respect fork for SIMPLY_PRIOR_1 (priority in act
in a respect, and priority in being, as separate senses) and re-bind the
spines. Then check whether `3e2366b5` still derives from `74eb9113`,
`a4d3261a` and `c6d6379b`. If it needs a bridge such as "nothing other than
the first being is prior to it in act in any respect", that bridge is the new
crux of the pure-act step. If no bridge is needed, the fork is harmless there.

Pending consumer dispositions for the `c0d99549` revision, for the formal
owner:
- `8c629064`: pending. Its conclusion `e078f07b` keeps its direct option on
  claim `3ed048c0`.
- `1ffd6090`: pending. `47b151ca` also follows from `e078f07b` and the
  second half of `47aff057`.

Cheap formal tests for the owner:

1. A zero-axiom Lean certificate, without Mathlib, that `8ab3d114`,
   irreflexive `W`, `2e248016`, `98efaa9e` and `InhabitedAt m w` are jointly
   inconsistent. Add a joint model of the repaired spine-II package
   (`a8298fbd`, a distinct `3ef67739`, `98efaa9e`) with a nonempty strict `D`.
2. A sibling of `b58472dd` deriving `97f5850f` from `42890b45` and `f10d5632`.
3. The PLG consistency lemma for acyclic strict-sequent sets (converse of
   `e86849cf`).

**Supersession.** One judgment is revised. The standing of `c0d99549` changes
from "poorly supported" and "underdetermined" to "faces a kept counterexample;
false as stated for non-esse respects". This applies to section 1's P8 row and
section 6 of this note, and to the 2026-11-11 judgment of
[causal-transitivity-1399.md](causal-transitivity-1399.md) ("leaves the
universal all-respects bridge underdetermined"). A formal `revisions`
declaration is deferred while #1757 is open. The positive received-esse warrant is retained for the esse
sibling `2068f91c`. No other earlier weighting changes. The sixteen premises had
no earlier `current_assessment`. First grades are given here to `fea5942a`,
`d85de8e1`, `3ef67739`, `71454b27`, `d6e558d0`, `57c5ed67`, `5dacb0db`,
`402cf70f` and `f10d5632`. The classifications of rows 1, 2 (for `000e1f65`),
11, 14 and 21 are new.
