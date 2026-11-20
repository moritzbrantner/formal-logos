# No ultimate foundation, radical law-change, and whole-history stability

This is an **ontic conditional** for the God-existence-stage explanation question
in #735, extending the exact existing #736 history-selection, #737 predictive,
#743 law-actuality and #1801 persistence-law distinctions. It addresses a
particularly sharp opponent: **there is no ultimate explanation of the order,
and no deeper necessity or actual power constrains which local law governs at a
later time**. Whether the opponent is committed to that second clause, rather
than a merely brute **stable** law, is the decisive live question.

The mathematical result is not an unconditional refutation of naturalism or of
no-foundation views. It asks what a *radically unconstrained future* costs **if
admitted as an ontic range of complete alternative histories**. No extensional
trace model by itself makes these histories metaphysically possible, and no
theorem derives that admissibility from absence of an ultimate ground. The
inference `no ultimate ground → all future transitions admitted` is **OPEN**.

## Exact formal discriminator

`TruthCore/Explanation/NoFoundationLawChaos.lean` imports existing
`UltimateExplanation.Profile`, `Follows`, `Cell`, `openFuture`, `stable`, and
`LawActuality.UsesRecord`, as well as the existing `History`/`SameHistory`
signature. Its four properties have separate frozen Challenge declarations:
`Certificate`, `LawSwitch`, `OneRival`, and `Omissions`.

1. **Unrestricted suffix, not merely one unexpected event.** `splice n tail`
   leaves the exact observed `true` values through `n` and installs an
   **arbitrary whole infinite Boolean suffix** thereafter. `SuffixComplete p n`
   says every such complete path belongs to `Cell p on n`; the exact `Certificate`
   characterizes `Cell (openFuture n) on n` as *all and only* the paths with
   that prefix. Thus any prescribed collection of later flips, including
   infinitely many, is admitted. No external probability or temporal-causal
   relation is assumed.
2. **Populated, distinct whole histories.** `realized : History Trace Bool Nat`
   represents exactly one Boolean state at every time in every path-world,
   with `ExistsAt` agreeing at now=0. For **each** unobserved `k ≥ n+1`,
   two witnesses agree at *every* observed index, differ at `k`, and have
   different `SameHistory` presence extensions. Both are populated, rather
   than a degenerate empty-world control. They represent state values, **not**
   the persistence of one concrete substance with a fixed identity.
3. **Every predictor and every later time.** For any `predict : Trace → Bool`
   satisfying the *existing* `UsesRecord n` (all possible inputs with the same
   entire record receive the same prediction), and **any** `k ≥ n+1`, there
   is no exact prediction uniformly correct across an `SuffixComplete` class.
   This is stronger than #737's failure of its particular persistence
   `forecast`, though related to #743's all-estimator failure at first
   unobserved time for a pair of individually unique laws. It tests a
   **uniform zero-error requirement**, not fallible justified induction.
4. **Every complete-history law claim.** `UniversalProjection p q n` means the
   same candidate `Profile q` is satisfied by **every** path in the admitted
   cell, not simply by one actual path. If `SuffixComplete p n`, any such `q`
   must permit **all four** Boolean successor pairs at every `t ≥ n+1`.
   Therefore *every* candidate law excluding at least one late transition
   fails that universal projection, and **no deterministic candidate law**
   can pass it. The result quantifies over *all* time-dependent relations
   `q.step`, not just persistence, periodicity or a finite list of laws.

The strongest piece is the **iff**, not merely a failure witness. For every
candidate `q`, `UniversalProjection (openFuture n) q n` holds *exactly when*:

| Law component | Necessary and sufficient across all admitted paths |
| --- | --- |
| Initial condition | `q.initial = true` |
| Earlier transitions `t < n` | `q.step t true true` |
| Boundary transition `t = n` | Both `q.step n true true` and `q.step n true false` |
| All later transitions `t ≥ n+1` | `q.step t a b` for **every** `a,b : Bool` |

So a law may still describe the already fixed past, and a fully permissive law
may be universally true; no surviving universal law restricts later Boolean
changes in this explicitly radical model. This is a statement about truth
across the *selected alternative space*, not about whether a stable law can be
true of the *one actual history*. It does **not** show that non-deterministic,
stochastic, dispositional, probabilistic or law-of-law constraints are impossible
under weaker rival commitments.

### One fixed radical rival, with explicit switching rule schedules

An important quantifier control avoids adjusting the theory with the cutoff.
The original #737 profile `openFuture n` changes as `n` changes. `OneRival`
instead uses the **same fixed** profile `unconstrained` at *every* possible
finite cutoff. Its admitted complete paths are exactly the paths with initial
value `true`; for any record prefix, all suffixes are available. This is one
coherent, nonempty alternative *model class* with arbitrarily late deviations,
not a new model selected opportunistically after each observation.

`scheduled switches` gives a different, **individually deterministic**
transition profile for every Boolean law schedule:

- `switches t = false`: next state equals current state (*copy law*).
- `switches t = true`: next state is its Boolean opposite (*toggle law*).
- `generated switches` is its unique complete state path from initial `true`.
- `toggleFrom k` copies through step `k-1` and **switches the rule** to toggling
  at `k` and thereafter. For every `n ≤ k`, its generated trace agrees with
  the never-toggle trace through the whole observed prefix `0..n` but
  disagrees at `k+1`. The laws themselves prescribe opposed transitions
  at `k`; this is not just two outcomes under one unchanged deterministic law.

Moreover, for **every** path `f` with `f 0 = true`, `scheduleOf f` records the
complete path's adjacent changes, and `f` satisfies that schedule's unique
deterministic profile. Therefore one fixed unrestricted class equals the union
of all individually deterministic schedule solutions. It can admit every later
rule reversal without any one governing schedule determining all possible
histories. The extracted schedule is **ex post, dependent on the entire
explanandum**, and is not an independently given mechanism, explanation or
epistemically available prediction. This limit is essential to the argument.

## Crucial omitted assumptions and controls

`Omissions` retains four controls in the same Boolean/model language:

| Comparison | What actually follows |
| --- | --- |
| Stable `Profile`, populated `Cell stable on n on` | All admitted stable paths follow the same copy law. There is no `SuffixComplete stable n`. Scientific stability is logically compatible with leaving ultimate grounding unexplained. |
| One open class, the admitted stable path `on` | `on` is admitted and follows `stable`. Suffix freedom allows a stable *admissible continuation*, rather than asserting that all histories really become chaotic. |
| Unrestricted profile `unconstrained` | It itself projects universally, but forbids no future transition and is nondeterministic. Our result forbids substantive future-excluding *universal* projections, not every tautological/procedural law statement. |
| `impossible` false initial condition with `on` observed | Its cell is empty, so arbitrary law projections pass vacuously. The main discriminator has explicit populated alternatives and does not use this escape. |
| Existing scopes `brute` and `grounded` | `brute` has **no** totality ground but can be paired with `stable`; `grounded` **does** have a totality ground and can be paired with `openFuture`. Grounding status and admissible law alternatives are independent model coordinates until bridged. |

The last control directly refutes the proposed **bare logical inference**
`¬ GroundedTotality → SuffixComplete` in the unrestricted product class. It
does not prove that a real brute world has stable laws, that a grounded world
has open laws, or that `GroundedTotality` is full ultimate adequacy. In #737,
`GroundedTotality` only means some supplied ground of `spacetime`; it does
not mean a necessary self-explanatory God or an adequate reason for everything.

## Whole-history explanation and law actuality: two debts, not one

The radical rival must answer **the same explananda** as a grounded-law account:

1. **Which whole history obtains?** #736 shows that an invariant whole
   reason-vector cannot be transformed by arbitrary information-only operations
   into an entailing selector when accessible different presence histories share
   that vector. #743 adds individually unique deterministic laws with identical
   finite observations and represented populations, without showing why the
   actual law rather than its rival obtains. A Humean best-system description
   can be *true of* the full selected mosaic while the question *why that mosaic
   is actual* remains open. The standard here is **entailing selection**,
   not a theorem that all adequate explanation must entail its effect.
2. **What fixes the laws' continuing operation?** Under the radical thesis,
   no constraint on later law schedules is supplied; every future copy/toggle
   pattern can be a distinct, individually deterministic complete history.
   The universal law projections that would prohibit some transition fail by
   the theorem. Observed regularity alone does not supply a stable cross-time
   restriction. To make robust global forecasts the opponent owes a warranted
   genuine restriction on admissible law schedules, a qualified propensity or
   exception structure, a necessary/dispositional nature, an actual mechanism,
   or a frankly limited methodological rule. Simply labeling the observed
   schedule a law *after the fact* does not select or constrain it.

These debts combine **only under the strong radical premise**. The proof does
not identify lack of ultimate explanation with unrestricted admissibility;
a restriction on law schedules is an additional substantive metaphysical
commitment whose actuality and warrant remain to be explained. The stable
model control and the existing comparisons in #737/#743 preserve this boundary.

At #1801, the dispute about existential inertia is even more specific:
a law plus **earlier existence** may explain a *later state or continuation*
without thereby offering a ground of the complete law/actuality conjunction.
If the law-fact is grounded by precisely the whole-history fact it purports to
ultimately ground, using that same grounding relation in both directions
conflicts **conditionally** with its independently defended asymmetry. Neither
whole-history law-supervenience nor grounding asymmetry, nor an actual present
productive sustaining requirement, is supplied by this module. A law of
*state* does not automatically govern the continuing *existence of the same
received-esse bearer*. The #1801 same-bearer and explanatory-status bridges
to `40a97664` remain **OPEN**, not silently settled by Bool state tokens.

## Provisional comparison and exact open bridges

As of the baseline `4aab093cc06bc1924bdf8067bd5780e11f438770`, the
strong radical rival has a genuine **conditional disadvantage** for global
law stability: it cannot simultaneously grant unrestricted future admissibility
and claim one all-history deterministic/future-excluding transition law, or
a record-only uniformly correct later forecast. This follows from a precise
model-theoretic contradiction, not an appeal to the psychological unpleasantness
of chaos. Its rational reply may reject the universal guarantee criterion,
restrict its metaphysical alternative set, defend a brute stable law or adopt
qualified empirically successful but fallible inference. Those are distinct
positions and must be reassessed under their own commitments.

It remains an **OPEN philosophical bridge** to infer from mere lack of a
necessary foundation that all possible future transitions or every law schedule
are ontically available. It is a further **OPEN bridge** that a real adequate
ultimate explanation must select this law/history in the strict #736 sense.
Theist accounts also owe a substantive account of how their proposed ultimate
ground sustains the particular governing structure and makes actual law use
and epistemic access possible. An unexplained choice by a necessary being
does not become an explained law schedule just by being attributed to God.

The most discriminating next test is therefore a defended **modal/causal
restriction principle about change in laws**, paired with a counterfactual
model at the same ontology and observed history. Does the radical rival
actually affirm arbitrary future law schedules, or only absence of ultimate
reason? What independently warrants the selected restrictions on whichever
side asserts them? If a law is said to ground whole-history actuality, test
the same fact/ground direction rather than transferring the result from a
mere law of state succession.

## Provenance, challenge and verification boundary

- Exact reuse: `TruthCore.Epistemology.UltimateExplanation.Profile/Follows/Cell/Deterministic/openFuture/stable/on`, `TruthCore.Explanation.LawActuality.UsesRecord`, `TruthCore.Modern.Hume.Regularity.GroundedTotality/brute/grounded`, and `TemporalHistory.History/CoherentAtNow` plus `HistoryContrastive.SameHistory`. No new logic, agent, evidence authority, grounding ontology or source claim.
- Prior #737/the pinned Hume *Enquiry* IV/V material compares finite past
  observations to future continuation; #736/#743 notes pin the global
  explanation and law actuality comparisons. Leibniz *Monadology* §§32,
  36–38 is the inherited PSR contrast; no new exact historical quotation or
  source attribution is asserted here. Source fidelity and the rival's
  metaphysical applicability must be judged separately.
- Frozen new Challenge:
  `TruthCore/Results/Explanation/NoFoundationLawChaos/Challenge.lean`, SHA256
  `c6b58fafc294479ea27516f8661d97532b2ae32240ffbc4339c4345bcabbcbed`.
  The `Solution.lean` proof is an independent draft consuming this unchanged
  Challenge interface.
- **Verification status:** no Lean/lake and no prepared `truth` CLI are present
  in this local research clone. Kernel, theorem binding, Comparator and NanoDa
  checks, the exact-head build and independent final-outcome review remain
  required. Neither this written proof draft nor its theorem names should be
  called mechanically certified until those checks pass.
- **Root impact:** four new analyst statements, premise-free conditional
  arguments, inference records, result records and Comparator configurations
  were generated from `specs/no-foundation-law-chaos.toml`. Existing root
  routes, premise statuses, closure flags and source claims were not changed.
  Expected root-frontier impact: **none**; exact `frontier-diff` remains pending
  the coordinator's CLI/CI. The live connection is an explicitly proposed
  bridge to the ultimate-ground and persistence explanatory comparison, not
  an already established root entailment.
