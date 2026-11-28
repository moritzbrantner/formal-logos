# Trolley principles and the senses of "wholly good"

Owner direction (2026-11-28): use concrete thought experiments as tests of
implicit principles. This note records the trolley pilot. All formulations are
the analyst's; attribution is deferred (AGENTS.md, "Logic first"). Philosophy-lab
exhibit texts were used for orientation only. Records:
[specs/trolley-principles.toml](../../specs/trolley-principles.toml),
[specs/trolley-rowe-goodness.toml](../../specs/trolley-rowe-goodness.toml),
[attempt](../../corpus/attempts/trolley-principles-pilot.json).

## Frame

`TruthCore.Ethics.Trolley` describes each scenario by a finite causal graph over
five event kinds (intervention, redirection of the threat away from the five,
the one's lethal harm, ending of the threat, survival of the five), the death
counts of intervening and refraining, the events the agent's plan includes, and
a supplied classification of the act's object. Causal paths are Mathlib
`Relation.ReflTransGen` paths. Principles are Lean definitions over this
description, and a premise `XGoverns F P` says that principle `X` fixes the
permissibility assignment `P` for intervening, scenario by scenario. Every
verdict is computed from the graph by reachability, so it could fail on another
description; the controls exhibit such descriptions.

Case descriptions (statements `SwitchFacts` and siblings, each its own premise):

| Case | causal links | plan includes the harm |
| --- | --- | --- |
| Switch | act → redirect → harm; redirect → saved | no |
| Footbridge | act → harm → threat stopped → saved | yes |
| Transplant | same graph as footbridge (no threat to redirect) | yes |
| Loop | act → redirect → harm → threat stopped → saved | no (acts because of the hit, not in order to) |

The frame does not separate footbridge from transplant (control 8): role duties,
consent, institutions and "personal force" are not represented.

Senses (`corpus/disambiguations`): KILLS_1 any causal path from the act to the
harm; KILLS_2 such a path avoiding the redirection of the existing threat.
MEANS_1 every causal path from act to saving passes through the harm; MEANS_2
the harm is planned and contributes causally. INTENDS_1 plan inclusion;
INTENDS_2 every known necessary causal means counts as intended (coincides with
MEANS_1 by its stated content). WHOLLY_GOOD_1–3 are below.

## Which principle survives which verdict

Computed values for intervening (P = permissible, I = impermissible):

| Principle | Switch | Footbridge | Transplant | Loop | Common triad |
| --- | --- | --- | --- | --- | --- |
| Act consequentialism (lives) | P | P | P | P | inconsistent (footbridge, transplant) |
| Causal no-killing (KILLS_1) | I | I | I | I | inconsistent (switch) |
| Classical double effect (MEANS_1, INTENDS_1) | P | I | I | I | entailed |
| Intention-only double effect (MEANS_2) | P | I | I | P | entailed |
| Kantian MEANS_1 principle | P | I | I | I | entailed |
| Redirection, Thomson/Kamm-style (KILLS_2) | P | I | I | P | entailed |

Results: `acFootbridge`, `acTransplant`, `causalNoKillingSwitch` (rival
verdicts derived); `footbridgeVerdictExcludesAC`, `transplantVerdictExcludesAC`,
`switchVerdictExcludesCausalNoKilling` (conditional refutations, recorded as
`refutes` relations that do not count until the verdicts are established);
`doubleEffectTriad`, `intentionDoubleEffectTriad`, `meansTriad`,
`redirectionTriad`; the four loop results; `jointModels` (each surviving
principle with all four case facts and the triad is satisfiable, with its loop
verdict); `controls`.

Two refutations of act consequentialism come from independent case data
(footbridge and transplant) but share the same open element: the verdict as
prima facie warrant. The KILLS_2 no-killing reading escapes the switch test, so
the switch verdict refutes only the KILLS_1 form of an absolute doing/allowing
deontology.

Controls (which fact each verdict depends on):

1. *Means/side-effect.* A side-effect footbridge (a dropped weight stops the
   trolley and its fall also kills the bystander) flips classical double effect
   and the means principle to permissible; act consequentialism does not change.
2. *Closeness.* The footbridge graph with the harm left out of the plan stays
   impermissible under classical double effect (causal condition 3) and becomes
   permissible under intention-only double effect.
3. *Intention.* A malicious switcher who wants the one dead is forbidden by both
   double-effect readings and permitted by the means and redirection principles.
4. *Numbers.* Reversed numbers defeat classical double effect, the means and
   redirection principles and act consequentialism.
5. *KILLS.* The switch kills in KILLS_1, not KILLS_2.
6. *Loop.* The loop harm is MEANS_1 but not planned; see below. Adding it to the
   plan makes intention-only double effect forbid the loop.
7. On the intention reading, condition 3 (MEANS_2) is implied by condition 2.
8. Footbridge and transplant coincide in the frame.
9. The case facts alone do not entail the common triad: the principle premise is
   needed.
10. INTENDS_1 and INTENDS_2 split exactly on the loop.

## Loop finding

Thomson's loop is the objection to double effect with a stated mechanism: the
one's being hit is causally needed to stop the trolley, yet the case differs from
the switch only by track behind the one. In the frame:

- Classical double effect forbids the loop. The failing condition is condition 3
  in MEANS_1 (every path to the saving passes through the harm), not condition 2:
  the plan omits the harm. The Kantian MEANS_1 principle agrees.
- Intention-only double effect permits the loop, but only given Kamm's plan
  reading; with the harm in the plan it forbids it (control 6). Its price is
  control 2: on the same reading a footbridge agent who plans only the impact
  escapes condition 2 and 3, so the reading needs an independent closeness
  criterion that the frame does not supply.
- The redirection principle permits the loop on causal structure alone (the harm
  lies downstream of redirecting the existing threat) and keeps the footbridge
  and transplant verdicts. Its price is control 3: it ignores intention, so the
  malicious switcher acts permissibly.

So double effect and the means principle diverge only on the intention reading:
classical double effect *is* a means principle on the loop, and the refinement
that rescues the loop verdict either moves condition 3 into the plan (and must
answer closeness) or replaces it by a causal-structure condition (and must
separate permissibility from intention). Whether the loop verdict itself has
warrant comparable to the triad verdicts is open; reported survey data are an
unread lead, not evidence here. If the loop verdict is not warranted, the loop is
not an objection to classical double effect.

## The strongest consequentialist account, stated symmetrically

- *Positive warrant.* Impartiality: each life counts equally, and the switch
  verdict itself shows that numbers carry weight. Act consequentialism is the
  simplest principle that fits the switch.
- *Paradox of constraints* (mechanism: if the harm is so bad, an agent-relative
  constraint forbids minimizing that very harm). In this frame the five are
  threatened by a trolley, not by agents' violations, so the paradox applies
  only in its outcome form; it does not touch double effect's distinction of
  intended from foreseen harm.
- *Debunking* (mechanism: footbridge and transplant responses correlate with
  personal-force features that the triad's moral content does not mention). The
  mechanism targets the warrant of those two verdicts, not the derivations. Its
  empirical basis is an unread lead here, so this note states the mechanism and
  assigns it no further weight. The side-effect control
  shows a feature the debunking story does not cover: causal role, not force,
  flips double effect.
- *Indirect consequentialism.* A rule or institutional consequentialist can
  forbid transplant through effects on trust. Those facts are absent from the
  case description, so in this frame that reply is a different principle with
  extra case facts, not a defense of act consequentialism on the stated cases.

## Senses of "wholly good" and Rowe's permission constraint

The coordinator redirected the root bearing through the problem of evil, not
through q.94 natural law: `DISAMB 9880c06b` records that the practical "good act"
predicate has no derivation from the ontological goodness on the root route.
`TruthCore.Ethics.TrolleyRowe` reuses Rowe's `Sig`, `BlockingCost` and
`PermissionConstraintReading` and describes each prevention way by a trolley
`Case` (intervening = preventing; `harmOne` = a harm the preventer itself would
do). `Better b e` is a supplied all-things-considered comparison.

- WHOLLY_GOOD_1 `OutcomeStandard`: never permits what would be strictly better
  prevented. With the OPEN outcome bridge `UnblockedPreventionBetter` (no
  blocking cost ⇒ preventing strictly better) it yields Rowe's simplified
  permission constraint (`outcomeSenseYieldsPermissionConstraint`). This is a new
  conditional support option for STMT-ROWE-PERMISSION-CONSTRAINT. The bridge
  fails if several individually lesser costs can jointly outweigh a suffering.
- WHOLLY_GOOD_2 `ConstraintStandard`: keeps the rescue duty unless every way of
  preventing fails double-effect condition 1–3. With the same bridge it yields
  only `ConstraintQualifiedPermission`: blocking cost *or* constraint-blocked
  prevention. Controls: it does not yield Rowe's constraint (a footbridge-shaped
  only way of prevention); one constraint-free way of preventing restores Rowe's
  requirement (easy rescue survives).
- WHOLLY_GOOD_3: supreme ontological goodness plus willing some good to every
  existing being (`GodIsSupremelyGood`, `DivineWillsGoodForAllExisting`, read as
  Rowe's `WhollyGood` on a shared carrier) is jointly satisfiable with an
  omniscient omnipotent bearer and failure of the constraint. It yields neither
  form without an added standard for permitting.

Consequence for the planned bridge from STMT-ROWE-NO-THEISTIC-BEING to
STMT-GOD-EXISTS: Rowe's core bites on the case's GOD_4 only if its goodness is
read with a permission standard. Under WHOLLY_GOOD_2, which the triad verdicts
support for human agents, Rowe additionally needs that some constraint-free way
of preventing the suffering exists. For an omnipotent preventer such ways look
easy to come by, so WHOLLY_GOOD_2 narrows Rowe's argument to cases where every
prevention would itself use harm as a means, as in the free-will defence recast
as a doing constraint. That last reading is an open lead; #1456 owns divine
permission versus intention.

## Reuse

Lean search (LeanSearch, lean-explore) found no normative-ethics vocabulary in
Mathlib; reachability reuses `Relation.ReflTransGen`. Reused by import: Rowe's
signature and constraints, `GodIsSupremelyGood`, `DivineWillsGoodForAllExisting`.
Not reused, because meanings do not coincide: `Ethics.HardCaseTyped` (opaque
factual predicates such as `deliberateKilling`, no causal graph; its killing
context is closest to transplant, with the offender as beneficiary),
`RossPermission`/`RossDerived` (ideal-frame and issued-norm permission, not a
governed assignment), `AgencyNeutrality` (pro-tanto reasons), `Population*` (real
welfare scales, not death counts), and the q.94 natural-law vocabulary (see
above).

## Shared edit

`corpus/statements/rowe-permission-constraint.json`: dropped the
APPARENTLY_POINTLESS (recognition) definition, which `PermissionConstraintReading`
does not use and which made every argument concluding it mix the two
POINTLESS_GRATUITOUS senses; added a connection plan to STMT-GOD-EXISTS.

## Overall provisional assessment

The triad verdicts are widely shared prima facie data. Given them, act
consequentialism and the KILLS_1 no-killing deontology are excluded at matching
scope, and four constraint principles survive the triad. The debunking objection
names the mechanism that would lower that warrant; its evidence is unread here,
and the side-effect control isolates causal role rather than force. Among
survivors, classical double effect and the redirection principle are the
strongest at matching scope: they agree on the triad and split on the loop and
the malicious switcher. The best surviving rival to classical double effect is
the redirection principle; its price is making intention irrelevant to
permissibility. The price of classical double effect is the loop verdict, whose
own warrant is unassessed. Act consequentialism survives only by rejecting two
verdicts, with debunking as its support.

For the case: these results establish no premise. They show that Rowe's
constraint follows from an outcome-minimizing sense of goodness and only a
weakened form from a constraint-respecting one, and that ontological goodness
alone yields neither.

## Next tests

1. Closeness: add separate impact and death events, and test a closeness
   criterion that lets intention-only double effect keep footbridge impermissible.
2. Warrant of the loop verdict at matching scope with the triad; then whether the
   loop is an objection to classical double effect at all.
3. Rowe: find a concrete prevention case for which every way of preventing an
   intense suffering is constraint-violating (free agency), coordinated with #1456.
4. Outcome bridge: a finite aggregation countermodel with several lesser costs.
5. Source leads, unread: Aquinas ST II-II q.64 a.7; manualist four conditions;
   Thomson 1985 and 2008; Kamm on triple effect.
