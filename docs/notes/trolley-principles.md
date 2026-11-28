# Trolley principles and the senses of "wholly good"

Owner direction (2026-11-28): use concrete thought experiments as tests of
implicit principles. This note records the trolley pilot, revised after an
independent semantic challenge. All formulations are the analyst's; attribution
is deferred (AGENTS.md, "Logic first"). Philosophy-lab exhibit texts were used
for orientation only. Records:
[specs/trolley-principles.toml](../../specs/trolley-principles.toml),
[specs/trolley-rowe-goodness.toml](../../specs/trolley-rowe-goodness.toml),
[attempt](../../corpus/attempts/trolley-principles-pilot.json).

## Frame

`TruthCore.Ethics.Trolley` describes each scenario by a finite causal graph over
five event kinds (intervention, redirection of the threat away from the five,
the one's lethal harm, ending of the threat, survival of the five), the death
counts of intervening and refraining, the events the agent's plan includes, and
a supplied classification of the act's object (double-effect condition 1).
Causal paths are Mathlib `Relation.ReflTransGen` paths. Principles are Lean
definitions over this description, and a premise `XGoverns F P` says that
principle `X` fixes the permissibility assignment `P` for intervening, scenario
by scenario. Every verdict is computed from the graph by reachability, so it
could fail on another description; the controls exhibit such descriptions.

| Case | causal links | plan includes the one's lethal harm |
| --- | --- | --- |
| Switch | act → redirect → harm; redirect → saved | no |
| Footbridge | act → harm → threat stopped → saved | yes |
| Transplant | same `Case` as footbridge (no threat to redirect) | yes |
| Loop | act → redirect → harm → threat stopped → saved | no (acts because of the hit, not in order to) |

Frame limits, stated once:

- Footbridge and transplant are the same `Case` value. Their verdicts are one
  formal datum carrying two labels, not independent data; they share defeaters
  such as personal force and using a person. Role duties, consent and
  institutions are not represented.
- There is no separate impact event. "Plan includes the harm" is the stipulation
  that carries the intention reading's footbridge verdict; the narrow-plan
  control shows what happens without it (closeness).
- Condition 1 (`objectNotEvil`) is stipulated true in all four descriptions.
  Only control 11 varies it. A tradition that classifies harvesting or pushing as
  evil by object would make those verdicts overdetermined.
- Only deaths are counted, so "act consequentialism" here is lives-only.

Senses (`corpus/disambiguations`): KILLS_1 any causal path from the act to the
harm (diverting kills, as in ordinary use); KILLS_2 a stipulated technical
relation, introducing a new threat (a path avoiding the redirection). MEANS_1
every causal path from act to saving passes through the harm; MEANS_2 the harm
is planned and some path leads from it to the saving (MEANS_2 does not entail
MEANS_1). INTENDS_1 plan inclusion; INTENDS_2 every known necessary causal means
counts as intended (by its stated content an alias of MEANS_1; no principle uses
it). The two readings of double-effect condition 3 (causal, MEANS_1; intention,
MEANS_2) are recorded as equal alternatives; neither is labelled "classical".

## Which principle fits which verdict

Computed values for intervening (P = permissible, I = impermissible):

| Principle | Switch | Footbridge | Transplant | Loop | Common triad |
| --- | --- | --- | --- | --- | --- |
| Lives-only act consequentialism | P | P | P | P | inconsistent (footbridge/transplant case) |
| Causal no-killing (KILLS_1) | I | I | I | I | inconsistent (switch) |
| Double effect, causal reading (MEANS_1, INTENDS_1) | P | I | I | I | entailed |
| Double effect, intention reading (MEANS_2) | P | I* | I* | P | entailed |
| Causal MEANS_1 principle (one Kantian-inspired reading) | P | I | I | I | entailed |
| Thomson-style redirection (KILLS_2) | P | I | I | P | entailed |

\* rests on the stipulated plan fact that the harm is planned.

Results: `acFootbridge`, `acTransplant`, `causalNoKillingSwitch` (rival verdicts
derived); `footbridgeVerdictExcludesAC`, `transplantVerdictExcludesAC`,
`switchVerdictExcludesCausalNoKilling` (conditional refutations, recorded as
`refutes` relations that do not count until the verdicts are established);
`doubleEffectTriad`, `intentionDoubleEffectTriad`, `meansTriad`,
`redirectionTriad`; the four loop results; `jointModels`; `controls`.

The two refutations of act consequentialism come from one formal case and share
its verdict-warrant dependency. The KILLS_2 reading escapes the switch test, so
the switch verdict refutes only the KILLS_1 form of an absolute no-killing
deontology. That switch verdict is itself contested: Thomson 2008, unread here,
is reported to reject the bystander's permission.

Controls (`TrolleyControls`):

1. *Causal path only.* The side-effect footbridge (a dropped weight stops the
   trolley and its fall also kills the bystander) and the narrow-plan footbridge
   share plan, death counts and object; the harm is off the rescue path in the
   first and on it in the second. This flips the causal reading of double effect
   and the causal means principle, not the intention reading or act
   consequentialism.
2. *Closeness.* The footbridge graph with the harm left out of the plan stays
   impermissible on the causal reading and becomes permissible on the intention
   reading.
3. *Intention.* A malicious switcher who plans the one's death is forbidden by
   both double-effect readings and permitted by the means and redirection
   principles.
4. *Numbers.* Reversed numbers defeat the causal reading, the means and
   redirection principles and act consequentialism.
5. *KILLS.* The switch is KILLS_1 but not KILLS_2.
6. *Loop.* The loop harm is MEANS_1 but not planned; planning it makes the
   intention reading forbid the loop.
7. MEANS_2 implies INTENDS_1, so on the intention reading condition 3 adds
   nothing to condition 2.
8. Footbridge and transplant coincide in the frame.
9. The case facts alone do not entail the common triad (trivially, by the empty
   assignment): the principle premise is needed.
10. INTENDS_1 and INTENDS_2 split on the loop and agree on the other three cases.
11. *Condition 1.* An evil object on the switch structure defeats both
    double-effect readings but not the means or redirection principles.

## Loop finding

Thomson's loop is an objection to double effect with a stated mechanism: the
one's being hit is causally needed to stop the trolley, yet the case differs
from the switch only by track behind the one. In the frame:

- The causal reading of double effect forbids the loop. The failing condition is
  condition 3 in MEANS_1, not condition 2: the plan omits the harm. The causal
  MEANS_1 principle agrees, so on these four cases the two are not separated.
- The intention reading permits the loop, but only given Kamm's plan reading;
  with the harm in the plan it forbids it (control 6). The same reading, applied
  to a footbridge agent said to intend only the impact, permits pushing
  (control 2), so it needs a closeness criterion that the frame does not supply.
- The redirection principle permits the loop on causal structure alone and
  permits the malicious switcher (control 3).

So double effect diverges from the causal means principle only on its intention
reading. Rescuing the permissive loop verdict either moves condition 3 into the
plan, which must then answer closeness, or replaces it by a causal-structure
condition that ignores intention. Whether the loop verdict has warrant is
unassessed; if it does not, the loop is not an objection to the causal reading.

## Survivors compared

The four principles that entail the triad, on the further cases, with the warrant
of every column's verdict unassessed:

| Principle | Loop | Malicious switcher | Closeness (narrow-plan footbridge) | Evil object |
| --- | --- | --- | --- | --- |
| Double effect, causal reading | I | I | I | I |
| Double effect, intention reading | P (plan-dependent) | I | P | I |
| Causal MEANS_1 principle | I | P | I | P |
| Thomson-style redirection | P | P | I | P |

No column has an assessed verdict, so no ranking follows. A principle's verdict
in a column is a cost only if that verdict conflicts with a warranted commitment.
For example, permitting the malicious switcher conflicts only with a commitment
that intention bears on permissibility, which is itself contested (some hold that
intention bears on the agent's character, not on permissibility; unread lead).
The survivors stand at parity in this frame.

## The consequentialist case, stated symmetrically

- *Positive warrant.* Impartiality, since each life counts equally, and
  simplicity: lives-only act consequentialism is the simplest principle that fits
  the switch, and the switch verdict shows that numbers carry weight.
- *Paradox of constraints* (mechanism: an agent-relative constraint forbids
  minimizing the very harm it treats as grave). In this frame the five are
  threatened by a trolley, not by agents' violations, so the paradox applies only
  in its outcome form; it does not touch the distinction of intended from foreseen
  harm.
- *Debunking* (mechanism: the footbridge and transplant responses would track
  personal-force features that the moral content of the verdicts does not
  mention). This targets the warrant of those verdicts, not the derivations. In
  the frame, double effect's verdict tracks causal role (control 1). Whether
  intuitive verdicts track causal role or force is the empirical question
  debunking raises; the evidence is unread here.
- *Indirect consequentialism.* A rule or institutional consequentialist can
  forbid transplant through effects on trust. Those facts are absent from the
  case description, so in this frame that reply is a different principle with
  extra case facts.

## Senses of "wholly good" and Rowe's permission constraint

The coordinator redirected the root bearing through the problem of evil, not
through q.94 natural law: `DISAMB 9880c06b` records that the practical "good act"
predicate has no derivation from the ontological goodness on the root route.
`TruthCore.Ethics.TrolleyRowe` reuses Rowe's `Sig`, `BlockingCost` and
`PermissionConstraintReading` and describes each prevention way by a trolley
`Case` (intervening = preventing; `harmOne` = a harm the preventer itself would
do). `Better b e` ("preventing is strictly better overall") is a supplied
primitive with its own definition record; it has no axiology or aggregation rule.

- WHOLLY_GOOD_1 `OutcomeStandard` with the OPEN outcome bridge
  `UnblockedPreventionBetter` gives Rowe's permission constraint
  (`outcomeSenseYieldsPermissionConstraint`). Because `Better` is free, this only
  relocates the constraint: goodness-sense control 6 proves that the premise
  bundle holds for some `Better` exactly when the constraint without its
  omniscience and intensity antecedents holds. The result is recorded as a
  near-transcription (assembly) and leaves the constraint's closure unchanged.
- WHOLLY_GOOD_2 `ConstraintStandard` with the same bridge relocates only the
  `ConstraintQualifiedPermission` condition (blocking cost, or every way of
  preventing violates double-effect conditions 1–3), also a near-transcription.
  Controls: with a footbridge-shaped way as the only supplied way, the qualified
  condition holds while Rowe's constraint fails (omnipotence does not constrain
  the supplied ways in that model); one constraint-free way restores Rowe's
  requirement (easy rescue survives).
- WHOLLY_GOOD_3 (`OntologicalGoodnessSense`: `GodIsSupremelyGood` and
  `DivineWillsGoodForAllExisting` on a shared carrier) is only a structural
  surrogate. Its model makes every relation true, and such relations exist for
  every signature, so the two predicates constrain no Rowe field. It omits the
  classical permission rule the corpus records (ST I q.2 a.3 ad 1;
  STMT-GOD-DRAWS-GOOD-FROM-EVERY-EVIL and its collective variants), and it is not
  the classical-theist sense. Its non-entailment is evidence about this encoding,
  not about the goodness of GOD_4.

Consequence for Rowe's argument: under WHOLLY_GOOD_2, Rowe's argument survives
for every suffering that has a constraint-free way of preventing it (control 2).
It loses force only where every prevention is constraint-violating, so it is the
theist's escape that WHOLLY_GOOD_2 confines to such cases. The triad is
compatible with WHOLLY_GOOD_2's constraint clause, as it is with the redirection
and means variants; it does not test rescue duties, and transferring human
verdicts to divine permitting is a further bridge (#1456).

## Reuse

Lean search (LeanSearch, lean-explore) found no normative-ethics vocabulary in
Mathlib; reachability reuses `Relation.ReflTransGen`. Reused by import: Rowe's
signature and constraint, `GodIsSupremelyGood`, `DivineWillsGoodForAllExisting`.
Not reused, because meanings do not coincide: `Ethics.HardCaseTyped` (opaque
factual predicates such as `deliberateKilling`, no causal graph; its killing
context is closest to transplant, with the offender as beneficiary),
`RossPermission`/`RossDerived` (ideal-frame and issued-norm permission, not a
governed assignment), `AgencyNeutrality` (pro-tanto reasons), `Population*` (real
welfare scales, not death counts), and the q.94 natural-law vocabulary.

## Shared edit

`corpus/statements/rowe-permission-constraint.json`: dropped the
APPARENTLY_POINTLESS definition, because the constraint concerns actual blocking
costs, not costs recognized by an investigator; with that link, every argument
concluding the statement mixed the two POINTLESS_GRATUITOUS senses. Added a
connection plan to STMT-GOD-EXISTS. The relocation leaves the statement's closure
as on main.

## Overall provisional assessment

The triad verdicts are treated as prima facie inputs. How widely they are shared,
the debunking evidence, the loop survey data and Thomson's later rejection of the
switch verdict are all unread here, and they get the same status. Given the
verdicts, lives-only act consequentialism and the KILLS_1 no-killing view are
excluded at matching scope, and four constraint principles fit the triad. They
split on the loop, the malicious switcher, closeness and evil objects, where no
verdict's warrant is assessed, so they stand at parity. Lives-only act
consequentialism rejects the footbridge/transplant verdicts. Its positive warrant
is impartiality and simplicity, and debunking is a possible defeater of those
verdicts.

For the case: these results establish no premise. The Rowe connection is a map of
senses, not support: WHOLLY_GOOD_1 and WHOLLY_GOOD_2 relocate Rowe's constraint
through a free comparison, and the WHOLLY_GOOD_3 surrogate shows only that two
stage-2 predicates without a permission rule fix nothing about permitting.

## Next tests

1. Give `Better` typed content that can fail, for example from Rowe's cost fields
   or from the ways' death counts, and retest the WHOLLY_GOOD_1 and WHOLLY_GOOD_2
   relocations.
2. Restore the classical permission rule (ST I q.2 a.3 ad 1, one of its recorded
   readings) on Rowe's signature, with a link from Rowe's events to the beings
   willed good, and retest WHOLLY_GOOD_3.
3. Closeness: add separate impact and death events, and test a closeness
   criterion that lets the intention reading keep the footbridge impermissible.
4. Warrant of the loop and malicious-switcher verdicts at matching scope with the
   triad.
5. Rowe: a concrete prevention case for which every way of preventing an intense
   suffering is constraint-violating (free agency), coordinated with #1456.
6. Source leads, unread: Aquinas ST II-II q.64 a.7; manualist four conditions;
   Thomson 1985 and 2008; Kamm on triple effect and the Principle of Permissible
   Harm; debunking and loop survey evidence.
