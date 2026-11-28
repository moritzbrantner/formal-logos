# The experience machine and "desirable insofar as perfect" (2026-11-28)

Exhibit-map lane 2. The thought experiment is used as a concrete test of the
principles behind ST I q.5 a.1's second premise, STMT-DESIRABLE-INSOFAR-AS-PERFECT
(`060e7a1a`, Lean `DesirableInsofarAsPerfectReading`). That premise feeds argument
`a5a50fe3`, which concludes STMT-GOODNESS-IS-ACTUALITY (`00e962ae`) on the
designated stage-2 routes. It is open and reaches the root, but it is a leaf of no
computed route, because `00e962ae` is closed by another argument (`f2ad40c3`).
Before this batch it had no recorded rival and no argument. All formulations here
are analyst formulations with attribution deferred. The thought experiment and the
literature below are **unread leads**: nothing in this note quotes or attributes
them.

Records: spec `specs/experience-machine-desirability.toml`, vocabulary
`TruthCore.Ethics.ExperienceMachine`, results `TruthCore.Results.Ethics.ExperienceMachine`,
and the attempt "Experience machine as a test of desirable-insofar-as-perfect".

## Encoding

The bearers of q.5's `DesirableIn`/`PerfectIn` are lives, that is, a person living a
life. A perfection of the life is therefore a perfection of the same bearer whose
desirability is assessed. This is the brief's proviso, and it is built in by typing.
Three parameters are new, each with a primitive definition record:

- `experience : Being → Profile`, the experiential profile ("how the life is from
  the inside");
- `BetterFor : Being → Being → Prop`, "better for its subject", the person-level
  comparison that a choice between lives elicits;
- the rival `ExperientialismReading experience DesirableIn` (statement `202c82fb`),
  encoded as Mathlib's `Function.FactorsThrough`. The map `x ↦ DesirableIn x`
  factors through the profile. `experientialism_iff_factor` gives the positive
  replacement account: some valuation of profiles fixes desirability in every
  respect. Hedonism proper, on which only pleasantness counts, is one such
  valuation.

Lean search before vocabulary: lean-explore and LeanSearch returned
`Function.FactorsThrough` and `Function.factorsThrough_iff`
(`Mathlib.Logic.Function.Basic`), and these are used. No Mathlib notion was found
for respect dominance or for betterness-for-a-subject. The strength-comparison
specifications reuse `TruthCore.Logic.StrengthComparison`.

## Results and re-presentation probes

| Result | Theorem | Kind | Probe outcome |
|---|---|---|---|
| Experientialism fails, from the stay-out verdict (argument `948b97b0`, result `39364840`) | `experientialismFailsFromStayOut`: `SameExperience e r m → StayOutVerdict B r m → BetterRequiresRespectDifference B D → ExperientialismFails e D` | declared near-transcription (instantiation); `refutes` the rival | **Equivalence holds.** Comparison conjunct 8 proves `(∃ r m B, Same ∧ Verdict ∧ Bridge) ↔ ExperientialismFails e D`. The verdict with the bridge *is* a counterexample, so the result adds no inferential content, and the refutation weighs exactly what the verdict weighs. It closes nothing: it is a transcription with open premises, and the refutation does not count. |
| Experience-machine comparison (argument `19b4aafd`, result `c7ace51f`) | `ExperienceMachineComparison`, premise-free, 8 conjuncts | `tests` 060e7a1a and the rival | Premise-free; it closes only its own conclusion, which no argument uses. Conjunct 2 is itself an exact equivalence, the "price" (below). |
| Joint models and controls (argument `00e2d085`, result `0a48ac7e`) | `ExperienceMachineControls`, premise-free, finite carrier | `tests` 060e7a1a and the refutation | Premise-free. No row makes every relation true: `Has` is false for 6 of the 12 life–good pairs, and every desirability relation is partial. In rows 1–5 betterness is set to strict respect dominance, so both transfer statements hold there **by construction**. This is disclosed: those rows test the desirability relations, not the bridge. |
| Forward and backward halves (results `68d2ed4e`, `4276866b`) | `perfectMakesDesirableOfInsofar`, `desirableOnlyIfPerfectOfInsofar` | declared transcriptions (instantiation), `strengthens` registrations | One direction of the premise's biconditional. They close nothing while 060e7a1a is open, and they sit outside the root path with connection plans. |
| Exact differences (results `af8859a4`, `aa54797d`) | `forwardExactDifference`, `backwardExactDifference` | `strength_comparison` equivalence certificates | Each certifies the other half as the exact content the biconditional adds. |

`truth frontier-diff --base b82d5b70f`: **no change**. 060e7a1a stays open, and it
now has one recorded rival whose refutation does not count.

## What the case does and does not show

Take q.5's biconditional as F ∧ B, where F is "perfect ⇒ desirable" (`7391aaac`)
and B is "desirable ⇒ perfect" (`9c2cd0fb`). Fix the case: same profile, and the real
life perfect in every respect the machine life is, plus achievement.

1. **The coherence of the case, not its verdict, already makes q.5 and
   experientialism contraries** (comparison conjunct 3). The exact price of holding
   both is that perfection supervenes on experience (conjunct 2). So a proponent of
   q.5 who grants the case's possibility must reject experientialism, whatever they
   intuit about plugging in.
2. **Experientialism conflicts with neither half alone.** Conjunct 7 shows that with
   F it makes the machine life desirable in the achievement it lacks. With B it makes
   the real life not desirable in the achievement it has. Rows 2 and 3 are
   nonvacuous joint models: hedonism with B, and presentational experientialism
   with F. Hedonism proper is compatible with "desirable only insofar as perfect"
   in the carrier, where felt pleasure is counted as a perfection both lives have.
3. **The verdict discriminates experientialism, not the halves.** The stay-out
   verdict holds in row 1 (F ∧ B), in row 4 (F ∧ ¬B, partial experientialism) and in
   row 5 (B ∧ ¬F, a restricted formal model). It fails in rows 2 and 3
   (experientialism).

**Direction finding.** This refines the brief. Within the case, the per-respect
verdict "real desirable in achievement, machine not" consists of one instance of F
(at the real life) and one instance of B (at the machine life). It is therefore
not evidence for one direction to the exclusion of the other. What it supports is the
existential core "some real perfection makes a desirability difference with
experience fixed" (the negation of experientialism). That is the claim
"real perfection makes desirable". It is not evidence for "desirable *only* insofar
as perfect" taken universally: row 4 denies that and still gives the verdict. The
same holds for the forward half taken universally (row 5). These rows are models,
not recorded positions: row 5 in particular is a formal non-entailment witness and
is not offered as a view anyone holds.

## Verdict/principle table (finite carrier)

| Account (row) | F | B | Experientialism | Stay-out verdict | Plug-in/indifference |
|---|---|---|---|---|---|
| q.5 biconditional, desirability = possession (1) | holds | holds | fails | holds | — |
| Hedonism, pleasure only as presented (2) | fails | holds | holds | fails | holds |
| Presentational experientialism (3) | holds | fails | holds | fails | holds |
| Partial experientialism: possession plus felt friendship (4) | holds | fails | fails | holds | — |
| Restricted model: possession except knowledge (5) | fails | holds | fails | holds | — |

Generic (comparison): the biconditional with respect dominance forces the verdict
(conjunct 4). Experientialism with the transfer bridge forbids it (conjunct 5).

## The transfer bridge (explicit, OPEN)

STMT "Betterness for a subject requires a respect desirable in the better life and
not in the other" (`0f73882f`, `BetterRequiresRespectDifference`) carries the
person-level welfare comparison over to q.5's per-perfection desirability. It makes
two commitments:

- it identifies the respects that ground betterness for a subject with q.5's respects
  of desirability, even though 060e7a1a does not specify whose appetite is in
  question (DEF-DESIRABLE-IN-A-PERFECTION);
- it leaves out betterness by degree within a respect both lives share.

The converse, respect dominance, is used only inside the comparison. Row 6 shows the
bridge is needed for the refutation: with a betterness relation unrelated to
desirability, experientialism, same experience and the verdict hold together.
Positive warrant offered for the bridge: in ST I q.5 a.1, *omnia appetunt suam
perfectionem* speaks of each thing's appetite for **its own** perfection. That
favours reading `DesirableIn` as desirability for the bearer. On that reading,
person-level betterness for the subject is the natural aggregate. This is analyst
interpretation and has not been checked against q.5 a.1 ad 1–3 or q.6 a.1 in this
batch.

## Strongest objection, and the experientialist's positive warrant

**Objection (status-quo bias / reversed machine).**

- *Target*: the verdict premise (`2c6ab1a6`).
- *Mechanism*: the stay-out preference would track the default rather than the value
  of reality. Subjects told that they are *already* in a machine would prefer to stay
  in it. If so, the verdict reflects a bias toward the present state and does not
  discriminate experientialism.
- *Empirical basis* (unread leads):
  - F. De Brigard, "If you like it, does it matter if it's real?", *Philosophical
    Psychology* 23 (2010), reversed-machine vignettes;
  - D. Weijers, "Nozick's experience machine is dead, long live the experience
    machine!", *Philosophical Psychology* 27 (2014), framing variants.
- *Relevance*: this is the only premise of the refutation that carries the case's
  evidential weight (probe above).
- *Effect if confirmed*: it undercuts the verdict. It does not rebut q.5: conjunct 3
  is unaffected, and it supplies no evidence *for* experientialism.

**Experientialist warrant.** The experience requirement: what makes no difference
to how a life is from the inside cannot make it go better for its subject. Unread
leads: Mill, *Utilitarianism* ch. 4; Sumner; Crisp. Further support comes from the
explanatory economy of one valuation of profiles (`experientialism_iff_factor`) and
from the uncontested desirability of pleasure. Row 2 shows that this last ground is
also available to B. The rival's recorded price: it must reject the verdict, reject
the bridge, or deny the case's same-profile stipulation (for example by
individuating profiles by intentional content).

**Equal footing.** The verdict and the debunking evidence have the same status here:
both are unread prima facie data. Neither is weighed against the other in this
batch. No ranking of hedonism against perfectionism is made on the case alone.

## Provisional assessment

The case adds a recorded positive rival, an exact price for combining it with the
q.5 premise, and a conditional refutation that is honestly a re-presentation. It
adds no warrant for the universal biconditional beyond the existential core, and it
does not touch STMT-GOOD-IS-DESIRABLE (`ff35f485`), which no encoding here uses.

The q.5 premise's best case-based support is therefore conditional on three open
inputs: the verdict, the bridge and the same-profile stipulation. The decisive open
question is empirical and interpretive (the debunking data), not formal.

Revision conditions:

- read reversed-machine data that survive framing controls → withdraw the verdict's
  standing;
- an argument that profiles are individuated by content → the case loses its
  same-profile premise.

Caution for closure: rule (c) would count 060e7a1a as defended if its *only*
recorded rival were refuted with established premises. Even then, the verdict would
support only the existential core (rows 4 and 5). Before any such refutation could
count, a composite (hybrid) welfare view denying B should be recorded as a rival if
its warrant is read.

## BLESSED_2 (secondary)

`DISAMB 70f4f510` reads BLESSED_2 as perfect intellectual being in act in
understanding: beatitude as an operation on what is, not a felt state. The machine
controls give a narrow formal analogue. A view on which desirability tracks actual
possession (row 1) separates two lives whose inner course is identical, so a
beatitude defined by operation on the real is not fixed by experiential profile. A
beatitude defined by its felt state would be (rows 2 and 3).

This does not decide Thomist (intellect) against Scotist (will's enjoyment)
beatitude. Both locate beatitude in an operation on the real good, and they differ on
which power's act is formally beatific. The machine case varies the reality of the
object, not the power. No BLESSED record is changed and no sense bridge is used.

## Next tests

1. Materialize and read the De Brigard / Weijers data before any change to the
   verdict's standing (owner policy: selected source research only).
2. A degree-valued version (Mathlib order on desirability) to drop the bridge's
   exclusion of within-respect degrees.
3. Record the composite welfare view as a rival to B if its warrant is read.
4. If the owner selects it, add `strong_version_needed` to `a5a50fe3`. The
   biconditional conclusion needs both halves (exact differences above). It is
   outside this batch's file ownership.
