# C2: what grounds the contingency of an actual being? (2026-11-23)

Follow-up to PR #1870 (gap 1 and next test 3), God-existence stage of the #143
root. Batch `specs/c2-contingency-grounding.toml`, vocabulary module
`TruthCore.Causality.ContingencyGrounding`, results module
`TruthCore.Results.Causality.ContingencyGrounding`, attempt
`137ac90d-d110-45db-a2a3-44e5f0406eea`. Analyst formulations, attribution
deferred (logic first). Locators below are navigation only; no source claim is
made and none of the cited texts was materialized or read for this slice.
Repaired after the independent semantic challenge of head `470f90b80`.

**Graph destination.** The same-witness First Way endpoint `f9208664`
(`FirstMoverNecessaryPureActAt`), which projects through result `402e5643` to
STMT-NECESSARY-CONCRETE-AT `b19ffd92`, which reaches the root. Second
destination: #1870's B2 ∨ B4 `3c9d683b`, which feeds the route-A∨B argument
`81a17728` to the same endpoint. Computed `truth frontier-diff` against the
merge base: open premises reaching the root 550 → 553 (400 → 403 bare,
92 supported, 58 stated); route cost unchanged (16); 4 verified support
alternatives added (unreceivedness `2e2ab9cc`, B2 ∨ B4 `3c9d683b`, C2
`6508c239`, endpoint `f9208664`); 4 bare premises added (PGP `20d5fecd`,
correlation `9163c423`, passive→receptive `16c760a3`, corruptible→POTENCY_1
`8bfc4ab7`); B2 ∨ B4 `3c9d683b` moved bare → closed. "Closed" is
frontier-diff's vocabulary for *proved from other premises*: its dossier
reads `established: false`. Its leaf is replaced by four new bare premises; no
premise is established.

**Question.** C2: *a metaphysically contingent actual being must possess some
relevant receptive potency or receive its actuality from something
metaphysically prior.* The owner's target is C2's substantive warrant, not
another reformulation of contingency → potency.

## 1. Fixed meanings and what separates them

| Notion | Formal reading | Separated from its neighbours by |
|---|---|---|
| Modal contingency | `ContingentAt F.history.ontic w x`: exists at `w`, absent at some accessible world (MODAL_CONTINGENCY_1) | — |
| Avicennian "possible in itself, necessary through another" | not formalized here; an emanated being can be modally necessary yet caused (q.2 a.3's necessary things caused by another) | C2 is about modal contingency only |
| (a) possible not to be in the subject | `CanFailToBe x F.esse` (DEF-CAN-FAIL-TO-BE at the respect of being, *corruptibile simpliciter*), sense POSSIBLE_NOT_TO_BE_1 of the new disambiguation `d25cee67` | `angelic`: contingent and incorruptible simply; law 10: not POTENCY_1 at esse |
| (b) possible not to be through another's power | some `y` with `PowerOverEsse y x` (POWER_OVER_ESSE_1, DEF `3fd6bddb`), sense POSSIBLE_NOT_TO_BE_2. This widens q.9 a.2's creator channel to the broad power, so (a) and (b) are not exclusive (a log that fire can destroy has both) | `angelic` (b without a); `corruptor` (a and b, b without causing esse) |
| (b′) giving power over esse | `GivingPowerOverEsse` (POWER_OVER_ESSE_2, DEF `220ca6f1`): the conjunction of power over esse and being a CAUSE_2 of it, not a primitive giving power | disambiguation `f5dda05f`; correlation is trivial under (b′) by definition of the conjunction (law 11), which says nothing about a primitive creator's-power reading; the batch uses (b) |
| (c) bare modal absence | `ContingentAt` itself | `bruteSimple`: (c) with neither (a) nor (b) |
| Unrealized POTENCY_1 | `AdoptedPotency.InPotency`: `CanBe ∧ ¬ InAct` | law 10 and #1870's R2 law: at esse it contradicts actual existence |
| Receptive potency | RECEPTIVE_POTENCY_1 (DEF-RECEPTIVE-POTENCY), a principle's potency to an act it may already have | `witness`: an actual contingent being receives esse in a principle in receptive potency to it |
| Passive potency (genus) | not a single predicate; its two species used here are (a) and matter's receptivity to form | passive→receptive is an OPEN bridge between them, not a definition |
| Existential composition | `esseOf x ≠ essenceOf x` (B6's consequent) | #1870 `bruteFirst`: distinct esse with no recipient |
| Received esse | `Received x p` (DEF-ESSE-RECEIVED-IN) | `uncausedComposite`: received esse with no cause |
| Existential receptivity | `ExistentiallyReceptive`, DEF `f9f58df7`: received esse in a principle in receptive potency to it, or matter–form composition | C2's "relevant" receptivity is typed no further: any such recipient or composition satisfies it |

**Reuse decision (differs from the brief).** The brief proposed a new
primitive `PotencyForNonbeing`. The corpus already has it: DEF-CAN-FAIL-TO-BE
reads `CanFailToBe x r` as the potency of the contradictory and identifies what
can fail to be with the corruptible; DEF-INCORRUPTIBLE-SIMPLY takes the
respect-of-being instance as *incorruptibile simpliciter*. DEF-CAN-FAIL-TO-BE
does not itself say "in the subject", while q.9 a.2 also calls creatures
"possible not to be" through another's power; disambiguation `d25cee67` now
records that this batch reads `CanFailToBe` at esse as the in-subject channel
only and represents the through-another channel by `PowerOverEsse`. Under that
reading Aquinas denies #1870's B4a (every contingent being can fail to be in
substance) for angels.

**Power over esse.** Two existing definitions bind `MutableThroughAnother` with
different readings: DEF-MUTABLE-THROUGH-ANOTHER (any power to change, the
potter example) and DEF-MUTABILITY-IN-ANOTHER (the creator's power to
originate or withdraw esse). Disambiguation `f5dda05f` separates them at esse
with distinct declarations; PGP and correlation use the broad sense.

## 2. Checked results

All theorems in `TruthCore.Results.Causality.ContingencyGrounding`;
Comparator and NanoDa pass; bind-check binds all eleven. Statement ids: C2
`6508c239`, C2⁻ `8478f367`, PGP `20d5fecd`, correlation `9163c423`,
passive→receptive `16c760a3`, corruptible→POTENCY_1 `8bfc4ab7`,
unreceivedness `2e2ab9cc`, controls `07a9006e`, C2-over-C2⁻ difference
`703d8c9c`, its equivalence `f0665fca`, its separator `63f55a6f`.

| Result | Theorem | Premises → conclusion |
|---|---|---|
| `32bf794f` | `c2FromPowerGrounding` | PGP, correlation, passive→receptive, no self-esse-cause `b62a64ab`, B3 `ee74c678` → C2 (constructive) |
| `96eb02fb` | `firstMoverUnreceivedFromSimplicity` | simplicity `78246da5`, R3 `65f3d0c7`, *De ente* `7fcfcee8`, irreflexivity `14325c83` → unreceivedness (constructive) |
| `e5d49f99` | `firstMoverNecessaryByReceptivityOrPriorCause` | EM, *prima via* `7bce7007`, B0 `bd0a4f81`, firstness `74eb9113`, pure act `6c18d52b` (carried), unreceivedness, C2 → endpoint `f9208664` |
| `61a1edec` | `c2FromReception` | R1 `ae9d9473`, *De ente* → C2 (instantiation) |
| `560b0d8d` | `c2FromEsseCause` | B2 `8a8d00e9`, B3 → C2 (instantiation) |
| `b1f14d6b` | `c2ImpliesWeak` | C2 → C2⁻ (strength order; relation `01163101`) |
| `8890e569` | `c2FromWeakAndPriority` | C2⁻, B3 → C2 |
| `bf2f0e8e` | `potencyOrEsseCauseFromPowerGrounding` | PGP, correlation, no self-esse-cause, corruptible→POTENCY_1 → B2 ∨ B4 `3c9d683b` |
| `7fcf8487` | `c2OverWeakExact` | premise-free: C2 ↔ C2⁻ ∧ difference |
| `dd9bccd1` | `unprioritizedSeparates` | premise-free: C2⁻ ∧ ¬C2 in the `unprioritized` setting |
| `cafd9800` | `controls` | premise-free laws 1–11 and ten models |

The strength comparison `07689384` certifies the C2/C2⁻ difference (#1598):
`truth strength-comparisons` reports "strict strengthening; exact
factorization proved; converse refuted by separating setting".

Laws (`Model.Laws`): (1) C2 → C2⁻; (2) C2⁻ ∧ B3 → C2; (3) R1 ∧ *De ente* → C2;
(4) B2 ∧ B3 → C2; (5) correlation → #1870 bridge (ii) restricted to beings
incorruptible simply; (6) PGP ∧ no power of anything over its own esse ∧
corruptible→POTENCY_1 → MUTABLE_3 for every contingent being (#1870 bridge (i));
(7) the PGP route composes to the endpoint; (8) B4b → corruptible→POTENCY_1;
(9) B4a → PGP; (10) with adopted POTENCY_1 and the existence-to-act interface,
B4b excludes every actual corruptible at `w`; (11) under POWER_OVER_ESSE_2 the
correlation is trivial, by definition of that sense as a conjunction containing
CAUSE_2; this does not show that a primitive creator's-power reading would
trivialize correlation.

**Findings that differ from the brief's expectations.**
- No excluded middle is needed for C2 from PGP (distinctness of the power's
  holder comes constructively from `b62a64ab`) or for unreceivedness. EM
  enters only where necessity is concluded.
- The brief's argument 2 is registered as two steps, so unreceivedness is a
  separate node: pure actuality (POTENCY_1), unreceived esse, underivedness
  (firstness) and necessary existence are four distinct propositions.
- #1870's bridge (ii) ("another's power over a thing's esse gives a distinct
  cause of its esse"): correlation yields it only for beings incorruptible
  simply (law 5). The unrestricted form is not derived, and its countermodel
  (`corruptor`) is an uncaused corruptible composite; under the tenseless
  CAUSE_2 an ordinary corruptible has a distinct esse-cause (its generator), so
  the model says nothing against the unrestricted form for ordinary
  corruptibles. Result `bf2f0e8e` registers a decomposition of B2 ∨ B4 that
  does not need the unrestricted form: the corruptibility channel goes through
  corruptible→POTENCY_1 (a new OPEN bridge).
- Law 10 is a new defect finding for #1870's B4b: read with the adopted
  POTENCY_1 it excludes every actual corruptible, as R2 excluded every actual
  receiver.
- C2 and B2 ∨ B4 are logically independent (`inertPowerHolder`: C2 without
  B2 ∨ B4; `potencyOnly`: B2 ∨ B4 without C2).
- `truth countermodel` does not support `CausalityFrame` parameters; all
  models are hand-written as in #1870.
- Duper (`--premise-pool all`, 8 candidates, 100000 heartbeats; C2, the
  endpoint and B2 ∨ B4, run on the pre-repair head): 2 proved, 1 unresolved.
  It re-found the endpoint from the grounding endpoint `11958874` (known), and
  B2 ∨ B4 from R2 `6e8942c8` with R1, which is vacuous at actual contingents
  (#1870 reception law) and not registered. C2 stayed unresolved.

## 3. Models (structural satisfiability, not metaphysical possibility)

Frames reuse `FirstMoverNecessity.Model.mk` (worlds, beings and respects
`Bool`, reading world `true`, `f` moves `x` in heat, `x` in POTENCY_1 in heat
only, so `f` is POTENCY_1-pure act relative to the frame's two respects).
Excluded middle is a logical premise and is not a model conjunct. "Admissible
on" names the metaphysics under which the structure could be read as a real
case; the model certifies only structural satisfiability.

| Model | What holds | What fails | Shows | Admissible on |
|---|---|---|---|---|
| `bruteSimple` (rivals 6.1/6.3) | every other premise of the PGP and C2 routes; CCR (degenerate check, see §12) | PGP, C2, endpoint | ¬C2 here needs ¬PGP (¬PGP alone does not give ¬C2: `uncausedComposite`) | a hybrid view: the First Way's act and potency for change, non-power modality for existence (primitivist, combinatorial, Lewisian counterpart, or essence-based with existence-conditional essences). Pure Humeans reject the model's act, potency and motion premises |
| `selfAnnihilator` v1 / v2 | PGP; v2 also correlation | v1 correlation; v2 no-self-esse-cause; C2 in both | self-annihilation must deny correlation or admit self-causation of esse | v2 only where self-causation of esse is admitted |
| `uncausedComposite` (6.2) | C2 (reception), R1, *De ente* | PGP, B2, C2's prior-cause disjunct | C2 does not entail PGP; C2 strictly weaker than B2 ∧ B3 | an ontology allowing an uncaused composite (it contradicts q.3 a.4, not C2) |
| `angelic` | every premise of the PGP argument; C2 by both disjuncts | B4, pure-act target (structural only) | possible non-existence without a potency to non-being; extrinsically grounded contingency | the Thomist account of a created intelligence for: contingent, incorruptible simply, C2 by both disjuncts, contingency grounded extrinsically. Not for the B4 and target failures: Aquinas's angels have potencies of intellect, will and place (q.9 a.2), which make B4 true and the target vacuous |
| `inertPowerHolder` | PGP, C2 (reception) | correlation, B2, B2 ∨ B4 | omission model of correlation (an inert power over being, no causal role); C2 ⊬ B2 ∨ B4 | — (it is the counterexample type in the revision conditions) |
| `bareCorruptible` | PGP, correlation, `b62a64ab`, B3 | passive→receptive, C2 | omission model | — |
| `unprioritizedSource` | PGP, correlation, passive→receptive, `b62a64ab`, C2⁻ | B3, C2 | omission model; C2 strictly strengthens C2⁻ | — |
| `witness` | every premise of every new argument, PGP, correlation, passive→receptive and corruptible→POTENCY_1 applied nonvacuously; C2, B2 ∨ B4, endpoint | — | nonvacuity | the Thomist account of a corruptible caused composite |
| `potencyOnly` (direction 9) | pure-act target at `w`, B4, B2 ∨ B4 | PGP, C2 | with `angelic`, PGP and C2 are independent of the target (unlike B4) | — |
| `corruptor` | correlation, PGP, C2 (through matter and form), restricted bridge (ii) | R1, unrestricted bridge (ii) | C2 does not require R1; unrestricted bridge (ii) not derivable from correlation | an uncaused corruptible composite (not ordinary corruption) |

**Deist originator.** With the tenseless `CausesIn`, a deist originator is a
CAUSE_2 of what it originates, so it satisfies the typed correlation, and C2's
prior-cause disjunct given B3 or an independent priority fact. The deist rival
bears only on a tensed (conserving)
strengthening of correlation (next test 2), not on the batch as typed.

## 4. Could a purely actual being be contingent? (direction 2)

Relative to the frame's two respects, yes structurally: `angelic` (and #1870
`conserved`) has a contingent being in POTENCY_1 in no modelled respect,
receiving esse from a necessary prior source under whose power it stands. That
is a structural separation only; the Thomist angel is not POTENCY_1-pure act
(intellect, will, place). Under "unreceived and underived" pure act, a
contingent pure-act being is exactly a counterexample to C2 at that being
(`bruteSimple`).

## 5. Strongest positive explanation (direction 3)

The Aristotelian-Thomistic explanation is that modal contingency is not a
brute fact about a thing: its possible non-being is *someone's potentiality*.
Either the thing has a passive potency to non-being (matter: corruptibility,
Θ.8 1050b), or another has power over its esse (q.9 a.2: "mutable by the power
of another"; q.104: conservation). By Θ.1 an active power over a thing either
works on a passive potency in it or, for the creation exception, is the giving
and withholding of esse (q.104 a.3). Results `32bf794f` and `bf2f0e8e` make
this case analysis explicit and show which premise carries each step. That is
clarification of the argument's structure, not additional warrant. As typed,
PGP and correlation are material disjunctions, weaker than the explanatory
claims that motivate them.

**General theory (navigation only, unread in this slice).** Powers- and
potentiality-based theories of modality ground possibility in the
potentialities of actual things (B. Vetter, *Potentiality*, 2015; J. Jacobs, "A
powers theory of modality", 2010; A. Pruss, *Actuality, Possibility, and
Worlds*, 2011; A. Borghini and N. Williams, "A dispositional theory of
possibility", 2008). It is a general modal metaphysics with motivations
independent of theism, not a Thomist thesis.

**The "too few potentialities" objection.** Target: the thesis that every
possibility has an actual grounding potentiality. Mechanism: some
possibilities (alien properties and individuals; that there might have been
nothing concrete) seem to have no actual bearer whose potentiality grounds
them. At the foundational being, PGP meets this mechanism exactly: by
hypothesis nothing actual has a potentiality for that being's absence. PGP's
narrowness (it concerns only the possible absence of an *actual* individual)
does not escape the mechanism; it bears only on the objection's evidential
force. For alien and global possibilities there are independently credible
modal data that a theory must accommodate. For the foundational being the only
datum, "it could be absent", is the disputed claim itself, supplied by
subtraction or conceivability arguments generalized from ordinary concreta,
which also satisfy PGP. So at this node the objection has its mechanism but
no independent datum behind it; equally, PGP has no datum beyond its general
theory.

## 6. Essence–esse (direction 4)

Received esse explains *how* dependence is possible: it supplies the recipient
for the second channel, and q.3 a.4 links distinct esse to an external cause.
But the modal step contingency → distinct esse (B6) or → reception (R1) is not
warranted by the composition thesis alone (#1870 `bruteFirst`). It rests on the
same power-grounding consideration or on the limitation principle (open in
#1881). So the essence–esse route is informative about mechanism but shares
C2's modal crux. Law 3: R1 with *De ente* implies C2, not conversely
(`corruptor`).

## 7. Able not to exist versus having an unrealized potency (direction 5)

On Aquinas's own view (q.9 a.2, q.50 a.5) angels are modally contingent with
no intrinsic potency to non-being. `angelic` formalizes this part: contingent,
incorruptible simply, under a prior source's power, C2 by both disjuncts. So
possible non-existence does not imply a potency to non-being. B4 ("in POTENCY_1
in some respect") holds of the Thomist angel through unrelated respects
(intellect, will, place), which `angelic` does not model; that is why B4 is
"any respect" and classically the target. At esse POTENCY_1 is excluded (R2
law, law 10). Under the in-subject reading of `CanFailToBe`, Aquinas denies
#1870's B4a for angels.

## 8. Rivals and their prices (direction 6)

Each entry names its target, mechanism, independent justification, relevance
and price.

- **Brute contingent simple first actuality (6.1/6.3, `bruteSimple`).**
  Target: PGP (and so C2) at the foundational being. Mechanism: the being's
  possible absence is no power's potentiality. Independent justification:
  developed general modal metaphysics that do not ground possibility of
  existence in powers: modal primitivism; combinatorialism (Armstrong's
  recombination admits contracted worlds lacking some actual individuals);
  Lewisian counterpart theory; essence-based modality (Fine, Lowe: de re
  possibility as the absence of an essential exclusion), a developed non-power
  account of exactly PGP's subject matter. Relevance: each denies PGP for the
  foundational case. Price: de re possibility of absence for an individual with
  no internal or external modal ground in any power. The subtraction premise's
  ordinary-case warrant does not discriminate; neither does PGP's (§13).
- **Essence-based modality applied to the first mover.** To conclude that a
  being whose esse is its essence is necessary, it needs esse = essence
  together with an essence that includes existence; existence-conditional
  essentialism ("necessarily, if `x` exists, `x` is F") blocks that step. This
  is the B6 crux, recorded here as a standing rival to B6 (#1870 route C); the
  essentialist rival to PGP is the previous bullet.
- **Hybrid rival.** It accepts the First Way's act and potency for change but
  uses non-power modality for existence. Relevant difference, with independent
  justification: existence is not a change (creation and annihilation are not
  changes, ST I q.45 a.2 ad 2, navigation only), so powers may ground
  possibilities of change without grounding possibilities of existence. PGP's
  counter-consideration at the foundational being is theoretical unity only (one
  account of modality for change and for existence). Aquinas grounds creatures'
  possible non-being in the creator's power (q.9 a.2), but the foundational
  being has no prior power-holder, so that does not count there. Both sides
  recorded; no winner is claimed.
- **Contingent uncaused substance (6.2, `uncausedComposite`).** Compatible with
  C2 iff it is receptively composed; it then contradicts q.3 a.4/B2, not C2.
- **Deist originator.** Satisfies the typed correlation, and C2 given B3 or an
  independent priority fact (§3); it bears
  only on a tensed strengthening.
- **Inert power-holder (`inertPowerHolder`).** A power over a being's esse
  with no causal role and no potency to non-being in the patient: the
  counterexample type to correlation. No defended instance is recorded.
- **Self-annihilation (`selfAnnihilator`).** Must deny correlation (v1) or make
  the being a cause of its own esse (v2, against `b62a64ab`); C2 fails in both
  variants.
- **No substantive objection identified** to passive→receptive beyond the
  bare-corruptible structure, for which no independent account is recorded.

## 9. ¬C2 evaluation (direction 7)

A contingent, unreceived, pure-act being must be: actual at `w`, absent at
some accessible `w'`, with no receiving principle and no matter, no prior
giver, no potency to non-being, and, unless it denies correlation, no being
with power over its esse. Its contingency must be primitive or
non-power-grounded.

- *Not internally inconsistent*: `bruteSimple` is a structural model, with
  admissible interpretations under the hybrid view above.
- *Not merely contrary to Thomism*: it contradicts power-grounded modality for
  existence, which has independent general defenders.
- *A coherent rival* whose price is de re possibility of absence for an
  individual with no internal or external modal ground.

**Parity.** Under PGP, the necessity of an actual being needs no extra
truthmaker: it is the absence of any power grounding its absence (PGP and
neither disjunct at `x` give ¬ContingentAt; EM gives NecessaryAt). Mirror:
under combinatorial or essentialist modality, contingency is the default and
likewise needs no extra truthmaker. Under Humean modality no individual is
necessary, so that rival is global, not specific to C2. Under primitivism both
are primitive. None of this decides between them; it locates the disagreement
in the general theory of de re modality for existence.

## 10. Weakening (direction 8)

C2 needs only existential receptivity (received esse or matter), not POTENCY_1
in any respect. C2 and B4 are independent (`potencyOnly`; `angelic`,
structurally); C2 and B2 ∨ B4 are independent (`potencyOnly`,
`inertPowerHolder`); C2 is implied by R1 with *De ente* (law 3) and by B2 with
B3 (law 4), strictly in the B2 case (`uncausedComposite`); C2 strictly
strengthens C2⁻ with certified difference `703d8c9c`.

## 11. Direction 9

The PGP route to the first mover's necessity is provably not equivalent to
`PureActBeingsNecessaryAt` (`potencyOnly`, `angelic`), unlike B4. Necessity is
derived from unreceived esse plus underivedness; POTENCY_1 pure act is carried
and does no work.

## 12. C1 comparison (direction 10)

The claim that C1-style dependence does not exclude a contingent first
actuality holds without a model: CCR only asserts a rooted bearer, not its
modal status. The `bruteSimple` CCR check adds nothing beyond that: the
adapter's one-world `Unit` frame reads existence as act of esse and the frame
has no esse-causes, so every bearer is trivially a root and CCR is modally
silent by construction.

"Underived" is used in two senses. CCR's root has no *actual* distinct
esse-cause; the route's underivedness is firstness (nothing else is
SIMPLY_PRIOR_1). C2's prior-cause disjunct does not require an actual cause,
and nothing identifies CCR's root with an unreceived being. **Connection plan**
(not delivered): (1) a bridge from "no actual distinct esse-cause" to
firstness or to the absence of any SIMPLY_PRIOR_1 esse-cause; (2) a bridge
from CCR's root to unreceivedness. #1882's vocabulary is not imported. Its "C1
does not give C2" uses C2 for the source's necessity, not this note's C2.
Composition-needs-a-cause (q.3 a.7) is a further open bridge.

## 13. Cumulative support and provisional judgment (direction 11)

**Shared dependencies.** The routes converge on one witness through shared
premises: the *prima via* base `7bce7007`, B0, firstness `74eb9113`, simplicity
`78246da5` (whose derivation uses firstness); R3, *De ente* and irreflexivity
are shared with #1870's B6 reception argument; B3 with route A; PGP and
correlation are shared by `32bf794f` and `bf2f0e8e`.

**Provisional judgment (2026-11-23, after semantic challenge).** C2 is not
contested by the rivals recorded here on any corruptible or dependent being,
given passive→receptive and B3 (both stay OPEN for those beings); that covers
the ordinary cases. Its contested scope is exactly the
foundational, underived, simple being, which is exactly where the route to the
first mover applies it. The ordinary cases therefore do not discriminate: the
rival also accepts PGP for every ordinary case, and the same verdict applies
to the subtraction generalization on the other side. C2's universal form adds
no warrant at the foundational case beyond the general theory of de re
possibility for existence. The C2 route's force at the first mover equals that
of power-grounded modality for existence: a serious, independently defended
theory, not shown superior in this slice to its rivals (combinatorial,
primitivist, existence-conditional essentialist, hybrid). The explicit case
analysis (results `32bf794f`, `bf2f0e8e`, law 5) is clarification, not
warrant. C2 is compatible with the uncaused-composite rival; the
self-annihilator must deny correlation or `b62a64ab` (C2 fails in both
`selfAnnihilator` variants); C2's relative logical weakness (laws 3–4) is not
warrant. No substantive objection shows C2 false. The standing rival's price
is de re possibility of absence for an individual with no internal or
external modal ground.

**Cumulative note.** #1870's B2 route (the q.3 a.4 causal principle), its B6
route (esse-identity essentialism) and this PGP route each rest on a different
modal-theoretic basis, and the brute rival must deny all three. But one Humean
or primitivist package denies all three at once, so these are correlated
denials, not three independent costs: convergence with a precisely identified
shared crux, not independent corroboration.

**Revision conditions (symmetric).** A matching-scope comparison of the
general modal theories for existence favouring one side; a counterexample to
correlation (an inert power over being, the `inertPowerHolder` type); an
independent datum for or against the possible absence of a foundational
simple being.

**Formal status.** B2 ∨ B4 `3c9d683b` is now derived (frontier status
proved/closed in frontier-diff's vocabulary, not established: dossier
"established: false"); its leaf is replaced by four new bare premises; no
premise is established.

## 14. Gaps and next tests

1. Compare power-grounded, combinatorial, primitivist and essentialist
   modality for existence at matching scope (the revision conditions).
   **Under way in #1887.** The reviewed matching-scope assessment (tests
   1–3) is in [foundational-absence-warrant.md](foundational-absence-warrant.md)
   (attempt `d067722e`). It finds parity at the foundational being:
   - neither "`n` could be absent" nor PGP's necessity verdict has
     discriminating warrant there;
   - PGP's substantive content (completeness over incorruptibles) has the
     same status as unrestricted recombination and as the concrete/abstract
     cut of concreta-restricted existence-conditional essentialism, which is
     now the strongest rival;
   - conceivability is unresolved, and its reply rests on a calibration
     premise shared with other routes.

   §13's conditional judgment stands, sharpened: the remaining disagreement
   is the unmotivated extra content of each general theory at existence
   without a subject. The formal framework comparison and Pruss's argument
   (tests 4–5) are in
   [modal-grounding-frameworks.md](modal-grounding-frameworks.md)
   (attempt `5ee2cbef`).
   - Each account's verdict at the foundational case is proved under exact
     extra commitments. PGP, B6 and unconditional essentialism give
     necessity. Existence-conditional essentialism and combinatorialism give
     possible absence; under the former, esse = essence carries no modal
     force. Primitivism fixes no verdict. The hybrid inherits the verdict of
     its existence component.
   - The route with Pruss's own premise reaches `b19ffd92` without PGP, C2
     or a Euclidean frame. Its possibility premise is the joint absence of
     the actual contingent concreta, with others perhaps in their stead; no
     recorded rival is shown to reject it.
   - It is formally independent of the C2 crux but dialectically tied to it:
     its grounding premise is the same power theory applied globally, and
     under the open transfer bridge it yields PGP's verdict on concreta.
2. Separate conserving from originating power in correlation by composing with
   the existing sustaining-causation vocabulary (attempt `c94eed5b`) instead
   of the tenseless `CausesIn` (the deist question).
3. Defend or refute passive→receptive for a corruptible being without matter
   (`bareCorruptible`).
4. Assess corruptible→POTENCY_1 (`8bfc4ab7`).
5. The two C1 connection bridges of §12 and the q.3 a.7 bridge for underived
   beings.

## Can the whole unreceived act be absent?

Analyst assessment of the rigid individual in issue #1887. Let P say that this
very n is absent at some world accessible from the actual world. Grant the
actuality, firstness, essence–esse identity, absence of reception, of a
matter–form composite, of corruptibility and of power over n's esse in
`FoundationalAt`. The further stipulation that **nothing grounds P** is stronger
than absence of a causal power. It excludes an essence or a recombination law
as a positive ground for P if those accounts purport to supply one. Under
that strict stipulation the live affirmative answer is a primitive modal fact.

**The direct case for necessity.** A dependent being's act can be distinguished
from what receives it. If an indispensable contribution could have been wholly
withheld, with no substitute for it, that gives a positive reason why this
very being might never have existed. For n there is
neither a recipient separable from its act nor a giver whose contribution
can be withheld. The identity of what n is with its act of being excludes retaining
the bearer while separating it from that act. Underivedness excludes
explaining its actual existence by an upstream giver. The best generalization
is that a real alternative to actuality should answer to a real difference in
what admits or accounts for it. We have independent reason to *look* for such a
difference. Varying something in a description is easy even when the variation
separates constitutively identical things. In ordinary cases, tracing which
contributions can vary helps correct that error. Applied as an explanatory
preference this is a case for necessity. Applied as an exceptionless rule
licensing an inference from the absence of a ground to the falsity of P, it
requires further warrant precisely at variations of a whole unreceived act.

**The strongest objection.** Consider the difference between keeping n while
subtracting its very act and omitting n and its very act together. Identity
decisively rules out the first operation. The second respects identity,
even if we grant that an act of being is intrinsically exercised whenever
there is such an act. There is no dormant act, bare essence awaiting
actualization, or second constituent that switches n on. A conditional in
our account of n introduces no such constituent into n. This answers the
internal-composition objection even on an interpretation excluding all real
intrinsic parts. Whether an order omitting the whole is admissible remains
open. The PrimitivistSilence twins and ConditionalIdentityModel check the
separation for their specified profiles; they do not certify an absent
world for a fully simple subsistent act. An alternative world is no later
stage in a single history. The objection defeats the inference from the
absence of passive potency alone. It leaves open timeless dependence on a
giver wherever there is one, or a noncausal restriction on admissibility.

**An independent argument by exhaustion.** Suppose n were absent. Either the
order in question contains no bearer existing by an unreceived act or a
different bearer exists by such an act. Two reasons for excluding these alternatives can be stated
without first assigning n a modal status.

1. Consider an order populated entirely by recipients of actuality. If the
   existence of each is derivative *in the very respect under explanation*,
   adding recipients supplies further instances of receipt. It gives no
   account of why there is anything to receive. This favors an unreceived
   source insofar as received actuality calls for an ultimate source. Its
   rivals include a beginningless order of dependence sufficient member by
   member and an order with no concrete recipients at all. Even a successful
   objection to an unfounded dependence order leaves the empty case. The
   abstractum/coexistence route in the modal spine gives a reason to resist
   emptiness if a necessary abstractum requires concrete instantiation or
   accompaniment. Both the dependence of abstracta on concreta and its
   compatibility with the alleged necessary abstractum matter. Necessary
   population alone yields no unreceived act.
2. Ask what would make a second unreceived act *this other act*. A common
   actuality received in different subjects has a familiar basis of
   multiplication. Removing receivers removes that basis. If unrestricted
   acts share one real nature, and numerical distinction requires a
   differentiating basis that unreceived acts lack, the purported substitute
   has no claim to be another individual. Simplicity within each individual
   alone leaves distinct simple natures and primitive numerical diversity
   open. The existing nature-uniqueness argument (`841e7c81`) needs common
   nature and individuation premises in its own class. Uniqueness among
   coexisting beings would still leave a different sole occupant elsewhere.
   Applying the reason to every possible substitute also requires showing
   that *every* unreceived act is unrestricted in the relevant sense. Lack
   of a receiver by itself leaves intrinsic limitation open.

This gives a positive, non-causal case for the *same* n. The first reason
addresses whether the role is occupied throughout, the second whether it
can change occupants. Neither premise says that n is necessary. Each has
consequences one can dispute independently, including for an impersonal
foundation. Each remains defeasible. See [the necessary-population
comparison](modal-spine.md), [disjunction grounding](disjunction-ground-485.md)
and [the individuation comparison](necessary-simple-plurality.md). Result
`514112f2` separates necessary population from a necessary individual.
No combination of separate control models exhibits a complete rival ontology.

**The best affirmative case.** The primitivist can accept objective modal
facts as basic alongside actual categorical facts. P then need involve no
causal power, dependence or internal difference. This answers the coherence
challenge, but primitivism permits primitive necessity equally. Recombination
offers a reason for a direction: keeping the character of numerically distinct
things fixed ordinarily leaves room to vary their company. To reach P it
uses unrestricted recombination and a distinct possibly existing concrete
companion on the existing route. The unrestricted rule licenses removal at n. A thing can be present wherever its companion exists without being
produced by the companion. Independence in production alone gives no right of
omission. Existence-conditional essentialism offers the most economical
interpretation of the act itself: wherever n exists, it is precisely this
exercised act. For P it also needs a represented absence, no essential
requirement from others, and a rule admitting what survives the essential
exclusions. A conceiving of total omission favors P if it tracks real
possibility even with incomplete access to the individual's nature. This is a
defeasible consideration, stronger than mere freedom to put a zero into a
model. If recombination or the exclusion rule actually grounds P, it answers
the weaker question of absence without a *power*. On the strict stipulation
it can serve as evidence for a primitive P only insofar as the rule is
independently credible as a guide to primitive facts.

**Verdict.** The joint omission answers a specific charge of incoherence
against P. Neither the truth of P nor its negation follows from that success.
I have high confidence that the change objection and act identity alone cannot
decide C2, and moderate confidence that suspension between P and its negation
is warranted at this individual. This is an assessment of the reasons, with
no numerical probability assigned to either world picture. The fundamental
disagreement is whether real alternatives for an individual must be licensed
by a positive feature of actuality, or whether primitive admissibility can
allow a whole actuality to be missing while respecting every constitutive
identity. On either side a general rule earns comparative weight by explaining
other modal distinctions and giving a reason its application survives at n.
A brute necessity and a brute permission have the same entitlement to be
proposed. A classical theist can accept the grounding demand, and an
impersonal necessitarian can do so too. A contingent-foundation rival can
retain powers for change at the cost of treating existential admissibility
as independently basic or governed by its own unrestricted rule. Coherence
of any of these worldviews supplies no automatic verdict about n.

I would move toward necessity if the population and individuation reasons
both held across accessible orders, or if an independent account of real
definition showed why the exercise of *this* whole act must obtain even
without conditioning on its existence. Under the strict no-ground stipulation I would move toward P if a reliable
way of recognizing that particular primitive de re possibility survived
the incomplete-knowledge objection. An independently motivated restriction
on real essence and account of admissibility that *grounds* whole omission
at n would instead support P while revising the no-ground stipulation.
The current barriers are existential import for necessity and a licence for
admissibility for possibility. Neither is removed by counting their
conditional formulations as further evidence.

Evidence reused: #1884 `32bf794f` and `e5d49f99` (C2 and its application
under their premises), #1888 (warrant), #1889 `1e6174ab`, `39df9612`,
`872a3832` (the opposed conditional verdicts), #1896 `ca973127` and controls
(under the exercise/existence link, the exercise-in-nature premise restates
the identity-to-essential-existence bridge), and #1897 (a collective absence
power need not distribute; a necessary holder still needs identification
with n). Draft #1901 at `7623b6d3` distinguishes reality-constrained
modality, positive makers, and power exhaustiveness. The present tests add
no theorem, framework, attribution or premise discharge.

### Testing occupation and replacement

Continuation of [the joint-omission assessment](#can-the-whole-unreceived-act-be-absent),
on the same accessible worlds and rigid individual. The two research questions
are whether every admissible order has an internally unreceived act of being
and what could show that the bearers in different orders are one individual.

**An order empty of concreta.** The weak Lowe result `7c5984f9` excludes this
case given a necessary non-concretum and concrete accompaniment of abstracta
throughout the accessible worlds. Its accompanying pair example lets the
concrete witnesses alternate. Lowe gives a substantive reason for
accompaniment. On his immanent account each positive finite cardinal needs an
instance. He takes its instances to be sets, rejects pure sets and argues
against a reciprocal dependence between sets and universals. One concrete seed
suffices to generate instances of arbitrarily large finite cardinality by
taking singletons repeatedly and collecting finitely many of the resulting
objects. His concrete particulars here are spatiotemporal. Transferring the
conclusion to a particular timeless foundation requires further argument.
[Lowe, “Why Is There Anything at All?”, §III, pp. 116–118](https://pdf.stafforini.com/lowe-1996-why-there-anything.pdf)

Hold the demand for instances and the set construction fixed. Start instead
with the empty set. The empty set, its singleton, and the pair comprising
them have sizes zero, one, and two. Iteration supplies an instance of every
finite cardinal without a concrete member anywhere in its membership ancestry.
There is a reason to take the seed seriously: if set difference always has a
set as its value, every difference of a set with itself picks out the same
memberless set by extensionality. Extensionality alone secures uniqueness
within the sort of sets. Existence requires the operation or another premise.
Lowe can retain the calculations by paraphrasing an empty difference as a
claim about the absence of any surviving member. The substantive burden then
concerns which mathematical constructions carry ontological commitment.
Memberlessness leaves dependence on a mind or another nonmember open.
Consequently the test weakens the inference from instantiation to concrete
accompaniment. It supplies no accessible world in which concreteness is absent.

**Can an abstract witness pick out n?** Compare a necessary cardinal with
the singleton of n. The cardinal has an independent claim to necessity, but
different instances can supply its cardinality. Given fixed membership for that singleton and Lowe's separate premise that
a set exists only where its members do, wherever that very singleton exists,
n must exist. Its formation from
n, however, warrants its existence conditional on n. Assigning the singleton
necessity merely to guarantee n would put the disputed claim into the
premise. This direct route by a single abstract witness therefore needs the *same* abstractum
both independently necessary and rigidly dependent on n. Observing those
features separately in different examples does not license their conjunction.
A contingent bearer cannot supply its presence in a world where it is absent.
A uniform explanatory rule with varying bearers is a further rival to a
uniform bearer; a rule whose whole content is universal occupancy would add
no explanation. The existing `a35b5d79` controls distinguish local grounds,
one reason throughout, and a reason consisting in a fixed individual's
existence. [Disjunction grounding](disjunction-ground-485.md)

**A populated order of recipients.** Specifying the sense of receipt changes
what this argument delivers. A root of the actual esse-cause relation is
externally underived in that relation. In `uncausedComposite`, an externally
uncaused individual receives its act in its own essence. Thus external
underivedness by itself cannot deliver the internally unreceived act sought
here. Conversely the isolated identity root beside a rootless regress
(`b49b53e7`) shows that there can be a root somewhere even though many
beings have no root among their ancestors. Occupation requires less than a
common explanation of everything. These are structural tests of the stated
inferences. [C2 control](../../TruthCore/Causality/ContingencyGrounding.lean)
and [closed-source controls](de-ente-esse-source-1628.md#exact-controls-and-rejected-shortcuts)

A positive argument survives both tests. Grant an actual bearer and root
access for it. Grant that a bearer whose essence differs from its esse has
another actual cause of its esse. With excluded middle the selected uncaused
root has its essence identical with its esse. If its only possible internal
receiver would be its own essence (R3), receipt entails receptive potency,
and nothing is in receptive potency to itself, the root's act is internally
unreceived. This combines the *pointwise reasoning* in the source-of-access
and first-mover proofs using the same interpretation of bearer, act and
cause. The application to arbitrary accessible orders remains an analyst
argument. Its local strength is that it uses neither uniqueness nor a ban
on every infinite chain. The rationale for root access is strongest for a
complete order of presently operative givers, each of whose power to give
is itself entirely derivative. The member-by-member rival grants actual
givers throughout and takes their local explanations to suffice. Merely
pointing to nonempty supply, or to an infinite chain, decides neither the
scope of the supply relation nor this dispute over sufficiency.
[Source of access](../../TruthCore/Results/Aquinas/DeEnte/ClosedEsseSource/Solution.lean)
and [reception at identity](../../TruthCore/Results/Causality/ContingencyGrounding/Solution.lean)

**Replacement by a different unreceived being.** A possible way to exploit
uniqueness within each accessible world would be to show that any two
concrete putative occupants, each admissible separately, could occupy the
role together as those very individuals in some world accessible from the
same starting point. Uniqueness throughout that scope would then exclude a
second candidate even across worlds. The subtraction rule of #1887 licenses one
individual's presence with another's *absence*. It supplies no such positive
coexistence premise. And origin independence gives a poor reason for it at
this specific role. Grant, for the sake of testing the inference, that each
candidate, wherever it occupies the role, supplies the esse of every other
concrete being there and itself has no supplier. Co-occupation would then
make each both supplied and unsupplied. This explains why the *role* excludes
a second simultaneous occupant while leaving untouched the hypothesis of
different occupants in disjoint orders. Universal supply is an additional
hypothesis here. This argument establishes no possible replacement. A proof
from a genuinely common individual essence could bypass coexistence, but
it must cover bearers in different orders and justify their numerical identity.
[Existing nature-uniqueness comparison](necessary-simple-plurality.md)

**Assessment and limits.** The positive case for an unreceived act has a conditional route
within populated orders of wholly derivative productive supply. The arithmetic
case for extending it to *every* order loses force once abstract instances
receive the same treatment as concrete ones. Neither change gives comparative
warrant for P or its negation at this individual. I retain moderate confidence
in suspension. The sharper revision conditions are a justified dependence on
concreta that survives the abstract-seed test, local root access and internal
nonreception warranted at the required worlds, and individuation covering
mutually exclusive occupants. Rigid dependence of an independently necessary
abstractum on this very n would be a separate sufficient route. A contingent
foundation remains entitled to the joint-omission defense but needs positive
warrant for that particular admissibility. The simple mathematical construction
tests an explanation; it supplies no modal evidence directly for P. Attempt
`91e562cc` records these tests. No formal premise changes.

**Can a separability argument independently warrant P?** Apply Van Cleve's
ordered-pair test in both directions. Let c be a companion disjoint from n.
The ability of n to exist without c is compatible with n's necessity. The
ability of c to exist without n would settle P immediately, without an empty
world. This is exactly where the warrant of the unrestricted rule matters.
Exempting necessary targets leaves open whether n qualifies for exemption.
The stronger rule would let c exist with only its own parts. Applying it to
c with n outside its parts in that alternative would remove n. Applying it
to n would leave n present. Separating c from each outsider in turn does not
give the joint isolation of c. Van Cleve offers isolation as a stronger axiom.
In its all-category reading, which permits isolating the universal itself,
it also bears against the immanent-universal rationale for population:
the dependence of a universal on *some* disjoint instance can survive the loss of
any particular instance. A concrete-only rule cannot isolate an abstract
universal. To challenge such dependence by invoking universal
isolation uses the controversial extension, not new evidence for it.
[Van Cleve, longer text, §§2, 4, pp. 22–25 in §4](https://dornsife.usc.edu/james-van-cleve/wp-content/uploads/sites/272/2025/09/No-Necessary-Connections-Btw-Distinct-Existences-for-website-7.17.25.pdf#page=22)

There is another distinction at the contingency-of-origin argument.
A restriction against a particular oak having a *different* origin can
leave open an originless history without establishing that history as
possible. Even evidence that c could lack a giver of its esse would remove
the giver from the explanatory role; n could still exist there without
giving c its esse. To infer P from that evidence one needs an independent
licence to omit n, or a warranted necessity that n supply c whenever they
coexist. The co-occupation test above assumed universal supply only to
test its consequences. It supplies no such warrant by itself. These results
close the specific source-reading question left open in §9, item 6, of the
[foundational-absence assessment](foundational-absence-warrant.md). A positive
test for P by this companion route would have to warrant the *same companion's* presence without n,
including the conditions on its parts and the scope of the separability rule.
The case for primitive existential modality survives without such a test, but
its verdict on this individual remains open.
[Van Cleve, §9, pp. 62–65](https://dornsife.usc.edu/james-van-cleve/wp-content/uploads/sites/272/2025/09/No-Necessary-Connections-Btw-Distinct-Existences-for-website-7.17.25.pdf#page=62)

### Could a genuinely ungrounded absence be recognized?

Fix the actual world w and the same concrete n as above. P is true at w
just if an accessible world lacks n. Take the strict stipulation to exclude
even a jointly sufficient noncausal metaphysical ground **for P at w**.
This is a hypothesis about reality. Our inability to identify a ground would
be much weaker. Actuality and simplicity alone do not establish the stipulation.

**A case for necessity from the way existential truths are grounded.**
Suppose P. Take an accessible alternative v in which n is absent. Consider
the view that particular alternatives ground individual possibilities as
their instances: whenever such an omission obtains, the facts that v is
admissible from w and lacks n, together with the constitutive modal rule if
required, fully explain why P holds at w. Mere explanatory relevance or
definitional equivalence in Lean would leave this premise open. On the
proposed view P has a ground, contrary to the strict stipulation.
On that account n must exist throughout the alternatives. This reasoning
needs no change, power over esse, or cause of a negative fact. It works even
if the admissibility of v has no deeper explanation. Primitive *worlds* and
a primitive *individual permission* occupy different places in the argument.

There is independent motivation for the explanatory premise. A particular
philosopher's being a philosopher can explain why there is at least one
philosopher. Which other features of the person one records is immaterial.
And a theory that independently explains which combinations of individuals
can occur together can explain their separate possibilities. The converse
inference from separate possibilities to joint possibility fails in the
existing Van Cleve control. These considerations support applying the
existential reasoning **if** the complete alternatives have the requisite
priority. Fine gives the ordinary existential example in *Guide to Ground*
§11. The application to a de re possibility is our own.
[Fine, §11](https://doi.org/10.1017/CBO9781139149136.002)
and [joint-absence controls](modal-grounding-frameworks.md).

**The strongest objection concerns explanatory direction.** Suppose a
primitive permission for n to be absent helps determine which complete
descriptions are admissible, together with independent constraints on what
else could exist. A description admitted partly on the strength of P
cannot then supply a prior ground for P. Adding a detail about the colour
of some companion, for instance, can give a more informative description
of the proposed alternative without better explaining n's removability.
The contrast with an independently admissible concrete-empty order is sharp.
If the latter's admissibility is metaphysically prior, it can ground P given
n's concreteness. If its admissibility derives in part from prior permissions
to omit its putative occupants, that explanation runs in reverse. Both
positions owe a realizable alternative if they assert P. Neither gets the
direction of ground from the existential truth condition alone. An analogy
is the relation between a fact and its inclusion in an accurate account
of reality. Inclusion records the fact if the account was compiled from what
is true. Kalhat applies this distinction to world-stories and modal
predication. [Kalhat, “Primitive Modality and Possible Worlds”, p. 510](https://doi.org/10.1017/S0031819108000855).

**Evaluate the proposed absence from inside the alternative.** In an
n-free v that accesses itself, n's absence there suffices for the truth at v
that n could be absent. Grant a stronger premise for the sake of argument:
an actual instance of absence at v, with the background modal rule, gives a
metaphysical ground there for its possibility. Then a primitivist cannot
both assert P and insist that this permission lacks a ground *at every such
point*. That does not follow from its lacking a ground at w. Even agreement
between worlds about which alternatives are possible would establish at most
agreement in modal verdict. Transferring the local ground requires a further
account of why explanation is invariant or why nonactual instances ground
actual modal facts. And using an occurrence to establish a possibility may
give evidence without giving its constitutive explanation. Thus this test
identifies where a claim of **absolute, world-invariant primitiveness** is
vulnerable, while leaving the actual-world stipulation intact.

There is a second, distinct question at v. If v accesses w in return, w
already supplies a witness for the possible existence of this very n as
evaluated at v. Symmetry is sufficient for the return edge and is no built-in
assumption at the C2 endpoint. Requiring v itself to contain a producer, name
or individuation principle for n would be an additional thesis about singular
modal facts. Asking what would select n *instead of* a different candidate
also assumes only one could be admitted. A rival can allow both. It still
owes warrant that either could exist, but no asymmetry of permission needs
explaining in that case. An individual essence conceived as a uniquely
exemplifiable property provides one way of specifying an absent individual
without producing it. Its own availability when unexemplified is disputed.
This sense of individual essence is separate from n's act of being. Even a
successful account of reference would not establish possible exemplification.
[Plantinga, “On Existentialism”, §§I–II](https://andrewmbailey.com/ap/On_Existentialism.pdf)
and [the reverse-direction power result](pruss-power-premises.md).

**A positive argument for possible absence from an effect.** Pick an actual
effect e distinct from n. Suppose n's existence on its own is sufficient
for the existence of this very e wherever n exists in the accessible
orders. Independently warrant an alternative in which e never exists.
That very alternative lacks n. The argument needs neither an exhaustive
inventory nor an inference from imaginable separation. If e could be
absent *because* n could be absent, the independently warranted
contingent existence of e could be evidence for a primitive P. Epistemic inference
can run upstream even when metaphysical explanation runs downstream.
An independently prior world grounding P through e would instead put us
back in the first argument. The existing source–effect incompatibility
already captures the consequence.
[Existing Lean argument](../../TruthCore/Causality/BruteFoundationRoutes.lean)
and [selected-effect controls](selected-effect-bridge-462.md).

The test turns on **what the evidence for e's contingency holds fixed**.
If it warrants a case with n present and e absent, it directly defeats the
sufficiency premise. If it holds fixed only some secondary conditions and
leaves n open, it can support e's omission without deciding the issue in
advance. The strongest rationale for sufficiency would be an exercise that
belongs inseparably to n and has this particular output independently of
external conditions. In ordinary production the missing effect is often
intelligible precisely because other conditions can vary. In a proposed
necessary emanation, the sufficiency premise is more credible to its
proponent, while the possibility of the same emanated individual's absence
needs independent warrant. Giving the condition-variation story from the
first case and the invariant output from the second does not make an argument
about a single effect. The existing control even retains one source, one
performed act, local output uniqueness and one response function as
conditions and outputs vary. This objection leaves essential production of
a particular effect open. Expanding the consequent to “some derivative being
exists” trades the token-identity burden for the stronger datum of an order
entirely free of derivative beings. The inquiry identified no effect with
both the required invariant link and independent omission evidence.

**Provisional judgment.** Under the strict stipulation, I favor necessity
with high confidence *conditional on independently prior, instance-grounding
worlds*. This conditional result has broader reach than the power argument
and correspondingly little specificity to a simple foundation. Under the
weaker premise that n lacks a power of nonbeing, that same account can
license a grounded P. For a primitivist defense, it is the absence of a full ground for P itself
at w that needs defending. Accepting irreducible modality somewhere in
one's worldview is insufficient. The strongest new way to favor P would
be independent evidence of an omissible effect with the stated invariant
link to n. For necessity, it would be a reason why at least one admissible
omission must be explanatorily prior to P whenever P obtains, or why the
grounds found at an absence world must carry over. The evidence here
supports none of those bridges sufficiently to select P or its negation.
I retain moderate confidence in suspension for the shared case. These are
analyst arguments and a warrant assessment; no new formal results.
