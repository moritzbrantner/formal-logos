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

**Current conclusion.** There is a positive case against obtaining a
populated world without n by subtraction. Grant a root in every populated
order and n as the sole actual root of the same relation of giving
existence. A populated alternative without n then requires either an actual
dependent that can be underived there or an underived individual outside
the actual concrete inventory. A contradiction eliminates the particular
proposal that entails it. Repeated failure to find an absence can favor
necessity if the inquiry stood a real chance of detecting one under some
still credible account of P. I retain moderate confidence in suspension
about P on the shared premises.
[Individual origins](#can-ordinary-individuals-identify-the-same-foundation-across-histories),
[groups and whole worlds](#what-can-a-group-or-a-whole-world-show-that-one-creature-cannot)
and [the cumulative assessment](#when-do-adverse-consequences-count-against-possible-absence).

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

### Can ordinary individuals identify the same foundation across histories?

Consider two claims about the actual foundation n. First, wherever n exists,
it is an ultimate source of every originated concrete individual in a specified
class there. Second, if such an individual has n as an ultimate source in one
history, that very individual requires n to have existed somewhere in every
history containing it. Fix the class independently of descent from n, for
example organisms, and keep n itself outside it. In each comparison use the
actual history and alternatives individually accessible from it. Presence
anywhere in a complete history suffices. Neither a causal transition between
worlds nor transitivity of modal accessibility enters the argument.

Suppose Ada originates in the actual history. A second contains Ada and is
where Ben originates. A third contains Ben and none of the actual organisms.
Ada requires n in the second. There n is a source of Ben by the first claim.
Ben therefore requires n in the third by the second claim. Repeating this
reasoning across any finite
sequence carries the very same n to the far end if, at each step, a member
of the chosen class originates in the history we are leaving and also exists
in the one we reach. Each creature can be contingent. Even the joint
omission of *all actual creatures* in the final history need not get outside
the argument. An accessible history lacking n would have to escape every
such sequence. Global necessity follows if the sequences cover all
alternatives. Coverage is a substantive third premise.

**What earns the two source premises?** For particular organisms there is a
reason to take their origin seriously. A second conception involving wholly
different gametes can occur alongside the first and yield a second child.
Resemblance to the first child would be poor grounds for identifying the two.
This supports investigating essential origins even for someone open to P.
If each link in an actual finite ancestry requires that very predecessor
whenever the descendant exists, the requirements compose. Calling a remote
cause a cause supplies none of the individual links. A parent might have
survived a different rescue, and an organism's biological origin does not
settle which ultimate source could have sustained its parents. Plotinus offers
a stronger rationale in a constitutive hierarchy. A derivative continually
needs the prior that sustains it, through any intermediates up to the
source. Applied to C2 this gives reason to look for dependencies that persist
as long as the creature does. Identifying the same ultimate source in a
different history still requires the transworld premise. Likewise a
uniform explanation of why dependent beings have existence might support
universal sourcehood, but an actual explanation of each one's existence by
*some* unreceived source supplies neither this universal source nor its
invariance wherever it exists. The established argument for an identity
source of each actual distinct esse concerns this last, local explanatory
question. [Actual source result](../../corpus/arguments/f05db25e-dd2a-4417-9059-ec0c4a6dc5f0.json)
and [origin and historical identity controls](fixed-initial-history-535.md).
[Plotinus, V.5.9](https://en.wikisource.org/wiki/Plotinus_(MacKenna)/Volume_4/Ennead_5.5)

**How far can one trace a particular origin?** Consider a trilobite fossil.
Its value as evidence of a particular organism's life depends on its history.
An exact manufactured replica would lack that history. Hermida uses this
case to motivate essential biological ancestry for remains and, conditionally
on organisms inheriting their particular lineages essentially, for their
more distant ancestors. This gives the origin argument a stronger example
than general causal dependence. It also identifies an actual limit on the
reason. An ancestor transmits life along the lineage. A source that gives
existence to the lineage need never have been one of its living ancestors.
Counting it as the first member would change the relation midway.
[Hermida, “Biological Antecedents Essentialism,” §§5–7](https://link.springer.com/article/10.1007/s10670-024-00846-z)

Can direct creation close that gap? Consider Aquinas's rational soul,
granting his account for this test. Its subsistence and immateriality give
him reasons why producing it requires creation. Only a first agent can
produce without presupposing something on which to act. This moves directly
from the individual effect to the role of its creator. Compare *n's creating
this soul* with *this soul*. Specifying the former fixes n. Aquinas himself
distinguishes active creation from the relation of origin in the creature,
and holds that the creature, as subject, is prior in being to that relation.
He also distinguishes many souls of one kind by the bodies whose acts they
first are. Thus even when there is only one creator, the account has a
reason for which soul is which that refers to embodiment. This gives no
sufficient condition for identifying a soul across different histories. A
second physician can take over the treatment of an already existing
patient. Creation, on the account being tested, has no already existing
soul whose maker could be varied in that way. A factor common to all souls
could also be indispensable to each. The comparison does show why
individuating the creative act by its agent
cannot simply be transferred to the soul. To infer n's presence everywhere
the soul exists, one still needs a reason that the soul depends on this
particular creator or that the creator role cannot change bearers.
Even a case of some other agent producing the soul would establish n's absence
only with a further exclusion of n's presence there.
[ST I.90.2–3](https://www.newadvent.org/summa/1090.htm#article2),
[I.45.3, especially replies 1 and 3](https://www.newadvent.org/summa/1045.htm#article3)
and [*De ente et essentia*, ch. 5](https://sourcebooks.fordham.edu/basis/aquinas-esse.asp).

There is also a route from divine power that dispenses with joint histories
of creatures. Take any accessible history containing a creature c in the
chosen class. If actual n has the power to produce **that very c as its
ultimate source**, and this power admits exercise in some history accessible
from actuality, there is a history in which n is c's ultimate source.
The premise about essential origins
then requires n in the original history containing c. Repeat for every c in
the class and this reaches even populations that cannot mix. Histories with
no member of the class, including creatureless histories, remain open.
Aquinas gives a rationale for the breadth of
power from an act of being unrestricted by a recipient or a particular kind
of being. The open application is from *c can exist* to *n can produce c as
its ultimate source*.
A power to produce every possible kind of creature can leave that step open:
producing another of exactly the same kind may be within n's power even if
this individual's origin is indispensable. Defining the feasible tasks as
whatever n can do would give no independent warrant for including this
task. Conversely, rejecting it solely because it would rule out a proposed
rival would beg the question against the power argument. The result turns on
whether origin permits this particular exercise of n's power. Importing a
divine power already derived from necessary existence would be circular here.
[ST I.25.2–3](https://www.newadvent.org/summa/1025.htm#article3) and
[the corpus scope of the power premise](../modal-ontology-120.md).

**The strongest test of coverage uses recombination in the opposite direction
to subtraction.** Take one ordinary creature from an actual history and one
from a proposed replacement history. Could those two creatures themselves
have coexisted, with the first originating in actuality and the second
originating in their joint history? If so, that history connects the endpoints
without first stipulating that the two foundations coexist. Local coexistence has
some warrant when the creatures need no incompatible material, place or
conditions of conception. It is substantially harder to warrant here. A
duplicate of each creature can stand beside the other without either original
being present. Lewis explicitly frames recombination in terms of duplicates.
And if the two creatures require distinct and necessarily exclusive ultimate
sources, their origins supply a concrete obstacle to joint existence even
where the bodies would fit. Assuming outright that originals with different
possible origins can always mix would decide this test in advance.
[Lewis, *On the Plurality of Worlds*, §1.8, pp. 88–89](https://15926.blog/topics/possible-worlds/Lewis-David-%281986%29-On-the-Plurality-of-Worlds.pdf)

Consider a solitary rival source r with no creatures. Even this case admits
a further test. Suppose the same r could produce a creature in a history
accessible from actuality, and that history can be connected to the actual
one in the way just described. Then n is present in the productive history.
If n and r each must occupy its sole ultimate-source role there, they are
identical. Rigid identity would carry n back to the solitary history. A
primitivist can allow an active rival while denying that *its* creatures
could mix with ours as the same individuals. They can also contest the
exclusive role. A simple foundation's lack of parts settles neither issue.
A concrete-empty alternative would escape even the productive-extension
argument. Conversely, a world containing n alone could also escape every
creature-sharing sequence. Failure to connect a history is evidence of a
limit on our test, never sufficient evidence of absence. The existing
empty-extension and restricted-history results illustrate how changing the
domain changes the necessity verdict.
[Existing controls](../../TruthCore/Case/Catholicism/StageOne/NecessaryIndividual/EmptyWorldFork.lean)

#### Testing things the foundation might guarantee

The direction of dependence matters. A creature that **requires** n can
bear witness to its presence. A condition that **n guarantees** could bear
witness to n's absence if it independently failed in an admissible order.
Three plausible examples let us test the evidence at matching scope.

- **An intellect.** Plotinus argues from the outward activity of perfected
  things to the First's production of Intellect. His distinction between
  the First's own activity and its expression supplies a reason for
  expecting *some* derivative intellection, without requiring this particular
  human thinker. Aquinas also takes perfect goodness to be communicative but
  holds that complete goodness requires no created recipient. The difference
  concerns whether a distinct effect must occur. The concrete omission with
  good ordinary warrant is that Socrates' parents might never have conceived
  him. Plotinus distinguishes the embodied person from the corresponding
  intelligible principle. The absence of the birth, or even of all embodied
  thinkers, leaves incorporeal intellection open. Supposing the First itself
  present without secondaries either illustrates its self-sufficiency or, if
  taken as a genuine possibility, undermines necessary production. The
  identification of this n with the Plotinian First also needs argument.
  [Plotinus, V.4.1–2](plotinian-composition-unity.md),
  [V.5.12](https://en.wikisource.org/wiki/Plotinus_(MacKenna)/Volume_4/Ennead_5.5),
  [V.7.1–2](https://en.wikisource.org/wiki/Plotinus_(MacKenna)/Volume_4/Ennead_5.7)
  and [Aquinas, ST I.19.2–3](https://www.newadvent.org/summa/1019.htm#article3).
- **Protection from a particular harm.** Compare two feasible interventions
  on a patient. One would spare severe additional pain while preserving the
  goods and claims of everyone affected and introducing no offsetting harm.
  Perfect care can require avoiding the added suffering even if there is no
  best creation overall. An independently credible alternative with the
  suffering could count for P if this very n, whenever present, knows of it,
  can relieve it on those terms and would protect the patient. A local
  analgesic comparison gives evidence of a means of relief. The further
  comparison of *all relevant costs to that provider* is a separate burden.
  In the existing Rowe reading the universal clause about omniscient and
  omnipotent preventers holds vacuously in an order with none. Using that
  absence to establish the crucial comparison would borrow the verdict.
  Holding fixed a patient whose very existence requires n would instead test
  the protection claim, as actual suffering does given actual n. And the
  positive-core route already assumes a necessary bearer and yields
  ontological goodness. Importing it cannot supply an independent argument
  for essential moral protection in C2. An impersonal source that invariably
  optimized in the relevant respect would face the same test.
  [Rowe's exact comparison](../../TruthCore/English/Rowe/EvidentialEvil.lean),
  [creation choice](optimal-creation-choice.md) and [C5's positive core](../modal-ontology-120.md).
- **A necessary mathematical content.** Here we test a route to necessary
  presence. An invariant content that requires n in each alternative would
  carry n to all of them. A real basis for each possible
  content would give a reason to resist the total cancellation of such a
  basis. Replacing its whole supplier while preserving the contents is a
  different claim. Compare a Euclidean triangle relation, whose proof needs
  no particular concrete bearer, with the singleton whose only member is n.
  Suppose impure singletons are admitted, their membership fixes their
  identity across worlds and they existentially depend on their members
  within each world. A different sole member then gives a different set, and
  pairing gives that very singleton wherever n exists. It supplies no premise
  that the singleton exists even in a history under consideration for n's
  absence. Requiring
  every such singleton unconditionally, while requiring its member there,
  would give necessary Socrates by the same argument. A necessitist can
  accept that consequence; a foundation-specific explanation owes a reason
  for the restriction. Appealing to the singular thought *that n might have
  been absent* fares similarly. Our capacity to refer to actual n does not
  require a token of that thought or its referent inside the described
  alternative. The invariant relation and the irreplaceable member earn
  different premises about different objects.
  [Material-basis investigation, #1790](https://github.com/moritzbrantner/formal-logos/issues/1790)
  and [Fine, “Essence and Modality,” pp. 4–5](https://doi.org/10.2307/2214160).

**Verdict.** The origin argument earns confidence about a specific range
of alternatives *to the extent that* the particular dependencies can be
traced. It also explains a selection effect in familiar modal reasoning.
Varying one circumstance while preserving a person can retain that person's
ultimate source without the thinker ever mentioning it. The reliability
of such comparisons within a family of histories offers little evidence
that they exhaust metaphysical possibility. Symmetrically, omitting every
named actual creature does little to establish that its source is absent.
Either a theist or a naturalist can posit essential ancestry or primitive
permissions. Both owe the same account of numerical identity, admissibility
and explanatory direction. Mere absence elsewhere involves no change in n.

The fundamental disagreement remains whether genuine alternative existence
requires a prior feature of reality licensing it, or whether an individual
permission can itself help determine what is admissible. The origin argument
adds a way to decide particular cases even across that divide. I have high
confidence in the restricted inference and moderate confidence that the
shared evidence still warrants suspension about P. Evidence that the same
ordinary individuals from seemingly separate histories really could coexist
on those origin terms, together with rigid ultimate dependence, would extend
the case for necessity. A universal verdict also needs reasons covering
histories with no such creatures and excluding a concrete-empty history.
One genuinely admissible concrete-empty history would settle P. An
independently admissible failure of a condition this very n guarantees would
move me toward P. Under the
strict question that evidence must be consistent with P itself lacking a
full metaphysical ground at actuality. These comparisons are analyst
arguments, with existing formal results reused at their stated scope.
Attempt `10c88ffa` records the findings.

### What can a group or a whole world show that one creature cannot?

Keep the same actual, simple, underived n and the same accessible histories.
P says that one such history lacks n altogether. An individual, a group
acting together and a complete order can each give evidence for or against
P. Enlarging the subject helps when the new facts eliminate an alternative
that the earlier facts left open.

**A group can identify a source that no member identifies alone.** Suppose
three pumps run simultaneously. Within a
fixed installation an interlock admits one supply at a time. Each backup can
power a different pair, and the main generator can power all three. Knowing
only one pump, or any two, to be running leaves a backup explanation open.
Knowing all three to be running singles out the main generator. The wiring,
interlock and supply inventory can each be checked independently. The same
inference can survive shared supply: if all backup feeds together pass
through a known bottleneck of capacity two pumps at the specified load,
even cooperating backups cannot power all three. Adding a plug-compatible
generator defeats the identification of the particular machine. These are
tests of simultaneous operation, not of the mere presence of three pumps.

For C2, ask of a proposed order of creatures what each eligible supplier,
or coalition of suppliers, could jointly sustain. If the order occurs,
requires supply, and no way of supplying it without n is possible, n is
present. This need not assume
a sole ultimate source, a common organism across worlds, or any individual
creature that can exist only with n. The independent work is to establish
the joint requirement, the limits of the rival suppliers, and the class of
histories in which these findings apply. Eliminating all proposed explanations
leaves open unconsidered suppliers and, unless independently excluded, a
brute occurrence. Several local sources can also happen to agree without
their agreement having a separate producer. Simply listing “all and only the
n-dependent groups” supplies no such work. The wiring example establishes
the form of the inference. There is no correspondingly established upper
bound on the joint powers of all metaphysical rivals.

Aquinas offers a reason to look for an explanation at this scale: diverse
things serve one another in one order, and he takes their unity of operation
to call for unity in its first cause. Hume's Philo points to the many people
who build one ship; coordination and the accumulation of skill yield a
single organized outcome. This is positive evidence that coordinated supply
can occur. Whether the cooperators themselves require one ultimate giver
of being is a further question. Even identifying one causal organization
falls short of identifying its numerically irreplaceable bearer. The corpus
already shows that two different ways of storing the contributing states
can agree under all interventions allowed at the public interface.
[Aquinas, ST I.11.3](https://www.newadvent.org/summa/1011.htm#article3),
[Hume, *Dialogues*, V](https://davidhume.org/texts/d/5) and
[existing intervention comparison](../../corpus/results/MECHANISM-INTERVENTION-PARITY.json).

A group can improve an explanation even when it cannot settle identity.
Suppose eight readouts all agree. If they faithfully copy one fair binary
signal, the probability of agreement on either value is 1. If they are
independent fair draws, it is 2/256. Each readout alone had the same odds
on both accounts. This favors common transmission over the specified
independent process. Another transmitter copying one signal predicts the
whole pattern just as well. Neither theism nor naturalism by itself sets
those odds, and this comparison gives no numerical probability for P.

**When would the whole add more than every finite group?** Suppose there are
finitely many candidate n-free ways of supplying an order, and each fails a
requirement already witnessed by a finite group. Taking one such group per
candidate gives a finite witness against them all. A single policy allowing
every finite population but only finite populations fails a global condition
with no such finite witness. A related case arises with infinitely many
candidate suppliers. Suppose each n-free supply arrangement has a fixed
finite capacity, yet every finite group of loads in the proposed order can
jointly be met by some arrangement. A *single genuinely possible order*
requiring unbounded supply
from its ultimate suppliers taken together would exclude all of them.
Arbitrarily large demands in **different** histories do not make that order.
Nor does an individual capacity bound establish a bound on the resources of
an infinite coalition. There is some philosophical motivation here. If a
recipient limits a power, an unreceived act can escape that particular limit.
Aquinas argues from unrestricted divine being to infinite active power.
That gives no upper bound on a different proposed unreceived source, and
the quantitative loads in the example supply no measure of the giving of
existence. On the explicit capacity and supply premises the order would attest to n's
presence there; to establish necessity by this route still takes coverage
of every admissible order. The repository's infinite-tail controls already
demonstrate how all finite tests can pass with different witnesses.
[Aquinas, ST I.25.2](https://www.newadvent.org/summa/1025.htm#article2),
[finite selections](../../corpus/results/GRIM-REAPER-FINITE-TESTS.json)
and [finite population covers](finite-population-cover-533.md).

**A group can also give evidence for absence.** Imagine two people in one
disaster. Given a timely available rescue for either, suppose that wherever
n is present in these circumstances it knows of the danger and ensures at
least one survives, without any offsetting moral cost. This guarantees no
particular survivor. An independently admissible history in which both die
would exclude n. A common danger supplies a positive reason to consider
joint loss; the separate possibility of each death would not suffice. The
cost and feasibility comparison must concern n's options there. An account
of what human rescuers could do cannot settle it. If the case for joint
loss keeps n present, it challenges the protection premise instead. The
same inference applies to an impersonal source with the same guarantee.
[Existing protection test](#testing-things-the-foundation-might-guarantee)
and [existing joint-absence controls](modal-grounding-frameworks.md).

There is a second route that need not identify a specific missing effect.
Suppose two incompatible outcomes of a decision, acceptance and refusal,
are each independently admissible from actuality under the same relevant
conditions. If n's presence together with those conditions would settle the
choice the same way each time, **at least one history lacks n**.
We need not know which. This gives the primitivist a route to evidence for
P without first asking anyone to imagine n's absence. Its strongest
objection is that the very warrant for the two outcomes may be a freedom
the agent exercises *with* n present. That would count against the fixed
outcome. Simplicity of the source and the actual occurrence of one outcome
do not establish that its presence settles every choice. On the present
evidence, variation puts more pressure on this claim of determination than
on necessary existence. [Selected-effect analysis](selected-effect-bridge-462.md).

**A test across three possible worlds can allow the circumstances to vary.**
Suppose three people rank three projects, in order of preference, ABC, BCA
and CAB. If offered A and B they vote for A by two to one; offered B and C
they choose B; offered C and A they choose C. Any two decisions fit some
strict transitive ranking of the projects. All three together fit none:
the first two require A above C, and the third requires C above A. This
ordinary mechanism gives a positive reason to take the three alternative
histories seriously. No individual voter need change their priorities.
[Arrow, “A Difficulty in the Concept of Social Welfare,” pp. 328–329](https://www.stat.uchicago.edu/~lekheng/meetings/mathofranking/ref/arrow.pdf)

Apply the test to a proposed selector of whole orders. If wherever n is
present it secures the uniquely preferred feasible outcome under **one
unchanging strict ranking of these same options**, n cannot be present in
all three histories with those feasible pairs and results. This needs
neither a single invariant outcome nor a verdict on which world lacks n.
But an agent can consistently institute majority rule and permit all three
outcomes. Ranking complete histories may also give weight to which options
were available or whether people decided freely. “A chosen over B” and
“A chosen over C” can then be differently valued histories even if both
deliver project A. Ties also let different outcomes count as best. To use
the cycle against n, one must establish that the relevant feasible pairs
really occur, that the same source ranks the options independently of the
menu, and that its governance secures the strict winner. The local vote
does not establish any of those claims about choosing universes. It does
explain why a cycle can be evidence against attributing one fixed ranking
of outcomes to a ruler, while supplying little evidence against that ruler's
presence. [Existing best-world and tied-choice comparisons](optimal-creation-choice.md).

**Can n actualize every possible world?** Distinguish an exact world, which
settles every fact including whether n exists, from a history described
entirely in terms that do not explicitly state who supplies the creatures
or which foundation is present. Keep any independently specifiable fact
about the creatures even if, given the source's powers, it rules a source
in or out. Such a history can fix the creatures' numerical identities,
internal relations, laws, actions and absences within the creature domain.
Including “this creature stands in this very relation of creation to n”
restores a source fact even though the subject of the sentence is a creature.
Keeping the source question open in the description leaves open what it
takes for the described order to obtain.

If n can bring about **each very world** by an exercise of its power within
that world, its absence was excluded by the premise. An agent can contribute
to a history containing itself without bringing itself into existence. The
converse also fails: an agent can be present when someone freely makes a
choice it cannot unilaterally secure as that person's libertarian choice.
If n can instead realize **each creature history**, each history has *a*
realization with n. Necessity requires n in *every* realization. Even a
completely empty creature history illustrates the difference. A solitary n
that freely creates nothing, a solitary different source, and a world with
no concrete beings would agree on every fact in that description, insofar
as each proposal is admissible. Evidence that n can refrain warrants only
an n-present history in which it refrains. Ruling out independent production
there is also needed to infer no creatures, and ruling out coexisting
uncreated beings is needed to infer solitude. A similar distinction applies
if n grounds representations of possible worlds. Even a representation
whose existence depends on its author can describe a scene in which its
author never appears. To infer necessity one must show that the obtaining
of every represented world requires n within that world. The availability
of a representation alone does not establish its metaphysical admissibility.
[Earlier distinction between the created order and its complete explanation](intrinsic-existence-reason-1595.md#fixed-bearer-facts-and-complete-explanandum)
and [Plantinga, *The Nature of Necessity*, ch. IX](https://doi.org/10.1093/0198244142.003.0009).

This gives the rivals a concrete disagreement. Grant that n can supply every
possible creature history. Then anyone also affirming P owes at least one
pair of possible worlds alike in their complete source-neutral creature
histories and different in n's presence. Conversely, anyone inferring
necessity from that universal power owes a reason why such a difference
is impossible. An intrinsically specified joint requirement like the
three-pump load could settle the matter for particular histories. Invoking
the completeness of the creature description cannot do so by itself.

**A whole cosmos as a rival.** Suppose an accessible order contains a
cosmos with proper parts that is underived in its very act of being. Suppose
also that n lacks proper parts wherever it exists and, wherever both exist as distinct
beings, n must give being to that cosmos. Then n cannot be identical to
the cosmos, and cannot coexist with it. This is a nonempty candidate for P
that requires neither a census of every immaterial being nor identifying a
particular missing creature. Schaffer's priority monism supplies a worked
account on which a material whole is basic and its parts derivative. He
expressly limits the domain to material objects. Being prior to all material
parts leaves open whether the whole receives existence from another being.
The stipulated case for testing C2 grants n's actual profile. It leaves its
universal giver role and the required transworld reading of simplicity open.
The argument for P needs all three premises at once: an independently
admissible cosmos underived in the relevant respect, n's essential simplicity,
and the essential giving role that would exclude coexistence. A theist who
defends that role has reason to take such a rival cosmos seriously as a
test. A naturalist who accepts only material priority has yet to supply it.
[Schaffer, “Monism: The Priority of the Whole,” §1.1, p. 33](https://achrafkassioui.com/library/Jonathan-Schaffer-Monism-The-Priority-of-the-Whole.pdf)
and [the corpus comparison](priority-monism-framework.md).

**Assessment.** I have high confidence that joint evidence can discriminate
where each creature alone leaves the source open. This improves both sides'
positive arguments. It weakens the move from one integrated order to one
irreplaceable individual and the move from many individually omissible
creatures to a world without n. Moderate confidence in suspension about
bare C2 remains appropriate. I would move toward necessity given independently
supported joint constraints that require this same n across all admissible
orders, including the case with no creatures. I would move toward P given
a credible joint outcome incompatible with an independently warranted
essential commitment of n. Such an outcome can provide evidence for P even
if a primitive permission for n's absence helps make the outcome possible.
If the admissible world instead *fully grounds* P at actuality, it conflicts
with the question's strict no-ground stipulation. Nothing in the group
argument treats absence in another world as an event that happens to n.
Attempt `bb466836` records this assessment and its open premises.

### When do adverse consequences count against possible absence?

The actual n exists on both hypotheses. P adds that an accessible history
lacks that very individual throughout. A bad outcome in such a history
can matter in three different ways. It can make the proposed history
undesirable, make it incompatible with commitments its proponent has
reason to retain, or put present beliefs at risk of error. Only the
second by itself defeats that combination of premises. For instance, a
world without inquiry could contain no successful inquiries. That is a
loss. A world literally devoid of *all* truths could not be one at which
it is true that n is absent. That is an incoherent specification. Neither
argument excludes a world without local thinkers in which it is true
that n is absent. Moving from truth *at* the world to a concrete
truthmaker *in* it needs a separate premise, as does identification of
that truthmaker with n. [Empty-world truthmaker controls](disjunction-ground-485.md#exact-empty-world-core-and-distinct-replies-554).

An appeal to goodness can go beyond wishing that n exist. Leibniz compares
possible universes by their degrees of perfection to explain the choice of
one. The comparison itself takes inferior candidates seriously as
possibilities. Pittard offers a different argument: if deceptive worlds
predominate among conceivable worlds containing one's internal duplicate,
confidence that our actual environment is hospitable to knowledge needs a
countervailing reason. He considers a fundamental order directed toward
goodness as such a reason. Even if this favors an ordering toward good,
one route to necessity for n would identify a good required in *every*
admissible order for which this individual's presence is indispensable.
Inferring that requirement
from the loss of a particular good in one proposed order would be circular
if the only reason for ruling out that loss were the assumption that n
must be present. The same test applies to a proposed impersonal guarantor.
Conversely, n's presence alone gives no guarantee that finite inquirers
exist or that a particular inquirer's method succeeds.
[Leibniz, *Monadology*, §§53–55](https://en.wikisource.org/wiki/Monadology/Latta_translation)
and [Pittard, “Deceptive Worlds, Skepticism, and Axiarchism”](https://doi.org/10.1080/0020174X.2021.1938902).

A proposed loss of scientific knowledge gives a second test. A view that
admits an immediate reversal of a law on the same evidence and claims
that this evidence *guarantees* the law's continuation cannot keep both
claims. A rival can posit a stable basic law or defend a fallible forecast.
Even granting instability in some n-free world does not put that reversal
among the futures of our actual history. Conversely, a necessary source
free to allow either future supplies no guarantee without a reason for
stability. This identifies a substantive disadvantage of the unrestricted
prediction claim and preserves a coherent reply.
[Law-change comparison](no-foundation-law-chaos.md) and
[scope of the practical objection](no-foundation-practical-collapse.md#exact-scope-of-the-collapse).

**What a successful subtraction would have to change.** Use one relation
throughout: giving a concrete being its existence in the relevant order.
Call a concrete bearer a root if no distinct concrete giver gives it
existence in that order. This is a relative description. It says nothing
by itself about the bearer's simplicity, its having no internal recipient,
its supplying everyone else, or its being divine. Grant two substantive
premises: n is the only actual root, and every populated accessible order
has a root in this same respect. The second has a positive rationale where
all candidate givers would otherwise merely pass on actuality they wholly
receive. Accounting for each link by another link need not account for
anyone's having actuality to pass on. Whether this applies to every
complete order is contested. The whole-roster result concerns the actual
root of a specified grounding relation. Applying it here requires matching
that relation to existential giving and defending coverage at each relevant
world. Actual firstness alone establishes neither premise.
[Complete orders of givers](unique-feedback-explanation-311.md)
and [scope of the whole-roster result](../../corpus/results/WHOLE-ROSTER-ROOT-EQUIVALENCE.json).

Now take any putative n-free history. If it contains something concrete,
choose a root there. If that individual is among the actual concreta, it
was dependent here, since n was the only actual root. If it is outside
that inventory, the proposed history includes a *different possible root*.
Thus the options are concrete emptiness, a change in the dependence status
of some actual individual across histories, or a root outside the actual
concrete inventory. The last two can occur together. This excludes every
populated proposal formed by deleting n and retaining only actual dependents
as dependents, **even if we also delete most of them and reassign every
particular giver**. No organism needs to retain its numerical parents and
no link needs to retain its actual direction, provided the two premises
and the retained dependence statuses hold. Nothing here treats cross-world
variation as a temporal change.

This is stronger than observing that a particular proposed omission has
no known cause. It also exposes the limit of the argument. Imagine a
different root supplying the same recipients. They still have givers; the
identity of the giver differs. This meets the two premises at the level
of the specification. Its genuine possibility remains open. An ordinary
reason for admitting a person who never actually existed is that a couple
could have had a different child. That reason invokes generation and gives
no comparable warrant for an additional *underived* bearer. Conversely,
the fact that no one could produce a new underived being in the actual
world gives no reason why one could never have existed in another. This
route to necessity needs to exclude **n-free** realizations of those cases.
A new root could coexist with n, as could a previously dependent individual
now underived, if two roots are admissible together. Ruling out all new
roots and all status changes would suffice for the populated cases, but
would be stronger than needed. Essence–esse identity in actual n settles
none of these questions about other bearers.
[Adams, “Actualism and Thisness,” §4.2](https://paperzz.com/doc/6797968/actualism-and-thisness)
and [the earlier replacement test](#testing-occupation-and-replacement).

**Can an actual dependent itself become the replacement?** Consider the
rational soul in Aquinas's account. Its inability to arise by rearranging
matter gives a reason about how it could be produced *if produced*. On
its own this would leave open an unproduced soul. Aquinas offers a stronger
reason. The soul is a subsistent form whose act of being it has by
participation. He holds that having being in this way entails having a
cause, even though no particular cause is mentioned in the definition of a
soul. If this mode of being belongs to the same soul wherever it exists,
and participation requires a distinct concrete giver there, then this very
soul cannot go from dependent here to underived in the alternative. Giving
it a beginningless history would leave the reason for dependence intact.
It could still receive existence from another source, if that source is
admissible. This excludes one proposal without assuming that n is necessary.

The strongest objection targets the inference from limited or participated
being to an *extrinsic giver*. Distinguishing what a soul is from its being
actual identifies a difference within the account of the soul. Treating
that difference alone as evidence of an efficient cause would skip the
participation premise. In Aquinas's example of iron heated by fire there
can be independent evidence of heat passing from one body to the other.
Simply observing that the iron's temperature is finite would not supply
that evidence. Likewise, if “participates” already means “gets its being
from another,” the work lies in showing why the soul meets that description
wherever it exists. The corpus's distinct-esse result concludes under
its premises that there is another actual cause, with its mode unspecified.
It does not establish the required concreteness, transworld scope or the
identity of the giver. Aquinas's full argument to the one God employs
further premises; the narrower argument can be assessed without importing
that conclusion. I give the exclusion of a brute soul substantial weight
*within the participation account* and little independent weight against a
world with a replacement giver.
[ST I.90.2–3](https://www.newadvent.org/summa/1090.htm#article2),
[I.44.1, especially reply 1](https://www.newadvent.org/summa/1044.htm#article1)
and [the precise distinct-esse premise](../../corpus/statements/457698e4-eb21-4561-ab32-eccbfb0a992e.json).

**What richer comparisons actually exclude.** A lamp can stay lit when
its main supply fails because a backup switches on. Recording the switch
position and energy flow as well as the lamp rules out *that explanation*
for two otherwise identical installation histories if those additional
records would differ. Likewise, retaining the independently specified fact
that a being receives existence from someone excludes declaring that same
being's existence wholly ungiven in the alternative. It does not name its
giver. Finally, persistence without a current conserver could explain a
being's later state. It cannot supply a whole history without n if n
indispensably supplied its origin in that history. These exclusions concern
different mechanisms. Once the remaining proposal says that every recorded
contribution is unchanged except who ultimately gives existence, more
readings from the same machinery cannot distinguish it. Nor would a
different way for the lamp to be lit show that its actual supply did no
work. [Intervention comparison](joint-cooperation-744.md) and
[origin versus conservation](causal-dependence-support-investigation.md).

There are two readings of “the complete creature history underdetermines
the foundation.” Two accounts may agree on everything we know of creatures
while disagreeing on what is possible. That establishes a limit of those
data. If instead there really are two admissible histories with the same
creature facts and opposite verdicts about n's presence, one of them
already witnesses P. Establishing the first reading repeatedly does not
establish the second. Equally, excluding a duplicate of the *actual*
history still leaves a possible absence in a quite different history.

**One kind of loss could matter here.** Suppose an inquirer claims to
know that this particular n exists from the public order of creatures.
On a demanding safety condition for knowledge, such a belief cannot
easily have been false when formed on the same basis. If the same inquirer
could very easily have made the same judgment about the same n by the
same method in an n-free history, that claim to knowledge is in trouble
already. One well-motivated error of this sort matters more than any
number of remote, uninhabited alternatives. A replacement observer who
correctly thinks “my source exists” does not supply the required false
belief. If the actual judgment requires acquaintance with n, retaining
its evidence and reference in an n-free world is itself in dispute.
An argument cannot appeal to the ease of precisely this error to motivate
replacement, then dismiss that same error as remote to defend knowledge
on the very same standard. Mere metaphysical accessibility, though,
implies no such ease. Necessity would guarantee the true answer to the
fixed question even when someone merely guessed. It would still leave
their warrant to be explained. These are costs to identifiable epistemic
commitments on either side.
[Pritchard, “In Defence of Modest Anti-Luck Epistemology,” §§II–III](https://escholarship.org/content/qt64p736bn/qt64p736bn_noSplash_e278f99b5301228f09e0b95f0fba857d.pdf)
and [truth versus access](transcendental-foundation-routes.md).

**How much does another failure to find an omission count?** Consider an
illustration about an investigator's evidence. Under necessity suppose the
investigator never falsely certifies an absence. Conditional on P, suppose
they initially give equal weight to two accounts. On one, each fresh,
independent inquiry would have a one-half chance of correctly detecting an
absence. On the other, this particular procedure could never detect one.
A first miss has probability 1 under necessity and 3/4 under P,
so the evidence multiplies the odds of necessity against P by 4/3. After
two misses the cumulative multiplier is 8/5. Even an arbitrarily long
series approaches a multiplier of only 2, because the undetectable account
predicts every miss just as well as necessity. The probabilities concern
the procedure, with independence only conditional on the detectable
account. They are neither a measure over worlds nor estimates for C2.
[Dependence between reports](correlated-testimony-1396.md) and
[contrastive confirmation](contrastive-worldview-934.md).

We have no calibrated detection rates or weights of this kind for
metaphysical inquiry. There is nevertheless a qualitative result. A
search that retains an individual independently known to require n has
no opportunity to discover an n-free world by varying that individual's
circumstances. Adding cases can increase our confidence in *why this search
is insensitive* without changing the comparative evidence for P. An
argument that instead decides whether concrete reality could be empty
would test a different class of alternatives. An independently grounded
judgment that a normally derivative bearer must remain derivative wherever
it exists would eliminate a status change for that bearer alone.

**Provisional judgment.** I favor the objection to unrestricted subtraction
over the inference from ordinary removability to P. On the two root
premises the objection is decisive for the populated histories specified
above. I have high confidence in that restriction and moderate confidence
in suspension about P itself. The most consequential outstanding question
for populated worlds is whether the evidence that identifies how a
particular being receives existence can distinguish the ultimate giver
from a replacement. Evidence of a genuinely admissible alternative whose
features preclude n's coexistence would move me toward P. Warranted
exclusions of concrete emptiness and of n-free realizations of the two
populated cases, together with the root premises, would support necessity.
If the explanation of an alternative is offered as a full prior ground for P at
actuality, it would revise the strict no-ground stipulation. An alternative
admitted partly because P is already permitted can give evidence for P
without being its prior ground. The strict question also requires that P
itself lack any other full ground at actuality. These are philosophical
assessments using the existing results. Attempt `27447619` records their scope.
