# C2: what grounds the contingency of an actual being? (2026-11-23)

Follow-up to PR #1870 (gap 1 and next test 3), God-existence stage of the #143
root. Batch `specs/c2-contingency-grounding.toml`, vocabulary module
`TruthCore.Causality.ContingencyGrounding`, results module
`TruthCore.Results.Causality.ContingencyGrounding`, attempt
`137ac90d-d110-45db-a2a3-44e5f0406eea`. Analyst formulations, attribution
deferred (logic first). Locators below are navigation only; no source claim is
made and none of the cited texts was materialized for this slice.

**Graph destination.** The same-witness First Way endpoint `f9208664`
(`FirstMoverNecessaryPureActAt`), which projects through result `402e5643` to
STMT-NECESSARY-CONCRETE-AT `b19ffd92`, which reaches the root. Second
destination: #1870's B2 ∨ B4 `3c9d683b`, which feeds the route-A∨B argument
`81a17728` to the same endpoint.

**Question.** C2: *a metaphysically contingent actual being must possess some
relevant receptive potency or receive its actuality from something
metaphysically prior.* The owner's target is C2's substantive warrant, not
another reformulation of contingency → potency.

## 1. Fixed meanings and what separates them

| Notion | Formal reading | Separated from its neighbours by |
|---|---|---|
| Modal contingency | `ContingentAt F.history.ontic w x`: exists at `w`, absent at some accessible world (MODAL_CONTINGENCY_1) | — |
| Avicennian "possible in itself, necessary through another" | not formalized here; an emanated being can be modally necessary yet caused (q.2 a.3's necessary things caused by another) | C2 is about modal contingency only; it says nothing of caused necessary beings |
| (a) intrinsic potency to non-being | `CanFailToBe x F.esse`, the existing DEF-CAN-FAIL-TO-BE primitive at the respect of being: *corruptibile simpliciter* (In Metaph. IX lect. 9), the two-way potency to be and not be | `angelic`: contingent and incorruptible; law 10: not POTENCY_1 at esse |
| (b) another's power over the thing's esse | `PowerOver y x F.esse`, new DEF `3fd6bddb`, the relation under MUTABLE_2 | `angelic` (b without a); `corruptor` (a and b, b without causing esse) |
| (c) bare modal absence | `ContingentAt` itself | `bruteSimple`: (c) with neither (a) nor (b) |
| Unrealized POTENCY_1 | `AdoptedPotency.InPotency`: `CanBe ∧ ¬ InAct` | law 10 and #1870's R2 law: at esse it contradicts actual existence |
| Receptive potency | RECEPTIVE_POTENCY_1 (DEF-RECEPTIVE-POTENCY), a principle's potency to an act it may already have | `witness`: an actual contingent being receives esse in a principle in receptive potency to it |
| Passive potency (genus) | not a single predicate; its two species used here are (a) and matter's receptivity to form | passive→receptive is an OPEN bridge between them, not a definition |
| Existential composition | `esseOf x ≠ essenceOf x` (B6's consequent) | #1870 `bruteFirst`: distinct esse with no recipient |
| Received esse | `Received x p` (DEF-ESSE-RECEIVED-IN) | `uncausedComposite`: received esse with no cause |
| Existential receptivity | `ExistentiallyReceptive`, new DEF `f9f58df7`: received esse in a principle in receptive potency to it, or matter–form composition | the matter–form disjunct keeps C2 faithful for views without a real essence–esse distinction (Suárez) |

**Reuse decision (differs from the brief).** The brief proposed a new
primitive `PotencyForNonbeing`. The corpus already has it: DEF-CAN-FAIL-TO-BE
reads `CanFailToBe x r` as the potency of the contradictory, identifies what can
fail to be with the corruptible, and DEF-INCORRUPTIBLE-SIMPLY takes the
respect-of-being instance as *incorruptibile simpliciter*;
DISAMB-CAN-FAIL-TO-BE-OR-BE-OTHERWISE says the bare-possibility sense is not
adopted anywhere. That is exactly the intrinsic potency to non-being of q.50
a.5. Reusing it (invariant 7) connects PGP to the existing B4a/B4b
decomposition (laws 8–9) and to the In Metaph. IX vocabulary.

## 2. Checked results

All theorems in `TruthCore.Results.Causality.ContingencyGrounding`;
Comparator and NanoDa pass; bind-check binds all nine. Statement ids: C2
`6508c239`, C2⁻ `8478f367`, PGP `20d5fecd`, correlation `9163c423`,
passive→receptive `16c760a3`, corruptible→POTENCY_1 `8bfc4ab7`,
unreceivedness `2e2ab9cc`, controls `07a9006e`.

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
| `cafd9800` | `controls` | premise-free laws 1–10 and ten models |

Laws (`Model.Laws`): (1) C2 → C2⁻; (2) C2⁻ ∧ B3 → C2; (3) R1 ∧ *De ente* → C2;
(4) B2 ∧ B3 → C2; (5) correlation → #1870 bridge (ii) restricted to beings
incorruptible simply; (6) PGP ∧ no power of anything over its own esse ∧
corruptible→POTENCY_1 → MUTABLE_3 for every contingent being (#1870 bridge (i));
(7) the PGP route composes to the endpoint; (8) B4b → corruptible→POTENCY_1;
(9) B4a → PGP; (10) with adopted POTENCY_1 and the existence-to-act interface,
B4b excludes every actual corruptible at `w`.

**Findings that differ from the brief's expectations.**
- No excluded middle is needed for C2 from PGP (distinctness of the power's
  holder comes constructively from `b62a64ab`) or for unreceivedness (the
  reductio derives `esseOf f ≠ essenceOf f` and contradicts simplicity
  directly). EM enters only where necessity is concluded.
- The brief's argument 2 is registered as two steps, so unreceivedness is a
  separate node: pure actuality (POTENCY_1), unreceived esse, underivedness
  (firstness) and necessary existence are four distinct propositions, and the
  graph shows which does work.
- #1870's bridge (ii), "another's power over a thing's esse gives a distinct
  cause of its esse", is **false as unrestricted** under the natural reading of
  the power relation: fire can destroy a log without causing its esse
  (`corruptor`). Correlation yields it only for beings incorruptible simply
  (law 5). So the q.9 a.2 channel reading of B2 ∨ B4 needs the restriction, and
  the corruption channel is covered instead by corruptible→POTENCY_1 (a new
  OPEN bridge). Result `bf2f0e8e` registers the corrected decomposition.
- Law 10 is a new defect finding for #1870's B4b: read with the adopted
  POTENCY_1 it excludes every actual corruptible, exactly as R2 excluded every
  actual receiver. B4a ∧ B4b is therefore not a viable decomposition of B4 at
  esse; corruptibility must stay distinct from POTENCY_1 at esse.
- C2 and B2 ∨ B4 are logically independent (`deistSource`: C2 without
  B2 ∨ B4; `potencyOnly`: B2 ∨ B4 without C2). The C2 route is a different
  modal bridge from #1870's route A ∨ B, not a restatement.
- `truth countermodel` does not support `CausalityFrame` parameters
  ("unsupported parameter F"); all models are hand-written as in #1870.
- Duper (`--premise-pool all`, 8 candidates, 100000 heartbeats; C2, the
  endpoint and B2 ∨ B4): 2 proved, 1 unresolved. It re-found the endpoint from
  the grounding endpoint `11958874` (already known), and B2 ∨ B4 from R2
  `6e8942c8` with R1. The latter is not worth registering: R2 with R1 and the
  existence-to-act interface excludes every contingent existent (#1870
  reception law), so that support is vacuous at actual contingents. C2 itself
  stayed unresolved (retrieval miss; unresolved is not a refutation).

## 3. Models (structural satisfiability, not metaphysical possibility)

Frames reuse `FirstMoverNecessity.Model.mk` (worlds, beings and respects
`Bool`, reading world `true`, `f` moves `x` in heat, `x` in POTENCY_1 in heat
only, so `f` is POTENCY_1-pure act throughout).

| Model | What holds | What fails | Shows | Admissible on |
|---|---|---|---|---|
| `bruteSimple` (rivals 6.1/6.3) | every other premise of the PGP and C2 routes; CCR on the same frame's q.3 a.4 profile, `f` uncaused | PGP, C2, endpoint | ¬C2 needs exactly ¬PGP given the other bridges; C1-style dependence does not exclude a contingent first actuality | modal primitivism; Humean/Armstrong combinatorial subtraction; Lewisian counterpart absence |
| `selfAnnihilator` v1 / v2 | PGP; v2 also correlation | v1 correlation; v2 no-self-esse-cause; C2 | self-annihilation must deny correlation or admit self-causation of esse | v2 only where self-causation of esse is admitted |
| `uncausedComposite` (6.2) | C2 (reception), R1, *De ente* | PGP, B2, C2's prior-cause disjunct | C2 does not entail PGP; C2 strictly weaker than B2 ∧ B3 | an ontology allowing an uncaused composite (it contradicts q.3 a.4, not C2) |
| `angelic` (Aquinas's own case) | everything; C2 by both disjuncts | B4, pure-act target | possible non-existence without a potency to non-being; extrinsically grounded contingency; a POTENCY_1-pure-act contingent being | the Thomist account of a created intelligence |
| `deistSource` (6.4) | PGP, C2 (reception) | correlation, B2, B2 ∨ B4 | the deist rival targets correlation's conserving reading and C2's second disjunct, not C2; C2 ⊬ B2 ∨ B4 | an originating-only, non-conserving creator |
| `bareCorruptible` | PGP, correlation, `b62a64ab`, B3 | passive→receptive, C2 | omission model | a corruptible simple (no matter, no recipient) |
| `unprioritizedSource` | PGP, correlation, passive→receptive, `b62a64ab` | B3, C2 | omission model | — |
| `witness` | every premise of every new argument; PGP, correlation, passive→receptive, corruptible→POTENCY_1 applied nonvacuously to the contingent `x`; C2, B2 ∨ B4, endpoint | — | nonvacuity | the Thomist account of a corruptible caused composite |
| `potencyOnly` (direction 9) | pure-act target at `w`, B4, B2 ∨ B4 | PGP, C2 | with `angelic`, PGP and C2 are independent of the target (unlike B4, classically equivalent to it) | — |
| `corruptor` | correlation, PGP, C2 (through matter and form), restricted bridge (ii) | R1, unrestricted bridge (ii) | see section 2; C2 does not require R1 | ordinary corruption |

## 4. Could a purely actual being be contingent? (direction 2)

Under POTENCY_1-pure act, yes structurally: `angelic` (and #1870 `conserved`)
has a contingent being in POTENCY_1 in no respect, receiving esse from a
necessary prior source under whose power it stands. Under "unreceived and
underived" pure act, a contingent pure-act being is exactly a counterexample to
C2 at that being (`bruteSimple`). So the brief's question splits: POTENCY_1
pure actuality is compatible with contingency; unreceived, underived actuality
is compatible with contingency only if C2 fails.

## 5. Strongest positive explanation (direction 3)

The Aristotelian-Thomistic explanation is that modal contingency is not a
brute fact about a thing: its possible non-being is *someone's potentiality*.
Either the thing has a passive potency to non-being (matter: corruptibility,
Θ.8 1050b), or another has power over its esse (q.9 a.2: "mutable by the power
of another"; q.104: conservation). By Θ.1 an active power over a thing either
works on a passive potency in it (back to the first case) or, for the creation
exception, is the giving and withholding of esse (q.104 a.3: annihilation is
ceasing to give being, not an action on a patient). Either way contingency
involves intrinsic limitation (a principle open to being and non-being) or
dependence of actuality. Results `32bf794f` and `bf2f0e8e` make this
case analysis exact and show which premise carries each step.

**Independent support for PGP** (navigation, attribution deferred, not read in
this slice): powers- and potentiality-based theories of modality ground
possibility in the potentialities of actual things (B. Vetter, *Potentiality*,
OUP 2015; J. Jacobs, "A powers theory of modality", *Philosophical Studies*
2010; A. Pruss, *Actuality, Possibility, and Worlds*, 2011; A. Borghini and
N. Williams, "A dispositional theory of possibility", *Dialectica* 2008). This
is a general modal metaphysics with motivations independent of theism (an
actualist, non-reductive account of de re modality), not a Thomist thesis.

**The strongest objection to potentiality modality and why PGP avoids it.**
Target: the general thesis that every possibility is grounded in an actual
potentiality. Mechanism: "too few potentialities" — alien properties, alien
individuals and global possibilities (that there might have been nothing
concrete) seem to have no actual bearer whose potentiality grounds them.
Independent justification: it is the standard objection the cited authors
themselves address. Relevance to C2: PGP is deliberately narrow. It concerns
only the possible absence of an *actual* individual, a de re possibility with
an actual subject. The relevant difference is that the bearer exists, so the
search for a grounding potentiality has a definite place to look: in the thing
(corruptibility) or in what has power over it. The alien and global cases lack
an actual subject; this one has one. PGP inherits the general theory's
motivation without its hardest cases.

## 6. Essence–esse (direction 4)

Received esse explains *how* dependence is possible: it supplies the recipient
for the second channel, and q.3 a.4 links distinct esse to an external cause.
But the modal step contingency → distinct esse (B6) or → reception (R1) is not
warranted by the composition thesis alone (#1870 `bruteFirst`: distinct esse,
no recipient, no cause). It rests on the same power-grounding consideration or
on the limitation principle (contingency as modal limitation of esse; open in
#1881). So the essence–esse route is informative about mechanism but shares
C2's modal crux; it is not independent corroboration. Law 3 makes the strength
relation exact: R1 with *De ente* implies C2, not conversely (`corruptor`: C2
holds through matter and form while no being receives esse, so R1 fails).

## 7. Able not to exist versus having an unrealized potency (direction 5)

On Aquinas's own view (q.9 a.2, q.50 a.5) angels are modally contingent with
no intrinsic potency to non-being. `angelic` formalizes this: contingent,
incorruptible simply, POTENCY_1-pure act, under a prior source's power. So
possible non-existence does not imply a present unrealized potency. B4 ("in
POTENCY_1 in some respect") holds of angels only through unrelated respects
(intellect, will), which is why it is "any respect" and classically the
target; at esse it is excluded (R2 law, law 10).

## 8. Rivals and their prices (direction 6)

Each entry names its target, mechanism, independent justification, relevance
and price.

- **Brute contingent simple first actuality (6.1/6.3, `bruteSimple`).**
  Target: PGP (and so C2) at the foundational being. Mechanism: the being's
  possible absence is no power's potentiality; its contingency is primitive or
  non-power-grounded. Independent justification: developed general modal
  metaphysics deny power grounding: modal primitivism; Humean combinatorialism
  (Armstrong's recombination admits "contracted" worlds lacking some actual
  individuals, a subtraction of a distinct existence); Lewisian counterpart
  theory (a world containing no counterpart of `x`). Baldwin-style subtraction
  arguments generalize "each concrete object might not exist" from ordinary
  concreta. Relevance: these directly deny PGP for the foundational case.
  Price: a modal fact (the being's possible absence) whose truthmaker, if any,
  is combinatorial or primitive rather than any power, at the foundational
  level, in a being with no internal slack (no matter, no recipient) and no
  external dependence. Assessment: the subtraction premise's warrant comes from
  ordinary concreta, every one of which (as far as independent evidence goes)
  is corruptible or dependent and so satisfies PGP; extending it to a being
  that lacks both is precisely what is at issue, so that warrant does not
  discriminate. The standing rival is the general modal metaphysics, not the
  subtraction generalization.
- **Contingent uncaused substance (6.2, `uncausedComposite`).** Compatible with
  C2 iff it is receptively composed; it then contradicts q.3 a.4/B2, not C2.
  No price at C2.
- **Deist necessary source (6.4, `deistSource`).** C2 holds by reception; the
  rival targets correlation's conserving reading (a power to have withheld `x`
  that is not now a giving of esse) and C2's prior-cause disjunct. Since the
  frame's `CausesIn` is tenseless, it cannot separate conserving from
  originating; that distinction is the existing sustaining-versus-originating
  work (attempt `c94eed5b`), not C2's burden.
- **Self-annihilation (`selfAnnihilator`).** Under Θ.1 an active power over a
  patient needs a passive potency in it; a simple being's power to unmake
  itself must either deny correlation (v1) or make the being a cause of its own
  esse (v2, against `b62a64ab`). Price: a self-directed power with no patient
  potency, or self-causation of esse.
- **Essence-grounded modality (Fine, Lowe).** Does not obviously support ¬C2.
  It bears on B6 instead: existence-conditional essentialism ("necessarily, if
  `x` exists, `x` is F") blocks the inference from esse = essence to de re
  necessity unless existence is itself essential. That is the honest B6 crux;
  it does not touch C2 or PGP.
- **No substantive objection identified** to correlation beyond the deist and
  self-annihilation readings above, or to passive→receptive beyond the
  bare-corruptible case, which is a structural omission model and not a
  defended position: no independent account of a corruptible being with
  neither matter nor a receiving principle is recorded.

## 9. ¬C2 evaluation (direction 7)

A contingent, unreceived, pure-act being must be: actual at `w`, absent at
some accessible `w'`, with no receiving principle and no matter, no prior
giver, no potency to non-being, and, unless it denies correlation, no being
with power over its esse. Its contingency must be primitive or
non-power-grounded.

- *Not internally inconsistent*: `bruteSimple` is a structural model, and it
  has admissible interpretations under Humean or primitivist modality.
- *Not merely contrary to Thomism*: it contradicts power-grounded modality for
  actual individuals, which has independent general defenders.
- *A coherent rival* whose price is a modal fact with no truthmaker in any
  power, at the foundational level, in a being with no internal slack and no
  external dependence.

**Parity.** Does the theist's necessary being need a ground for its
necessity? Under PGP, no extra truthmaker is needed: necessity of an actual
being is the absence of any power grounding its absence (formally: PGP and
neither disjunct at `x` give ¬ContingentAt, and EM gives NecessaryAt). Under
Humean modality no individual is necessary, so that rival rejects every
necessary concrete being: it is global, not specific to C2. Under modal
primitivism both the rival's contingency and the theist's necessity are
primitive, so primitivism alone favours neither. None of this defeats the
rival; it locates the disagreement in the general theory of de re modality.

## 10. Weakening (direction 8)

C2 needs only existential receptivity (received esse or matter), not POTENCY_1
in any respect. Formal comparison: C2 and B4 are independent (`potencyOnly`:
B4 without C2; `angelic`: C2 without B4); C2 and B2 ∨ B4 are independent
(`potencyOnly`, `deistSource`); C2 is implied by R1 with *De ente* (law 3) and
by B2 with B3 (law 4), strictly in the B2 case (`uncausedComposite`).

## 11. Direction 9

The PGP route to the first mover's necessity uses vocabulary (powers,
correlation, corruptibility) whose warrant comes from ordinary cases of
generation, corruption and dependence; it is provably not equivalent to
`PureActBeingsNecessaryAt` (`potencyOnly`, `angelic`), unlike B4. Necessity is
derived from unreceived esse plus underivedness; POTENCY_1 pure act is carried
and does no work.

## 12. C1 comparison (direction 10)

C1 (complete existential dependence → an underived bearer; CCR `20babef7`)
does not exclude a contingent first actuality: in `bruteSimple`, CCR holds on
the frame's own q.3 a.4 profile and its uncaused bearer is the contingent,
simple `f`. Terminology: #1882's "C1 does not give C2" uses C2 for the source's
necessity; this note's C2 is the receptivity-or-prior-cause bridge. The two are
complementary: C1 supplies an underived bearer, and C2 with unreceivedness (or
simplicity with the reception premises) turns underived into necessary.
#1882's vocabulary is not imported. Horizontal note: composition-needs-a-cause
(q.3 a.7) would make any receptively composed underived being impossible, so
for an underived being C2 would reduce to "not contingent"; that is a further
open bridge, not a delivered result.

## 13. Cumulative support and provisional judgment (direction 11)

**Convergence, not independent corroboration.** The First Way (firstness), *De
ente* (reception), intrinsic explanation (power grounding) and dependence (C1/
CCR) converge on one witness, but through shared premises: the *prima via*
base `7bce7007`, B0, firstness `74eb9113`, and simplicity `78246da5` (whose
derivation also uses firstness). The reception premises R3, *De ente* and
irreflexivity are shared with #1870's B6 reception argument; B3 is shared with
route A; PGP and correlation are shared by `32bf794f` and `bf2f0e8e`.

**Provisional judgment (2026-11-23; independent semantic challenge pending).**
C2 is *modestly favoured*. Grounds: (i) PGP's general warrant from
powers-based modal metaphysics, independent of theism, and PGP's narrowness,
which avoids that theory's hardest objection; (ii) the ordinary cases: every
contingent being to which we have independent access is corruptible or
dependent; (iii) Aquinas's channel analysis (q.9 a.2), now exact (results
`32bf794f`, `bf2f0e8e`, law 5) and corrected for the corruption channel;
(iv) C2 is weaker than both existing bridges R1 and B2 and survives the
uncaused-composite, deist and self-annihilation rivals at C2 itself.
Standing rival: the brute contingent simple first actuality, priced at
non-power-grounded de re modality for a foundational individual. Revision
conditions: a defended non-power modal metaphysics for concrete existence
whose motivation discriminates the foundational case; a counterexample to
correlation (a power over a thing's being that neither works on its potency to
non-being nor gives its being); or a defended brute contingent simple being.
This is warrant, not formal status: every new premise (PGP, correlation,
passive→receptive, corruptible→POTENCY_1) is OPEN and nothing is closed.

## 14. Gaps and next tests

1. Assess PGP against Humean/combinatorial modality at matching scope: does
   the combinatorialist's contraction of a foundational simple have any
   motivation beyond the ordinary-case generalization?
2. Separate conserving from originating power in correlation by composing with
   the existing sustaining-causation vocabulary (attempt `c94eed5b`) instead
   of the tenseless `CausesIn`.
3. Defend or refute passive→receptive for a corruptible being without matter
   (the `bareCorruptible` structure): is there any independent account of
   such a being?
4. Certify the C2/C2⁻ strength difference (#1598): the exact delta is "every
   contingent being with a distinct esse-cause is receptive or has a prior
   one".
5. Assess corruptible→POTENCY_1 (`8bfc4ab7`): corruptibles' matter is in
   potency to other forms on the Thomist account; record whether any
   corruptible could be in POTENCY_1 in no respect.
6. q.3 a.7 bridge for underived beings (section 12).
