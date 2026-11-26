# The power premises of the route with Pruss's own premise (2026-11-23)

Issue #1887, continued (coordinator slice 2: "the warrant for the Pruss
route's power premises"), God-existence stage of the #143 root.

**Batch.** `specs/pruss-power-premises.toml`; vocabulary
`TruthCore.Modal.PrussPowerPremises`; results
`TruthCore.Results.Modal.PrussPowerPremises`. Attempt
[`daf87aca-9ae5-44e0-b56c-b37712ec2710`](../../corpus/attempts/daf87aca-9ae5-44e0-b56c-b37712ec2710.json).

**Target.** The route with Pruss's own premise of #1889
(`docs/notes/modal-grounding-frameworks.md` §5): result `42da6b2d`
(EM, P1′ `95bf8780`, P2′ `906f5c39`, P3′ `a6906cab`, P4′ `18e5bd4e`, P5
`c76b6e2c` ⊢ `b90ee2de`), then `ad42c376` ⊢ STMT-NECESSARY-CONCRETE-AT
`b19ffd92`. The questions concern its grounding premise P1′ (a power, held at
`w`, for the joint absence of the concrete beings contingent at `w`; written
`q` below) and #1889 gaps 3, 6 and 7.

**Evidence level.** Analyst formulations, attribution deferred. Read for this
slice on 2026-11-23 (navigation for the formulations; no claim record):

- ST I q.104 a.3, respondeo, ad 1 and ad 3, New Advent,
  <https://www.newadvent.org/summa/1104.htm>. Respondeo: "Some have held that
  God, in giving existence to creatures, acted from natural necessity. Were
  this true, God could not annihilate anything"; "just as before things
  existed, God was free not to give them existence, and not to make them; so
  after they are made, He is free not to continue their existence". Ad 1:
  "Non-existence has no direct cause ... indirectly God can be the cause of
  things being reduced to non-existence, by withdrawing His action therefrom."
  Ad 3: annihilation "would not imply an action on God's part; but a mere
  cessation of His action".
- Aristotle, *Metaphysics* Θ.2 (1046b) and Θ.5 (1048a), Ross translation,
  <http://classics.mit.edu/Aristotle/metaphysics.9.ix.html>. Θ.2: powers with
  a rational formula are "alike capable of contrary effects, but one
  non-rational power produces one effect; e.g. the hot is capable only of
  heating"; the formula exhibits the contrary "by denial and removal". Θ.5: for
  non-rational potencies, "when the agent and the patient meet in the way
  appropriate to the potency in question, the one must act and the other be
  acted on"; for rational ones "there must ... be something else that decides;
  I mean by this, desire or will".
- A. Pruss, "The Actual and the Possible" (2001), plain-HTTP copy
  <http://alexanderpruss.com/papers/ActualAndPossible.html>, sections "An
  Aristotelian alternative" and "A combined account". Mere possibility: "there
  actually was a substance capable of initiating a causal chain, perhaps
  non-deterministic, that could lead to the state of affairs". His conclusion
  is "a necessary first cause (perhaps a non-unitary cause which is an
  aggregate of causes) that non-deterministically produces the historical
  universe". His direction: "there is a substance x in w1 which could have
  initiated a causal chain that could lead to w0 being actual", using "the
  axiom S5".

Everything else cited (Vetter, propensity accounts of chance) is navigation
only.

## 1. Fixed meanings

All on the shared `CausalityFrame` of #1784. No new primitive: every new
relation is defined from frame fields and the existing primitives `PowerFor`
(DEF `bf7eddca`) and `PowerOver` (POWER_OVER_ESSE_1, DEF `3fd6bddb`).

| Term | Lean | DEF | Meaning |
|---|---|---|---|
| gives being in a world | `GivesTo F v y x` | `62dfa893` | `∃ t, F.GivesAt v y x t`: in world `v`, `y` exercises causation of `x`'s being at some moment (frame primitive, DEF `158301bc`). Weaker than both CAUSE_OF_BEING senses (`88a8fba7`). World-relative exercise, unlike the tenseless `CausesIn`. |
| one-way (fixed) giver | `FixedGiver F y` | `7bc1d667` | Wherever `y` exists, it gives being to the same beings. Θ.5's non-rational rule for a holder whose exercise needs no patient. |
| varying giving | `GivingVariesAt F w y` | `bd4c434d` | `y` exists at `w` and gives being otherwise at an accessible world where it exists. |
| two-way giver (withholding form) | `TwoWayGiverAt F w y` | `e006ddeb` | `y` gives `x` being at `w` and, existing at an accessible world, does not give it there. An act-or-refrain profile (Θ.5: with a rational potency it is "not necessary" to act); Θ.2's "contrary effects" is an analogy only. |

**Reading step (stated, not attributed).** Θ.2 and Θ.5 speak of one potency
for contraries, decided by desire or will. The types here are
**extensional exercise profiles**. `TwoWayGiverAt` is satisfied alike by
choice, by chance and by a varying external condition; it does not type
intellect, will or decision.

**Collective/distributive.** The split is the one of disambiguation
`197f0097` (C1, #1882), transposed from a cause of a totality to a power for a
totality's absence:

- the *collective* reading is P1′ itself: one power for the joint
  proposition `q`;
- the *distributive* reading is one of three, which must be kept apart:
  - *varying holders*: each member's possible absence is grounded in some
    being's power for that member's absence (`EachActualAbsenceGrounded`);
  - *one present holder* (law 8): one concrete being at `w` that, for each
    member, exists at an accessible world lacking that member;
  - *one holder with power over each esse*: POWER_OVER_ESSE_1 over each member
    (`SomeHolderHasPowerOverEachActualContingent`, `eb41bc9a`). This is the
    transfer's target. It gives necessity only at a concrete foundational
    being, through `c5da5e62` (law 9, `2cc7e260`), not through law 8.
- the transfer bridge is the analogue of C1's premise B (whole to members).

No new disambiguation record was created; `197f0097` is linked from the
transfer statements and the controls.

## 2. Results

All verified (`verify-result.sh`; bind-check 10 bound, 0 mismatch). New open
premises:

- P2δ `5cf75a6b`: initiator presence with a difference in giving;
- factive giving `3ef41442`;
- holders give each `9f7b1778`: the creator reading;
- transfer `f0ac2f76`;
- withheld giving is power over esse `d1593e5c`;
- Pruss's direction:
  - grounding at the absence worlds `607e94cf`;
  - initiator presence there `9c8e99e7`;
  - holders concrete there `887d5efc`.

| Result | Theorem | Premises ⊢ conclusion |
|---|---|---|
| `a47906a5` | `transferGivesPowerOverEachActualContingent` | P1′, P4′, P5, transfer `f0ac2f76` ⊢ `eb41bc9a` (one holder of the power for `q` with POWER_OVER_ESSE_1 over each actual contingent concretum). Constructive. |
| `4ce57995` | `actualAbsenceHolderIsNecessaryVaryingGiver` | EM, P1′, P2δ, P3′, P4′, P5 ⊢ `256a5e0a` (a necessary concrete holder of the power for `q` whose giving varies). Composes `42da6b2d`. Only the necessity is derived; the varying conjunct is P2δ's own clause applied to `42da6b2d`'s witness. |
| `b1f6a376` | `varyingGiverGivesNecessaryPowerHolder` | `256a5e0a` ⊢ `b90ee2de` (assembly). Its bundle is `42da6b2d`'s with P2′ strengthened to P2δ, so it adds no warrant for `b90ee2de`. |
| `56024b0c` | `actualAbsenceRealizedByWithholding` | P1′, P2′, P4′, P5, holders give each `9f7b1778`, factive giving `3ef41442` ⊢ `b8a2a9e1` (the joint absence realized by the holder's withholding being from each). Constructive. |
| `84cc194c` | `withholdingGivesPowerOverEachActualContingent` | `b8a2a9e1`, withheld-giving bridge `d1593e5c` ⊢ `eb41bc9a`. |
| `2cc7e260` | `powerOverEachGivesNecessaryConcrete` | EM, `eb41bc9a`, concrete foundational being `c5da5e62` ⊢ `b19ffd92`. |
| `6eb4d324` | `prussDirectionNecessaryHolder` | EM, symmetric access (STMT-ACCESSIBILITY-SYMMETRIC), P4′, P5, `607e94cf`, `9c8e99e7`, `887d5efc` ⊢ `1af99585` (a necessary concrete being that, at a world lacking the actual contingents, has a power for `w`'s obtaining). |
| `95078e7b` | `prussDirectionNecessaryConcrete` | `1af99585` ⊢ `b19ffd92` (assembly). |
| `8ad1804e` | `prussPowerControls` | premise-free ⊢ `d8c38bb0` (laws and models below). After the challenge the certificate's type `Model.Controls` unfolds differently: `CollectiveWithoutDistributive` was rebuilt with the holder's power over the replacement's esse. The change is a strengthening and was re-verified; no frozen Challenge statement was weakened (invariant 12). |
| `9bba1325` | `twoMemberCollective` | premise-free ⊢ `bff9cbfa` (`Model.TwoMemberCollective`: collective without distributive at the level of `PowerFor`, with two actual contingents). |

**Sense bridge.** `6eb4d324` declares NECESSARY_8 → NECESSARY_2 with role
conclusion, the pattern of the #1889 projections. The symmetric-access
statement links the Kripke-box definition `153fcebf` (NECESSARY_8). What holds
is a definitional coincidence: `NecessaryAt m w x` is `Box m.frame (ExistsAt · x)
w` on the same `Frame`. Symmetry is a frame property, and no box occurs in the
proof. As in `specs/logical-necessity-profiles.toml`, none of `153fcebf`'s
sourced KB-embedding commitments (the possibilist constant domain) is imported.
`b19ffd92` does not presuppose symmetry, so this support for it holds only on
symmetric frames.

**P2δ carries the anti-fixed-exercise content.** Its added clause
`ExistsAt v y ∧ ¬ GivingSameIn F y w v` is the denial of `FixedGiver`
restricted to one world. Law 1 unfolds it in one step, and `4ce57995`'s
varying conjunct is its direct instantiation. The one-way exclusion is
therefore assumed through P2δ, not tested: without P2δ an inert fixed
necessary `g` holds P1′'s power and satisfies P2′ (Omission 1). P2δ's warrant
is one of two:

- the creator reading `9f7b1778`, from which law 5 derives it with factive
  giving. That reading is much stronger and is a dependency shared with the
  second support of `eb41bc9a` and the PGP link;
- the prima facie principle that exercise over existence shows in giving.
  This excludes exercise mediated through other frame fields (prevention, or
  motion through `MovesIn`/`CausesIn`), and preventive powers for an absence
  are ordinary.

### Laws (`Model.Laws`)

1. **One-way exclusion.** A fixed giver existing at `w` holds no power for `q`
   that satisfies P2δ.
2. P1′, P2δ, P4′ and P5 exclude that every being at `w` is a fixed giver.
3. **Collapse.** A fixed giver necessary at `w`, with factive giving, gives
   being at `w` only to beings necessary at `w`.
4. **Necessary fixed-output (deterministic) sources.** Suppose every concrete
   being contingent at `w` is given being at `w` by some necessary fixed giver,
   whether one source or an aggregate. With factive giving, no concrete being
   is then contingent at `w`: P5 fails. A chancy necessary source is not a
   fixed giver and is not covered.
5. Under the creator reading `9f7b1778`, with factive giving, P2′ and P5 give
   P2δ. Under that reading P2δ is not an extra assumption.
6. Withholding (`b8a2a9e1`) with P5 gives a two-way giver that is not a fixed
   giver.
7. **Pruss's direction relocates the abstention.** Take a being existing at
   `w` and at an accessible world lacking the actual contingents. If it gives
   one of them being at `w`, then with factive giving it is a two-way giver at
   `w`.
8. **The joint one.** Take a concrete being at `w` that, for each actual
   contingent concretum, exists at an accessible world lacking it. With EM it
   is necessary. No joint-absence premise is used.
9. With EM, `eb41bc9a` makes every concrete foundational being at `w`
   necessary. This is registered as `2cc7e260`.

### Models (structural surrogates, not metaphysical possibility)

| Model | Holds | Fails | Shows | Admissible on |
|---|---|---|---|---|
| `TheistNonvacuity` (`theistG`) | every premise of every argument; every conclusion; `g` a two-way giver, not fixed | — | nonvacuity of all nine arguments | classical theism (creation and conservation) |
| `CollectiveWithoutDistributive` (`replacementG`) | P1′, P2′, P2δ, P3′, P4′, P5, factive giving; `g` necessary with varying giving (it gives a replacement `d`) and POWER_OVER_ESSE_1 over `d` | holders-give-each; transfer; `eb41bc9a`; withholding; two-way (withholding form) | the transfer is not derivable from the collective power; omission models of the transfer (`a47906a5`) and of holders-give-each (`56024b0c`). Formally the transfer fails because `PowerOver` is unconstrained; the replacement structure only makes that choice admissible. One actual contingent, so collective and distributive coincide here; the separation shown is PowerFor → POWER_OVER_ESSE_1, already for one member | the thin reading of `PowerFor` only: the actual `c` is uncaused, and the holder's chain issues in a world with `d` instead. Not the Thomist reading (§3) |
| `DistributiveWithoutCollective` (`vanCleveG`) | a necessary `g` with POWER_OVER_ESSE_1 over each of two actual contingents, each contingent; with `gPower`, `g` also holds a power for `q` | P4′; P2′ for that power | power over each member's esse does not give the joint possibility: P4′ and initiator presence fail, though a power for `q` is held | — |
| `TwoMemberCollective` (`twoMemberG`, result `9bba1325`) | two actual contingents `c`, `d` (each possibly absent alone and jointly), a necessary `g` holding a power for exactly their joint absence; P1′, P2′, P3′, P4′, P5 | the varying-holder distributive grounding: no being at `w` has a power for `c`'s absence alone | the whole-to-member step for powers (C1's premise B applied to `PowerFor`) is not valid as typed; this model, unlike `replacementG`, separates collective from distributive | thin or causal reading alike (no giving occurs; structural) |
| `MutualAnnihilators` (`mutualG`) | distributive grounding with varying holders (`c` for `d`'s absence and conversely), initiator presence, P4′, P5 | any necessary being; the collective P1′ | the varying-holder distributive reading does not support the route | a world of mutually destructible contingents |
| `Omissions` 1–8 | all premises but one | that premise; the conclusion | P2δ (`4ce57995`), factive giving (`56024b0c`), the withheld-giving bridge (`84cc194c`), and symmetric access, grounding at the absence worlds, initiator presence there, concreteness there and P4′ (`6eb4d324`) are each needed | — |
| `Rivals` 1 (`inertG`) | a necessary fixed (inert) `g`; P4′, P5 | P1′, by the model's choice of no powers (`noPower`) | the inert necessary being. In general it is excluded only given P2δ (law 1): Omission 1 has an inert `g` holding P1′'s power | non-power modality with an idle necessary being |
| `Rivals` 2 (`necessitarianG`) | a necessary fixed `g` giving `c` being everywhere; factive giving; P4′ (vacuously, since the frame has an accessible world) | P5 | the necessary fixed-output (deterministic) source; a chancy necessary source is not covered | Spinoza-type necessitarianism |
| `Rivals` 3 (`theistG` with positive-outcome powers) | a necessary two-way `g`; P4′, P5, symmetric access; every premise and the conclusion of Pruss's direction | P1′ | positive-outcome-only powers reject P1′ but ground Pruss's direction | a powers theorist who denies powers for negative states |

## 3. Question 1: the transfer bridge

**Which reading P1′ needs: the collective one.** Distributive grounding with
varying holders, each member's absence grounded in another actual being's
power, holds in `MutualAnnihilators`, where no being is necessary. The
one-present-holder reading (one being present, for each member, at an
accessible world lacking it) suffices without any joint-absence premise
(law 8). This is C1's lesson again: the substantive content is that *one*
being is present wherever each actual contingent is absent. The readings only
shift which premise carries that content (P1′ with P4′, or the
one-present-holder clause). The one-holder POWER_OVER_ESSE_1 reading
(`eb41bc9a`) is different: it gives necessity only at a concrete foundational
being (law 9). Pruss's own "(perhaps a non-unitary cause which is an aggregate of
causes)" is not modelled: the holder `y` is one candidate (gap 4).

**Which reading the transfer needs: the distributive one**, one holder with
POWER_OVER_ESSE_1 over each member.

**Is the passage valid? No, as typed; it needs a bridge.**

- `CollectiveWithoutDistributive` satisfies every premise of the route and P2δ,
  yet the holder has no power over the actual contingent's esse.
- Formally the transfer fails because `PowerOver` is unconstrained. The
  replacement structure only makes that choice admissible: the holder has
  POWER_OVER_ESSE_1 over the replacement `d` it gives being, and none over the
  actual `c`.
- **Which reading of `PowerFor` the model adopts.** `replacementG` (and
  Omission 1) adopt the *thin* reading: a chain initiated by the holder whose
  outcome world satisfies `q`. A chain that produces a replacement array
  satisfies it.
- **What ad 1 shows, and what it does not.** Ad 1 shows that the absence is
  never the holder's *direct* effect ("non-existence has no direct cause").
  But ad 1 continues: "indirectly God can be the cause of things being reduced
  to non-existence, by withdrawing His action therefrom", and ad 3 makes
  annihilation "a mere cessation of His action". So for Aquinas the only way
  to cause an absence is to withdraw a giving: the creator/withholding
  reading. In `replacementG`, `g` never acts on `c`, so by ad 1 it causes
  `c`'s absence neither directly nor indirectly. Under Aquinas's principles
  the replacement holder has a power for `q` only on the thin reading. Ad 1
  therefore shows that the transfer needs a stated bridge; it does not support
  replacement as the Thomist reading.
- **Which step fails.** `replacementG` has one actual contingent, so
  collective and distributive coincide there: the separation it shows is
  `PowerFor` → POWER_OVER_ESSE_1, already for one member (on the thin
  reading). The whole-to-member step itself is separated by
  `TwoMemberCollective` (`9bba1325`): a power for the joint absence of two
  actual contingents is held while no being at `w` has a power for either's
  absence alone. The transfer thus spans two gaps, whole to member and
  `PowerFor` to POWER_OVER_ESSE_1, and both are open as typed.
- The note of the governing `PowerFor` DEF `bf7eddca` was amended to match,
  for the actual-indexed target only: replacement is a positive-production
  example on the thin reading, and the claim that only withholding is
  available holds on the causal reading only. For the global target (no
  contingent concretum ever exists) the abstention claim holds on both
  readings: a world satisfying it contains no concretum contingent there, so
  no replacement array of contingent beings satisfies it.
- The converse also fails (`DistributiveWithoutCollective`): power over each
  member's esse does not give the joint possibility.

**Where the bridge's warrant comes from.** The transfer's conclusion `eb41bc9a`
has a second support option, `56024b0c` + `84cc194c`. It uses:

- the creator reading `9f7b1778` (the holder gives each actual contingent
  being at `w`);
- factive giving;
- the withheld-giving bridge, which follows the respondeo of q.104 a.3 (free
  to give, free to withhold, hence able to annihilate).

So the distributive powers come from the holder's *giving* each member being,
together with the withholding world that P1′/P2′ supply. They do not come from
the collective power as such. In the replacement model the creator reading is
what fails.

**Formal link to the C2 crux.** Through `2cc7e260`, either support of
`eb41bc9a` reproduces PGP's verdict at C2's concrete foundational being
`c5da5e62`. The route uses no PGP and no Euclidean premise. This answers #1889
gap 3 for the route with Pruss's own premise: the link holds exactly under the
transfer, or under creator reading + factive giving + withheld-giving bridge.
The creator reading is a substantive theistic commitment, close to what the
route is meant to establish. The link therefore relocates the C2 crux; it
does not supply independent corroboration of PGP.

## 4. Question 2: powers to abstain

**The hypothesis, tested.** A one-way power cannot ground P1′; the power must
be two-way, or the abstention outcome must be grounded otherwise.

- **Confirmed, conditionally on P2δ's warrant.**
  - With P2δ, no fixed (one-way) giver holds P1′'s power (law 1). P1′, P2δ, P4′
    and P5 exclude a world of fixed givers only (law 2). These are direct
    instantiations of P2δ's anti-fixed clause (§2), not independent tests:
    without P2δ, an inert fixed giver holds P1′'s power (Omission 1).
  - The holder is a necessary concrete being whose giving varies across
    accessible worlds where it exists (`4ce57995` → `256a5e0a`). Only the
    necessity is derived; the variation is P2δ's clause.
  - P2δ's warrant is either the creator reading or the principle that exercise
    over existence shows in giving (§2). Under the creator reading P2δ is
    derivable from P2′ (law 5). The joint
    absence is then realized by withholding (`56024b0c`). The holder actually
    gives each actual contingent being at `w` and withholds it at the absence
    world: a two-way giver in the withholding form (law 6).
  - This matches the sources' structure, read as navigation:
    - Θ.5: with a rational potency it is "not necessary" to act, which is the
      act-or-refrain structure;
    - q.104 a.3 ad 3 makes annihilation "a mere cessation" of action, not an
      action;
    - the respondeo says a giver from natural necessity "could not annihilate
      anything".
    - Θ.2's "contrary effects" is an analogy only: there both contraries are
      produced by exercise ("the scientific man produces both the contrary
      effects"), whereas withholding is non-exercise.
  - So, under these premises, **the holder's giving has a two-way
    (withholding) exercise profile**. Whether the power for `q` and the giving
    are one Θ.2-type potency is untyped (gap 5). The batch does not represent
    a separate power whose exercise produces non-being; it shows that, under
    the creator reading, the joint absence is realized by non-exercise of a
    giving that is exercised at `w`.
- **Not confirmed.**
  - *Rational* (choice-decided). Varying or two-way giving is satisfied equally
    by chance and by a varying external condition. Θ.5's "desire or will" is
    the open bridge below.
  - *An external condition.* Any varying condition must be ungrounded in fixed
    necessary givers. Law 4 rules out every fixed necessary source, or
    aggregate of them, that gives all actual contingents being.
- **One part of the hypothesis is false as stated.** "Not a positive
  outcome" is not what excludes one-way powers. On the thin reading of
  `PowerFor`, the replacement model has a holder whose power for `q` is
  realized by a positive giving at the absence world (on the causal, Thomist
  reading it is not a power for `q` at all, §3). What excludes a one-way
  holder, given P2δ, is that its exercise is fixed by its existence (Θ.5 with
  no patient), not the polarity of the outcome.

**Modal collapse, stated exactly.** If a holder exists necessarily and its
exercise is fixed (one-way), then everything it gives being at `w` exists at
every accessible world (law 3, with factive giving). If it, or an aggregate of
such holders, gives being to every actual contingent concretum, P5 fails
(law 4; `Rivals` 2). The joint-absence possibility P4′ is then not lost: it
holds vacuously, because nothing concrete is contingent, provided some world
is accessible from `w` (seriality at `w`; true in `necessitarianG`, not in
general). What is lost is contingency itself. The brief's "P4′ fails" is
corrected here: P5 fails, and P4′ becomes idle. Laws 3–4 cover necessary
fixed-output (deterministic) sources only; a chancy necessary source is not a
fixed giver.

This is the frame/`GivesAt` counterpart of #555's `BeingCarriesAct` collapse
and #462's `fixedEffects`. The varying-giving conclusion is extensional: it
does not decide whether an intrinsically invariant act can have varying
*extrinsic* termini, which is #555's simplicity boundary (gap 6).

## 5. Question 3: rivals at matching scope

All rivals concern the same proposition `q` at the same frame and world.

1. **Inert necessary being** (`Rivals` 1).
   - P1′ fails *given P2δ*: an inert being is a fixed giver, and by law 1 no
     fixed giver holds a P2δ-power for `q`. Without P2δ an inert `g` can hold
     P1′'s power (Omission 1). The model `inertG` gets the failure from its
     choice of no powers (`noPower`).
   - Price: `q` (P4′) must be grounded by a non-power modal theory. This is
     the #1889 "too few potentialities" crux. No new discriminating evidence
     arises here.
2. **Necessary fixed-output (deterministic) source** (`Rivals` 2, laws 3–4).
   - P5 fails if the source gives every actual contingent being. P4′ holds
     vacuously given an accessible world.
   - A chancy necessary non-rational source (Pruss's "non-deterministically
     produces") is not a fixed giver and is not covered by laws 3–4.
   - The conflict is with P5 (`c76b6e2c`), the contingency of some actual
     concretum. A necessitarian who denies P5 is consistent at this scope.
   - Its standing is lowered relative to any account that keeps P5. It is not
     refuted.
3. **Powers theorist who denies powers for negative global states**
   (`Rivals` 3).
   - P1′ fails, so `q` needs another ground: a hybrid, or denial of P4′.
   - Under positive-outcome-only powers, Pruss's own direction survives. Its
     premises and conclusion hold in the same model. This rival is therefore
     answered by Pruss's direction, not by P1′.
4. **Pruss's own direction** (`6eb4d324`; #1889 gap 6, one-step powers).
   - *It avoids the abstention problem in content.* The power is for a
     positive outcome, `w`'s obtaining.
   - *Costs:*
     - Aristotelian grounding applied at a non-actual world;
     - initiator presence for a world-proposition;
     - symmetric access. Only the B part of S5 is used, a finding: Pruss
       invokes S5.
   - *It does not avoid the abstention fact.* The holder exists at the
     absence world without giving the actual contingents being. If it gives
     any of them being at `w`, it is a two-way giver there (law 7). Pruss's
     direction does not itself say that the holder gives anything at `w`. His
     "further argument" that `x` is the first cause of all contingent beings
     in `w0` is mentioned, not given, in the paper.

**Substantive objection to the will bridge (applied symmetrically).** The
target is the bridge from two-way giving to will (Θ.5: "something else that
decides ... desire or will").

- *Mechanism:* an indeterministic power whose exercise varies without choice
  satisfies `TwoWayGiverAt`.
- *Independent support:* propensity accounts of objective chance are developed
  positions (navigation only). Pruss's own definition allows chains "perhaps
  non-deterministic", and his conclusion speaks of a cause that
  "non-deterministically produces the historical universe".
- *Relevance:* the theist model is equally admissible on a chance reading. The
  types cannot tell them apart.

No substantive objection is identified to the inferences, to factive giving,
to P3′ or to P4′. The omission models show only that each premise is needed.

## 6. Provisional judgment

**What is supported, and on what condition.** Grant EM, P1′ in its collective
form, P3′, P4′ and P5. Then either of the following makes the holder a
necessary being whose giving varies across the worlds where it exists:

- P2δ, warranted by the prima facie principle that exercise over existence
  shows in giving (which excludes mediated or preventive exercise);
- or P2′ with the creator reading `9f7b1778` and factive giving (law 5), a
  dependency shared with the PGP link.

Under the creator branch, the holder's giving has a two-way (withholding)
exercise profile (law 6). Whether the power for `q` and the giving are one
Θ.2-type potency is untyped (gap 5).

The judgment is **conditional on one of these two warrants for P2δ**. P2δ is
not weak: it carries exactly the anti-fixed-exercise content, so the
conclusion that the holder is not a one-way source is only as strong as its
warrant. On that condition, the inferences are verified and the profile
agrees with Θ.5 (act or refrain) and q.104 a.3 as read; Θ.2 is an analogy.
It is a **candidate input** to stage two (plan, §7): a necessary being with
contingent giving.

**What is not supported.**

- The transfer as a bare collective-to-distributive passage: the countermodel
  on the thin reading of `PowerFor`; ad 1 shows the absence is never the
  holder's direct effect, so a stated bridge is needed (it does not make
  replacement the Thomist reading).
- The P2δ-free claim that no one-way source can hold P1′'s power (Omission 1).
- Choice rather than chance.
- Independent corroboration of PGP. The link to C2 holds only via the creator
  reading.

**Revision conditions (symmetric).**

- *Against the two-way reading:*
  - a typed account on which a fixed-exercise source grounds an unrealized
    joint absence through a varying external condition with its own ground;
  - a defence of a power for `q` whose exercise leaves the holder's giving
    unchanged, so that P2δ fails for a real case;
  - a reason why the replacement reading of `q` is the only coherent one. Then
    the creator reading fails and the C2 link drops.
- *For the will bridge:* a reason why chance cannot be exercised by a
  patientless necessary being. (The candidate "chance requires a chancy set-up
  with contingent conditions" was examined in
  [will-versus-chance.md](will-versus-chance.md) §5 and rejected: it names
  set-up chance, CHANCE_2, and begs the question against an indeterministic
  propensity, CHANCE_3.)
- *For the transfer:* a derivation of the creator reading from P1′ together
  with a principle that a member's possible absence is grounded in power over
  its being. That would make the transfer warranted, but it would share PGP's
  crux.

## 7. Stage-two connection (plan; not built)

- **Inputs:** `256a5e0a` (a necessary concrete varying giver) and `b8a2a9e1`
  (withholding). Under the creator reading `b8a2a9e1` gives a two-way giver
  (law 6).
- **Target:** STMT-GOD-HAS-WILL `66aecdd7` (`GodHasWill IsGod HasWill`, HAS_WILL_1
  at the capacity level) and its consumer of `WillFollowsIntellectReading`.
- **Missing bridges:**
  1. **Θ.5 bridge:** a necessary concrete being whose giving of being varies
     across accessible worlds where it exists, with no varying external
     condition, has will (HAS_WILL_1). It is blocked by the chance rival in §5.
     Continued in [will-versus-chance.md](will-versus-chance.md): built for
     sources with an invariant set-up (arguments C and D), with the restricted
     Θ.5 premise shown to be exactly the denial of CHANCE_3 in its scope; an
     intellect-and-one-power route discriminates without it.
  2. **Identification:** the holder is GOD_4 (uniqueness and the existing
     identification nodes).
- **Related existing work:** #435 and #462 (models of a necessary source with
  varying activity on `Ontic.Causes`), #555 `SimplicityCollapse`, and #1737/#1875
  `OptimalCreationChoice` (attempt [`8ab7f5a1`](../../corpus/attempts/divine-knowledge-choice-creation-1737.json)). Those certify consistency by
  models. This batch *derives* varying giving from a modal-grounding premise.
  Actual-root correspondence between `GivesAt` and those relations is not
  claimed.

## 8. Claim versus type

| Record | Prose | Lean type | Check |
|---|---|---|---|
| `5cf75a6b` P2δ | a power for `q` issues where its holder exists and gives otherwise | `∀ y, PowerFor w y q → ∃ v, access w v ∧ q v ∧ ExistsAt v y ∧ ¬ GivingSameIn F y w v` | existential in `v`; universal over holders; difference unspecified. The clause `ExistsAt v y ∧ ¬ GivingSameIn` is `¬ FixedGiver` restricted to one world: it carries the anti-fixed-exercise content |
| `3ef41442` | what is given being in a world exists there | `∀ v y x, GivesTo F v y x → ExistsAt v x` | all worlds, not only accessible ones |
| `9f7b1778` | holders give each actual contingent concretum being at `w` | `∀ y, PowerFor w y q → ∀ x, concrete x → ContingentAt w x → GivesTo F w y x` | at `w` only; not sole giving |
| `f0ac2f76` | transfer | `∀ y x, PowerFor w y q → concrete x → ContingentAt w x → PowerOverEsse F PowerOver y x` | POWER_OVER_ESSE_1 (broad) |
| `d1593e5c` | withheld giving is power over esse | `∀ y x v, GivesTo F w y x → access w v → ExistsAt v y → ¬ GivesTo F v y x → PowerOverEsse …` | needs an actual withholding world; freedom not typed |
| `607e94cf`, `9c8e99e7`, `887d5efc` | grounding, initiator presence, concreteness at each accessible world lacking the actual contingents, for `w`'s obtaining | `∀ v, access w v → NoActualContingentConcreteIn F concrete w v → [AristotelianGroundingFor / InitiatorPresentFor / PowerHoldersConcreteFor] F PowerFor v (fun u => u = w)` | one-step powers; the proposition is `u = w` |
| `eb41bc9a` | one holder with POWER_OVER_ESSE_1 over each | `∃ y, ExistsAt w y ∧ PowerFor w y q ∧ ∀ x, concrete x → ContingentAt w x → PowerOverEsse …` | no necessity or concreteness of `y` |
| `256a5e0a` | necessary concrete holder that varies its giving | `∃ y, concrete y ∧ ExistsAt w y ∧ NecessaryAt w y ∧ PowerFor w y q ∧ GivingVariesAt F w y` | nothing about what decides the variation |
| `b8a2a9e1` | the joint absence realized by withholding | `∃ y, ExistsAt w y ∧ PowerFor w y q ∧ ∃ v, access w v ∧ q v ∧ ExistsAt v y ∧ ∀ x, concrete x → ContingentAt w x → GivesTo F w y x ∧ ¬ GivesTo F v y x` | one withholding world for all members |
| `1af99585` | Pruss's direction's conclusion | `∃ y v, concrete y ∧ ExistsAt w y ∧ NecessaryAt w y ∧ access w v ∧ q v ∧ ExistsAt v y ∧ PowerFor v y (fun u => u = w)` | the power is held at `v`, not at `w` |
| `d8c38bb0` | laws and models | `Model.Controls` | structural surrogates only |

Every hypothesis of each theorem is a listed premise (bind-check). No source
is attributed. No statement says "God", "will", "choice" or "freedom".

## 9. Remaining gaps and next tests

1. The Θ.5 bridge from two-way giving to will, and the chance rival (§5, §7).
2. Identification of the holder with GOD_4. Built conditionally in
   [holder-root-identification.md](holder-root-identification.md): every
   holder is an actual root given existence at `w` and NAR (necessary actual
   concreta are underived), then the common GOD_4 root or at most one root.
3. A tensed variant over `IsAt` (from #1889 gap 2). Withholding in time,
   annihilation of something existing, is not represented; `GivesTo` is "at
   some moment".
4. Pruss's aggregate holder ("a non-unitary cause"). Law 4 covers aggregates
   of fixed givers only.
5. Intensional powers: one potency for contraries (Θ.2) is not typed. Only
   exercise profiles are.
6. Simplicity: whether varying extrinsic giving is compatible with one
   intrinsic act (#555 `BeingCarriesAct`). It is not modelled here.
7. Iterated powers (Pruss) and the "further argument" to a first cause of all
   contingents in `w0`.
8. The warrant of the creator reading `9f7b1778` independent of the route.
9. `truth countermodel` does not handle `CausalityFrame` parameters, so all
   models are hand-written.

## 10. Cross-lane edits

- **`corpus/definitions/bf7eddca-8291-4744-8470-379babcd7781.json`** (the
  `PowerFor` DEF of #1889): its note gained an amendment distinguishing the
  thin reading (replacement is a positive-production example) from the causal
  reading (only withholding counts, by q.104 a.3 ad 1 and ad 3), scoped to the
  actual-indexed target; for the global target the abstention claim holds on
  both readings. Definition text and Lean declaration are unchanged. Made
  after the semantic challenge (P1-2) and scoped after its re-check (N2).
- **`docs/notes/modal-grounding-frameworks.md`** (#1889, coordinator-owned;
  authorized for this one pointer): a short *later scoping* pointer after
  "The only available example is an abstention" (§1), referring to the
  `bf7eddca` amendment with the same scope. Affected downstream use of the
  amendment.
- disambiguations `197f0097`, `f5dda05f` and `88a8fba7` are linked, not
  edited;
- `corpus/definition-status.json` gained only this module's four entries;
  other stale entries were not refreshed.

## 11. Fixed-roster aggregation and one-recipient giving (2026-11-26)

Write (w) for the reading world and (A_w) for its rigid roster of concrete
beings with CONTINGENCY_1. Roster membership requires existence at (w) and
an accessible world where the same bearer is absent. A world's population
may vary. Accessibility here admits whole histories for the selected modal
reading. An edge conveys neither a time step nor a causal mechanism.
Concreteness is the supplied world-independent predicate throughout.

The [fixed-roster batch](../../specs/modal-power-holder.toml) supplies three
conditional routes on this carrier. The Lean results reuse finite omission
from #533 and the replacement witness from #1889. Their conclusions feed
the ordinary Pruss route and its global variant (including the local-access
route of #2022), and the varying-giver route to `b90ee2de`.

| Target | Claim and type boundary | Result |
|---|---|---|
| `18e5bd4e`, some successor lacks all of (A_w) | A successor exists, (A_w) has a finite list cover, and every pair of successors has another successor whose (A_w)-population is contained in both. Individual absence witnesses are supplied by membership in (A_w). The finite list constrains neither the ambient domain nor other worlds' total populations. | [`jointAbsenceOfFiniteRoster`](../../corpus/results/e165bc1e-b947-4b8d-a787-136661f39dbe.json) |
| `0dc833c1`, some successor has no local contingent concreta | Take the same witness (v) of joint absence. Require that concrete contingents at an accessible joint-absence world already exist at (w), plus transitivity at (w). A hypothetical local contingent at (v) would exist at (w) and have an absence witness reachable from (w). It would belong to (A_w) and be absent at (v), contradicting its local contingency. Necessary concreta can still exist at (v). | [`globalAbsenceOfRosterCoverage`](../../corpus/results/7eb6cabd-d805-4db9-8b18-1f73d45553f5.json) |
| `5cf75a6b`, P2δ | Each holder gives at least one (A_w)-member at (w), with the recipient allowed to depend on the holder. P2′ gives a single accessible (v) with joint absence and the same holder present. Factive giving excludes its giving to that same recipient at (v), so the sets of recipients differ. `GivesTo` means there is some time of giving in the world. | [`differentGivingOfOneRecipient`](../../corpus/results/313d3625-83d0-4767-86c2-d6e4ab00a7d1.json) |
| Both failures on equivalence frames | Universal access on the three populated profiles ({a,b}, {a}, {b}) gives two individually contingent actual beings and a contingent positive conjunction. Every successor has a resident, so joint absence and amalgamation fail. On the two-world swapped profile, (A_w={a}) and the other world has only (b), itself contingent there. Joint absence holds, while roster coverage and global absence fail. The causal and giving slots play no role. | [`controls`](../../corpus/results/4eda66b6-a2c1-439e-984f-f22a0c747727.json) |

### Which modal step needs a new commitment?

- **Aggregation.** The exact missing compatibility is a successor in the
  intersection of every roster member's absence condition. The finite route
  uses a sufficient pair rule on **projected** populations. It needs common
  lower bounds under containment, with no exact intersection or restriction
  on outside beings. Finite omission composes the rule finitely. The existing
  #533 infinite-tail control has an amalgamating population and witnesses for
  every finite omission, while an inhabitant survives at every world. An
  infinite actual roster does not by itself require a limit or compactness
  principle: if some accessible world has only finitely many present roster
  members, applying finite omission to those members and amalgamating the
  result with the chosen world leaves an empty common subpopulation, even when
  infinitely many roster members exist at the reading world. A limit or
  compactness principle is needed only when no such world is available.
  `ActualRosterFinite` remains an explicit sufficient premise of the
  registered theorem. Conversely, a joint-absence world itself witnesses the
  pair rule for every pair, since its projected population is empty; on the
  finite-roster and successor assumptions, amalgamation and joint absence are
  therefore equivalent. The forward proof is a genuine finite induction, but
  the pair rule's warrant cannot exceed that of joint absence. What could
  independently motivate it is an account of the roster's existence
  conditions on which the absence conditions of distinct contingents never
  exclude one another. Granting each absence independently has prima facie force for ordinary
  destructible objects. Extending a compatibility rule from these cases to
  all concrete contingents requires information about how their existence
  conditions interact.
- **Big conjunctive fact.** A Leibnizian candidate with truth condition
  “every member of (A_w) exists” is false whenever a member is missing. Its
  contingency is therefore compatible with at least one actual-roster member
  being present at each world, with the member varying by world, as the first
  model shows. A fact with truth condition “some member
  of (A_w) exists” has the required scope: its possible falsity is exactly
  the joint-absence claim in the classical reading. A total fact that records
  all positives and negatives can also change by variation of one conjunct.
  An explanation of the actual total fact would still need an explicit
  alternative whose truth conditions say every actual member is absent.
  These are analyst readings of candidate facts, with historical attribution
  deferred. See the corpus result `JointContingencyLocalization.equivalence`
  for the existing distinction between failure of a joint positive condition
  and failure of its members.
- **S5 and replacement.** Reflexivity and Euclideanness constrain the edges.
  Neither countermodel relies on missing edges between admitted histories.
  The forward transfer from local nonexistence at a successor to possible
  nonexistence at (w) needs only the inclusion of that successor's outgoing
  edges in (w)'s. The registered route assumes this at every successor and
  tests coverage only at joint-absence worlds. Its proof uses coverage and
  the inclusion only at the chosen witness. In a shared equivalence
  component, a candidate present only at a nonactual history is a concrete
  mechanism for replacement because the accessible actual history witnesses
  its nonexistence. A policy limiting the population of those histories has
  content beyond S5. The direct joint-absence premise remains available even
  to a theory allowing replacement.
- **Third Way.** Under the hypothesis that each actual concretum is
  contingent, joint absence removes the actual concrete roster in one
  alternative. The global conclusion removes local **contingent** concreta
  there. To infer that no concrete being exists there would also require
  that any concretum present there is contingent **there**, or a corresponding
  exclusion of necessary survivors. An empty history is a separate claim
  from an empty time followed by production within the actual history.
  The latter argument needs the same-history temporal realization, a rule
  excluding new being after the specified empty time, and a link to actual
  present existence. See [the temporal collective-possibility
  comparison](collective-possibility-route-boundary.md). The Kenny/Mackie
  quantifier-shift concern is evaluated here as a logical objection, with
  historical attribution deferred. Its strongest positive counteraccount is
  a succession or family of admissible populations in which at least one
  member always occupies a populated alternative although each actual member
  can be omitted. Its precise rejection is aggregation (or the direct
  collective possibility), and the finite model settles the alleged
  entailment even with rigid identity and finite roster. The model supplies
  no reason by itself to assert that metaphysical histories obey the
  permanent-population policy.

### Which holder, and when does it give?

- `95bf8780` conditionally supplies a holder **at (w)** for the coordinated
  outcome. The initiator-premise `906f5c39` is a restriction on how that
  power is realized. On the tenseless reading its motivation is that a
  chain-initiator is in the history of its own initiating event. Then
  `a6906cab` puts the holder in the concrete kind. Together with actual
  contingency, actual joint absence and explicit excluded middle, the
  [existing holder result](../../corpus/results/42da6b2d-00b5-4451-81bc-01f155737144.json)
  derives NECESSARY_2 for this same witness within the model: if it
  could be absent, it would be in the actual roster it survives. This
  argument needs neither S5 nor exclusion of replacements. The worked
  inference is existential; the separate `b517ca3e` concerns **every**
  holder at (w). Its serious-actualist reading remains a live direct
  commitment. A nonconcrete initiator is excluded only by the chosen
  causal-concreteness bridge. Neither occupancy of a world nor a
  world-relative power predicate by itself gives occupancy at each of
  that world's times.
- The `9f7b1778` creator premise gives every recipient. Its known use in
  law 5 can be restricted to one recipient for the P2δ route. The older
  universal route for withholding **each** recipient and the collective to
  distributive POWER_OVER_ESSE_1 bridge `f0ac2f76` still need their own
  warrants. For `d1593e5c`, actual giving in (w) and absence of the same
  giver's giving at (v) are the typed antecedent facts. They do not show
  that withholding by this giver makes the recipient cease, as opposed
  to coinciding with its absence. The existing ST I q.19 a.10 support
  (`988f35e6`, #2018) leaves dependency on the giver's continued exercise
  open. #2029's momentary-giving routes supply some giver at each relevant
  received presence under their own bridges. They leave open whether it
  is this holder through time and whether its withdrawal suffices for
  cessation. The uniqueness result of #2016 is scoped to roots. Applying it
  to the present recipient needs both candidate explanations classified
  under that scope. The earlier
  [holder/root controls](holder-root-identification.md) exhibit a necessary
  holder grounded through another, so merely reusing uniqueness is
  insufficient.
- **Necessary natural ground.** The rigid-bearer reading of a necessary
  initial substrate plus law-governed objective chance retains the same
  initial candidate across accessible histories while allowing distinct
  downstream populations. It can accept the necessary-holder existence
  conclusion if the substrate initiates the relevant outcomes, while
  rejecting the inference from variable recipients to intellectual
  selection. On a productive-only construal of its power, it explains
  downstream events without claiming a power whose exercise directly
  produces universal withholding. That construal contests P1′ as applied
  to the negative outcome, and an onset-only construal also contests
  continuing giving. The motivation is the positive account of a common
  start and alternative chance developments, with the restricted
  accessibility and rigid identity assumptions stated in
  [the existing Oppy assessment](fixed-initial-history-535.md#oppys-modal-readings-in-the-pinned-chapter).
  The modal roster controls do not encode chance, laws or intellect.
  The source's fixed-output variant faces a different cost: with
  factive giving, a necessary source that gives to the same recipients
  wherever it exists would make those actual recipients necessary.
  That conflicts with retaining actual contingency of any such recipient.
  The chance variant survives that test.

**Provisional assessment.** World-bounded initiator presence and factive
giving have direct motivation on the selected meanings. The finite
aggregation result isolates a substantial population commitment. The
positive conjunction and frame axioms do not warrant it and the replacement
model gives a concrete reason to keep the global step separate.
Aristotelian grounding of this particular negative outcome and actual
giving by the selected holder remain the load-bearing causal commitments.
An impersonal chance source still accounts for variation at the typed
scope. The next discriminating test is a received effect at a specified
continued time whose contemporaneous giver can be identified with the
modal holder using an independently justified dependence and source
criterion. Test whether continued presence requires that giver's same
exercise even with alternative productive or sustaining sources admitted.
That is the point where a positive sustainment account and an onset-only
account differ. For the collective premise, reopen a stronger assessment
when there is a warranted admissibility rule combining absence conditions
for the actual roster, including, if the roster is infinite, either a limit
principle or an accessible world with finitely many present roster members.
Formal results supply conditional support options. They establish
no framework premise.

Research records for this checkpoint cover
[roster aggregation and replacement](../../corpus/attempts/modal-power-holder-roster.json),
[holder identity](../../corpus/attempts/modal-power-holder-identity.json), and
[actual giving](../../corpus/attempts/modal-power-holder-giving.json).
