# The power premises of the route with Pruss's own premise (2026-11-23)

Issue #1887, continued (coordinator slice 2: "the warrant for the Pruss
route's power premises"), God-existence stage of the #143 root.

**Batch.** `specs/pruss-power-premises.toml`; vocabulary
`TruthCore.Modal.PrussPowerPremises`; results
`TruthCore.Results.Modal.PrussPowerPremises`. Attempt
`daf87aca-9ae5-44e0-b56c-b37712ec2710`.

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
| two-way giver (withholding form) | `TwoWayGiverAt F w y` | `e006ddeb` | `y` gives `x` being at `w` and, existing at an accessible world, does not give it there. Θ.2's "capable of contrary effects", read on world-relative giving. |

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
- the *distributive* reading is one of two:
  - *varying holders*: each member's possible absence is grounded in some
    being's power for that member's absence (`EachActualAbsenceGrounded`);
  - *one holder*: POWER_OVER_ESSE_1 over each member
    (`SomeHolderHasPowerOverEachActualContingent`).
- the transfer bridge is the analogue of C1's premise B (whole to members).

No new disambiguation record was created; `197f0097` is linked from the
transfer statements and the controls.

## 2. Results

All verified (`verify-result.sh`; bind-check 9 bound, 0 mismatch). New open
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
| `4ce57995` | `actualAbsenceHolderIsNecessaryVaryingGiver` | EM, P1′, P2δ, P3′, P4′, P5 ⊢ `256a5e0a` (a necessary concrete holder of the power for `q` whose giving varies). Composes `42da6b2d`. |
| `b1f6a376` | `varyingGiverGivesNecessaryPowerHolder` | `256a5e0a` ⊢ `b90ee2de` (assembly). |
| `56024b0c` | `actualAbsenceRealizedByWithholding` | P1′, P2′, P4′, P5, holders give each `9f7b1778`, factive giving `3ef41442` ⊢ `b8a2a9e1` (the joint absence realized by the holder's withholding being from each). Constructive. |
| `84cc194c` | `withholdingGivesPowerOverEachActualContingent` | `b8a2a9e1`, withheld-giving bridge `d1593e5c` ⊢ `eb41bc9a`. |
| `2cc7e260` | `powerOverEachGivesNecessaryConcrete` | EM, `eb41bc9a`, concrete foundational being `c5da5e62` ⊢ `b19ffd92`. |
| `6eb4d324` | `prussDirectionNecessaryHolder` | EM, symmetric access (STMT-ACCESSIBILITY-SYMMETRIC), P4′, P5, `607e94cf`, `9c8e99e7`, `887d5efc` ⊢ `1af99585` (a necessary concrete being that, at a world lacking the actual contingents, has a power for `w`'s obtaining). |
| `95078e7b` | `prussDirectionNecessaryConcrete` | `1af99585` ⊢ `b19ffd92` (assembly). |
| `8ad1804e` | `prussPowerControls` | premise-free ⊢ `d8c38bb0` (laws and models below). |

**Sense bridge.** `6eb4d324` declares NECESSARY_8 → NECESSARY_2 with role
conclusion, the pattern of the #1889 projections. The symmetric-access
statement links the Kripke-box definition `153fcebf` (NECESSARY_8). The
conclusion's `NecessaryAt` is the box of existence over that same frame.

### Laws (`Model.Laws`)

1. **One-way exclusion.** A fixed giver existing at `w` holds no power for `q`
   that satisfies P2δ.
2. P1′, P2δ, P4′ and P5 exclude that every being at `w` is a fixed giver.
3. **Collapse.** A fixed giver necessary at `w`, with factive giving, gives
   being at `w` only to beings necessary at `w`.
4. **Necessary non-rational sources.** Suppose every concrete being contingent
   at `w` is given being at `w` by some necessary fixed giver, whether one
   source or an aggregate. With factive giving, no concrete being is then
   contingent at `w`: P5 fails.
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
| `CollectiveWithoutDistributive` (`replacementG`) | P1′, P2′, P2δ, P3′, P4′, P5, factive giving; `g` necessary with varying giving (it gives a replacement `d`) | holders-give-each; transfer; `eb41bc9a`; withholding; two-way (withholding form) | the transfer is not derivable from the collective power; omission models of the transfer (`a47906a5`) and of holders-give-each (`56024b0c`) | a replacement reading: the actual `c` is uncaused, and the holder's chain issues in a world with `d` instead (structural; see §3) |
| `DistributiveWithoutCollective` (`vanCleveG`) | a necessary `g` with POWER_OVER_ESSE_1 over each of two actual contingents, each contingent | P4′; P2′ even for a holder of every power | power over each member's esse gives neither the joint possibility nor a power for it | — |
| `MutualAnnihilators` (`mutualG`) | distributive grounding with varying holders (`c` for `d`'s absence and conversely), initiator presence, P4′, P5 | any necessary being; the collective P1′ | the varying-holder distributive reading does not support the route | a world of mutually destructible contingents |
| `Omissions` 1–8 | all premises but one | that premise; the conclusion | P2δ (`4ce57995`), factive giving (`56024b0c`), the withheld-giving bridge (`84cc194c`), and symmetric access, grounding at the absence worlds, initiator presence there, concreteness there and P4′ (`6eb4d324`) are each needed | — |
| `Rivals` 1 (`inertG`) | a necessary fixed (inert) `g`; P4′, P5 | P1′ | the inert necessary being | non-power modality with an idle necessary being |
| `Rivals` 2 (`necessitarianG`) | a necessary fixed `g` giving `c` being everywhere; factive giving; P4′ (vacuously) | P5 | the necessary non-rational source | Spinoza-type necessitarianism |
| `Rivals` 3 (`theistG` with positive-outcome powers) | a necessary two-way `g`; P4′, P5, symmetric access; every premise and the conclusion of Pruss's direction | P1′ | positive-outcome-only powers reject P1′ but ground Pruss's direction | a powers theorist who denies powers for negative states |

## 3. Question 1: the transfer bridge

**Which reading P1′ needs: the collective one.** Distributive grounding with
varying holders, each member's absence grounded in another actual being's
power, holds in `MutualAnnihilators`, where no being is necessary. The
one-holder distributive reading suffices without any joint-absence premise
(law 8). This is C1's lesson again: the substantive content is that *one*
being is present wherever each actual contingent is absent. The readings only
shift which premise carries that content (P1′ with P4′, or the one-holder
clause). Pruss's own "(perhaps a non-unitary cause which is an aggregate of
causes)" is not modelled: the holder `y` is one candidate (gap 4).

**Which reading the transfer needs: the distributive one**, one holder with
POWER_OVER_ESSE_1 over each member.

**Is the passage valid? No, as typed; it needs a bridge.**

- `CollectiveWithoutDistributive` satisfies every premise of the route and P2δ,
  yet the holder has no power over the actual contingent's esse.
- Mechanism: `PowerFor w y q` asks only for a chain whose outcome world
  satisfies `q`. A chain that produces a replacement array satisfies it while
  the actual contingent's absence there is not the holder's effect. This
  failure has independent support in the theist's own principle: "non-existence
  has no direct cause" (q.104 a.3 ad 1).
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

- **Confirmed under explicit premises.**
  - With P2δ, no fixed (one-way) giver holds P1′'s power (law 1). P1′, P2δ, P4′
    and P5 exclude a world of fixed givers only (law 2).
  - The holder is a necessary concrete being whose giving varies across
    accessible worlds where it exists (`4ce57995` → `256a5e0a`).
  - Under the creator reading P2δ is derivable from P2′ (law 5). The joint
    absence is then realized by withholding (`56024b0c`). The holder actually
    gives each actual contingent being at `w` and withholds it at the absence
    world: a two-way giver in the withholding form (law 6).
  - This matches the sources' structure, read as navigation:
    - Θ.2 places the privative contrary inside the *rational* power ("by
      denial and removal");
    - q.104 a.3 ad 3 makes annihilation "a mere cessation" of action, not an
      action;
    - the respondeo says a giver from natural necessity "could not annihilate
      anything".
  - So P1′'s power, if real, is best read as the **privative side of a two-way
    power whose positive side is exercised at `w`**. It is not a separate power
    whose exercise produces non-being, which would be a one-way power for a
    negative outcome.
- **Not confirmed.**
  - *Rational* (choice-decided). Varying or two-way giving is satisfied equally
    by chance and by a varying external condition. Θ.5's "desire or will" is
    the open bridge below.
  - *An external condition.* Any varying condition must be ungrounded in fixed
    necessary givers. Law 4 rules out every fixed necessary source, or
    aggregate of them, that gives all actual contingents being.
- **One part of the hypothesis is false as stated.** "Not a positive
  outcome" is not what excludes one-way powers. The replacement model has a
  holder whose power for `q` is realized by a positive giving at the absence
  world. What excludes a one-way holder is that its exercise is fixed by its
  existence (Θ.5 with no patient), not the polarity of the outcome.

**Modal collapse, stated exactly.** If a holder exists necessarily and its
exercise is fixed (one-way), then everything it gives being at `w` exists at
every accessible world (law 3, with factive giving). If it, or an aggregate of
such holders, gives being to every actual contingent concretum, P5 fails
(law 4; `Rivals` 2). The joint-absence possibility P4′ is then not lost: it
holds vacuously, because nothing concrete is contingent. What is lost is
contingency itself. The brief's "P4′ fails" is corrected here: P5 fails, and
P4′ becomes idle.

This is the frame/`GivesAt` counterpart of #555's `BeingCarriesAct` collapse
and #462's `fixedEffects`. The varying-giving conclusion is extensional: it
does not decide whether an intrinsically invariant act can have varying
*extrinsic* termini, which is #555's simplicity boundary (gap 6).

## 5. Question 3: rivals at matching scope

All rivals concern the same proposition `q` at the same frame and world.

1. **Inert necessary being** (`Rivals` 1).
   - P1′ fails: an inert being is a fixed giver, and by law 1 no fixed giver
     holds a P2δ-power for `q`.
   - Price: `q` (P4′) must be grounded by a non-power modal theory. This is
     the #1889 "too few potentialities" crux. No new discriminating evidence
     arises here.
2. **Necessary non-rational source with necessary output** (`Rivals` 2,
   laws 3–4).
   - P5 fails if the source gives every actual contingent being. P4′ holds
     vacuously.
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

**What is supported.** Granting P1′ in its collective form, any of the
following makes the holder a necessary being whose giving varies across the
worlds where it exists:

- the minimal exercise condition P2δ;
- or the creator reading with factive giving.

The holder is not a one-way source. Its power for the joint absence is the
privative side of a two-way power exercised at `w`.

This is moderately supported. The inferences are verified. P2δ is weak and,
under the creator reading, derivable. The reading agrees with Θ.2, Θ.5 and
q.104 a.3 as read. It is a horizontal link to stage two: necessary being with
contingent giving.

**What is not supported.**

- The transfer as a bare collective-to-distributive passage: countermodel,
  plus the theist's own "no direct cause of non-existence".
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
  patientless necessary being, for example if chance requires a chancy set-up
  with contingent conditions. This would strengthen the Θ.5 bridge.
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
  2. **Identification:** the holder is GOD_4 (uniqueness and the existing
     identification nodes).
- **Related existing work:** #435 and #462 (models of a necessary source with
  varying activity on `Ontic.Causes`), #555 `SimplicityCollapse`, and #1737/#1875
  `OptimalCreationChoice` (attempt `8ab7f5a1`). Those certify consistency by
  models. This batch *derives* varying giving from a modal-grounding premise.
  Actual-root correspondence between `GivesAt` and those relations is not
  claimed.

## 8. Claim versus type

| Record | Prose | Lean type | Check |
|---|---|---|---|
| `5cf75a6b` P2δ | a power for `q` issues where its holder exists and gives otherwise | `∀ y, PowerFor w y q → ∃ v, access w v ∧ q v ∧ ExistsAt v y ∧ ¬ GivingSameIn F y w v` | existential in `v`; universal over holders; difference unspecified |
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
2. Identification of the holder with GOD_4.
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

None to records owned by other lanes:

- disambiguations `197f0097`, `f5dda05f` and `88a8fba7` are linked, not
  edited;
- `corpus/definition-status.json` gained only this module's four entries;
  other stale entries were not refreshed.
