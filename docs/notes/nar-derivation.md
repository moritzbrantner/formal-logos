# Deriving NAR: the root's withholding, grounding-to-giving bridges and the will route (#1926 phase 3)

Outcome label (rigor contract 6): **a new bridge**, conditional. NAR
(`43651417`) is now the conclusion of a verified, non-transcription argument
(N1), so the computed frontier counts it as closed. That is a formal closure,
**not establishment**.

- N1's premise (a) restates NAR under the companions of law 3.
- N2 and N3 are two routes to (a). Neither restates NAR.
- The decisive content moves into the new open premises recorded below, with
  their warrant.

Lean: `TruthCore.Causality.NarDerivation` (vocabulary, laws, models) and
`TruthCore.Results.Causality.NarDerivation` (Solution). Spec:
`specs/nar-derivation.toml`. Every argument is an analyst formulation,
attribution deferred. Every model is a finite structural surrogate on #1897's
frames; it witnesses only its formal interpretation, never metaphysical
possibility. `truth countermodel` does not handle `CausalityFrame` parameters,
so all models are hand-written.

## 1. Target and question

- **Premise targeted.** NAR, `43651417`: every NECESSARY_2 actual concretum
  is an actual root of the selected grounding relation `G`. In
  [holder-root-identification.md](holder-root-identification.md) (#1944) it
  carries the step from "every holder is necessary" to "every holder is the
  root", and through it intellect (`813a9181`) and will (`66aecdd7`) at the
  holder. Its warrant there: direct prima facie plausibility, judged moderate.
- **Strongest standing rival.** The necessary-through-another holder: a
  NECESSARY_2 being grounded by the root that holds the two-way power itself.
- **Question** (#1944 gap 1, as corrected by review). Can NAR be derived from
  - (a) the root's giving to every `G`-grounded concretum is two-way, and
  - (b) an explicit `G`-to-giving bridge?

  And does (a) follow from one power, an invariant set-up and simplicity
  through a uniform mode of giving (#555; #1897 gap 6)?

## 2. Fixed meanings

| Term | Formal content | Status |
| --- | --- | --- |
| fixed toward `x` (NECESSITATE_5, DEF `02aa24f8`) | `FixedTowardAt F w y x`: gives `x` being at `w` and at every accessible world where `y` exists | definition |
| two-way toward `x` (DEF `8c945061`) | `TwoWayTowardAt`: exists at `w`, gives `x` at `w`, withholds it at an accessible world where `y` exists | definition |
| uniform mode (DEF `1c4078eb`) | `UniformGivingModeAt`: two-way toward one effect ⇒ two-way toward each effect given at `w` | definition |
| required by `y`'s end (DEF `90719cb5`) | `EndRequires y x`, a primitive parameter: the teleological means-to-end relation | primitive |
| (b1) | `ActualRootsGiveGroundedHere`, `2dd1f217` | new OPEN bridge |
| (b2) | `ActualRootsGiveNecessaryGroundedWherever`, `eeccc832` | new OPEN bridge |
| (a) | `ActualRootsWithholdEachGrounded`, `fbd0a6d3` | new OPEN premise; derived by N2 and N3 |
| necessary roots | `ActualRootsNecessary`, `d164f730` | new OPEN premise |
| uniformity at the root | `ActualRootsGiveUniformly`, `19f2e094` | new OPEN premise |
| one power at the root | `ActualRootsOnePower`, `06145e71` | new OPEN premise |
| WN | `RationalFixedGivingIsRequired`, `0266eac2` | new OPEN premise |
| SS | `ActualRootsEndRequiresNoOther`, `85f3fea2` | new OPEN premise |

`FixedTowardAt` is appended to the NECESSITATE disambiguation `5836e1f6` as
NECESSITATE_5. It is per effect; NECESSITATE_2 (`FixedGiver`) fixes all of a
giver's effects. A giver can therefore be fixed toward one effect and two-way
toward another (a *mixed-mode* giver).

**Formal form of (a).** (a) says that the root withholds each grounded actual
concretum at some accessible world where the root exists. It omits "gives `x`
at `w`", which (b1) supplies in N2 and N3; N1 uses only the withholding
clause, together with (b2).

**The bridge (b), split into what is used.** #1944 gap 1's bridge (b) ("a
`G`-grounded concretum exists at `v` only if its `G`-ground gives it being at
`v`") is not registered in its general form. The arguments use two parts, each
only at the root:

- **(b1)**, local: every actual root gives being at `w` to each existing being
  it grounds there. N2 and N3 use it, and law 2.
- **(b2)**, rigidity at the root for necessary grounded beings: every actual
  root gives each NECESSARY_2 being it grounds being at every accessible world
  where the root exists. Only N1 uses it, and law 3.

The general form would also assert rigidity for contingent grounded beings
and for every ground. That has a substantive objection: a contingent being can
exist at an accessible world while sustained there by another source, or with
no sustainer at all (#1897's `replacementG`; ordinary cases of several
sustainers). It would also allow giving at worlds where the ground is absent.
Neither restricted form has these features, and no argument needs them. No
strength order is registered, because the general form is not a statement
here.

### Semantic grounding

**(b1) and (b2), from grounding to giving.** These are the only premises that
join `G` to giving (rigor contract 5; #1626).

- *Meaning:*
  - (b1): what the root grounds, it gives being, where both exist.
  - (b2): the root keeps giving being to a necessary being it grounds, at
    every accessible world where the root exists.
- *(b1) reads grounding by the root as productive dependence for being,* the
  sustaining CAUSE_OF_BEING sense of `88a8fba7`.
- *(b2) is a rigidity claim,* restricted to necessary grounded beings and to
  worlds where the root exists.
- *Examples:*
  - classical conservation: God gives each creature being wherever it exists
    (ST I q.104 a.1, navigation);
  - Avicenna's First, as standardly reported, gives the first intelligence
    being in every world.
- *Non-examples, where (b1) fails:* grounding as non-productive metaphysical
  dependence. A singleton depends on its member, but the member does not give
  the singleton being. A fact is grounded in its constituent facts.
- *Rival to (b1):* `G` read as non-productive dependence. On the composed
  routes, `G` is tied to esse-causation in one direction by `cb1cdea9`: a
  distinct esse-cause is an actual concrete ground. (b1) is a bridge in the
  converse direction, at the root. A grounding relation whose root edges
  include non-productive dependence would falsify it.
- *Rival to (b2):* a necessary being that its actual root grounds but does
  not give being at some world where the root exists, so that it is sustained
  there by another source or by none. No developed defence of this was
  identified. The contingent-sustainer cases above do not bear on (b2), which
  is restricted to necessary grounded beings.
- *Structure:* neither assumes an order property of `G`.

**`EndRequires`, required by a being's own end** (DEF `90719cb5`).

- *Meaning:* the **teleological means-to-end relation**. `x` is a means
  without which the good that `y`'s appetite is ordered to cannot be
  attained. This is the food-for-life, ship-for-voyage sense of ST I q.19 a.3
  and q.82 a.1 (paraphrase, navigation). It is a primitive parameter,
  constrained only by WN and SS.
- *Not strict modal co-existence.* That `x` exists at every world where `y`
  exists, or that `x` exists necessarily, does not make `EndRequires y x`
  true.
- *Examples:* an animal's flourishing requires food; a voyage requires a ship.
- *Non-examples:* a generous person's goodness does not require the particular
  gifts given. On classical theism, the divine goodness requires no creature.
- *Distinct from:* grounding and causing. `x` can be required by `y`'s end
  without either grounding the other.
- *Structural properties:* none assumed.
- **Rejected reading: strict modal.** Read `EndRequires y x` as "`x` exists at
  every accessible world where `y` exists" (`StrictModalRequirement`). Then
  every NECESSARY_2 being is required by every end, and WN is trivial for
  necessary effects. With a common root, SS alone then yields NAR: law 6,
  verified. So N3 would beg the question, and the emanationist rival would
  deny SS rather than WN. The assessments in §5–§7 hold **only on the
  means-to-end reading**.
- *OPEN:*
  1. a criterion of "cannot be attained without" that is not covertly modal,
     i.e. that does not reduce to co-existence across worlds;
  2. whether "end" applies univocally to a first source;
  3. whether the necessary diffusion of the good counts as the end requiring
     its effects, or as a fixity without requirement. The second is how WN's
     rival is stated here (§5).

## 3. Results

| Arg. | Result | Theorem | Premises → conclusion | Axioms |
| --- | --- | --- | --- | --- |
| N1 | `9c431f7b` | `narFromRootWithholding` | common root `0c27f65a` (root and reach clauses only), (b2) `eeccc832`, (a) `fbd0a6d3` → **NAR `43651417`** | none |
| N2 | `ab40dc6f` | `rootWithholdingFromUniformity` | (b1) `2dd1f217`, factive giving `3ef41442`, `0c27f65a`, necessary roots `d164f730`, some contingent `c76b6e2c`, uniformity `19f2e094` → (a) | none |
| N3 | `d6588ea7` | `rootWithholdingFromWill` | EM `ee4ab504`, `0c27f65a`, #1941's willed giving `5c1aba17`, one power `06145e71`, (b1), WN `0266eac2`, SS `85f3fea2` → (a) | none |
| N4 | `0cf250b9` | `narDerivationControls` | premise-free laws and models | Mathlib three |

Controls statement: `b8ee1a50`. Attempts: `245028b2` (derivations) and
`e2ea61bc` (the uniformity limit and models).

**Premise choice in N1 and N2.** The weakest common-root premise is
`a6b46d2e` (`ActualCommonRootAt`). The Solution proves N1 from it
(`nar_of_commonRoot`). The registered arguments instead use `0c27f65a`, whose
root and reach clauses are exactly `a6b46d2e`; its God-naming and intellect
clauses are unused there. The reason: `a6b46d2e`'s legacy `definition_ids`
carry several senses of four terms (e.g.
INTRINSIC_PRODUCTIVE_CONTRIBUTION_VERSUS_SOURCE_BACKED_1/2, NECESSARY_2/4/11).
Any new argument with it as a premise is then an unbridged sense mixing; the
one existing user is allowlisted. Pruning those links is a definition-coverage
(#216) task, not done here.

**Laws** (`Model.Laws`).

1. `TwoWayGiverAt F w y` holds exactly when `y` is two-way toward some effect.
2. **The root is two-way toward the contingents.** With (b1), factive giving,
   a common root, necessary roots and some concrete contingent being, every
   actual root is two-way toward a concrete contingent being. This is derived
   without #1897's holder premises.
3. **Relocation.** With (b2), factive giving, a common root, necessary roots
   and excluded middle, NAR holds exactly when (a) holds.
4. **Exercise-level simplicity yields only uniform fixity.** Suppose:
   - `y` exercises toward each effect, at every accessible world where it
     exists, whatever it exercises toward at `w`;
   - every exercise is a giving;
   - every giving at `w` exercises some power.

   Then `y` is two-way toward nothing. This is the agency-overlay counterpart
   of #555 `rigid_core`.
5. **The will route without (b1).** With reflexive access at `w`, (a) follows
   from excluded middle, `0c27f65a`, `5c1aba17`, one power, WN and SS.
6. **The strict-modal reading of `EndRequires` begs the question.** With a
   common root, SS read with `StrictModalRequirement` yields NAR outright.

**Models.**

- *Theist nonvacuity* of N1–N3. (b2) and WN hold here only vacuously: there is
  no necessary being other than `g`, and nothing is required.
  `MixedModeRoot` with `gRequiresD` is the model in which (b2) and WN hold
  non-vacuously.
- *The mixed-mode root* (§4).
- *Omissions of N1:*
  - without (b2), #1944's `gdWithholdG`: the root grounds the necessary `d`
    and gives nothing anywhere, so (a) holds and NAR fails;
  - without (a), the mixed-mode root;
  - without the common root, mutual grounding of `g` and `d`.
- *Omissions of N2:*
  - without uniformity, the mixed-mode root;
  - without (b1), a root that gives only `d`;
  - without factive giving;
  - without necessary roots (a contingent root);
  - without some contingent concretum;
  - without the common root: the chain `d → g → c`, a mediated creator whose
    root fixedly gives the necessary `g` being and gives `c` nothing.
- *Omissions of N3:*
  - without WN, and without SS: the mixed-mode root, with nothing required or
    with `g`'s end requiring `d`;
  - without `5c1aba17`: natural emanation by an intellectual one-power root;
  - without one power: #1941's `twoPowerChancer`;
  - without `0c27f65a`: an emanating root without intellect;
  - without (b1): a frame whose access from `false` is not reflexive (law 5
    shows that this is the only way to omit it).

**Encoding disclosures** (true by construction in every model, unless
stated):

- `G` and `EndRequires` are the same at both worlds.
- The `Ontic` causal field and the frame's other relations are empty.
- A holder holds every power.
- The agency overlays have constant states and no external conditions.
- In the N2 omission models, uniformity holds only vacuously: the root is
  two-way toward nothing.
- In N1's mutual-grounding model, (a) and (b2) hold only vacuously: its one
  root `c` grounds nothing.
- In `MixedModeRoot`:
  - `d` gives `c` being without `G`-grounding it;
  - `rationalGD` gives `d` a rational power although `d` has no intellect;
  - `Exercises` holds where nothing is given (inherited from #1941's
    overlays).
- `MixedModeRoot` shows non-entailments in one encoding. It does not show that
  an emanation scheme is coherent, nor that Avicenna's system is captured.

## 4. Does a uniform mode of giving follow from one power, an invariant set-up and simplicity?

**No.** Model `MixedModeRoot` (frame `mixedG`, overlay `rationalGD`):

- *The root `g`:* it is the only actual root, grounds every other being, has
  intellect and is GOD_4. It gives the necessary `d` being at both worlds, so
  it is fixed toward `d`. It gives the contingent `c` being at the actual
  world only, so it is two-way toward `c`.
- *Its power and set-up:* `g` has one rational power under a constant set-up
  with no external conditions, and every giving of `g` exercises that power.
- *What holds:*
  - `OnePower`, `SetupInvariantAt` and `WilledTwoWayAt` at `g`;
  - #1941's willed giving `5c1aba17`;
  - (b1), (b2), factive giving, the common root, necessary roots, some
    contingent;
  - #1944's holder premises with `d` as holder: P2′, P3′, holders at `w`, and
    the creator reading (`d` also gives `c` being).
- *What fails:* uniformity at `g`, (a), NAR, and #1944's argument-1 conclusion
  (holders are actual roots).

**The precise obstacle.** Simplicity constrains the mode of giving in two
ways, and neither yields uniform *two-way* giving.

- *Intrinsic simplicity* (one power, an invariant set-up) constrains the
  source. It does not constrain how the giving relates to each effect across
  worlds.
- *Exercise-level simplicity* (#555's one act carried by the being, with
  strict efficacy) does constrain the mode, but only toward uniform *fixity*
  (law 4). Law 2 shows that uniform fixity fails at a necessary root with a
  contingent effect.

The classical reply to modal collapse is "one intrinsic act, varying
extrinsic termini". That reply saves two-way giving, but it is the same move
that leaves the mode toward each effect unconstrained.

**Analogical evidence only.** On the theist's own account, the mode of one
will varies by object (navigation only, not attributed):

- God wills his own goodness necessarily and other things not necessarily
  (ST I q.19 a.3).
- The Father begets the Son by nature, not by will (ST I q.41 a.2).

Neither case is a giving of being to an effect in the carrier `B`, so neither
is a counterexample to uniformity over effects. They are analogical support
for judging uniformity weak.

If the divine persons were distinct concreta in `B` and their origin fell
under giving, the Nicene structure would be a mixed-mode source. This is the
same compatibility condition #1944 recorded for NAR: `G` and giving exclude
intra-divine origin, or the persons are not distinct concreta here (sense
GOD_AS_DIVINE_BEING_VERSUS_DIVINE_1 of `852f282b`).

**What simplicity does contribute.** In N3, one power plus intellect makes
every giving of the root an exercise of its one rational power (`5c1aba17`).
Simplicity thus yields a uniform *kind* of power, not a uniform *mode*. WN
and SS supply the mode.

## 5. Warrant of the new premises

All judgments involving WN and SS in this section and in §6–§7 hold **on the
means-to-end reading of `EndRequires`** (§2). On the strict-modal reading,
N3 begs the question (law 6).

- **(b1)** (`2dd1f217`): **moderately high on the productive reading of `G`**.
  - Both classical theism and Avicenna's emanation accept it, so it does not
    separate the identification from the strongest rival.
  - It fails if the root's `G`-edges include non-productive dependence. Its use
    therefore records an interpretation choice for `G` at the root:
    productive dependence for being.
- **(b2)** (`eeccc832`): **moderately high.**
  - The classical theist posits no necessary grounded being, so for them (b2)
    holds only vacuously. Only the necessary-through-another rival accepts it
    in substance.
  - The objection to general rigidity (contingent beings sustained elsewhere,
    or not at all) does not apply to it, because it is restricted to
    necessary grounded beings at worlds where the root exists.
  - No substantive objection to this restricted form was identified.
- **(a)** (`fbd0a6d3`): **no independent warrant of its own.** By law 3, given
  (b2), factive giving, a common root, necessary roots and EM, it is NAR in
  the giving register. Different presentations of one assumption are not
  additional evidence. Its warrant is whatever N2 or N3 supply.
- **Necessary roots** (`d164f730`): inherited from the necessary-root routes.
  Not assessed here.
- **Uniformity at the root** (`19f2e094`): **weak.**
  - It is not entailed by one power, an invariant set-up and willed exercise
    (`MixedModeRoot`).
  - The theist cases in §4 are analogical evidence against "one power, one
    mode".
  - A restricted form (uniformity across effects distinct in nature from the
    source) may be defensible. The only warrant identified for it is N3's
    reasons, not simplicity. Given the bundle, N2 adds nothing to NAR beyond
    uniformity's own (weak) warrant.
- **One power at the root** (`06145e71`): power-level simplicity (ST I q.19
  a.4 ad 4; q.25 a.1, navigation). This is the root counterpart of #1941's
  holder premise `9856239a`, whose warrant is assessed in
  [will-versus-chance.md](will-versus-chance.md).
- **WN** (`0266eac2`): **moderate on the means-to-end reading; the new crux.**
  - *Positive warrant:* the analysis of rational appetite. A will adheres of
    necessity to its end and to what the end cannot be had without, and to
    nothing else (ST I q.19 a.3; q.82 a.1–2, navigation). This is a principle
    about wills in general, assessable apart from grounding and modal
    necessity.
  - *Rival:* a perfect will is fixed (NECESSITATE_5, metaphysically) toward
    effects that its good does not require. Developed defences (navigation):
    - the necessary diffusion of the good (Plotinus; Avicenna's First as
      standardly reported, whose consent to emanation is necessitated);
    - Rowe's argument that a perfectly good creator of the best is not free
      (world-level; not represented. A narrow being-level "one best effect"
      variant, `b72a790a`, has a non-counting conditional refutation, G1 of
      [orphan-graft-map.md](orphan-graft-map.md); it does not touch the
      mediated creator or the world-level optimizer `78af5042`. Selective
      diffusion is recorded as `ea1425c0`, unrefuted);
    - Kretzmann's Dionysian argument that goodness must diffuse.
  - *Not a rival in this sense:* Leibniz. His moral necessity of choosing the
    best is not metaphysical necessity, so it does not make the choice fixed
    toward its effects across worlds.
  - *Objection check against the Substantive Objection Standard:*
    - *target:* WN;
    - *mechanism:* perfect goodness determines the will toward an effect
      without requiring it;
    - *independent justification:* the diffusiveness of the good, and the
      choice-of-the-best argument;
    - *relevance:* any rival that grants the remaining premises of N3.

    The objection is substantive and stays unresolved.
- **SS** (`85f3fea2`): **high within the perfection routes, on the
  means-to-end reading.**
  - The root's good requires nothing other than itself as a means: aseity of
    the good, pure act. On Aquinas's account the divine goodness is complete
    without other things (ST I q.19 a.3, paraphrase, navigation).
  - On the strict-modal reading, SS would deny that any other necessary being
    exists, and with a common root it would yield NAR (law 6). That reading is
    rejected (§2).
  - Within this batch no substantive objection to SS was identified on the
    means-to-end reading. Process and relational theisms deny it, but they
    also deny `0c27f65a`'s classical root, which is a different branch.

**Shared dependencies.**

- N2 and N3 share (b1) and `0c27f65a`'s root and reach clauses.
- N3 also uses `0c27f65a`'s intellect and `5c1aba17`. Those are also inputs of
  #1944's arguments 2 and 5. So N3 adds nothing against a rival that denies
  intellect at the root (#1941's chance rival).
- N3 also adds nothing against a rival that denies the common root's direct
  reach (the mediated creator, §6).
- N3's value is against a rival that grants the common root's direct reach,
  intellect, willed giving, one power, (b1) and SS on the means-to-end
  reading. That rival must deny WN.

## 6. The rival's updated price

The necessary-through-another rival now comes in three variants.

- **Violating (b1)/(b2)** (#1944's `NecessaryThroughAnother`, where the root
  grounds `d` and gives nothing). It must read `G` as non-productive at the
  root. Its price is NAR's denial, one more concretum, and the denial of (b2):
  a root that grounds a necessary being without ever giving it being.
- **Respecting (b1) and (b2)** (`MixedModeRoot`). The root fixedly gives the
  necessary `d` being and gives the contingents being two-way. Derived price,
  given the rest of N3's premises:
  - it denies WN or SS (the model shows each way);
  - it is a mixed-mode root;
  - it has one more concretum.

  **Conditional on the means-to-end reading:** an Avicennian-style rival that
  grants the common root's direct reach, intellect, willed giving, one power,
  (b1) and SS must deny WN. That is a named, developed position (necessary
  diffusion), not an unusual price, and it is not shown to conflict with an
  accepted floor item.
- **The mediated creator** (`chainG`), where the root gives only the
  necessary intermediary. It denies the common root's direct reach, and N3
  does nothing against it. Its price is the one already recorded in #1944 §5
  (it denies the genus principle's universal reach).

**Which premise the historical Avicennian system denies is unresolved
(unread).** His emanation is standardly reported as mediated: from the one
only one proceeds (*Ilāhiyyāt* IX.4, navigation only, not read for this
slice). If so, the historical system denies `0c27f65a`'s direct-reach clause
and is the mediated-creator variant, not the (b1)/(b2)-respecting variant against
which N3 has force.

## 7. Overall provisional judgment

- **Formal consequence:** verified and zero-axiom.
  - N1: NAR follows from (a), (b2) and the common root.
  - N2: (a) follows from uniformity, (b1), factive giving, the common root,
    necessary roots and some contingent.
  - N3: (a) follows from EM, `0c27f65a`, `5c1aba17`, one power, (b1), WN and
    SS.
- **Formal status:** NAR is closed by the computed rule as the conclusion of a
  non-transcription result. It is **not established**. The new open leaves
  that now carry it are (b1), (b2), WN, SS, one power, uniformity and
  necessary roots. The reused leaves `0c27f65a`, `5c1aba17`, `3ef41442`,
  `c76b6e2c` and EM carry it too.
- **Warrant for NAR,** on the means-to-end reading of `EndRequires`:
  - *Before:* moderate, on prima facie plausibility alone.
  - *Now:* **moderate, with one partly independent support bundle** (N3). It
    moves the crux from a claim about grounded necessary beings to WN, a claim
    about rational wills that has its own analysis and its own well-known
    opponents.
  - *Not counted:* N2 adds nothing beyond uniformity's weak warrant, and the
    relocation law shows that (a) is NAR restated.
  - *Net:* a slight strengthening only against a rival that grants the common
    root's direct reach, intellect, willed giving, one power, (b1) and SS.
    Such a rival must now deny WN explicitly. No change against the chance
    rival (N3 presupposes intellect at the root). No change against the
    mediated creator, which may be the historical Avicennian system (§6,
    unresolved).
- **The identification** (#1944): unchanged in structure. It now has a support
  option conditional on (b1), (b2), WN and SS (with one power and willed
  giving), beside the bare NAR option.
- **Holder-restricted NAR:** not needed. N1 derives the general form from the
  same premises, so the restriction would only weaken the conclusion.
  #1944's reason for the general form (near-transcription) no longer applies
  either.
- **Strength registration:** none. No single stronger statement implies NAR on
  its own; the relocation equivalence holds only relative to a bundle. The
  general (b) is not registered (§2), so no general-to-restricted order
  arises.

**Revision conditions.**

- *Toward NAR:*
  - an argument for WN from the nature of rational appetite that does not
    assume the source's freedom toward creatures;
  - a refutation of necessary diffusion;
  - a non-modal criterion for `EndRequires` (OPEN 1).
- *Against NAR:*
  - a defence of a perfect will necessitated toward an effect its good does
    not require that the theist cannot block without begging the question;
  - evidence that the root's `G`-edges on the composed routes include
    non-productive dependence, which falsifies (b1) and (b2);
  - a showing that `EndRequires` can only be read modally, which collapses N3
    into a restatement (law 6).

## 8. Claim versus type

| Record | Prose | Lean type | Check |
| --- | --- | --- | --- |
| (b1) `2dd1f217` | every actual root gives being at `w` to each being it grounds that exists at `w` | `∀ n x, ActualRoot gp w n → ActualConcreteGround gp w n x → ExistsAt w x → GivesTo F w n x` | roots only; `w` only |
| (b2) `eeccc832` | every actual root gives each NECESSARY_2 being it grounds being at accessible worlds where the root exists | `∀ n x, ActualRoot gp w n → ActualConcreteGround gp w n x → NecessaryAt F.history.ontic w x → ∀ v, access w v → ExistsAt v n → GivesTo F v n x` | roots only; necessary grounded beings only; where the root exists |
| (a) `fbd0a6d3` | every actual root withholds each grounded actual concretum somewhere accessible | `∀ n x, ActualRoot gp w n → ActualConcrete gp w x → ActualConcreteGround gp w n x → ∃ v, access w v ∧ ExistsAt v n ∧ ¬ GivesTo F v n x` | does not assert giving at `w` |
| necessary roots `d164f730` | every actual root is NECESSARY_2 at `w` | `∀ n, ActualRoot gp w n → NecessaryAt F.history.ontic w n` | universal; no existence |
| uniformity `19f2e094` | every actual root gives uniformly | `∀ n, ActualRoot gp w n → UniformGivingModeAt F w n` | over all effects given at `w` |
| one power `06145e71` | every actual root has one power | `∀ n, ActualRoot gp w n → OnePower A n` | no existence |
| WN `0266eac2` | a rational power is fixed toward a given being only if the giver's end requires it | `∀ y p x, PowerOf y p → Rational p → Exercises w y x p → FixedTowardAt F w y x → EndRequires y x` | exercise at `w`; NECESSITATE_5; `EndRequires` is means-to-end |
| SS `85f3fea2` | no other being is required by a root's end | `∀ n x, ActualRoot gp w n → x ≠ n → ¬ EndRequires n x` | roots only; means-to-end reading |
| NAR `43651417` (reused) | NECESSARY_2 actual concreta are roots | at `groundProfile F concrete G` | as in #1944 |
| `0c27f65a` (reused) | common GOD_4 root with intellect | at `groundProfile F concrete G` | N1 and N2 use the root and reach clauses only |

Every hypothesis of each theorem is a listed premise (bind-check). No source
is attributed and no claim record is added. ST I q.19 a.3, q.41 a.2,
q.82 a.1–2 and q.104 a.1 and *Ilāhiyyāt* IX.4 are navigation only, not read
for this slice. Nothing from them is quoted; they are paraphrased.

## 9. Remaining gaps and next tests

1. **WN's warrant** (decisive). Next test: formalize the necessary-diffusion
   rival as a premise ("a perfect will is fixed toward every effect its good
   could overflow into") and compare it with WN at matching scope.
   - Does total diffusion conflict with #1897's two-way profile toward the
     contingents?
   - Can the rival keep contingent concreta while diffusing necessarily
     toward `d` only? That selective version needs a principle that picks out
     `d`, which is the next place to look for a price.
2. **`EndRequires`'s non-modal criterion** (OPEN 1 of DEF `90719cb5`). Without
   it, the rejection of the strict-modal reading rests on stipulation.
3. **The historical Avicennian system:** read *Ilāhiyyāt* IX.4 to settle whether
   it denies direct reach (and is then the mediated creator) or WN.
4. **(b1)'s reading of `G`:** tag `G` on the composed routes as productive or
   non-productive (a parameter-level sense, #1784). That tag would decide
   whether (b1) holds by meaning.
5. **`a6b46d2e`'s legacy definition links:** prune them (#216). N1 and N2 can
   then be registered on the bare common root.
6. **Necessary roots** (`d164f730`): answered by G2 of
   [orphan-graft-map.md](orphan-graft-map.md): derived from `91b085c4` (a
   unique necessary actual root), registered `strengthens`. Closed, not
   established.

## 10. Edits outside the batch

- `corpus/disambiguations/5836e1f6-…` (NECESSITATE, #1941): NECESSITATE_5
  appended (append-only), and the resolution extended.
- `docs/notes/holder-root-identification.md` §10 gap 1: a pointer here.
- Generated: `TruthCore/Imports/Causality.lean` and
  `TruthCore/Imports/Results/Causality.lean`.

## Which giver reaches all the way to the recipients?

At the selected world, suppose each actual concrete being can be traced by
finitely many existential grounding steps to some actual concrete root.
Suppose also that an actual root exists and all actual roots there coincide.
Then the paths for all these beings lead to **the same source**. The first
premise supplies a path for each recipient. The second identifies its initial
bearer. Both premises can also be recovered from a finite path to one unique
source for every actual node. These are translations on one profile. A path
of length zero covers the source itself. Longer paths keep all contributors
actual and concrete. No bound on their lengths or on other branches is needed.
[Forward proof](../../corpus/results/0dcb0397-8a2a-4f8f-8550-4bbac1192c2b.json),
[access projection](../../corpus/results/a53edd5b-49de-4251-855a-31aea94e58e1.json)
and [uniqueness projection](../../corpus/results/273fb2d3-d2e8-404e-adad-f6ae2c821169.json)

The graph used here is `ConcreteExistentialSupply.graph m w`. Its contributors
and recipients exist at w and are concrete, and an edge is `m.grounds w`.
In the same three-being example below, the ordinary causal relation
`Ontic.Causes` is empty. Its three existing beings are isolated sources,
whereas the grounding graph has a single root. This difference is why the
corpus records the conclusion specifically for actual concrete grounding.
The abstract graph argument must be instantiated on that relation. Results
on ordered parts, past events or another causal relation need an explicit
identification to apply. The return paths in the corpus preserve the option
of directly accepting each premise. Using the forward and reverse arguments
in a circle supplies no additional warrant for either existence or uniqueness.

**An independent way to identify two proposed beings.** Suppose an argument
supplies a being g satisfying GOD_4 and another argument supplies an actual
root n. If the God-description entails that g reaches **every actual concrete
being** by a finite path of existential grounds, then g reaches n. A nonempty
path into n would have a last incoming ground, contradicting its roothood.
The path is empty, so g is n. The inference applies to every actual root in
this profile. It requires neither global well-foundedness nor a direct edge
from g to every distinct recipient. Existence of a God is a premise here.
This use identifies a candidate secured elsewhere. It adds no independent
argument for that existence when the witnesses are obtained from a route
that already presupposes the same identification.
[Witness identification and finite reach](../../corpus/results/0269173b-9dd1-43f9-909f-c2462710fb1a.json)

One way to warrant the path premise conditionally is the stronger causal
reading that each God causes every other being's esse, together with the
correspondence that a distinct esse cause of an actual concretum is an actual
concrete ground. With explicit excluded middle for identity the path then
has length zero or one. This is where an argument for that correspondence,
including one from sustaining causation, can enter. Receipt of form or the
transmission of material from an earlier patient would need further evidence
to count as existential grounding here.
[Direct-cause argument](../../corpus/results/acc12ba2-a7e2-4146-bbed-f5c964602bbb.json)

**Test both claims on the earlier mediated creator.** At the actual world
of `chainG`, d grounds g, and g grounds c. The existing optimum assignment
allows the root d one immediate object of giving, g. The new result keeps
that very assignment and exhibits finite grounding access from d to every
actual concretum, including c. Its failure of direct common-root coverage
persists. An explanation can thus trace every recipient to d through the
intermediary while giving d no direct edge to c. Tracing each path supplies
something stronger than merely observing a recipient. It does not establish
that the ultimate source itself immediately gives being at every link.
[Same-profile control](../../corpus/results/1e652b87-fba4-4653-801e-1911fbd4b957.json)

Now consider g as the proposed universal source in **that same interpretation**.
It exists at both accessible worlds. It directly grounds and gives being at
the actual moment to **every actual contingent concretum**. There is one
such recipient, c, which is absent from the other world. Yet d directly
grounds g. The underlying model therefore distinguishes two candidates
even after one grants necessity of the proposed giver and complete coverage
of the contingent recipients. The predicate selecting g only designates a
candidate for the test. Attributing Godhood to it would require independent
warrant. Giving at a moment and the selected grounding edge are separately
verified in this assignment. Their coincidence here proves no general law.
[Contingent-recipient test](../../corpus/results/012166ef-0b65-4785-a163-1900d60044c9.json)

**Provisional judgment.** Once an account supplies finite origins for the
actual recipients and a reason for their roots to coincide, it has a positive
explanation of common ancestry even where intermediate givers are real. A
theory that merely identifies a necessary giver for all contingents still owes
a reason why that giver is underived if it claims ultimacy for it. The mediated
account permits the last gift to vary while the first source keeps the same
immediate recipient. The two worlds exhibit this compatibility. Explaining *why* it varies,
and whether one required act can admit that variation, needs a further account
of the intermediary. The distinguishing test for the necessity inference is
to determine what supplies the being of the putative necessary intermediary
itself. For direct reach, identify what the first source contributes to the
remote patient's own existence over and above sustaining an intermediary
that gives being to it. The present comparison settles neither issue by naming
the first source God.
