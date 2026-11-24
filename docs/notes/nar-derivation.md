# Deriving NAR: the root's withholding, a grounding-to-giving bridge and the will route (#1926 phase 3)

Outcome label (rigor contract 6): **a new bridge**, conditional. NAR
(`43651417`) is now the conclusion of a verified, non-transcription argument
(N1), so the computed frontier counts it as closed. That is a formal closure,
**not establishment**. The decisive content moves into new open premises,
recorded below with their warrant, and one of the two routes to them is a
restatement of NAR (law 3).

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
| required by `y`'s end (DEF `90719cb5`) | `EndRequires y x`, a primitive parameter | primitive |
| (b) | `ActualGroundsGiveWhereverGroundedExists`, `c02c7bbe` | new OPEN bridge |
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
at `w`", which (b) supplies. That is the only part N1 uses.

### Semantic grounding

**(b), from grounding to giving.** This is the only premise that joins `G` to
giving (rigor contract 5; #1626).

- *Meaning:* whatever actually grounds `x` gives `x` being at `w` and wherever
  `x` exists among the accessible worlds.
- *Two components:*
  - (b1) a local bridge: a `G`-ground is a giver of being. This reads `G` as
    productive dependence for being, the sustaining CAUSE_OF_BEING sense of
    `88a8fba7`.
  - (b2) rigidity of the actual ground's giving: the being that grounds `x`
    here gives `x` being wherever `x` exists. Compare necessity of origin, or
    conservation by the same source.
- *Examples:* classical conservation (God gives each creature being wherever
  it exists; ST I q.104 a.1, navigation); Avicenna's First giving the first
  intelligence being in every world.
- *Non-examples, where (b1) fails:* grounding as non-productive metaphysical
  dependence. A singleton depends on its member, but the member does not
  give the singleton being. A fact is grounded in its constituent facts.
- *Rival:* `G` read as non-productive dependence. On the composed routes, `G`
  is tied to esse-causation one way by `cb1cdea9`: a distinct esse-cause is an
  actual concrete ground. (b) is a converse-direction bridge. A grounding
  relation that also includes non-productive dependence would falsify it.
- *(b2)'s rival:* a necessary being grounded by different beings at different
  worlds. No developed defence of this was identified, so no substantive
  objection to (b2) is recorded.
- *Structure:* (b) assumes no order property of `G`.

**`EndRequires`, required by a being's own end.**

- *Meaning:* `y`'s own good cannot be had without `x`. It is a primitive
  parameter, constrained only by WN and SS.
- *Examples:* an animal's flourishing requires food; a voyage requires a ship.
- *Non-examples:* a generous person's goodness does not require the
  particular gifts given. On classical theism, God's goodness requires no
  creature.
- *Distinct from:* grounding and causing. `x` can be required by `y`'s end
  without either grounding the other.
- *Structural properties:* none assumed.
- *OPEN:*
  - whether "end" applies univocally to a first source;
  - whether the necessary diffusion of the good counts as the end requiring its
    effects, or as a fixity without requirement. The second is how WN's rival
    is stated here (§5).

## 3. Results

| Arg. | Result | Theorem | Premises → conclusion | Axioms |
| --- | --- | --- | --- | --- |
| N1 | `9c431f7b` | `narFromRootWithholding` | common root `0c27f65a` (root and reach clauses only), (b) `c02c7bbe`, (a) `fbd0a6d3` → **NAR `43651417`** | none |
| N2 | `ab40dc6f` | `rootWithholdingFromUniformity` | (b), factive giving `3ef41442`, `0c27f65a`, necessary roots `d164f730`, some contingent `c76b6e2c`, uniformity `19f2e094` → (a) | none |
| N3 | `d6588ea7` | `rootWithholdingFromWill` | EM `ee4ab504`, `0c27f65a`, #1941's willed giving `5c1aba17`, one power `06145e71`, (b), WN `0266eac2`, SS `85f3fea2` → (a) | none |
| N4 | `0cf250b9` | `narDerivationControls` | premise-free laws and models | Mathlib three |

Controls statement: `b8ee1a50`. Attempts: `245028b2` (derivations) and
`e2ea61bc` (the uniformity limit and models).

**Premise choice in N1 and N2.** The weakest common-root premise is
`a6b46d2e` (`ActualCommonRootAt`). The Solution proves N1 from it
(`nar_of_commonRoot`). The registered arguments instead use `0c27f65a`, whose
root and reach clauses are exactly `a6b46d2e`; its God-naming and intellect
clauses are unused there. The reason: `a6b46d2e`'s legacy `definition_ids`
carry several senses of four terms (e.g.
INTRINSIC_PRODUCTIVE_CONTRIBUTION_VERSUS_SOURCE_BACKED_1/2, NECESSARY_2/4/11),
so any new argument with it as premise is an unbridged sense mixing. The one
existing user is allowlisted. Pruning those links is a definition-coverage
(#216) task, not done here.

**Laws** (`Model.Laws`).

1. `TwoWayGiverAt F w y` holds exactly when `y` is two-way toward some effect.
2. **The root is two-way toward the contingents.** With (b), factive giving, a
   common root, necessary roots and some concrete contingent being, every
   actual root is two-way toward a concrete contingent being. This is derived
   without #1897's holder premises.
3. **Relocation.** With (b), factive giving, a common root, necessary roots and
   excluded middle, NAR holds exactly when (a) holds.
4. **Exercise-level simplicity yields only uniform fixity.** Suppose `y`
   exercises toward each effect, at every accessible world where it exists,
   whatever it exercises toward at `w`; every exercise is a giving; and every
   giving at `w` exercises a power. Then `y` is two-way toward nothing. This
   is the agency-overlay counterpart of #555 `rigid_core`.
5. **The will route without (b).** With reflexive access at `w`, (a) follows
   from excluded middle, `0c27f65a`, `5c1aba17`, one power, WN and SS.

**Models.**

- *Theist nonvacuity* of N1–N3.
- *The mixed-mode root* (§4).
- *Omissions of N1:*
  - without (b), #1944's `gdWithholdG`: the root grounds the necessary `d`
    and gives nothing anywhere, so (a) holds and NAR fails;
  - without (a), the mixed-mode root;
  - without the common root, mutual grounding of `g` and `d`.
- *Omissions of N2:*
  - without uniformity, the mixed-mode root;
  - without (b), a root that gives only `d`;
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
  - without (b): a frame whose access from `false` is not reflexive (law 5
    shows that this is the only way to omit it).

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
  - (b), factive giving, the common root, necessary roots, some contingent;
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

**Theist-internal evidence against unrestricted uniformity.** On the theist's
own account, the mode of one power varies by object (navigation only, not
attributed):

- God wills his own goodness necessarily and other things not necessarily
  (ST I q.19 a.3).
- The Father begets the Son by nature, not by will (ST I q.41 a.2).

If the divine persons were distinct concreta in `B` and their origin fell
under giving, the Nicene structure would itself be a mixed-mode source. This
is the same compatibility condition #1944 recorded for NAR: `G` and giving
exclude intra-divine origin, or the persons are not distinct concreta here
(sense GOD_AS_DIVINE_BEING_VERSUS_DIVINE_1 of `852f282b`).

**What simplicity does contribute.** In N3, one power plus intellect makes
every giving of the root an exercise of its one rational power (`5c1aba17`).
Simplicity thus yields a uniform *kind* of power, not a uniform *mode*. WN
and SS supply the mode.

## 5. Warrant of the new premises

- **(b)** (`c02c7bbe`): **moderately high on the productive reading of `G`**.
  - Both classical theism and Avicenna accept it, so it is not what separates
    the identification from the strongest rival.
  - It fails on a non-productive reading of `G`. Its use therefore records an
    interpretation choice for `G`: productive dependence for being.
  - No substantive objection to (b2) was identified.
- **(a)** (`fbd0a6d3`): **no independent warrant of its own.** By law 3,
  given (b), factive giving, a common root, necessary roots and EM, it is
  NAR in the giving register. Different presentations of one assumption are
  not additional evidence. Its warrant is whatever N2 or N3 supply.
- **Necessary roots** (`d164f730`): inherited from the necessary-root routes.
  Not assessed here.
- **Uniformity at the root** (`19f2e094`): **weak.**
  - It is not entailed by one power, an invariant set-up and willed exercise
    (`MixedModeRoot`).
  - The theist's own account denies "one power, one mode" across objects
    (§4).
  - Its only defensible restricted form, uniformity across effects
    *distinct in nature from the source*, gets its warrant from the reasons of
    N3, not from simplicity. Given the bundle, N2 adds nothing to NAR that
    uniformity's own (weak) warrant does not supply.
- **One power at the root** (`06145e71`): power-level simplicity (ST I q.19
  a.4 ad 4; q.25 a.1, navigation). This is the root counterpart of #1941's
  holder premise `9856239a`, whose warrant is assessed in
  [will-versus-chance.md](will-versus-chance.md).
- **WN** (`0266eac2`): **moderate; the new crux.**
  - *Positive warrant:* the analysis of rational appetite. A will adheres of
    necessity to its end and to what the end cannot be had without, and to
    nothing else (ST I q.19 a.3; q.82 a.1–2, navigation). This is a principle
    about wills in general, assessable apart from grounding and modal
    necessity.
  - *Strongest rival:* a perfect will is fixed toward effects that its good
    does not require. Two developed defences:
    - the necessary diffusion of the good (Plotinus; Avicenna's First, whose
      consent to emanation is necessitated);
    - the moral necessity of choosing the best (Leibniz; Rowe's argument that
      a perfectly good creator is not free).
  - *Objection check against the Substantive Objection Standard:*
    - *target:* WN;
    - *mechanism:* perfect goodness determines the will toward an effect
      without requiring it;
    - *independent justification:* the diffusiveness of the good, and the
      choice-of-the-best argument;
    - *relevance:* exactly the Avicennian rival.

    The objection is substantive and stays unresolved.
- **SS** (`85f3fea2`): **high within the perfection routes.** The root's good
  requires nothing other than itself: aseity of the good, pure act (ST I q.19
  a.3, navigation). Avicenna's First is self-sufficient in the same sense, so
  the main rival grants SS. No substantive objection was identified within
  the scope of this batch. Process and relational theisms deny it, but they
  also deny `0c27f65a`'s classical root, which is a different branch.

**Shared dependencies.**

- N2 and N3 share (b) and `0c27f65a`'s root and reach clauses.
- N3 also uses `0c27f65a`'s intellect and `5c1aba17`. Those are also inputs of
  #1944's arguments 2 and 5. So N3 adds nothing against a rival that denies
  intellect at the root (#1941's chance rival).
- N3's value is against the Avicennian rival, which grants an intellectual,
  self-sufficient First.

## 6. The rival's updated price

The necessary-through-another rival now comes in two variants.

- **Violating (b)** (#1944's `NecessaryThroughAnother`, where the root grounds
  `d` and gives nothing). It must read `G` as non-productive. Its price is
  NAR's denial, one more concretum, and the denial of (b): a ground that gives
  its grounded being nothing.
- **Respecting (b)** (`MixedModeRoot`). The root fixedly gives the necessary
  `d` being and gives the contingents being two-way. Derived price, given the
  rest of N3's premises:
  - it denies WN or SS (the model shows each way);
  - it is a mixed-mode root;
  - it has one more concretum.

  For the historical Avicennian system the denial falls on **WN**: an
  intellectual, self-sufficient First whose will is fixed toward an effect its
  good does not require. That is a named, developed position (necessary
  diffusion), not an unusual price, and it is not shown to conflict with an
  accepted floor item.
- **The mediated creator** (`chainG`), where the root gives only the
  necessary intermediary. It denies the common root's reach. Its price is the
  one already recorded in #1944 §5 (it denies the genus principle's universal
  reach).

## 7. Overall provisional judgment

- **Formal consequence:** verified and zero-axiom.
  - N1: NAR follows from (a), (b) and the common root.
  - N2: (a) follows from uniformity, (b), factive giving, the common root,
    necessary roots and some contingent.
  - N3: (a) follows from EM, `0c27f65a`, `5c1aba17`, one power, (b), WN and
    SS.
- **Formal status:** NAR is closed by the computed rule as the conclusion of a
  non-transcription result. It is **not established**: the open leaves (b),
  WN, SS, one power, uniformity and necessary roots now carry it.
- **Warrant for NAR:**
  - *Before:* moderate, on prima facie plausibility alone.
  - *Now:* **moderate, with one partly independent support bundle** (N3). It
    moves the crux from a claim about grounded necessary beings to WN, a claim
    about rational wills that has its own analysis and its own well-known
    opponents.
  - *Not counted:* N2 adds nothing beyond uniformity's weak warrant, and the
    relocation law shows that (a) is NAR restated.
  - *Net:* a slight strengthening of NAR's standing against the Avicennian
    rival, which must now deny WN explicitly. No change against the chance
    rival, since N3 presupposes intellect at the root.
- **The identification** (#1944): unchanged in structure. It is now
  conditional on (b), WN and SS (with one power and willed giving) instead of
  on bare NAR, or on NAR directly; both remain support options.
- **Holder-restricted NAR:** not needed. N1 derives the general form from the
  same premises, so the restriction would only weaken the conclusion. #1944's
  reason for the general form (near-transcription) no longer applies either.
- **Strength registration:** none. No single stronger premise implies NAR
  alone. The relocation equivalence holds only relative to a bundle, which a
  `strengthens` record cannot express.

**Revision conditions.**

- *Toward NAR:* an argument for WN from the nature of rational appetite that
  does not assume the source's freedom toward creatures, or a refutation of
  necessary diffusion.
- *Against NAR:*
  - a defence of a perfect will necessitated toward an effect its good does
    not require (Leibniz/Rowe; Avicenna) that the theist cannot block without
    begging the question;
  - evidence that `G` on the composed routes includes non-productive
    dependence, which falsifies (b).

## 8. Claim versus type

| Record | Prose | Lean type | Check |
| --- | --- | --- | --- |
| (b) `c02c7bbe` | an actual ground gives its grounded being being wherever it exists | `∀ y x, ActualConcreteGround gp w y x → (ExistsAt w x → GivesTo F w y x) ∧ ∀ v, access w v → ExistsAt v x → GivesTo F v y x` | actual ground at `w`, giving at `w` and accessible worlds; not "every ground at `v`" |
| (a) `fbd0a6d3` | every actual root withholds each grounded actual concretum somewhere accessible | `∀ n x, ActualRoot gp w n → ActualConcrete gp w x → ActualConcreteGround gp w n x → ∃ v, access w v ∧ ExistsAt v n ∧ ¬ GivesTo F v n x` | does not assert giving at `w` |
| necessary roots `d164f730` | every actual root is NECESSARY_2 at `w` | `∀ n, ActualRoot gp w n → NecessaryAt F.history.ontic w n` | universal; no existence |
| uniformity `19f2e094` | every actual root gives uniformly | `∀ n, ActualRoot gp w n → UniformGivingModeAt F w n` | over all effects given at `w` |
| one power `06145e71` | every actual root has one power | `∀ n, ActualRoot gp w n → OnePower A n` | no existence |
| WN `0266eac2` | a rational power fixed toward a given being only if the giver's end requires it | `∀ y p x, PowerOf y p → Rational p → Exercises w y x p → FixedTowardAt F w y x → EndRequires y x` | exercise at `w`; NECESSITATE_5 |
| SS `85f3fea2` | no other being is required by a root's end | `∀ n x, ActualRoot gp w n → x ≠ n → ¬ EndRequires n x` | roots only |
| NAR `43651417` (reused) | NECESSARY_2 actual concreta are roots | at `groundProfile F concrete G` | as in #1944 |
| `0c27f65a` (reused) | common GOD_4 root with intellect | at `groundProfile F concrete G` | N1/N2 use the root and reach clauses only |

Every hypothesis of each theorem is a listed premise (bind-check). No source
is attributed and no claim record is added. ST I q.19 a.3, q.41 a.2,
q.82 a.1–2 and q.104 a.1 are navigation only, not read for this slice.

## 9. Remaining gaps and next tests

1. **WN's warrant** (decisive). Next test: formalize the necessary-diffusion
   rival as a premise ("a perfect will is fixed toward every effect its good
   could overflow into") and compare it with WN at matching scope. Find out
   whether it conflicts with #1897's two-way profile toward the contingents
   (it seems to, if the diffusion is total), and so whether the Avicennian
   rival can keep contingent concreta and diffuse necessarily toward `d`
   only. The selective version needs a principle that picks out `d`. That
   principle is the next place to look for a price.
2. **(b)'s reading of `G`**: tag `G` on the composed routes as productive or
   non-productive (a parameter-level sense, #1784). That tag would decide
   whether (b) holds by meaning.
3. **`a6b46d2e`'s legacy definition links**: prune them (#216). N1 and N2 can
   then be registered on the bare common root.
4. **Necessary roots** (`d164f730`): connect to an existing necessary-root
   derivation, e.g. a universal form of the necessary-root trilemma's horn.
5. **Uniformity's restricted form**: uniformity across effects distinct in
   nature from the source, with an explicit definition of "distinct in
   nature". Only worth doing if it can be warranted otherwise than by N3's
   premises.

## 10. Edits outside the batch

- `corpus/disambiguations/5836e1f6-…` (NECESSITATE, #1941): NECESSITATE_5
  appended (append-only), and the resolution extended.
- `docs/notes/holder-root-identification.md` §10 gap 1: a pointer here.
- Generated: `TruthCore/Imports/Causality.lean`,
  `TruthCore/Imports/Results/Causality.lean`, the docs index.
