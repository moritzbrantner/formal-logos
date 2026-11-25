# Identifying the holder of the joint-absence power with the root (#1926 phase 3)

Outcome label (rigor contract 6): **a new bridge**, conditional. It closes
the derivation gap named in #1897 (`pruss-power-premises.md` §7, §9 gap 2) and
#1941 (`will-versus-chance.md` §10 gaps 2–3) under explicit premises. It does
not discharge them: one new open premise carries the decisive step, and its
strongest rival is recorded below.

Lean: `TruthCore.Causality.HolderRootIdentification` (vocabulary, laws,
models) and `TruthCore.Results.Causality.HolderRootIdentification` (Solution).
Spec: `specs/holder-root-identification.toml`. Every argument is an analyst
formulation, attribution deferred. Every model is a finite structural
surrogate on #1897's frames; it witnesses only its formal interpretation, never
metaphysical possibility. `truth countermodel` does not handle
`CausalityFrame` parameters (#1897 gap 9), so all models are hand-written.

## 1. Target and question

- **Open premises targeted.** `813a9181` (whatever has the power for the
  actual contingents' joint absence HAS_INTELLECT_1), and the missing converse
  of `0050b6ed` (every GOD_4 holds that power; "not that every holder is
  GOD_4").
- **Consumer gap.** #1941's argument B (`963e9689`) concludes `fdd2b1cf`
  (some holder is a willed two-way giver), which had no root consumer.
- **Question.** Under explicit premises, is every holder the root that the
  intellect and God routes are about? Equivalently, #1926 phase 3 bridge 5
  applied at the holder: what uniqueness interface identifies two
  descriptions of a first source, and what does the identification cost?

Throughout, `q` is `NoActualContingentConcreteIn F concrete w` (every concrete
being contingent at `w` is absent), a *holder* is a `y` with
`PowerFor w y q` (DEF `bf7eddca`), and the *root* is an actual root of a
selected grounding relation `G` (`ActualRoot`, DEF `c57e2682`).

## 2. Fixed meanings and the frame join

| Term | Formal content | Status |
| --- | --- | --- |
| holder exists at `w` | `ActualAbsenceHoldersExistAt`: `∀ y, PowerFor w y q → ExistsAt w y` | new OPEN premise |
| NAR | `NecessaryActualConcretaAreRoots m w`: every actual concretum NECESSARY_2 at `w` (`NecessaryAt`, existence at every accessible world) is an actual root | new OPEN premise |
| holders are actual roots | `ActualAbsenceHoldersAreActualRoots F PowerFor concrete G w` | derived under open premises (argument 1) |
| at most one holder | `AtMostOneActualAbsenceHolder` | derived under open premises (argument 4) |
| holders are GOD_4 | `ActualAbsenceHoldersAreGod` | derived under open premises (argument 3) |

**The frame join.** The holder premises live on the shared `CausalityFrame`
(#1784); the root nodes on a `Profile` (#505). They are joined only through
the existing adapter `FirstMoverNecessity.groundProfile F concrete G =
⟨F.history.ontic, concrete, G⟩`: the profile on the frame's own world-relative
existence, with the holder premises' `concrete` predicate and a selected
grounding relation `G` that stays a parameter. Two consequences:

- **No relation is identified in this batch.** `G` is not the frame's
  `GivesAt`, `CausesIn`, `DependsForBeing` or `PriorSimply`, and no premise of
  this batch relates them (rigor contract 5; #1626). In particular, "the holder
  gives each actual contingent being" (#1897's creator reading `9f7b1778`) is
  *not* used to make the holder their ground. On the composed routes the reused
  root nodes do relate `G`, one way and by explicit open bridges: to
  esse-causation by `cb1cdea9` (an actual concretum's distinct esse cause is
  its actual concrete ground) and to simple priority by the priority bridge
  `86efed1a` of `0c27f65a`'s route. So a causal rival (necessary emanation)
  bears on NAR only through `cb1cdea9`.
- **One existence predicate and one `concrete`.** The root premises `0c27f65a`
  and `49fdec01` are schematic in their profile; the arguments instantiate
  them at `groundProfile F concrete G`. That is a choice of interpretation: the
  root node's existence and concreteness are the holder premises'. It is
  explicit in every theorem type. For existence it is an equality of the
  *same* kind of primitive (world-relative existence,
  DEF-KANT-ONTOLOGICAL-MODEL), not an identification of two relations. For
  concreteness it is an owed sense identification (gap 3): `49fdec01`'s label
  reads CONCRETE_6 (esse in re), while P3′ (`a6906cab`) speaks of "the selected
  world-independent concreteness predicate".

**Semantic grounding of NAR.** NAR introduces no relation. It relates two
existing ones: modal necessity (NECESSARY_2, DEF `38b92bb6`) and having an actual
concrete ground in `G` (DEF `a1b2e330`).

- *Meaning:* whatever exists at `w` and could not have been absent from any
  accessible world has no actual concrete ground at `w`.
- *Example:* on classical theism, God; every creature is grounded and, being
  freely created, modally contingent.
- *Proposed counterexample:* Avicenna's intellects, necessary through the
  First's necessary emanation. That is a causal description; it bears on NAR
  only through `cb1cdea9`.
- *Non-example of the issue:* the tertia via's "necessary beings that have
  their necessity from another" are NECESSARY_3/NECESSARY_4 (disambiguation
  `83264cf5`): incorruptible, not modally necessary. On Aquinas's own account
  they are modally contingent, since God could have refrained from creating
  them (ST I q.19 a.3, navigation). The sourced statement `8c3870b7` (ST I
  q.44 a.1 ad 2: some necessary things have causes of their necessity; linked
  to DISAMB-NECESSARY with no sense fixed) is compatible with NAR **only if it
  is read as NECESSARY_3/NECESSARY_4**. Read as NECESSARY_2 with a cause that
  is an actual concrete `G`-ground (via `cb1cdea9`), it contradicts NAR.
- *Structure:* NAR is not an order property of `G`; it is universal over
  actual concreta at one world. It is constructively equivalent to "whatever
  actual concretum (concrete, existing at `w`) has an actual concrete ground at
  `w` is not NECESSARY_2 at `w`"; with excluded middle, such a concretum is
  contingent at `w`. The unrestricted form (over all beings, not only actual
  concreta) is strictly stronger.
- *Consequences with the reused nodes:*
  - NAR with `0c27f65a`: no actual concretum other than the common root is
    NECESSARY_2 at `w` (each other one is grounded by the root);
  - NAR with `cb1cdea9`: no NECESSARY_2 actual concretum has a distinct
    actual concrete esse-cause.
- *Relation to existing work:* the `NecessarilyUnderived` family (#495) asks
  whether *some* necessary bearer is underived. NAR asks it of *every*
  necessary actual bearer, at one world.

## 3. Results

| Arg. | Result | Theorem | Premises → conclusion | Axioms |
| --- | --- | --- | --- | --- |
| 1 | `88f1ee6e` | `holdersAreActualRoots` | EM `ee4ab504`, P2′ `906f5c39`, P3′ `a6906cab`, holders at `w`, NAR → holders are actual roots | none |
| 2 | `1be2993c` | `holdersHaveIntellectFromCommonRoot` | arg. 1's conclusion, common GOD_4 root with intellect `0c27f65a` → **`813a9181`** | none |
| 3 | `cb42e5e2` | `holdersAreGodFromCommonRoot` | arg. 1's conclusion, `0c27f65a` → holders are GOD_4 | none |
| 4 | `9b7683e1` | `atMostOneHolderFromAtMostOneRoot` | arg. 1's conclusion, at most one actual root `49fdec01` → at most one holder | none |
| 5 | `834ddcfa` | `godHasWillFromWilledHolder` | `fdd2b1cf`, `0050b6ed`, at most one holder, rational power is will `65e0179f` → **`66aecdd7`** | none |
| 6 | `d8073ba0` | `holderRootIdentificationControls` | premise-free laws and models | Mathlib three |

New statements:
- holders at `w`: `b517ca3e`;
- NAR: `43651417`;
- holders are actual roots: `0a995309`;
- at most one holder: `5f93d4f0`;
- holders are GOD_4: `2146ebc9`;
- controls: `4c28b2d3`.

Attempts: [`3c556cdd`](../../corpus/attempts/3c556cdd-cf98-4211-a8c5-b89782d493b5.json) (derivation) and [`f68fa861`](../../corpus/attempts/f68fa861-541e-4ee0-8403-29700ac0dd61.json) (models).

**Computed premise delta** (`truth frontier-diff`, base `87857479e`):

- *Support alternatives added:* `0a995309` (argument 1), `813a9181`
  (argument 2), `5f93d4f0` (argument 4), `66aecdd7` (argument 5), and #1941's
  `5c1aba17` and `fdd2b1cf` (arguments A and B, which now reach the root
  through argument 5).
- *Bare premises now reaching the root:* `43651417` (NAR), `b517ca3e`
  (holders at `w`), and #1941's `71fc097b` and `9856239a` (through argument
  B).

**Laws** (`Model.Laws`).

1. With P2′, P3′ and holders at `w`, no holder is contingent at `w`
   (constructive). With excluded middle every holder is concrete, exists at
   `w` and is NECESSARY_2 there. #1897 derived the necessity only for *some*
   holder (`256a5e0a`); law 1 is the universal form.
2. Add a common root of `G` (`ActualCommonRootAt`): every holder is that
   root, or a NECESSARY_2 actual concretum directly grounded by it.
3. NAR excludes the second horn, so the common root is the only holder.

**Models.**

- Theist nonvacuity of arguments 1–5 (`theistG`).
- The necessary-through-another holder (§4).
- Omissions of argument 1:
  - without holders at `w`, a holder only at the non-actual world;
  - without P2′, the holder is the contingent `c`;
  - without P3′, a necessary non-concrete holder;
  - without NAR, §4.
- Two roots: both holders are necessary and underived. At most one root and
  the common root fail, and so do the conclusions of arguments 2–4.
- A root holder beside a derived holder: at most one root holds, at most one
  holder fails.
- Omissions of argument 5:
  - without at most one holder, a willed non-GOD_4 holder beside a GOD_4
    holder without will;
  - without `65e0179f`;
  - without `0050b6ed`;
  - without `fdd2b1cf`, which is #1941's chance rival.

## 4. Step 1: is the holder an actual root?

**What follows without new premises.** Law 1: given P2′, P3′ and existence at
`w`, every holder is a necessary concrete being. Nothing follows about its
grounds: `G` is unconstrained by the holder premises, and law 2 shows the exact
remainder. Under a common root, a holder is the root or *a necessary being
grounded by the root*. Necessity does not exclude being grounded.

**Which premise closes it.** NAR, in its general form over all actual
concreta. The holder-restricted form ("every NECESSARY_2 holder is an actual
root") is weaker and would suffice. With law 1, however, it would make
argument 1 nearly a transcription, and it would hide what the step assumes
about necessary beings in general. The general form is therefore used, and the
restricted form is not registered.

The sibling "whatever actual concretum has an actual concrete ground at `w`
is contingent at `w`" implies NAR constructively and is equivalent to it with
excluded middle. Excluded middle is closed (self-evident), so the sibling is
not registered. No strength order is claimed: no classical model could
separate the two.

**Warrant for NAR.** Its warrant is **direct prima facie plausibility**: that
what could not have failed to exist does not owe its existence to another.
None of the following is independent support:

- *Aseity of modal necessity* restates NAR.
- *#1941 part A* is only a scope remark: it excludes necessitating sources of
  *contingent* effects, so it leaves a ground of a necessary being untouched.
- *Coherence with the holder's two-way profile* is not support. #1897's
  two-way profile concerns giving, and nothing relates giving to `G` here.
- *Free creation* (ST I q.19 a.3; q.104 a.3, navigation) entails NAR only
  within classical theism, so it begs the question against the rival.

Provisional judgment: **moderate**, on prima facie plausibility alone. The
contrary combination (a modally necessary being that nonetheless has an
actual ground) is formally satisfiable (model `NecessaryThroughAnother`) and has
a developed defence in the causal register (Avicenna; Neoplatonic emanation).
That defence reaches `G` only through `cb1cdea9`. The sourced `8c3870b7` is
read here as NECESSARY_3/4, so it is not counted as support for the rival. No argument found here discharges NAR.

**Strongest rival: a necessary-through-another holder.** Model
`NecessaryThroughAnother`:

- a root `g`: GOD_4, intellect, common root, the only root;
- a necessary `d` that `g` grounds, and which alone holds the power for `q`.
  `d` gives the contingent `c` being at the actual world and withholds it at
  the other, so it is a two-way giver that satisfies #1897's creator reading
  and factive giving.

The model satisfies excluded middle, P2′, P3′, holders at `w`, `0c27f65a` and
`49fdec01`. NAR fails, and so do the holder conclusions of arguments 1–3: `d`
is not an actual root, has no intellect and is not GOD_4. The model's own
conjuncts carry this; it shows a non-entailment only. In it `g` gives nothing:
`g` grounds `d` without any giving.

*Encoding.* In all models:
- `G` is the same at both worlds;
- the `Ontic` causal field is empty;
- a holder holds every power.

In the argument-1 omission models other than this one, nothing gives
anything. None of this bears on argument 1's premises, which do not mention
giving or the `Ontic` causal field.

- *Target:* NAR, hence argument 1.
- *Mechanism:* a NECESSARY_2 actual concretum with an actual concrete `G`-ground
  holds the power for `q`.
- *Independent justification:* that a modally necessary being can have a
  cause has a developed defence: Avicenna's necessary in itself versus
  necessary through another (*The Healing* I.6, cited in
  `contingency-receptivity-c2.md`), and Neoplatonic emanation of necessary
  intelligences. It bears on NAR through `cb1cdea9`.
- *Relevance:* Avicenna's Active Intellect, a necessary emanated being, gives
  forms to sublunary contingents.
- *Status:* **live as a rival to NAR; weaker at the holder.** In the typed
  premises the historical necessitarian system does not deny P4′ or P2′: if
  nothing is contingent at `w`, P4′ holds vacuously, and P2′ holds for any
  holder existing at some accessible world. It denies `c76b6e2c` ("some
  concrete being is CONTINGENCY_1 at `w`"), a premise of #1941's argument B
  and of #1897's withholding route `f872a512`, together with the two-way
  profile. So the historical system is not a model of the route through
  `c76b6e2c`. The rival at the holder is a variant that keeps contingent
  concreta and a two-way holder.
- *A further instance.* The Nicene structure ("God from God … through him
  all things were made") has the hybrid's shape *if* the divine persons were
  distinct concreta in `B` and their origin fell under `G`. The case's root
  will need those creed commitments. NAR is compatible with them on either of
  two conditions: `G` excludes intra-divine origin (a principle, not a cause;
  navigation only), or the persons are not distinct concreta in this carrier
  (sense GOD_AS_DIVINE_BEING_VERSUS_DIVINE_1 of disambiguation `852f282b`:
  every quantified God is a divine being, not a divine person). That
  compatibility condition is recorded, not derived.

**Price of the rival.**

- *Derived* (given `0c27f65a` and law 1): it denies NAR, and it has one more
  concretum, since the holder is distinct from the root.
- *Recorded features of the historical Avicennian version, not derived
  here:* necessitated emanation and fixed giving (NECESSITATE_2) at the first
  source. Reaching them needs `cb1cdea9` plus an unstated
  causing-or-grounding to giving bridge. The model above shows that a `G`-ground
  need not give at all.
- *Not derived:* that the rival "needs two necessary beings". `0c27f65a`
  asserts no necessity of the root at other worlds, and a model cannot show a
  need.

None of these is shown to conflict with an accepted floor item.

## 5. Step 2: one root, two sources

Two uniqueness sources are used. They are different premises, not two
presentations of one premise.

| Source | Where its uniqueness comes from | Used in | Rival and price |
| --- | --- | --- | --- |
| Common-root reach, `0c27f65a` (via `6eb3fb5c`) | the genus principle at being `da09703b` (whatever is maximal in being causes every other being's being) with the esse-cause bridge `cb1cdea9`: the root grounds every other actual concretum, so any second root is grounded, a contradiction (uniqueness through a common upstream) | arguments 2, 3 | two independent roots, neither causing the other: denies the genus principle's universal reach (`necessary-simple-plurality.md`, cooperation versus common origin) |
| At most one actual root, `49fdec01` (via `c056ad5c`) | `a576300f` (at most one actual being has esse identical with its essence), from De ente's inventory of the modes of multiplication (`860eae63`), with `457698e4` and `cb1cdea9` making every root such a being. It gives only "any two actual roots are the same" | argument 4, hence 5 | two pure acts differing by primitive thisness (`necessary-simple-plurality.md`, "Can primitive thisness distinguish two pure acts?"): it denies that the inventory is exhaustive. Its price, recorded there: a bare numerical difference with no qualitative or receptive ground, which the same note finds owes an account of what individuates without limiting |

**Bridge 5 scope.** This slice *applies* an existing uniqueness node
(`49fdec01`, whose uniqueness premise `a576300f` is De ente's
no-multiplication argument) at the holder. It builds no
no-multiplication-without-a-limiting-principle *interface*.

- *Delivered for bridge 5:*
  - one consumer of the existing node;
  - the finding that uniqueness is not where the holder identification
    fails.
- *Remaining for bridge 5:* the interface itself. That is one parametric
  statement "plurality of unreceived, unlimited beings needs a
  differentiator, and a differentiator is a limit", with `a576300f` and the
  other uniqueness premises registered against it.

**Shared dependencies.** Both sources use the esse-cause bridge `cb1cdea9`
and existing-in-act `0436de86`. Argument 2 also carries `0c27f65a`'s governor
and naming premises (`571094b6`, `1ec205ed`) and the transfer premises.

Uniqueness alone does not identify the holder. In the
necessary-through-another model both `0c27f65a` and `49fdec01` hold, and the
holder is still not the root. **The identification's crux is NAR, not
uniqueness.** This is the main finding of the slice.

## 6. What changes for will versus chance

- **`813a9181` now has a verified derivation** (argument 2): from `0c27f65a`'s
  intellect, through NAR, P2′, P3′ and existence at `w`. The holder's intellect
  *is* the root's intellect, so this adds no warrant for intellect at the root.
  It does locate the chance rival's commitments more exactly. A one-power
  chancy source with all the will bridges must now deny one of:
  - `0c27f65a`'s intellect or reach (the governor route, or the genus
    principle at being);
  - NAR, P2′ or P3′.
- **Argument B (`fdd2b1cf`) gets a root consumer** (argument 5, conclusion
  `66aecdd7`).
  - *Honest weight:* argument 5 shares the will-specific premise `090be689`
    (through argument A) with `571e36f0` and `13338e9c`. So it adds no
    independent support for the will-follows-intellect step.
  - *Its intellect input* is the governor endpoint `0c27f65a`, not
    `29818edd` (every GOD_4 has intellect, a premise of `571e36f0`).
    `0c27f65a` is a one-witness endpoint: it does not say that arbitrary GOD_4
    bearers have intellect. Through `0050b6ed` and at most one holder,
    argument 5's premises jointly imply that every GOD_4 has that witness's
    intellect. It is an
    alternative intellect bundle, not a re-presentation of `571e36f0`.
  - *What it adds at the exercise level:* under its premises, the GOD_4 whose
    will `66aecdd7` asserts is the very being whose giving of the actual
    contingents is willed rather than CHANCE_3 (`fdd2b1cf`). Carrying that
    exercise-level fact into a root-route statement still needs the bridge
    from rational-power giving to the `Wills` relation of `a94c5dfc` (gap 4).
- **The `0050b6ed` converse is now derived** (argument 3). With `0050b6ed`, the
  holders at `w` are exactly the GOD_4s existing at `w`, under the premises of
  arguments 1 and 3.

## 7. Matched-scope comparison (same explanandum)

Explanandum: a necessary being holds, at `w`, the power for the joint absence
of all actual contingent concreta (P2′, P3′, existence at `w`), and there is a
common root of `G` with intellect (`0c27f65a`).

| Criterion | Holder = root (NAR) | Holder grounded by the root |
| --- | --- | --- |
| Concreta needed for the explanandum (derived) | the root | the root and a distinct holder |
| Intellect at the holder | inherited from the root (argument 2) | open; the root's intellect does not transfer |
| Fit with independent families | coheres with the intellect, governor and De ente uniqueness routes | coheres with Avicennian necessary-through-another; the historical system denies `c76b6e2c` |
| Primitive owed | NAR | a NECESSARY_2 being with an actual concrete ground |
| Mode of the root's giving | not fixed by these premises | not fixed by these premises; necessitated emanation is a recorded feature of the historical version only, needing `cb1cdea9` and an unstated grounding-to-giving bridge |

**Verdict at this scope: a slight edge to the identification; otherwise
parity.**

- *The discriminating reason (parsimony):* given `0c27f65a` and law 1, the
  rival posits one more concretum (a holder distinct from the root). It adds
  no explanatory work for this explanandum: the holder's two-way giving is
  the same on both accounts.
- *What does not discriminate:* each side owes one primitive (NAR, or a
  necessary being with a ground), and the fit rows favour each side by its
  own allies.
- *Not counted:* that the historical system denies `c76b6e2c` is a fact about
  the rival's best source, not a defect of the variant itself.

## 8. Overall provisional judgment

- **Formal consequence:** verified, zero-axiom. Under excluded middle, P2′,
  P3′, existence at `w` and NAR, every holder is an actual root of `G`.
  - With `0c27f65a`, every holder is the common root, so it has intellect
    (`813a9181`) and is GOD_4.
  - With `49fdec01`, there is at most one holder, and #1941's willed holder
    yields GOD_4's will.
- **Warrant:**
  - *P2′ and P3′:* #1897's premises; their warrant is assessed there.
  - *Existence at `w`:* serious actualism about powers. No substantive
    objection identified.
  - *NAR:* moderate, on direct prima facie plausibility. It is the crux.
  - *Uniqueness:* inherited from the existing routes and assessed in their
    notes.
- **Strongest standing rival:** the necessary-through-another holder; its
  derived price is NAR's denial and one more concretum (§4).
- **Overall:** the holder–root identification is a reasonable provisional
  bridge **conditional on NAR**. Confidence in the consequence is high;
  confidence in NAR is moderate.

**Revision conditions.**

- *Toward the identification:* a derivation of NAR from independently
  supported premises (gap 1). An argument from simplicity (#555-type, e.g.
  that a necessitating giving of a distinct being would make the giver's
  nature include its effect) bears on NAR only with an explicit bridge from
  `G` to giving. Without it, it constrains giving, not grounding.
- *Against the identification:*
  - a developed account of a NECESSARY_2 being with an actual ground that
    itself gives two-way;
  - evidence that ST I q.44 a.1 ad 2 (`8c3870b7`) means NECESSARY_2, with a
    cause that is an actual concrete `G`-ground;
  - a defence of multiple underived roots that answers the multiplication
    argument.

## 9. Claim versus type

| Record | Prose | Lean type | Check |
| --- | --- | --- | --- |
| holders at `w` | holders exist at `w` | `∀ y, PowerFor w y q → F.history.ontic.ExistsAt w y` | this power only |
| NAR | NECESSARY_2 actual concreta are roots | `∀ x, ActualConcrete m w x → NecessaryAt m.ontic w x → ActualRoot m w x` | one world; actual concreta only; not NECESSARY_3/4 |
| holders are actual roots | every holder is an actual root of `G` | `∀ y, PowerFor w y q → ActualRoot (groundProfile F concrete G) w y` | universal; no existence |
| at most one holder | any two holders are equal | `∀ y z, PowerFor w y q → PowerFor w z q → y = z` | no existence |
| holders are GOD_4 | every holder is GOD_4 | `∀ y, PowerFor w y q → IsGod y` | no existence |
| `813a9181` (reused) | holders HAS_INTELLECT_1 | `∀ y, PowerFor w y q → HasIntellect y` | derived by argument 2 |
| `66aecdd7` (reused) | God has will | `∀ g, IsGod g → HasWill g` | world-free conclusion from premises at one `w`, as in #1941's argument D |
| `0c27f65a`, `49fdec01` (reused) | common GOD_4 root with intellect; at most one root | at `groundProfile F concrete G` | instantiation of schematic profile premises; concreteness sense owed (§2, gap 3) |

Every hypothesis of each theorem is a listed premise (bind-check). No source is
attributed; no claim record is added.

## 10. Remaining gaps and next tests

1. **Warrant for NAR** (decisive). Next test: derive NAR from two premises.
   - (a) The root's giving to every `G`-grounded concretum is two-way.
   - (b) A `G`-grounded concretum exists at `v` only if its `G`-ground gives it
     being at `v`. This is an explicit `G`-to-giving bridge.

   Then a `G`-grounded concretum is absent where the giving is withheld, so it
   is not NECESSARY_2. Premise (b) is the new bridge that rigor contract 5
   requires to be explicit.

   Premise (a) extends #1897's two-way profile, which is derived only for the
   giving of the actual contingents, to putatively necessary beings. That
   extension is exactly what the rival denies, and it is close to the
   theist-internal free-creation premise. So (a) relocates the question rather
   than discharging it, unless (a) is itself derived. One candidate
   derivation: one power, an invariant set-up and simplicity give a uniform
   mode of giving across effects (#555; #1897 gap 6).

   **Done in [nar-derivation.md](nar-derivation.md).** NAR follows from (a),
   the root-restricted rigidity bridge (b2) and the common root (N1). Under
   (b2) and its companions, (a) is equivalent to NAR. Uniformity does not
   follow from one power, an invariant set-up and willed exercise
   (mixed-mode root model). (a) also follows from the will route (WN and SS,
   N3), which, on the means-to-end reading of `EndRequires`, moves the crux
   to WN.
2. **Existence of a holder at `w`:** the arguments are universal over holders.
   #1897's P1′ supplies existence; with argument 3 it gives GOD_4's existence
   at `w` as a further route, which is not registered here.
3. **Concreteness sense, an owed identification.** Arguments 2–4 instantiate
   the root nodes' profile `concrete` with the holder premises' `concrete`.
   - `49fdec01`'s label reads CONCRETE_6 (HasEsseInRe, DEF `008cb21a`),
     without a definition link.
   - P3′ `a6906cab` speaks of a "selected world-independent concreteness
     predicate".

   Argument 4 instantiates both with one `concrete`. That is a sense
   identification still owed, not established. A parameter-level sense tag
   (#1784) on both, or a bridge statement, would discharge or refute it.
4. **Root consumer at the exercise level:** a bridge from giving by a rational
   power to the `Wills` relation of `a94c5dfc` (#1941 gap 3) remains unbuilt.
5. **A ground for P2′ that does not presuppose existence at `w`:** with
   symmetric access, existence at the absence world and NAR at that world
   might replace the existence premise. Not tried.
6. **Bridge 5 interface:** the parametric no-multiplication statement (§5)
   remains to be built.

## 11. Edits outside the batch

- **Existing records, minimal reconciliation:**
  - the connection-plan paraphrase of `813a9181` (via
    `specs/will-versus-chance.toml`) now points at argument 2;
  - the gap lists of `docs/notes/will-versus-chance.md` §10 and
    `docs/notes/pruss-power-premises.md` §9 point here.
- **Generated:** `TruthCore/Imports/Causality.lean` and
  `TruthCore/Imports/Results/Causality.lean`. The docs index is unchanged.
- **New:**
  - the two Lean modules (Challenge generated);
  - the spec and its generated records;
  - this note;
  - attempt records.
