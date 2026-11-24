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
| holders are actual roots | `ActualAbsenceHoldersAreActualRoots F PowerFor concrete G w` | derived (argument 1) |
| at most one holder | `AtMostOneActualAbsenceHolder` | derived (argument 4) |
| holders are GOD_4 | `ActualAbsenceHoldersAreGod` | derived (argument 3) |

**The frame join.** The holder premises live on the shared `CausalityFrame`
(#1784); the root nodes on a `Profile` (#505). They are joined only through
the existing adapter `FirstMoverNecessity.groundProfile F concrete G =
⟨F.history.ontic, concrete, G⟩`: the profile on the frame's own world-relative
existence, with the holder premises' `concrete` predicate and a selected
grounding relation `G` that stays a parameter. Two consequences:

- **No relation is identified.** `G` is not the frame's `GivesAt`, `CausesIn`,
  `DependsForBeing` or `PriorSimply`; no premise relates them (rigor contract
  5; #1626). In particular, "the holder gives each actual contingent being"
  (#1897's creator reading `9f7b1778`) is *not* used to make the holder their
  ground.
- **One existence predicate and one `concrete`.** The root premises `0c27f65a`
  and `49fdec01` are schematic in their profile; the arguments instantiate
  them at `groundProfile F concrete G`. That is a choice of interpretation: the
  root node's existence and concreteness are the holder premises'. It is
  explicit in every theorem type and is an equality of the *same* kind of
  primitive (world-relative existence, DEF-KANT-ONTOLOGICAL-MODEL), not an
  identification of two relations. The `concrete` parameter is untagged in
  both families (its sense is recorded only through the CONCRETE
  disambiguation link), so the sense check cannot confirm or refute that the
  two uses agree; this is gap 3 below.

**Semantic grounding of NAR.** NAR introduces no relation. It relates two
existing ones: modal necessity (NECESSARY_2, DEF `38b92bb6`) and having an actual
concrete ground in `G` (DEF `a1b2e330`).

- *Meaning:* whatever could not have been absent from any accessible world has
  no actual concrete ground; it exists from itself, not "through another".
- *Example:* on classical theism, God; every creature is grounded and, being
  freely created, modally contingent.
- *Counterexample (proposed):* Avicenna's intellects, necessary through the
  First's necessary emanation.
- *Non-example of the issue:* the tertia via's "necessary beings that have
  their necessity from another" are NECESSARY_3/NECESSARY_4 (disambiguation
  `83264cf5`): incorruptible, not modally necessary. On Aquinas's own account
  they are modally contingent, since God could have refrained from creating
  them (ST I q.19 a.3, navigation). So the tertia via does not conflict with
  NAR.
- *Structure:* NAR is not an order property of `G`; it is universal over
  actual concreta at one world. With excluded middle it is equivalent to "no
  actual concretum with an actual concrete ground at `w` is NECESSARY_2 at
  `w`".
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

New statements: holders at `w` `b517ca3e`, NAR `43651417`, holders are actual
roots `0a995309`, at most one holder `5f93d4f0`, holders are GOD_4 `2146ebc9`,
controls `4c28b2d3`. Attempts `3c556cdd` (derivation) and `f68fa861`
(models).

**Computed premise delta** (`truth frontier-diff`, base `8b4eba77e`): six
verified support alternatives added (arguments 1, 2, 4, 5, and #1941's A and B,
which now reach the root through argument 5); four bare premises now reach the
root (NAR, holders at `w`, and #1941's `71fc097b` and `9856239a` through
argument B); the lowest expanded-route cost is unchanged (16).

**Laws** (`Model.Laws`). (1) With P2′, P3′ and holders at `w`, no holder is
contingent at `w` (constructive); with excluded middle every holder is
concrete, exists at `w` and is NECESSARY_2 there. #1897 derived the necessity
only for *some* holder (`256a5e0a`); law 1 is the universal form. (2) Add a
common root of `G` (`ActualCommonRootAt`): every holder is that root, or a
NECESSARY_2 actual concretum directly grounded by it. (3) NAR excludes the
second horn, so the common root is the only holder.

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

**Which premise closes it.** NAR, stated in the weakest form the argument uses.
Its stronger sibling "whatever has an actual concrete ground at `w` is
contingent at `w`" implies it constructively and is equivalent to it with
excluded middle. Excluded middle is closed (self-evident), so the sibling is
not registered, and no strength order is claimed: no classical model could
separate the two.

**Positive warrant for NAR.**

- *Aseity of modal necessity.* If a being's existence in every accessible
  world is owed to another, it holds only because that other's giving is fixed
  across worlds. #1941 part A shows that a necessitating source is excluded
  for *contingent* effects, but a source that necessitates a *necessary*
  effect is not excluded there. So NAR adds content beyond part A: no
  necessitated emanation of a distinct necessary being.
- *Free creation.* On classical theism every being other than the first is
  given being freely (ST I q.19 a.3; q.104 a.3, navigation) and is therefore
  modally contingent. That supports NAR only *within* the theist hypothesis:
  as evidence against the rival below it begs the question.
- *Coherence with the holder's own profile.* #1897 derived that the holder
  gives the actual contingents by a two-way (withholding) profile. A hybrid
  holder that is necessarily emanated but itself gives two-way is not
  excluded by that profile; it is only not supported by it.

Provisional judgment on NAR: **prima facie plausible and open**. Its
non-question-begging support is the general demand that modal necessity be
from the being itself. That demand is contested by a developed tradition, and
no argument found here discharges it.

**Strongest rival: the necessary-through-another holder.** Model
`NecessaryThroughAnother`: a root `g` (GOD_4, intellect, common root, the only
root) and a necessary `d` that `g` grounds, which alone holds the power for
`q`. `d` gives the contingent `c` being at the actual world and withholds it at
the other, so it is a two-way giver that satisfies #1897's creator reading and
factive giving. The model satisfies excluded middle, P2′, P3′, holders at `w`,
`0c27f65a` and `49fdec01`. NAR fails, and so do the holder conclusions of
arguments 1–3: `d` is not an actual root, has no intellect and is not GOD_4.
The model's own conjuncts carry this; it shows a non-entailment only.

*Encoding.* In all models `G` is the same at both worlds, the `Ontic` causal
field is empty, and a holder holds every power. In the argument-1 omission
models other than this one, nothing gives anything. None of this bears on
argument 1's premises, which do not mention giving or the `Ontic` causal
field.

- *Target:* NAR, hence argument 1.
- *Mechanism:* a necessary first necessarily emanates a distinct necessary
  being, which holds the two-way power over the actual contingents.
- *Independent justification:* Avicenna's distinction of necessary in itself
  and necessary through another (*The Healing* I.6, cited in
  `contingency-receptivity-c2.md`), and Neoplatonic emanation of necessary
  intelligences. Both are developed positions with arguments of their own.
- *Relevance:* Avicenna's Active Intellect, a necessary emanated being, gives
  forms to sublunary contingents.
- *Status:* **live as a rival to NAR; weak as a rival at the holder.** The
  historical Avicennian system is necessitarian throughout. It denies P4′/P2′
  (no accessible world lacks the actual contingents), so it is not a model of
  the holder premises. The rival at the holder is a *hybrid*: necessary
  emanation above, two-way giving below. No developed source defends that
  combination. It is recorded as the formal residue NAR excludes, not as an
  established alternative.

**Price of the hybrid**, derived or recorded:

1. It denies NAR (model).
2. It must give the root a necessitated giving toward at least one distinct
   necessary being. That is consistent with #1941 part A, which constrains only
   contingent effects, but it reintroduces fixed giving (NECESSITATE_2) at the
   first source.
3. It needs two necessary beings at `w`. That is a plurality of necessary
   concreta, though not of roots, so `49fdec01` does not exclude it (model).
4. Recorded, not derived: the hybrid must explain why the first's giving is
   fixed while the intermediary's giving of the contingents varies. The theist
   explains the variation by a two-way power at the first. The hybrid places a
   two-way power at a being that receives its own being by necessitation, with
   no stated reason for the change of mode.

None of these is shown to conflict with an accepted floor item.

## 5. Step 2: one root, two sources

Two uniqueness sources are used. They are different premises, not two
presentations of one premise.

| Source | Where its uniqueness comes from | Used in | Rival and price |
| --- | --- | --- | --- |
| Common-root reach, `0c27f65a` (via `6eb3fb5c`) | the genus principle at being `da09703b` (whatever is maximal in being causes every other being's being) with the esse-cause bridge `cb1cdea9`: the root grounds every other actual concretum, so any second root is grounded, a contradiction (uniqueness through a common upstream) | arguments 2, 3 | two independent roots, neither causing the other: denies the genus principle's universal reach (`necessary-simple-plurality.md`, cooperation versus common origin) |
| At most one actual root, `49fdec01` (via `c056ad5c`) | `a576300f` (at most one actual being has esse identical with its essence), from De ente's inventory of the modes of multiplication (`860eae63`), with `457698e4` and `cb1cdea9` making every root such a being. **This is the no-multiplication-without-a-limiting-principle interface of #1926 bridge 5**: plurality needs a differentiator, and every listed differentiator (difference, reception, matter) is a limit | argument 4, hence 5 | two pure acts differing by primitive thisness (`necessary-simple-plurality.md`, "Can primitive thisness distinguish two pure acts?"): it denies that the inventory is exhaustive. Its price, recorded there: a bare numerical difference with no qualitative or receptive ground, which the same note finds owes an account of what individuates without limiting |

**Shared dependencies.** Both sources use the esse-cause bridge `cb1cdea9`
(an actual concretum's distinct esse cause is its actual concrete ground) and
existing-in-act `0436de86`. Argument 2 also carries `0c27f65a`'s governor and
naming premises (`571094b6`, `1ec205ed`) and the transfer premises. These are
the intellect route's own dependencies, not new ones.

Uniqueness alone does not identify the holder. In the
necessary-through-another model both `0c27f65a` and `49fdec01` hold, and the
holder is still not the root. **The identification's crux is NAR, not
uniqueness.** This is the main finding of the slice.

## 6. What changes for will versus chance

- `813a9181` now has a verified derivation (argument 2): from 0c27f65a's
  intellect, through NAR, P2′, P3′ and existence at `w`. The holder's intellect
  *is* the root's intellect. This adds no warrant for intellect at the root.
  It locates the chance rival's commitments more exactly: a one-power chancy
  source with all the will bridges must now deny 0c27f65a's intellect or reach
  (the governor route, or the genus principle at being), or NAR, P2′ or P3′.
- Argument B (`fdd2b1cf`) gets a root consumer (argument 5, conclusion
  `66aecdd7`).
  - *Honest weight:* its expanded bundle contains the intellect route of
    `571e36f0`: `813a9181` comes from `0c27f65a`'s intellect, and will follows
    intellect `090be689` is used through argument A. That route already gives
    `66aecdd7`, so argument 5 adds no independent warrant for God's will at the
    capacity level.
  - *What it adds:* under its premises, the GOD_4 whose will `66aecdd7`
    asserts is the very being whose giving of the actual contingents is willed
    rather than CHANCE_3. That is an exercise-level fact (`fdd2b1cf`) that
    `571e36f0` does not state. Carrying it into a root-route statement still
    needs the bridge from rational-power giving to the `Wills` relation of
    `a94c5dfc` (gap 4).
- The `0050b6ed` converse is now derived (argument 3). With `0050b6ed`, the
  holders at `w` are exactly the GOD_4s existing at `w`, under the premises of
  arguments 1 and 3.

## 7. Matched-scope comparison (same explanandum)

Explanandum: a necessary being holds, at `w`, the power for the joint absence
of all actual contingent concreta (P2′, P3′, existence at `w`), and there is a
common root of `G` with intellect.

| Criterion | Holder = root (NAR) | Holder necessary through the root |
| --- | --- | --- |
| Number of necessary concreta | one | at least two |
| Mode of the root's giving | two-way toward the contingents (#1897) | fixed toward the intermediary; the intermediary two-way |
| Intellect at the holder | inherited from the root (argument 2) | open; the root's intellect does not transfer |
| Fit with independent families | coheres with the intellect, governor and De ente uniqueness routes | coheres with emanation schemes above the intermediary; those schemes are necessitarian below as well, so they reject P2′ |
| Primitive owed | NAR (aseity of modal necessity) | a necessitated emanation plus a change of mode at the intermediary |

**Verdict at this scope: a slight edge to the identification; otherwise
parity.**

- *The discriminating reason.* The rival adds a second necessary being and a
  necessitated emanation. Neither does any work in explaining this
  explanandum: the holder's two-way giving is the same on both accounts.
- *What does not discriminate.* Each side owes one primitive (NAR, or a
  necessitated emanation with a change of mode). The fit rows favour each side
  by its own allies, so they are not evidence.
- *Not counted.* That emanation schemes reject P2′ is a fact about the
  rival's best sources, not a defect of the hybrid itself.

## 8. Overall provisional judgment

- **Formal consequence:** verified, zero-axiom. Under excluded middle, P2′, P3′,
  existence at `w`, NAR and either uniqueness source, every holder is the
  selected root. With `0c27f65a`, every holder has intellect (`813a9181`) and
  is GOD_4. With `49fdec01`, there is at most one holder, and #1941's willed
  holder yields GOD_4's will.
- **Warrant:**
  - *P2′ and P3′:* #1897's premises; their warrant is assessed there.
  - *Existence at `w`:* near-analytic for an actualist account of powers. No
    substantive objection identified.
  - *NAR:* prima facie plausible, open. It is the crux.
  - *Uniqueness:* inherited from the existing routes and assessed in their
    notes.
- **Strongest standing rival:** the necessary-through-another holder; its price
  is in §4.
- **Overall:** the holder–root identification is a reasonable provisional
  bridge **conditional on NAR**. Confidence in the consequence is high.
  Confidence that NAR holds is moderate and rests mainly on the aseity of modal
  necessity.

**Revision conditions.**

- *Toward the identification:* an argument that modal necessity cannot be
  received, e.g. that a necessitating giving of a distinct being would make the
  giver's nature include its effect, contrary to simplicity (#555-type). This
  would give NAR non-theist-internal support.
- *Against:* a developed account of a necessary being necessarily emanated
  from another and itself giving two-way, or a defence of multiple underived
  necessary roots that answers the multiplication argument.

## 9. Claim versus type

| Record | Prose | Lean type | Check |
| --- | --- | --- | --- |
| holders at `w` | holders exist at `w` | `∀ y, PowerFor w y q → F.history.ontic.ExistsAt w y` | this power only |
| NAR | NECESSARY_2 actual concreta are roots | `∀ x, ActualConcrete m w x → NecessaryAt m.ontic w x → ActualRoot m w x` | one world; not NECESSARY_3/4 |
| holders are actual roots | every holder is an actual root of `G` | `∀ y, PowerFor w y q → ActualRoot (groundProfile F concrete G) w y` | universal; no existence |
| at most one holder | any two holders are equal | `∀ y z, PowerFor w y q → PowerFor w z q → y = z` | no existence |
| holders are GOD_4 | every holder is GOD_4 | `∀ y, PowerFor w y q → IsGod y` | no existence |
| `813a9181` (reused) | holders HAS_INTELLECT_1 | `∀ y, PowerFor w y q → HasIntellect y` | derived by argument 2 |
| `66aecdd7` (reused) | God has will | `∀ g, IsGod g → HasWill g` | world-free conclusion from premises at one `w`, as in #1941's argument D |
| `0c27f65a`, `49fdec01` (reused) | common GOD_4 root with intellect; at most one root | at `groundProfile F concrete G` | instantiation of schematic profile premises, see §2 |

Every hypothesis of each theorem is a listed premise (bind-check). No source is
attributed; no claim record is added.

## 10. Remaining gaps and next tests

1. **Warrant for NAR** (decisive): a non-theist-internal argument that modal
   necessity cannot be had from another. One test is whether #555's
   simplicity collapse extends to a necessitated emanation of a distinct
   necessary being, i.e. whether a simple source whose giving is fixed toward
   one effect can be two-way toward others (gap 6 of #1897 is the same
   question).
2. **Existence of a holder at `w`:** the arguments are universal over holders.
   #1897's P1′ supplies existence; with argument 3 it gives GOD_4's existence
   at `w` as a further route, which is not registered here.
3. **Concreteness sense:** `concrete` is an untagged parameter in both the
   holder premises and the root nodes. A parameter-level sense tag (#1784)
   would let `truth check` confirm that the instantiation uses one sense.
4. **Root consumer at the exercise level:** a bridge from giving by a rational
   power to the `Wills` relation of `a94c5dfc` (#1941 gap 3) remains unbuilt.
5. **A ground for P2′ that does not presuppose existence at `w`:** with
   symmetric access, existence at the absence world and NAR at that world
   might replace the existence premise. Not tried.

## 11. Edits outside the batch

- Existing records, minimal reconciliation: the connection-plan paraphrase of
  `813a9181` is unchanged (a derivation now exists; the dossier shows it);
  `docs/notes/will-versus-chance.md` §10 and
  `docs/notes/pruss-power-premises.md` §9 gap lists point here.
- Generated: `TruthCore/Imports/Causality.lean`,
  `TruthCore/Imports/Results/Causality.lean`, docs index.
- New: the two Lean modules (Challenge generated), the spec and its generated
  records, this note and attempt records.
