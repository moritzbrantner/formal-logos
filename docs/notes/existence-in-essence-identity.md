# Does existence belong to an essence when essence is esse? (#1887, B6 crux, 2026-11-23)

Issue #1887, next slice 1 after #1888 and #1889. God-existence stage of the
#143 root. Analyst formulations, attribution deferred (logic first); every
text used is listed in §11 as **read** (URL, section, date) or **navigation
only**. No source claim is made.

**Batch.** `specs/existence-in-essence-identity.toml`; vocabulary
`TruthCore.Ontology.ExistenceInEssence`; results
`TruthCore.Results.Ontology.ExistenceInEssence`; attempt
`a88768a8-8cc3-4f7d-aa0c-55e0ab323f22`.

**Question.** Does the thesis that existence never belongs to an essence
apply to a being whose essence is identical with its act of being (ST I q.3
a.4; *De ente* c.4)? It decides between two results of #1889:

- `f9b26559`: essence grounds necessity `54bafc9f` plus the unconditional
  bridge `565ccd6c` (esse = essence puts the being's existence in its nature)
  gives B6 `96971e31`, and through `39df9612` the necessity verdict at the
  foundational case;
- laws 3–4 of `TruthCore.Modal.ModalGrounding`: under existence-conditional
  essentialism (EC, `857654fe`) esse = essence is modally idle.

**Graph destination.** STMT-NECESSARY-CONCRETE-AT `b19ffd92`, through
`565ccd6c` → `96971e31` → `666f06a4` → `b27c88b0`. The rival verdict
`fe8c3a1d` ("every foundational being is contingent") gains a second support
bundle.

**Short answer.** The thesis does not apply to the identity *by itself* in
any sense examined. In the conceptual sense it is consistent with the
identity, with existence in the nature, and with necessity. It excludes the
identity only through a bridge making the concept adequate to the nature, and
Kant's arguments, as read, do not supply that bridge. In the essential-truth
sense (EC), its motivations at the identity case presuppose the being's
contingency or are the unresolved conceivability argument. Conversely, the
identity does not give existence in the nature by itself: that step needs
"exercise in the nature" (AN). AN's identified support is shared with the
power/potency route or merely removes a defeater. Parity at the foundational
being stands. The B6 crux is now located exactly in AN (§7).

## 1. Fixed meanings

| Sense | Meaning | Lean declaration | DEF |
|---|---|---|---|
| EXISTENCE_IN_ESSENCE_1, conceptual containment (a) | the proposition that `x` exists is a determination contained in the supplied concept of `x` | `ConceptContainsExistence` | `90353211` |
| EXISTENCE_IN_ESSENCE_2, essential truth (b) | it lies in the nature of `x` (ESSENCE_5) that `x` exists, unconditionally | `EssentialExistence` | `1fda7b2c` |
| EXISTENCE_IN_ESSENCE_3, act identity (c) | `x`'s represented esse is its represented essence (ESSENCE_3 maps). An identity of principles, not a determination inside a quiddity; no world index | `EsseIsEssence` | `b2e22524` |
| EXISTENCE_IN_ESSENCE_4 (d) | NECESSARY_EXISTENCE_BY_OWN_NATURE_3, essence membership of the existence fact (reused, not bridged) | `EssenceReasonSeparation.OwnEssentialExistence` | `72a1e556` |
| EXISTENCE_IN_ESSENCE_5, consequential essential truth | some essential truth of `x` entails `x`'s existence | `NatureEntailsExistence` | `316780ef` |

The disambiguation is `f704b7ca` (EXISTENCE_IN_ESSENCE). (d) is kept as a
sense. Its profile type (existence facts in `InEssence`) cannot state an
existence-conditional essence, so no bridge to (b) is encoded.

**Two new primitives**, each with meaning, examples, exclusions and open
obligations in its DEF:

- `ConceptContent Contains x φ` (DEF `16c40fbe`): `φ` is a determination
  contained in the supplied concept of `x`. *Which* concept is meant is not
  part of the primitive. It is fixed by which premises hold of the supplied
  relation:
  - a concept **formed from effects** ("the first cause of whatever else
    exists"), which does not satisfy concept adequacy;
  - a concept **adequate to the nature** (the *ratio* in itself), which
    satisfies it by construction.
- `EsseExercisedAt Exercised v p` (DEF `25d4df96`): the principle `p` is in
  act at point `v`; for an esse principle, its act of being is exercised
  there. It is world-indexed, unlike the q.3 a.4 `InAct x esse`. It is
  registered as WORLD_RELATIVE_EXISTENCE_METAPHYSICAL_ESSE_NECESSITY_6 of
  DISAMB-EXISTENCE-ESSE-SUPPORT, beside `_1` (the existence fact `ExistsAt`)
  and `_5` (the frame respect `esse`).

**Points and access.** The frame's points are the represented (logical)
space; accessibility is real possibility. EC and "entails existence"
quantify over all points; necessity and contingency over accessible ones.
This is the distinction Kant draws in note 67 (§11) between the logical
possibility of a concept and the real possibility of a thing.

**Theses and bridges** (all OPEN, analyst formulations):

| Name | Content | Lean |
|---|---|---|
| KT, Kant's thesis (conceptual form) `9014eea0` | no determination contained in a being's concept entails that being's existence over the represented points | `ExistenceNotConceptual` |
| K1, concept adequacy `effbb158` | whatever lies in a being's nature is contained in the concept | `ConceptAdequateToEssence` |
| K2, identity in the concept (laws only) | whatever has esse = essence has its existence contained in the concept | `IdentityInConcept` |
| E-link, the act–fact link `3a2af70f` | a being's act of being is exercised exactly at the points where it exists | `EsseExercisedWhereExists` |
| AN, exercise in the nature `823d4312` | whatever has esse = essence has, in its nature, the unconditional exercise of its esse | `IdentityPutsExerciseInNature` |
| SA-essence at `x` (laws only) | every essential truth of `x` entails `x`'s existence (an unconditional predication of `x`) | `SeriousActualistEssenceAt` |

## 2. Results

| Result | Theorem | Premises ⊢ conclusion |
|---|---|---|
| `ca973127` (argument `cb110da0`) | `exerciseInNatureGivesEssentialExistence` | E-link `3a2af70f`, AN `823d4312` ⊢ `565ccd6c` |
| `63ac77e7` (argument `b08d83a2`) | `kantAdequacyFoundationalContingent` | KT `9014eea0`, K1 `effbb158`, essentialist account `9d8a8d2e`, unrequired-by-others `38200db5` ⊢ `fe8c3a1d` |
| `037bfce4` (argument `c9d8491f`) | `controls` | premise-free ⊢ laws and models `ac557772` |

- **`ca973127`** factors the bridge `565ccd6c`.
  - The act–fact link turns "the act of being of `x` is exercised" into "`x`
    exists", pointwise. Extensionality then identifies the two
    world-propositions inside the nature. The result uses `propext` and
    `funext`.
  - Neither premise mentions existence in a nature, so this is not a
    transcription.
  - Each premise is needed (factorization omissions 1–2).
  - Sense bridges: ESSENCE_3 → ESSENCE_5 through AN, and esse-as-act `_6` →
    existence-fact `_1` through E-link.
- **`63ac77e7`** is a second support bundle for the "possibly absent"
  verdict, beside the EC bundle `872a3832`. It replaces EC and the
  representability premise with Kant's thesis plus adequacy.
  - It is constructive, and each premise is needed (Kant-adequacy omissions
    1–4).
  - It is nonvacuous (`conditionalIdentity`).
  - **Its two concept premises must hold of one concept relation.** So it
    needs Kant's thesis to govern a concept *adequate to the nature*.

### Laws (`Model.Laws`)

1. KT excludes conceptual containment of existence, for every being.
2. KT + K1: no essential truth of any being entails that being's existence.
   This is EC's modal effect, without a representability premise.
3. KT + K1 + `565ccd6c` exclude every esse = essence identity.
4. KT + K2 exclude every esse = essence identity.
5. KT gives contingency only when every point is accessible from `w`
   (represented space = real possibility) and the being has a nonempty
   concept. The proof is classical.
6. EC + E-link + AN exclude every identity being whose absence is
   representable. So EC rejects AN, not E-link.
7. Under E-link, wherever an identity being exists, its essence is
   exercised. The conditional reading of AN holds of *every* identity being,
   necessary or not: under EC the identity contributes only this.
8. (b) ⇒ (e).
9. Essence grounds necessity (EGN) + (e) ⇒ necessary.
10. EGN + contingent ⇒ ¬(e).
11. **Equivalence within essentialism.** Assume excluded middle, EGN, the
    essentialist account of possibility, that no other nature requires `x`,
    and that `x` exists at `w`. Then (e) at `x` ⇔ `x` is necessary at `w`.
12. **Serious-actualist essences.** EGN, every essential truth of `x` an
    unconditional predication, and a nonempty nature together make `x`
    necessary.

### Models (structural surrogates on the `ModalGrounding.Model` frames; not metaphysical possibility)

| Model | What holds | What fails | Shows | Admissible on |
|---|---|---|---|---|
| `kantAquinas` (access only to point `true`; both beings exist only there) | `true` is foundational with esse = essence; E-link, AN, `565ccd6c`, EGN, (b), necessity; its absence is representable (point `false`) but not really possible. For the concept formed from effects ("if anything else exists, `true` exists"): KT holds. For the adequate concept (the nature itself): K1 and K2 hold | for the effects concept: K1, K2 and (a). For the adequate concept: KT | KT in sense (a) is consistent with (c), (b), AN and necessity. KT blocks the identity only through K1 or K2. Omission model of K1 for law 3 and of K2 for law 4. Nonvacuity of `ca973127` | a Thomist reading of q.2 a.1 (not self-evident to us; self-evident in itself) with KT restricted to concepts from effects; Kant's note 67 on logical versus real possibility |
| `conditionalIdentity` (universal access; both beings only at `true`) | `true` is foundational with esse = essence; E-link; EC with only the conditional exercise in the nature; EGN; the essentialist account; unrequired-by-others; KT and K1 for the adequate concept; contingency; the "possibly absent" verdict | AN, `565ccd6c`, K2, (e) | identity + E-link + EC + a Kantian adequate concept + contingency are jointly satisfiable: the identity is modally idle there. Nonvacuity of `63ac77e7` | Fine/Lowe EC with KT extended to adequate concepts |
| Kant-adequacy omissions 1–4 | all premises of `63ac77e7` but one | that premise; the verdict | each premise is needed. Omission 4 (`requiredFrame`): the creature's nature requires `true` conditionally on its own existence | — |
| Factorization omissions 1–2 | 1: AN with `true`'s act exercised at every point. 2: E-link with no essences | 1: E-link. 2: AN. Both: `565ccd6c` | each premise of `ca973127` is needed. Omission 1 is a separation (an act exercised where its bearer is absent), admissible on no view examined | — |

Excluded middle is never omitted: every model is built in Lean.

## 3. The key test: does Kant's thesis reach the identity?

**Formal answer.**
- KT is about concepts. By itself it excludes only (a) (law 1).
- It reaches (b) through K1 (law 2), and excludes (c) only through K1 with
  `565ccd6c` (law 3), or through K2 (law 4).
- With neither bridge it is consistent with (c), (b), AN, E-link and
  necessity (`kantAquinas`).
- It gives *real* possibility of absence only by identifying represented
  with real possibility (law 5). Kant's note 67 explicitly refuses that
  identification ("concluding, from the possibility of a conception—which is
  logical—the possibility of a thing—which is real").

**Is a bridge warranted?** Three of Kant's arguments in the section read
(§11) bear on this.

1. **Existence is positing, not a real predicate.** "Being is evidently not
   a real predicate, that is, a conception of something which is added to the
   conception of some other thing. It is merely the positing of a thing."
   - *Target:* the ontological argument's step, sense (a).
   - *At the identity:* (c) does not make existence a determination added to
     a quiddity. On the reading it formalizes, the identity being has no
     quiddity distinct from its act. So the argument does not touch (c)
     unless every essence is a content of real predicates.
   - That premise denies (c) as an act. It does not show the act modally
     idle.
   - The Thomist can accept the positing thesis for every quidditative
     concept.
2. **The hundred thalers / adequacy argument.**
   - If existence added content, "my conception would not be an expression of
     the whole object, and would consequently be an inadequate conception of
     it". And "by whatever and by whatever number of predicates—even to the
     complete determination of it—I may cogitate a thing", existence adds
     nothing.
   - This is the closest Kant comes to K1. It is K1 in the form "the
     complete determination of a thing by real predicates is adequate to
     it".
   - At the identity case that form assumes the essence is exhaustively a set
     of real predicates. That is the same premise as in argument 1.
3. **Annihilation and the analytic/synthetic dilemma.**
   - "Annihilate its existence in thought, and you annihilate the thing itself
     with all its predicates; how then can there be any room for
     contradiction?"
   - Kant states the opposing claim and its burden himself: "There are certain
     subjects which cannot be annihilated in thought. But this is nothing more
     than saying: There exist subjects which are absolutely necessary—the very
     hypothesis which you are called upon to establish."
   - His own support is first-personal: "I find myself unable to form the
     slightest conception of a thing which when annihilated in thought with
     all its predicates, leaves behind a contradiction."
   - The dilemma rests on "every existential proposition is synthetical", as
     "every reasonable person must" confess.
   - Applied to *our* concepts, the argument is sound against a proof from
     concepts. Aquinas agrees: "not self-evident to us" (q.2 a.1).
   - Applied to a concept adequate to an identity being's nature, it
     *asserts* that annihilating the thing in thought leaves no
     contradiction. That is the claim that its absence is free of
     contradiction, which is the point in dispute. It uses the same
     structure Kant charges against his opponent. The symmetry is noted, not
     credited to either side.

**Result of the test.** A bridge (K1 for a Kantian concept, or K2) is needed,
and none of the arguments read establishes it at the identity case without
assuming that every essence is a content of real predicates. That assumption
does not show the identity modally idle. It denies the identity's
intelligibility: a rival to (c) (§5, Frege/Russell), not an application of
the thesis to it. The Kant-adequacy route `63ac77e7` therefore holds only
under that disputed extension.

## 4. Equivocation check: esse as act and existence as fact

`565ccd6c` does pass from one to the other.
- Its antecedent is an identity of world-invariant principles (`esseOf x =
  essenceOf x`).
- Its consequent is a world-indexed existence proposition (`fun v => ExistsAt
  v x`) in the nature.
- ST I q.3 a.4 ad 2 (read) separates the two: "to be" as the act of essence,
  which "we cannot understand" of God, and as the composition of a
  proposition, whose truth "we know … from His effects".

The factorization `ca973127` makes the passage explicit.
- **E-link** (act ↔ fact) is accepted by both essentialisms. It holds in
  `kantAquinas` and in `conditionalIdentity`.
- Its rival is the quantifier view (§5). That view rejects the act-of-being
  side as empty, not the equivalence.
- **AN** carries the whole modal dispute (law 6).

So `565ccd6c` is not an unflagged equivocation: it was already an explicit
sense bridge. But it bundled an uncontroversial act–fact link with the
substantive AN, and now they are separate.

**Boundary.** The step uses propositional extensionality inside the nature,
because `Essential` takes world-propositions, as in `ModalGrounding`. Fine's
essence is hyperintensional (navigation only). On that reading E-link alone
does not license substitution inside `□ₓ`, and `ca973127` needs a further
substitution premise. Recorded as open.

## 5. Arguments for "existence never belongs to an essence", at the identity

Each entry gives the target, mechanism, independent justification, and
relevance at the identity case.

- **Kant** (read). See §3.
  - *Target:* (a).
  - *Mechanism:* existence is positing, not content.
  - *Justification:* the analysis of judgement and the thalers.
  - *At the identity:* it reaches (b) or (c) only with K1 or K2. Its
    extension to an adequate concept of an act-essence is asserted, not
    argued. **No application to the identity without a bridge.**
- **Hume** (read, *Dialogues* IX).
  - *Text:* "Whatever we conceive as existent, we can also conceive as
    non-existent. There is no being, therefore, whose non-existence implies a
    contradiction."
  - *Target:* every necessary being, through conceivability.
  - *Hume and the ignorance reply.* He anticipates the "if we knew his whole
    essence" reply and answers that "this can never happen, while our
    faculties remain the same as at present". He concedes the argument
    extends to the Deity only "so far as we have any conception of him", and
    allows "unknown, inconceivable qualities, which can make his
    non-existence appear impossible".
  - *Where his reply turns.* It then becomes an identification objection
    (why not matter?), not a defence of possible absence.
  - *At the identity:* this is the conceivability argument assessed in #1888
    §2.1b. It is unresolved and rests there on the calibration premise.
    Hume's own scope ("our faculties") marks the same gap. **No new weight.**
- **Frege/Russell** (read as report, SEP *Existence*, introduction and §1).
  - *Target:* existence as a first-level property, that is, (a) and a
    property reading of (b).
  - *Mechanism:* existence is a second-order property (instantiation of a
    concept or propositional function).
  - *At the identity:* (b) in operator form ("it lies in the nature of `x`
    that `x` exists") is well-formed on the quantifier view, so the argument
    does not reach (b).
  - It reaches (c) only with a further thesis: there is no act of being
    beyond instantiation. That thesis is a **rival to (c)'s intelligibility**.
  - If it succeeds, the identity clause of `FoundationalAt` and q.3 a.4's
    premise lose their content. It does not support EC *at* an identity it
    deems empty.
  - SEP §3 reports the Linsky–Zalta/Williamson view on which every individual
    is a necessary existent. That view does not discriminate the
    foundational being either.
- **Fine** (read as report, SEP *Essential vs. Accidental Properties* §1.1,
  §3).
  - §3 reports Fine's objection that "existence is intuitively not a whatness
    essential property of every entity". Its scope is *every*.
  - §1.1 objects to the existence-conditioned characterization that it rules
    out existence being "modally essential to numbers (or God) but only
    modally accidental to Emma".
  - Both point toward existence being essential to *some* entities. They do
    **not** support EC at the identity.
  - The God-intuition is not credited (consistent with #1888 §4).
- **Serious actualism** (read as report, SEP *The Possibilism–Actualism
  Debate* §4.1.1; Plantinga's existence-conditioned essential properties
  §4.2.1).
  - *Mechanism:* an object must exist to have properties, so unconditional
    essential predications would make every bearer of a nature a necessary
    existent (law 12). EC is the conditionalization that keeps bearers
    contingent.
  - *Justification for ordinary concreta:* their contingency has independent
    evidence (generation and corruption).
  - *At the identity:* by law 11, within essentialism EC's effect at `x` is
    equivalent to `x`'s contingency. So the serious-actualist motivation for
    EC at the identity being **presupposes its contingency**. This is exactly
    #1888 revision condition (b)'s presupposition.
- **Aquinas** (read: ST I q.2 a.1, q.3 a.4 with ad 2, New Advent; *De ente*
  c.4, Miller).
  - *De ente:* "I can understand what a man is or what a phoenix is and
    nevertheless not know whether either has existence in reality". So
    existence is other than essence "unless perhaps there is something whose
    quiddity is its very own existence".
  - The *intellectus essentiae* argument therefore establishes
    existence-outside-essence only for essences understood without esse, and
    names the identity case as its exception.
  - *q.2 a.1:* "God exists" is self-evident in itself, because the predicate
    is included in the essence of the subject (God is His own existence). It
    is not self-evident to us, because we do not know God's essence.
  - Formally, Aquinas's position is `kantAquinas`: KT holds of the concept
    from effects; K1 and K2 hold of the adequate concept; (c) holds in re.
  - The step from identity to "the predicate is the same as the subject" is
    K2 for the adequate concept. Given q.3 a.4 ad 2's distinction, that step
    passes from the act to the composition: E-link plus AN. This is an
    analyst reading; no equivocation is attributed to Aquinas.

**Assessment.** None of these yields EC at the identity case. Each argument
either:
- concerns concepts and needs an unwarranted bridge (Kant);
- is the unresolved conceivability argument (Hume);
- denies the identity's intelligibility instead (Frege/Russell, and Kant read
  as "every essence is a content");
- points the other way (Fine); or
- presupposes the being's contingency (serious actualism).

Aquinas's own reason for distinct esse explicitly excludes the case.
**#1888 revision condition (b) (EC side) is assessed and not met.**

## 6. The symmetric test: motivation for unconditional essential existence at the identity

`conditionalIdentity` shows that the identity, with E-link, does not give (b).
The extra step is AN. Its candidate motivations:

1. *The exclusion reason lapses.* *De ente*'s reason for putting existence
   outside essence does not apply at the identity. This removes a defeater.
   It does not supply positive support: the absence of an objection is not a
   proof.
2. *Pure act has no potency to non-being.* This is AN in the dress of the
   power/potency account: PGP and C2 (`20d5fecd`, `e5d49f99`), whose extra
   content at the foundational being #1888 found unmotivated there. **Shared
   dependency, not independent warrant.**
3. *A principled cut.* AN's antecedent (c) is non-modal and specified
   independently, so the exemption is not gerrymandered, unlike a bare "unless
   necessary". This answers an ad hoc charge; it is not evidence that AN is
   true. EC's concrete/abstract cut lacks even this at `n` (#1888 §4), but
   lacking a defeater-answer is not lacking warrant either.
4. *Fit with essential existence for abstracta.* Fine-type views let numbers
   exist essentially, but the support for that (mathematical necessity) does
   not transfer to a concretum. Not credited.
5. *q.2 a.1's step.* This is K2 for the adequate concept, which presupposes AN
   with E-link (§5). Not independent.

So **no motivation for AN is identified that does not run through a
necessity-favouring general theory** (the power/potency account), just as no
motivation for EC at the identity is identified that does not presuppose
contingency there. Law 11 states the parity formally: inside essentialism,
the disputed essence thesis at an actual `x` is equivalent to the disputed
modal verdict at `x`. Essentialism alone cannot discriminate at the identity
case; any discrimination must come from outside it.

## 7. Provisional judgment (2026-11-23, evidence revision: this branch)

**Scope.** The B6 crux: whether, at a being with esse = essence (the
foundational case of #1889), "existence never belongs to an essence" makes
the identity modally idle, or the identity makes existence essential.
Criteria: the substantive objection standard, applied symmetrically, and
matching-scope comparison (#1888 §6).

1. **The Kant-type thesis does not apply to the identity on any assessed
   motivation without a bridge or a presupposition.**
   - In sense (a) it is consistent with identity, essential existence and
     necessity.
   - It reaches the identity only with concept adequacy for a Kantian concept,
     which Kant's arguments do not establish at an act-essence.
   - In sense (b) (EC) its motivations presuppose contingency or are the
     unresolved conceivability argument.
   - This meets #1888's "toward PGP" condition (d) **as stated**. Its effect
     is to close an "unassessed" entry, since EC's cut at `n` was already
     without identified motivation. It creates no relative standing for the
     necessity verdict, because of point 2.
2. **The identity does not give essential existence by itself.**
   - The step needs AN.
   - AN's identified support is shared with the power/potency route (so it is
     correlated with PGP/C2, not independent corroboration) or only removes a
     defeater.
   - `565ccd6c` keeps its direct-assumption option. But no direct ground for
     it at the identity case was identified that is not a ground for AN given
     E-link. So the support `f9b26559` (and `39df9612`) gives the necessity
     verdict rests, at this case, on AN's warrant.
3. **Parity at the foundational being stands, sharpened.**
   - Within essentialism the dispute *is* the modal verdict (law 11).
   - The B6 crux is located in AN, given E-link, which both sides accept.
   - The rival verdict now has two support bundles (EC + representability;
     Kant + adequacy). The second needs Kant's thesis extended to adequate
     concepts, which is disputed at exactly this case.
4. **Not established:** that existence belongs to the foundational being's
   nature; that it does not; any premise. No formal closure changes beyond
   the computed frontier delta (§12).

**Shared dependencies.**
- `ca973127` and `f9b26559` share EGN with the EC verdict `872a3832` and with
  `63ac77e7` (EGN is accepted by both essentialisms).
- AN is dialectically tied to PGP/C2 (point 2).
- `63ac77e7` shares the essentialist account `9d8a8d2e` and
  unrequired-by-others `38200db5` with `872a3832`.

## 8. Revision conditions (symmetric)

Toward EC at the identity, or possible absence:

- (a) An argument that every essence, including an act-essence, is
  adequately given by a concept of determinations (K1 for a concept KT
  governs). It must not presuppose that no essence is an act.
- (b) A defended reduction of the act of being to instantiation, the
  quantifier view's further thesis. This would remove (c) and the identity
  clause, not idle them.
- (c) A motivation for conditionalizing essences at an act-essence that does
  not run through the bearer's contingency. For example, a theory of essence
  on which natures state only what a thing is, defended on independent
  grounds and shown to cover act-essences.
- (d) #1888 conditions (a) and (g): a secondary conceiving of the absence, or
  modal rationalism without the calibration premise.

Toward AN, or necessity:

- (a) An argument from (c) to AN that does not pass through potency or power.
  For example, showing that the conditional form "if `x` exists, its act of
  being is exercised" fails to state the nature of an act-essence, on
  grounds EC accepts.
- (b) #1888 "toward PGP" (a) or (b): the actualist grounding demand, or PGP's
  completeness over incorruptibles, defended without presupposing a creator.
- (c) Independent warrant that some concretum exists necessarily.

Either way: a hyperintensional account of essence on which E-link does not
license substitution inside the nature would block `ca973127` as encoded and
require a separate substitution premise (§4).

## 9. Claim versus type

| Record | Prose | Lean type | Check |
|---|---|---|---|
| `3a2af70f` E-link | a being's act of being is exercised exactly where it exists | `∀ v x, EsseExercisedAt Exercised v (esseOf x) ↔ ExistsAt v x` | over all points, not only accessible ones; both directions |
| `823d4312` AN | an identity being has the unconditional exercise of its esse in its nature | `∀ x, esseOf x = essenceOf x → Essential x (fun v => Exercised v (esseOf x))` | unconditional proposition; no modality asserted |
| `9014eea0` KT | no determination in a being's concept entails its existence | `∀ x φ, Contains x φ → ¬ ∀ v, φ v → ExistsAt v x` | over represented points; says nothing about accessibility; the concept relation is a parameter |
| `effbb158` K1 | whatever lies in the nature is in the concept | `∀ x φ, Essential x φ → Contains x φ` | one direction only |
| `565ccd6c` (conclusion of `ca973127`) | esse = essence puts existence in the nature | `esseOf x = essenceOf x → Essential x (fun v => ExistsAt v x)` | unchanged; now derived from E-link and AN |
| `fe8c3a1d` (conclusion of `63ac77e7`) | every foundational being at `w` is contingent | `∀ f, FoundationalAt … f → ContingentAt … w f` | universal; asserts no foundational being |
| `ac557772` controls | laws 1–12, models | `Model.Controls` | law 5 classical; models are structural surrogates; law 11 needs excluded middle as a hypothesis |

Every hypothesis of each theorem is a listed premise. The definitions of
`ConceptContent` and `EsseExercisedAt` are parameter wrappers; no condition
is added to any source.

## 10. Remaining gaps and next tests

1. **AN's warrant.** The crux now lies here. Next test: whether the
   conditional form of an act-essence is coherent by EC's own standards
   (revision condition, toward AN, (a)), or whether a hyperintensional
   essence theory gives EC a principled reason at act-essences (toward EC,
   (c)).
2. **The hyperintensional boundary of `ca973127`** (§4): a substitution
   premise for E-link inside `Essential`, with a model in which it fails.
3. **The act-of-being dispute** (Kenny versus Gilson/Klima, navigation only).
   This bears on (c)'s intelligibility, and so on the identity clause of
   `FoundationalAt`, `565ccd6c` and the q.3 a.4 route at once.
4. **Kant's A/B pagination** was not checked against the Meiklejohn edition
   (navigation only). Fine (1994), Plantinga, Lowe and Kant's *Beweisgrund*
   are unread.
5. **No strength relation** is registered between (b) and (e) (law 8 only).
6. `truth countermodel` does not handle `CausalityFrame` parameters; all
   models are hand-written (as in #1889).

## 11. Literature (accessed 2026-11-23)

**Read:**

- Aquinas, *Summa Theologiae*, Dominican translation, New Advent:
  - I q.2 a.1 (body, ad 2), <https://www.newadvent.org/summa/1002.htm>;
  - I q.3 a.4 (obj. 2, body, ad 2), <https://www.newadvent.org/summa/1003.htm>.
- Aquinas, *De ente et essentia*, c. 4, trans. R. T. Miller (1997), Internet
  Medieval Sourcebook, <https://sourcebooks.fordham.edu/basis/aquinas-esse.asp>.
- I. Kant, *Critique of Pure Reason*, trans. J. M. D. Meiklejohn, Project
  Gutenberg #4280 (mirror <https://gutenberg.pglaf.org/cache/epub/4280/pg4280.txt>),
  Transcendental Dialectic, Book II, ch. III, sect. IV, "Of the Impossibility
  of an Ontological Proof", with note 67. A/B pagination (A592/B620 ff.,
  A598/B626) is navigation only.
- D. Hume, *Dialogues Concerning Natural Religion*, Part IX, Project
  Gutenberg #4583 (mirror <https://gutenberg.pglaf.org/cache/epub/4583/pg4583.txt>).
- M. Nelson, "Existence", SEP (rev. 2020-05-05),
  <https://plato.stanford.edu/entries/existence/>, introduction, §1, §3.
  Reports on Frege, Russell, Kant, Linsky–Zalta and Williamson are read as
  reports.
- P. Atkins, F. Correia and T. Robertson Ishii, "Essential vs. Accidental
  Properties", SEP (rev. 2026-08-21),
  <https://plato.stanford.edu/entries/essential-accidental/>, §1.1, §3.
  Reports on Fine are read as reports.
- "The Possibilism–Actualism Debate", SEP (rev. 2025-01-31),
  <https://plato.stanford.edu/entries/possibilism-actualism/>, §4.1.1, §4.2.1.
  Reports on Plantinga, Pollock and Fine are read as reports.

**Navigation only, not read:** K. Fine, "Essence and Modality" (1994);
E. J. Lowe, "Two Notions of Being" (2008); A. Plantinga, "On Existentialism"
(1983); A. Kenny, *Aquinas on Being* (2002); G. Klima, "Aquinas' Theory of
the Copula and the Analogy of Being" (2002); É. Gilson, *Being and Some
Philosophers*; ST I q.12 a.7 (no created intellect comprehends God's
essence).

## 12. Computed frontier change and cross-lane edits

**Frontier.** Computed by `truth frontier-diff --base a2011fb21` at
`3895b122`:
- open premises reaching the root: 569 → 570 (bare 419 → 420);
- one verified support alternative added: `565ccd6c` ← {E-link `3a2af70f`,
  AN `823d4312`};
- `565ccd6c` moves from bare to closed in frontier-diff's vocabulary. That
  means derived from open premises, not established.
- The two new premises are bare.
- The lowest expanded-route cost is unchanged (16).

The direct-assumption option for `565ccd6c` is retained. The Kant-adequacy
route to `fe8c3a1d` does not reach the root and so does not appear in the
delta.

**Cross-lane edits.**
- `corpus/disambiguations/existence-esse-support.json`: sense `_6`
  (`EsseExercisedAt`, DEF `25d4df96`) appended, with one resolution
  paragraph.
- `corpus/definition-status.json`: only this module's six entries were added.
