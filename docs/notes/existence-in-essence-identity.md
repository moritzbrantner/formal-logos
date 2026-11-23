# Does existence belong to an essence when essence is esse? (#1887, B6 crux, 2026-11-23)

Issue #1887, next slice 1 after #1888 and #1889. God-existence stage of the
#143 root. Analyst formulations, attribution deferred (logic first); every
text used is listed in §11 as **read** (URL, section, date) or **navigation
only**. No source claim is made.

**Revision history.** The first draft (head `2ce14478`) received an
independent semantic challenge: mergeable after listed repairs (6 P1s,
several P2s). This version carries the repairs; the disposition table is §13.

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

**Short answer.**
- The thesis does not apply to the identity *by itself* in any sense
  examined.
  - In the conceptual sense it is consistent with the identity, with
    existence in the nature, and with necessity.
  - It excludes the identity only through a bridge that makes the concept
    adequate to the nature. Kant's four arguments examined (§3), as read, do
    not supply that bridge at an act-essence. Arguments 1–3 need the content
    premise. Argument 4's bridge exists iff EC holds of the nature (laws 13,
    16), so at the identity it presupposes EC there.
  - In the essential-truth sense (EC), its motivations at the identity case
    either presuppose the being's contingency, are the unresolved
    conceivability argument, or deny the identity's intelligibility instead.
- Conversely, the identity does not give existence in the nature by itself.
  That step needs "exercise in the nature" (AN). Given the act–fact link,
  AN is *equivalent* to `565ccd6c`: the factorization restates the crux at
  the level of the act and separates out the link; it does not narrow it.
- AN's identified support is either shared with the power/potency route or
  merely removes a defeater.
- Parity at the foundational being stands (§7).

## 1. Fixed meanings

| Sense | Meaning | Lean declaration | DEF |
|---|---|---|---|
| EXISTENCE_IN_ESSENCE_1, conceptual containment (a) | the proposition that `x` exists is a determination contained in a concept `C` of `x` (`C : ConceptRelation`, its own type) | `ConceptContainsExistence` | `90353211` |
| EXISTENCE_IN_ESSENCE_2, essential truth (b) | it lies in the nature of `x` (ESSENCE_5) that `x` exists, unconditionally | `EssentialExistence` | `1fda7b2c` |
| EXISTENCE_IN_ESSENCE_3, act identity (c) | `x`'s represented esse is its represented essence (ESSENCE_3 maps). An identity of principles, not a determination inside a quiddity; no world index | `EsseIsEssence` | `b2e22524` |
| EXISTENCE_IN_ESSENCE_4 (d) | NECESSARY_EXISTENCE_BY_OWN_NATURE_3, essence membership of the existence fact (reused, not bridged) | `EssenceReasonSeparation.OwnEssentialExistence` | `72a1e556` |
| EXISTENCE_IN_ESSENCE_5, consequential essential truth | some essential truth of `x` entails `x`'s existence | `NatureEntailsExistence` | `316780ef` |

- The disambiguation is `f704b7ca` (EXISTENCE_IN_ESSENCE).
- (a) and (b) are distinct as types. A concept is a value of the structure
  `ConceptRelation`, not an essence relation. The concept adequate to a
  nature is *constructed* from the essence relation (`adequateConcept`), not
  identified with it.
- (d) is kept as a sense. Its profile type (existence facts in `InEssence`)
  cannot state an existence-conditional essence, so no bridge to (b) is
  encoded.

**Two new primitives**, each with meaning, examples, exclusions and open
obligations in its DEF:

- `ConceptContent C x φ` (DEF `16c40fbe`): `φ` is a determination contained
  in the concept `C` of `x`. *Which* concept is meant is fixed by which
  premises hold of `C`:
  - a concept **formed from effects**, which does not satisfy concept
    adequacy. In the models (`effectConcept`) its only content is the
    coexistence conditional "if the other being exists, this one exists". It
    does not use the frame's causation relation;
  - a concept **adequate to the nature** (the *ratio* in itself), which
    satisfies it by construction.
- `EsseExercisedAt Exercised v p` (DEF `25d4df96`): the principle `p` is in
  act at point `v`; for an esse principle, its act of being is exercised
  there.
  - It is world-indexed, unlike the q.3 a.4 `InAct x esse`.
  - It is WORLD_RELATIVE_EXISTENCE_METAPHYSICAL_ESSE_NECESSITY_6 of
    DISAMB-EXISTENCE-ESSE-SUPPORT, beside `_1` (the existence fact `ExistsAt`)
    and `_5` (the frame respect `esse`).
  - The `Exercised` binders of E-link and AN carry this tag.

**Points and access.** The frame's points are the represented space;
accessibility is real possibility. EC and "entails existence" quantify over
all points; necessity and contingency over accessible ones. This is
**analogous to**, not the same as, Kant's distinction in note 67 (§11)
between the logical possibility of a concept and the real possibility of a
thing. Kant's real possibility is objective reality established from
principles of possible experience. Mapping it to frame accessibility is the
analyst's analogy.

**Theses and bridges** (all OPEN, analyst formulations):

| Name | Content | Lean |
|---|---|---|
| KT, Kant's thesis (conceptual form) `9014eea0` | no determination contained in a being's concept entails that being's existence over the represented points | `ExistenceNotConceptual` |
| CNC, conditional conceptual necessity (laws only) | every determination in the concept of `x` holds wherever `x` is absent: a concept yields only "if `x` is posited, …" (Kant's triangle paragraph, analyst form) | `ConceptualNecessityConditional` |
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
    world-propositions inside the nature (`propext`, `funext`).
  - **The converse holds too** (law 15). Given E-link, AN and `565ccd6c` are
    equivalent. So the factorization restates the bridge at the level of the
    act; it does not narrow it.
  - It is still not a transcription: neither premise mentions existence in
    a nature.
  - Each premise is needed (factorization omissions 1–2).
  - Sense bridges: ESSENCE_3 → ESSENCE_5 through AN; `_6` → `_1` through
    E-link.
- **`63ac77e7`** is a second support bundle for the "possibly absent"
  verdict, beside the EC bundle `872a3832`. It replaces EC and the
  representability premise with KT plus K1.
  - It is constructive, and each premise is needed (Kant-adequacy omissions
    1–4).
  - It is nonvacuous (`conditionalIdentity`).
  - **Both concept premises must hold of one concept `C`.** So it needs
    Kant's thesis to govern a concept *adequate to the nature*.

### Laws (`Model.Laws`)

1. KT excludes conceptual containment of existence, for every being.
2. KT + K1: no essential truth of any being entails that being's existence.
   This is EC's modal effect, without a representability premise.
3. KT + K1 + `565ccd6c` exclude every esse = essence identity.
4. KT + K2 exclude every esse = essence identity.
5. KT yields only representable absence. Identifying the represented space
   with real possibility (access from `w` to every point) is **one
   sufficient** bridge to real absence: under it, a being existing at `w`
   with a nonempty concept is contingent at `w`. `kantAquinas` shows that
   *some* bridge is needed; weaker bridges also suffice. The proof is
   classical.
6. EC, E-link and AN are **jointly inconsistent** with an identity being
   whose absence is representable. The law does not say which member to
   reject.
7. Under E-link, for every identity being `x` and every point at which `x`
   exists, `x`'s essence principle is exercised there. So the
   world-proposition "if `x` exists, its essence is exercised" is true at
   every point. `Essential` does not occur: the law says nothing about what
   lies in any nature.
8. (b) ⇒ (e).
9. Essence grounds necessity (EGN) + (e) ⇒ necessary.
10. EGN + contingent ⇒ ¬(e).
11. **Equivalence within essentialism.** Assume excluded middle, EGN, the
    essentialist account of possibility, that no other nature requires `x`,
    and that `x` exists at `w`. Then (e) at `x` ⇔ `x` is necessary at `w`.
12. **Serious-actualist essences.** EGN, every essential truth of `x` an
    unconditional predication, and a nonempty nature make `x` necessary.
13. CNC + K1 ⇒ EC.
14. CNC ⇒ KT at every being whose absence is representable.
15. E-link + `565ccd6c` ⇒ AN (the converse of `ca973127`).
16. EC ⇒ CNC and K1 for `adequateConcept` (the converse of law 13). So a
    CNC concept adequate to the nature exists exactly when EC holds of the
    nature.

### Models (structural surrogates; not metaphysical possibility)

The models now give distinct beings distinct principles (type `Pr`):
- `true`'s esse is its essence;
- `false` has an esse distinct from its essence.

So E-link no longer forces the two beings to co-exist.

| Model | What holds | What fails | Shows | Admissible on |
|---|---|---|---|---|
| `kantAquinas` | See the list below the table | See the list below the table | KT and CNC (sense (a)) are consistent with (c), (b), AN, E-link and necessity. KT blocks the identity only through K1 or K2. Omission model of K1 for law 3 and of K2 for law 4. Nonvacuity of `ca973127` | about `true` only: a Thomist reading of q.2 a.1 (not self-evident to us; self-evident in itself) with KT restricted to concepts from effects. It is **not** a model of Thomism as a whole |
| `conditionalIdentity` (`bothContingent`, distinct principles) | `true` is foundational with esse = essence; E-link; EC with only the conditional exercise in the nature; EGN; the essentialist account; unrequired-by-others; KT, CNC and K1 for the adequate concept; contingency; the "possibly absent" verdict | AN, `565ccd6c`, K2, (e) | identity + E-link + EC + a Kantian adequate concept + contingency are jointly satisfiable: the identity does no modal work there. Nonvacuity of `63ac77e7` | Fine/Lowe EC with KT extended to adequate concepts |
| Kant-adequacy omissions 1–4 | all premises of `63ac77e7` but one | that premise; the verdict | each premise is needed. These models do not use E-link, so their shared esse principle (`esseTrue`) does no work | — |
| Factorization omissions 1–2 | 1: AN, with every principle exercised at every point. 2: E-link, with no essences | 1: E-link. 2: AN. Both: `565ccd6c` | each premise of `ca973127` is needed. Omission 1 is a separation, admissible on no view examined | — |

**`kantAquinas` in detail.** The frame has represented points `a`, `b`, `c`.
From `a`, only `a` and `b` are really possible.

What holds:
- `true` is foundational with esse = essence, exists at `a` and `b`, and is
  necessary.
- `false` exists only at `a`, so it is contingent. Its esse is distinct from
  its essence, and `true` causes its esse.
- E-link, AN, `565ccd6c`, EGN and (b).
- `true`'s absence is representable (point `c`) but not really possible.
- For the concept from effects (the coexistence conditional only): KT and CNC.
- For the adequate concept: K1 and K2.

What fails:
- For the concept from effects: K1, K2 and (a).
- For the adequate concept: KT and CNC.

Excluded middle is never omitted: every model is built in Lean.

## 3. The key test: does Kant's thesis reach the identity?

**Formal answer.**
- KT is about concepts. By itself it excludes only (a) (law 1).
- It reaches (b) through K1 (law 2), and excludes (c) only through K1 with
  `565ccd6c` (law 3), or through K2 (law 4).
- With neither bridge it is consistent with (c), (b), AN, E-link and
  necessity (`kantAquinas`).
- It yields only representable absence. Real absence needs a further bridge
  (law 5, `kantAquinas`). Kant's note 67 refuses to conclude "from the
  possibility of a conception—which is logical—the possibility of a
  thing—which is real".

**Is a bridge warranted?** Four of Kant's arguments in the section read
(§11) bear on this.

1. **Existence is positing, not a real predicate.** "Being is evidently not
   a real predicate, that is, a conception of something which is added to the
   conception of some other thing. It is merely the positing of a thing."
   - *Target:* the ontological argument's step, sense (a).
   - *At the identity:* (c) does not make existence a determination added to
     a quiddity. On the reading it formalizes, the identity being has no
     quiddity distinct from its act. So the argument does not touch (c)
     unless every essence is a content of real predicates.
   - That premise denies (c) as an act; it does not show the act modally
     idle.
2. **The hundred thalers / adequacy argument.** If existence added content,
   "my conception would not be an expression of the whole object, and would
   consequently be an inadequate conception of it". And "by whatever and by
   whatever number of predicates—even to the complete determination of it—I
   may cogitate a thing", existence adds nothing.
   - This is the closest Kant comes to K1: the complete determination of a
     thing by real predicates is adequate to it.
   - At the identity it assumes the essence is exhaustively a set of real
     predicates: the same premise as argument 1.
3. **Annihilation and the analytic/synthetic dilemma.** "Annihilate its
   existence in thought, and you annihilate the thing itself with all its
   predicates; how then can there be any room for contradiction?"
   - This is a **structural** argument: once the subject is suppressed with
     all its predicates, nothing remains to contradict. Kant adds:
     "contradiction is the only criterion of impossibility in the sphere of
     pure à priori conceptions". That clause supports reading the thesis as
     about concepts.
   - Kant states the opposing claim and its burden himself: "There are
     certain subjects which cannot be annihilated in thought. But this is
     nothing more than saying: There exist subjects which are absolutely
     necessary—the very hypothesis which you are called upon to establish."
   - The dilemma rests on "every existential proposition is synthetical",
     which "every reasonable person must" confess.
   - Applied to concepts, it is sound against a proof from concepts, and
     Aquinas agrees for our concepts ("not self-evident to us", q.2 a.1).
   - Its scope is fixed by its own criterion: impossibility *among pure
     concepts*, which is contradiction. It shows that no contradiction arises
     in thought. It does not show that the absence of a being whose essence is
     its esse is really possible. Kant's note 67 keeps logical and real
     possibility apart.
   - Applied to a concept adequate to an identity being's nature, it
     presupposes that this concept is a content of predicates, which is
     again the premise of arguments 1–2.
4. **The triangle paragraph: necessity of judgements is conditional.** "The
   unconditioned necessity of a judgement does not form the absolute
   necessity of a thing. On the contrary, the absolute necessity of a
   judgement is only a conditioned necessity of a thing … upon condition that
   a triangle exists, three angles must necessarily exist—in it." Even a
   concept made to "embrace existence" yields existence only "under the
   condition of my positing this thing as given".
   - *Target:* the inference from a concept's content to the absolute
     necessity of a thing.
   - *Mechanism:* any necessity obtained from a concept is conditional on
     positing its subject. This is the analyst premise CNC.
   - *Independent justification:* the subject–predicate structure of
     analytic judgement.
   - *Formal relations:*
     - CNC is EC's conceptual counterpart. With K1 it gives EC (law 13).
     - With representable absence it gives KT (law 14).
     - It holds of the concept from effects in `kantAquinas`, together with
       identity, AN and necessity. So by itself it does not block the
       identity.
   - *What it needs at the identity.* Argument 4 needs a CNC concept that is
     adequate to the nature. Such a concept exists **if and only if** EC holds
     of the nature:
     - law 13: CNC + K1 ⇒ EC;
     - law 16: EC ⇒ CNC and K1 for `adequateConcept`.

     So at the identity, argument 4 presupposes EC there rather than
     supplying it.
   - *Grounds for that bridge.* Kant's ground is the content premise: every
     necessity of a thing is the necessity of a judgement about a content of
     predicates. At an act-essence, the necessity in question (AN) is claimed
     for the thing's own act, not for a predicate in a subject. So the content
     premise either denies (c) as an act or denies that an absolute necessity
     of a thing is intelligible. It is **not the only possible ground**. A
     Fine/Lowe EC holder needs no content premise. Their grounds fall under
     toward-EC revision condition (c) (§8), and §5 assesses the grounds
     identified.
   - *Kant's intelligibility doubt.* He doubts whether "by means of the
     conception of the unconditionally necessary I think of something, or
     really of nothing at all". On note 67's standard (real possibility only
     from principles of possible experience), the analyst reading is that
     this doubt bears equally on cognizing the *real possibility* of the
     non-being of a being outside possible experience. It is neutral between
     the verdicts, not support for EC.
   - *Assessment:* argument 4 is the strongest Kantian support for EC *for
     natures that are contents*. At the identity case it needs a CNC concept
     adequate to the nature, which exists iff EC holds of the nature (laws
     13, 16). Kant's ground for it is the content premise; other grounds fall
     under toward-EC revision condition (c).

**Result of the test.** A bridge (K1 for a Kantian concept, or K2) is
needed.
- Arguments 1–3 establish it at the identity case only by assuming that every
  essence is a content of real predicates.
- Argument 4's bridge exists exactly when EC holds of the nature (laws 13,
  16), so at the identity it presupposes EC there. Kant's own ground for it
  is again the content premise.
- The content premise does not show the identity modally idle. It denies the
  identity's intelligibility, which makes it a rival to (c) (§5,
  Frege/Russell), not an application of the thesis to (c).
- A non-Kantian ground for EC at the identity would have to meet toward-EC
  revision condition (c). §5 assesses the grounds identified (serious
  actualism, conceivability, Fine) and finds none that meets it.
- The Kant-adequacy route `63ac77e7` therefore holds only under a disputed
  extension: Kant's thesis governing an adequate concept, which presupposes
  EC at the identity.

## 4. Equivocation check: esse as act and existence as fact

`565ccd6c` passes from one to the other.
- Its antecedent is an identity of world-invariant principles (`esseOf x =
  essenceOf x`).
- Its consequent is a world-indexed existence proposition (`fun v => ExistsAt
  v x`) in the nature.
- ST I q.3 a.4 ad 2 (read) separates the two: "to be" as the act of essence,
  which "we cannot understand" of God, and as the composition of a
  proposition, whose truth "we know … from His effects".

`ca973127` makes the passage explicit. It was already a declared sense
bridge, so it is not an unflagged equivocation.

- **E-link (act ↔ fact).**
  - It is *satisfiable with each essentialist bundle*: `kantAquinas` and
    `conditionalIdentity`, with distinct principles.
  - No substantive objection to it is identified **among views that accept
    an act of being**.
  - That is not a claim that every view accepts it.
- **The quantifier view** recognizes no act of being beyond instantiation.
  For it, E-link either:
  - is **false** wherever `x` exists, if "exercised" is empty; or
  - is a trivial **identification**, if "exercised" is deflated to
    "exists". In that case AN collapses into `565ccd6c` itself.
- **AN.** Given E-link, AN is equivalent to `565ccd6c` (`ca973127` and law
  15).
- **Law 6.** EC, E-link and AN are jointly inconsistent at a representably
  absent identity being. *Among views that accept an act of being and
  E-link*, the dispute between EC and unconditional essentialism falls on AN.
  This is not a general verdict on which member to reject.

**Boundary.** The step uses propositional extensionality inside the nature,
because `Essential` takes world-propositions, as in `ModalGrounding`. Fine's
essence is hyperintensional (navigation only). On that reading E-link alone
does not license substitution inside `□ₓ`, and `ca973127` needs a further
substitution premise. Recorded as open.

## 5. Arguments for "existence never belongs to an essence", at the identity

Each entry gives the target, mechanism, independent justification, and
relevance at the identity case.

- **Kant** (read). See §3, arguments 1–4.
  - *Target:* (a), and the necessity of things derived from concepts.
  - *At the identity:* it reaches (b) or (c) only with K1 or K2.
    - Arguments 1–3 need the premise that every essence is a content of
      predicates.
    - Argument 4 needs a CNC concept adequate to the nature, which exists iff
      EC holds of the nature (laws 13, 16). Kant's ground for it is the same
      content premise; other grounds fall under toward-EC revision condition
      (c).
  - **No application to the identity without the content premise, or EC at
    the identity on some other ground.**
- **Hume** (read, *Dialogues* IX; the speaker is **Cleanthes**, and
  attribution of the view to Hume himself is not assumed). Two claims:
  - *Conceivability:* "Whatever we conceive as existent, we can also
    conceive as non-existent. There is no being, therefore, whose
    non-existence implies a contradiction."
    - Cleanthes anticipates the "if we knew his whole essence" reply: "this
      can never happen, while our faculties remain the same as at present".
    - He concedes "unknown, inconceivable qualities, which can make his
      non-existence appear impossible", and turns to an identification
      objection (why not matter?).
    - *At the identity:* this is the conceivability argument of #1888
      §2.1b. It is unresolved and rests on the calibration premise; his own
      scope ("our faculties") marks the same gap.
  - *Unintelligibility:* "The words, therefore, necessary existence, have no
    meaning; or, which is the same thing, none that is consistent."
    - *Target:* the intelligibility of necessary existence, and so of the
      necessity verdict at `n`.
    - *Mechanism:* the meaning of necessity is fixed by what the mind cannot
      but conceive, and we can always conceive non-existence.
    - *Justification:* an empiricist account of modal meaning, not assessed
      here.
    - *Relevance:* it does not support EC as a theory of essence, which uses
      meaningful modal claims. It rejects the necessity verdict as
      unintelligible. Its premise ties modal meaning to our conceiving, which
      is the same calibration question.
  - **No new weight at the identity beyond #1888.**
- **Frege/Russell** (read as report, SEP *Existence*, introduction and §1).
  - *Target:* existence as a first-level property, that is, (a) and a
    property reading of (b).
  - *Mechanism:* existence is a second-order property.
  - *At the identity:* (b) in operator form is well-formed on the
    quantifier view, so the argument does not reach it.
  - It reaches (c) only through the further thesis that there is no act of
    being beyond instantiation. That is a **rival to (c)'s
    intelligibility**, which would empty the identity clause of
    `FoundationalAt` and q.3 a.4's premise (§4 on E-link). It does not
    support EC *at* an identity it deems empty.
  - SEP §3 reports the Linsky–Zalta/Williamson view on which every
    individual is a necessary existent. That view does not discriminate the
    foundational being either.
- **Fine** (read as report, SEP *Essential vs. Accidental Properties* §3).
  - Fine's reported objection is that "existence is intuitively not a
    whatness essential property of every entity". This is a "not every"
    claim. It is compatible with existence being whatness-essential to none.
  - It targets the existence-conditioned modal characterization of whatness
    essence. If anything, it suits EC for ordinary things.
  - **Neutral at the identity.**
  - The §1.1 remark about existence being "modally essential to numbers (or
    God)" is the SEP authors' own argument, not Fine's. It is given **no
    weight** here; the God case would be a conceivability-type intuition
    (#1888 §4).
- **Serious actualism** (read as report, SEP *The Possibilism–Actualism
  Debate* §4.1.1; Plantinga's existence-conditioned essential properties
  §4.2.1).
  - *Mechanism:* an object must exist to have properties. So unconditional
    essential predications would make every bearer of a nature a necessary
    existent (law 12). EC is the conditionalization that keeps bearers
    contingent.
  - *Justification for ordinary concreta:* their contingency has independent
    evidence (generation and corruption).
  - *At the identity:* by law 11, within essentialism EC's effect at `x` is
    equivalent to `x`'s contingency. So this motivation for EC at the
    identity being **presupposes its contingency**, exactly #1888 revision
    condition (b)'s presupposition.
- **Aquinas** (read: ST I q.2 a.1, q.3 a.4 with ad 2, New Advent; *De ente*
  c.4, Miller).
  - *De ente:* "I can understand what a man is or what a phoenix is and
    nevertheless not know whether either has existence in reality". So
    existence is other than essence "unless perhaps there is something whose
    quiddity is its very own existence". The *intellectus essentiae*
    argument thus establishes existence-outside-essence only for essences
    understood without esse, and names the identity case as its exception.
  - *q.2 a.1:* "God exists" is self-evident in itself, because the predicate
    is included in the essence of the subject (God is His own existence). It
    is not self-evident to us, because we do not know God's essence.
  - What `kantAquinas` says about `true` matches this:
    - KT holds of the concept from effects;
    - K1 and K2 hold of the adequate concept;
    - (c) holds.

    The model is not a model of Thomism as a whole.
  - The step from identity to "the predicate is the same as the subject" is
    K2 for the adequate concept. Given q.3 a.4 ad 2's distinction, it passes
    from the act to the composition: E-link plus AN. This is an analyst
    reading; no equivocation is attributed to Aquinas.

**Assessment.** None of these yields EC at the identity case. Each one
either:
- needs a bridge it does not establish at the identity (Kant). Arguments 1–3
  need the content premise; argument 4 presupposes EC at the identity (laws
  13, 16);
- is the unresolved conceivability argument, or an unintelligibility claim
  about necessary existence resting on the same calibration question
  (Cleanthes);
- denies the identity's intelligibility instead (Frege/Russell, and Kant
  read as "every essence is a content");
- is neutral (Fine); or
- presupposes the being's contingency (serious actualism).

Aquinas's own reason for distinct esse explicitly excludes the case. **#1888
revision condition (b) (EC side) is assessed and not met.**

## 6. The symmetric test: motivation for unconditional essential existence at the identity

`conditionalIdentity` shows that the identity, with E-link, does not give
(b). The extra step is AN, which given E-link is equivalent to `565ccd6c`.
Candidate motivations:

1. *The exclusion reason lapses.* *De ente*'s reason for putting existence
   outside essence does not apply at the identity. This removes a defeater.
   It does not supply positive support.
2. *Pure act has no potency to non-being.* This supports the **necessity
   verdict** directly, through the power/potency account (PGP and C2,
   `20d5fecd`, `e5d49f99`). It supports AN only through that verdict.
   **Shared dependency, not independent warrant.**
3. *A principled cut.* AN's antecedent (c) is non-modal and specified
   independently, so the exemption is not gerrymandered. This answers an
   ad hoc charge. It is not evidence that AN is true.
4. *Fit with essential existence for abstracta.* The SEP §1.1 suggestion for
   numbers is not Fine's and is given no weight; the support for
   mathematical necessity does not transfer to a concretum. Not credited.
5. *q.2 a.1's step.* This is K2 for the adequate concept, which presupposes
   AN with E-link (§5). Not independent.

So **no motivation for AN is identified that does not run through a
necessity-favouring general theory** (the power/potency account). Likewise,
no motivation for EC at the identity is identified that does not presuppose
contingency there. Law 11 states the parity formally: inside essentialism,
the disputed essence thesis at an actual `x` is equivalent to the disputed
modal verdict at `x`. Essentialism alone cannot discriminate at the identity
case.

## 7. Provisional judgment (2026-11-23, evidence revision: this branch, repaired after challenge)

**Scope.** The B6 crux: at a being with esse = essence (the foundational case
of #1889), does "existence never belongs to an essence" make the identity
modally idle, or does the identity make existence essential? Criteria: the
substantive objection standard, applied symmetrically, and matching-scope
comparison (#1888 §6).

1. **The Kant-type thesis does not apply to the identity on any assessed
   motivation without a bridge or a presupposition.**
   - In sense (a), with CNC, it is consistent with identity, essential
     existence and necessity.
   - It reaches the identity only with concept adequacy for a Kantian
     concept. Arguments 1–3 establish that only with the content premise.
     Argument 4's bridge exists iff EC holds of the nature (laws 13, 16), so
     at the identity it presupposes EC; other grounds for EC fall under
     toward-EC revision condition (c).
   - In sense (b) (EC) its motivations either presuppose contingency, are
     the unresolved conceivability argument (or an unintelligibility claim
     resting on the same question), or deny (c)'s intelligibility instead.
   - This meets #1888's "toward PGP" condition (d) **as stated**. It creates
     no relative standing for the necessity verdict, for two reasons:
     - #1888 §4–§6 had already scored concreta-restricted EC's cut at `n` as
       having no identified motivation, and this assessment does not change
       that score;
     - PGP's relative standing depends on #1888's "toward PGP" condition (a)
       (the actualist grounding demand excluding non-power grounds of
       absence), which remains unmet.
2. **The identity does not give essential existence by itself.**
   - The step needs AN, which given E-link is equivalent to `565ccd6c`.
   - AN's identified support either runs through the power/potency route
     (correlated with PGP/C2) or only removes a defeater.
   - `565ccd6c` keeps its direct-assumption option. But no direct ground for
     it at the identity case was identified that is not a ground for AN given
     E-link. So the support that `f9b26559` (and `39df9612`) gives the
     necessity verdict rests, at this case, on AN's warrant.
3. **Parity at the foundational being stands.**
   - Within essentialism the dispute *is* the modal verdict (law 11).
   - Among views accepting an act of being and E-link, the essentialist
     dispute falls on AN, equivalently `565ccd6c`. The factorization
     relocates the crux to the act level; it does not narrow it.
   - The rival verdict now has two support bundles (EC + representability;
     Kant + adequacy). The second needs Kant's thesis extended to adequate
     concepts, which is disputed at exactly this case.
4. **Not established:** that existence belongs to the foundational being's
   nature; that it does not; any premise. No formal closure changes beyond
   the computed frontier delta (§12).

**Change to #1888's §5 table (proposed for the coordinator; that note is not
edited here).**

| #1888 row | Before | After this note |
|---|---|---|
| Existence-conditional essentialism (concreta-restricted) / "possibly absent" | "No independent motivation for the cut at `n` is identified; the general Kant-type thesis is unassessed" | **Unchanged score** ("no / open"). The Kant-type thesis is now assessed: it does not apply at `n` without K1/K2, i.e. without the content premise or EC at `n` (laws 13, 16). The serious-actualist *motivation for EC at `n`* presupposes `n`'s contingency (law 11); serious actualism itself allows necessary beings. Fine is neutral. New support bundle for the verdict: `63ac77e7` (Kant + adequacy), which needs KT extended to concepts adequate to the nature. |
| PGP | "no / open, as for EC" | **Unchanged.** Relative standing still requires "toward PGP" (a), unmet. |
| Unconditional essentialism | "through simplicity and B6, which are open" | Its step from simplicity to necessity needs AN, equivalent to `565ccd6c` given E-link. AN's identified support is shared with PGP/C2 (via the necessity verdict). **Score unchanged.** |
| Revision conditions | "against PGP at `n`" (b); "toward PGP" (d) | (b): assessed, not met. (d): met as stated, no standing change (reasons in point 1). |

**Shared dependencies.**
- `ca973127` and `f9b26559` share EGN with the EC verdict `872a3832` and
  with `63ac77e7`. EGN is accepted by both essentialisms.
- AN's support is tied to PGP/C2 (§6 item 2).
- `63ac77e7` shares the essentialist account `9d8a8d2e` and
  unrequired-by-others `38200db5` with `872a3832`.

## 8. Revision conditions (symmetric)

Toward EC at the identity, or possible absence:

- (a) An argument that every essence, including an act-essence, is
  adequately given by a concept of determinations (K1 for a concept KT or
  CNC governs). It must not presuppose that no essence is an act.
- (b) A defended reduction of the act of being to instantiation (the
  quantifier view's further thesis). This would remove (c) and the identity
  clause rather than idle them, and it would make E-link false or trivial
  (§4).
- (c) A motivation for conditionalizing essences at an act-essence that does
  not run through the bearer's contingency. For example, a theory of essence
  on which natures state only what a thing is, defended on independent
  grounds and shown to cover act-essences.
- (d) #1888 conditions (a) and (g): a secondary conceiving of the absence, or
  modal rationalism without the calibration premise. Also: a defence of
  Cleanthes's meaning premise.

Toward AN, or necessity:

- (a) An argument from (c) to AN that does not pass through potency or power.
  For example, showing that the conditional form "if `x` exists, its act of
  being is exercised" fails to state the nature of an act-essence, on
  grounds EC accepts.
- (b) #1888 "toward PGP" (a) or (b): the actualist grounding demand, or PGP's
  completeness over incorruptibles, defended without presupposing a creator.
- (c) Independent warrant that some concretum exists necessarily.

Either way: a hyperintensional account of essence on which E-link does not
license substitution inside the nature would block `ca973127` and law 15 as
encoded, and would require a separate substitution premise (§4).

## 9. Claim versus type

| Record | Prose | Lean type | Check |
|---|---|---|---|
| `3a2af70f` E-link | a being's act of being is exercised exactly where it exists | `∀ v x, EsseExercisedAt Exercised v (esseOf x) ↔ ExistsAt v x` | over all points, not only accessible ones; both directions; "satisfiable with each bundle", not "accepted by all" |
| `823d4312` AN | an identity being has the unconditional exercise of its esse in its nature | `∀ x, esseOf x = essenceOf x → Essential x (fun v => Exercised v (esseOf x))` | unconditional proposition; no modality asserted; equivalent to `565ccd6c` given E-link (law 15) |
| `9014eea0` KT | no determination in a being's concept entails its existence | `∀ x φ, C.contains x φ → ¬ ∀ v, φ v → ExistsAt v x` | over represented points; nothing about accessibility. **Stronger than "existence is not a real predicate"**: it also rules out any content that entails existence, such as an unconditional "`x` is omnipotent" true only where `x` exists |
| `effbb158` K1 | whatever lies in the nature is in the concept | `∀ x φ, Essential x φ → C.contains x φ` | one direction only; `C` has its own type |
| `565ccd6c` (conclusion of `ca973127`) | esse = essence puts existence in the nature | `esseOf x = essenceOf x → Essential x (fun v => ExistsAt v x)` | unchanged; now derived from E-link and AN |
| `fe8c3a1d` (conclusion of `63ac77e7`) | every foundational being at `w` is contingent | `∀ f, FoundationalAt … f → ContingentAt … w f` | universal; asserts no foundational being |
| `ac557772` controls | laws 1–16, models | `Model.Controls` | law 5: identification *suffices*, not "only when"; law 6: joint inconsistency, no member selected; law 7: a world-proposition true at every point, no `Essential`; law 5 is classical; law 11 takes excluded middle as a hypothesis; models are structural surrogates |

Every hypothesis of each theorem is a listed premise. `ConceptContent` wraps
the field of `ConceptRelation`, and `EsseExercisedAt` is a parameter wrapper.
No condition is added to any source.

## 10. Remaining gaps and next tests

1. **AN's warrant** (equivalently `565ccd6c`'s, given E-link). Next tests:
   - whether the conditional form of an act-essence is coherent by EC's own
     standards (toward AN, (a));
   - whether a hyperintensional essence theory gives EC a principled reason
     at act-essences (toward EC, (c)).
2. **The hyperintensional boundary** of `ca973127` and law 15 (§4): a
   substitution premise for E-link inside `Essential`, with a model in which
   it fails.
3. **The act-of-being dispute** (Kenny versus Gilson/Klima, navigation only).
   It bears on (c)'s intelligibility, and so on the identity clause of
   `FoundationalAt`, `565ccd6c` and the q.3 a.4 route at once.
4. **Tagging.** The `Essential` binders of the new declarations are not
   tagged ESSENCE_5, because the record is pinned by bundle audits. They
   remain unknown.
5. **Kant's A/B pagination** was not checked against the Meiklejohn edition
   (navigation only). Fine (1994), Plantinga, Lowe and Kant's *Beweisgrund*
   are unread.
6. **No strength relation** is registered between (b) and (e) (law 8 only).
7. `truth countermodel` does not handle `CausalityFrame` parameters, so all
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
  of an Ontological Proof": the opening paragraphs, the triangle paragraph,
  the annihilation paragraphs, the real-predicate and hundred-dollars
  paragraphs, and note 67. A/B pagination (A592/B620 ff., A598/B626) is
  navigation only.
- D. Hume, *Dialogues Concerning Natural Religion*, Part IX (Cleanthes's
  reply to Demea), Project Gutenberg #4583 (mirror
  <https://gutenberg.pglaf.org/cache/epub/4583/pg4583.txt>).
- M. Nelson, "Existence", SEP (rev. 2020-05-05),
  <https://plato.stanford.edu/entries/existence/>, introduction, §1, §3.
  Reports on Frege, Russell, Kant, Linsky–Zalta and Williamson are read as
  reports.
- P. Atkins, F. Correia and T. Robertson Ishii, "Essential vs. Accidental
  Properties", SEP (rev. 2026-08-21),
  <https://plato.stanford.edu/entries/essential-accidental/>, §1.1 (the
  authors' own arguments), §3. Reports on Fine are read as reports.
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

**Frontier.** Computed by `truth frontier-diff --base a2011fb21`:
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
- `corpus/disambiguations/existence-esse-support.json`:
  - sense `_6` (`EsseExercisedAt`, DEF `25d4df96`) appended, with
    parameter tags on the `Exercised` binders of E-link and AN;
  - one resolution paragraph added;
  - the sentence "Only DEF-KANT-ONTOLOGICAL-MODEL reaches the root" amended,
    since `25d4df96` now reaches it through `3a2af70f` and `823d4312`.
- `corpus/definition-status.json`: only this module's entries were added.

## 13. Challenge disposition (review of head `2ce14478`)

| Finding | Disposition | Where |
|---|---|---|
| P1-1 Fine "points the other way" | **Accepted.** Fine is neutral; §1.1 credited to the SEP authors with no weight; removed from §5, §6 and the attempt | §5 Fine, §6 item 4, attempt |
| P1-2 Kant: "first-personal"; triangle paragraph missing | **Accepted.** Argument 3 restated as structural, with the "only criterion" clause. Argument 4 added and assessed. At the identity it needs a CNC concept adequate to the nature, which exists iff EC holds of the nature (laws 13, 16; law 16 added in the second re-check). Kant's ground for it is the content premise; other grounds fall under toward-EC revision condition (c). Its intelligibility doubt is neutral between the verdicts. Formalized as CNC, laws 13–14 and 16, and in the models. Verdict unchanged | §3, §5, laws 13–14 |
| P1-3 law 5 "only when" | **Accepted.** "A represented-to-accessible bridge is needed; identification suffices" in Lean doc, `ac557772`, `9014eea0` and the note | Lean `Laws` doc, spec, §2, §3 |
| P1-4 law 7 prose | **Accepted.** States the world-proposition true at every point, with no `Essential` | Lean `Laws` doc, `ac557772`, §2 |
| P1-5 E-link acceptance; quantifier view; law 6 "so" | **Accepted.** Models rebuilt with distinct esse principles (`Pr`). "Satisfiable with each bundle; no substantive objection identified among views that accept an act of being". Quantifier-view sentence corrected (false or trivial). Law 6 made a joint inconsistency with no member selected | vocab models, `3a2af70f`, `ca973127` description, §4 |
| P1-6 "Formally, Aquinas's position is kantAquinas" | **Accepted.** Model rebuilt: the second being is caused by `true`, contingent, with distinct esse. The claim is limited to what the model says about `true`, "not a model of Thomism as a whole" | vocab doc, §2 table, §5 Aquinas |
| P2 factorization is an equivalence | **Accepted.** Law 15 proves the converse; "located exactly in AN" replaced by "restates, does not narrow" | §2, §4, §7 |
| P2 (d) reason | **Accepted.** Reasons replaced (#1888's existing score; "toward PGP" (a) unmet); #1888 table change stated for both sides | §7 |
| P2 Hume | **Accepted.** Speaker Cleanthes; unintelligibility claim assessed separately | §5 |
| P2 KT strength | **Accepted.** Added to the §9 row, the statement paraphrase and the Lean doc | §9, `9014eea0` |
| P2 note 67 | **Accepted.** "Analogous to"; Kant's real possibility characterized | §1, Lean module doc |
| P2 senses (a)/(b) not type-distinct; untagged parameters | **Accepted.** `ConceptRelation` structure introduced; `Exercised` binders tagged `_6`; `Essential` tag gap recorded | vocab, `existence-esse-support.json`, §10 item 4 |
| P2 cross-lane sentence | **Accepted.** Amended | `existence-esse-support.json` |
| P2 §6 item 2 | **Accepted.** Relabelled as support for the necessity verdict; still "shared dependency" | §6 |

### Re-check of head `42755e2e` (accepted, mergeable as is)

The re-check confirmed all P1s and P2s resolved, with no new P1. Three P2s
and one nit were folded in:

| Finding | Disposition | Where |
|---|---|---|
| Argument 4 does not reduce exactly to the content premise: its bridge exists iff EC holds of the nature | **Accepted.** Law 16 added (EC ⇒ CNC and K1 for `adequateConcept`). The burden is restated: at the identity, argument 4 presupposes EC; Kant's ground for it is the content premise; other grounds fall under toward-EC revision condition (c) | Lean law 16, §2, §3 argument 4 and result, §5 Kant and assessment, §7, §13 P1-2 row, attempt |
| #1888 table: serious actualism | **Accepted.** The serious-actualist *motivation for EC at `n`* presupposes contingency; serious actualism itself allows necessary beings | §7 table |
| #1888 table symmetry | **Accepted.** The EC / "possibly absent" row lists the new bundle `63ac77e7`, which needs KT extended to adequate concepts | §7 table |
| Nit: `effectConcept` | **Accepted.** Described as the coexistence conditional only, not using the frame's causation | Lean doc, spec, §1, §2 |
