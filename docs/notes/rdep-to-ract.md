# The "unde" inference: from dependence on being to the act of being

Fourth checkpoint of the warrant phase (owner direction 2026-11-27, #2103, #143). It
takes up the next test of checkpoint 3 ([mode-of-being-subsistent-esse.md](mode-of-being-subsistent-esse.md),
PR #2171). Can the dependence of every actuality on being (R-dep, `7067553d`), which
every rival grants, warrant the act-of-being theses R-act₁ (`8c64b036`, esse received
and limited) and R-act₂ (`254ee26f`, intensive esse)?

Baseline: main `1c76d343`, with PR #2171 (head `d06eda76`) merged in, because R-act₁
and R-act₂ are registered there.

[Attempt record](../../corpus/attempts/05f20bb4-1b78-4ccd-b3ff-4d94554c26d1.json) ·
[Batch spec](../../specs/rdep-to-ract.toml) ·
[Lean vocabulary](../../TruthCore/Causality/DependenceToActOfBeing.lean) ·
[Lean results](../../TruthCore/Results/Causality/DependenceToActOfBeing/Solution.lean)

This is a provisional judgment under the systematic loop. It changes no frontier rule
and no existing theorem or Challenge. It is **unreviewed** until the independent
semantic challenge.

## 1. The sources, read in full

All five were read in the materialized witnesses:

| Text | Passage |
| --- | --- |
| ST I q.4 a.1 | `5ae232fc` |
| ST I q.3 a.4 | `c7da7c37` |
| De ente capp.3–4 (Baur/Koch numbering; capp.4–5 in the common numbering) | `7070ccdd` |
| ST I q.7 a.1 | `5f8926e5` |
| ST I q.7 a.2 | `fb608477` |

**ST I q.4 a.1, objection 3 and ad 3.** The objection: "ipsum esse videtur esse
imperfectissimum: cum sit communissimum, et recipiens omnium additiones". The reply,
in full:

> ipsum esse est perfectissimum omnium: comparatur enim ad omnia ut actus. Nihil enim
> habet actualitatem, nisi inquantum est: unde ipsum esse est actualitas omnium rerum,
> et etiam ipsarum formarum. Unde non comparatur ad alia sicut recipiens ad receptum:
> sed magis sicut receptum ad recipiens. Cum enim dico esse hominis, vel equi, vel
> cuiuscumque alterius, ipsum esse consideratur ut formale et receptum: non autem ut
> illud cui competit esse.

The respondeo supplies the sense of "perfect": "secundum hoc enim dicitur aliquid esse
perfectum, secundum quod est actu".

**The steps of the reply:**

| Step | Text | Role |
| --- | --- | --- |
| (a) | "ipsum esse est perfectissimum omnium" | thesis |
| (b) | "comparatur enim ad omnia ut actus" | reason for (a) |
| (c) | "nihil enim habet actualitatem, nisi inquantum est" | reason for (b); this is R-dep |
| (d) | "unde ipsum esse est actualitas omnium rerum, et etiam ipsarum formarum" | first "unde" |
| (e) | "unde non comparatur ad alia sicut recipiens ad receptum: sed magis sicut receptum ad recipiens" | second "unde"; this answers the objection's "recipiens omnium additiones" |
| (f) | "esse hominis … consideratur ut formale et receptum: non autem ut illud cui competit esse" | illustration of (e) |

**ST I q.3 a.4 co.**

- *First proof.* It is conditional: "Si igitur ipsum esse rei sit aliud ab eius
  essentia". It then argues that such esse must be caused by another.
- *Second proof.* It parallels (c)–(e): "esse est actualitas omnis formae vel naturae:
  non enim bonitas vel humanitas significatur in actu, nisi prout significamus eam
  esse. Oportet igitur quod ipsum esse comparetur ad essentiam quae est aliud ab ipso,
  sicut actus ad potentiam." Its ground is stated at the level of signification, and
  its conclusion is again conditional on an essence "quae est aliud ab ipso".
- *Third proof.* The participation argument ("illud quod habet esse et non est esse,
  est ens per participationem").
- *Ad 1.* Esse without addition is either "esse divinum" or "esse commune".
- *Ad 2.* Esse is said in two ways: "actum essendi" and "compositionem propositionis".

**De ente cap.3 [69874]** (the "intelligences" text), in order:

1. *Intellectus essentiae (DE1).* "Quicquid enim non est de intellectu essentiae vel
   quiditatis, hoc est adveniens extra et faciens compositionem cum essentia … possum
   enim intelligere quid est homo vel Phoenix et tamen ignorare an esse habeat in rerum
   natura. Ergo patet quod esse est aliud ab essentia vel quiditate, nisi forte sit
   aliqua res, cuius quiditas sit ipsum suum esse."
2. *Uniqueness (DE2).* Such a thing "non potest esse nisi una". Plurification happens
   only in three ways: (i) "per additionem alicuius differentiae"; (ii) "per hoc quod
   forma recipitur in diversis materiis"; (iii) "per hoc quod unum est absolutum et
   aliud in aliquo receptum". "Unde oportet quod in qualibet alia re praeter eam aliud
   sit esse suum et aliud quiditas."
3. *Causation (DE3).* "Omne autem quod convenit alicui vel est causatum ex principiis
   naturae suae … vel advenit ab aliquo principio extrinseco". Esse cannot be caused by
   the quiddity, so everything whose esse differs from its nature "habeat esse ab
   alio", and the series reduces to the first cause.
4. *Reception (DE4).* "Omne autem quod recipit aliquid ab alio est in potentia
   respectu illius, et hoc quod receptum est in eo est actus eius." Hence the quiddity
   is in potency to the esse it receives from God.
5. *Equivocity.* "pati, recipere, subiectum esse et omnia huiusmodi … aequivoce
   conveniunt substantiis intellectualibus et corporalibus".
6. *Plurality (DE5).* Because potency and act are in the intelligences, "non erit
   difficile invenire multitudinem intelligentiarum; quod esset impossibile, si nulla
   potentia in eis esset". They are distinguished "secundum gradum potentiae et actus".

**De ente cap.4 [69875].**

- *Three modes of having an essence.*
  - God "in ipso esse suo omnes perfectiones habet": "modo excellentiori omnibus rebus,
    quia in eo unum sunt", "sicut si aliquis per unam qualitatem posset efficere
    operationes omnium qualitatum".
  - Intelligences: "esse earum non est absolutum, sed receptum et ideo limitatum et
    finitum ad capacitatem naturae recipientis".
  - Composites: "esse est receptum et finitum, propter hoc quod ab alio esse habent".
- God is not "illud esse universale, quo quaelibet res formaliter est".

**ST I q.7.**

- *a.1 co.* A form "in se considerata, communis est ad multa: sed per hoc quod recipitur
  in materia, fit forma determinate huius rei". Then: "Illud autem quod est maxime
  formale omnium, est ipsum esse, ut ex superioribus patet". The "superiora" are the
  q.4 a.1 ad 3 text above.
- *a.2 co.* "forma creata sic subsistens habet esse, et non est suum esse, necesse est
  quod ipsum eius esse sit receptum et contractum ad determinatam naturam".
- *a.2 ad 1.* "hoc est contra rationem facti, quod essentia rei sit ipsum esse eius,
  quia esse subsistens non est esse creatum".
- *a.2 ad 3.* Prime matter "non existit in rerum natura per seipsam, cum non sit ens in
  actu".

## 2. The formalization

Vocabulary: [`DependenceToActOfBeing`](../../TruthCore/Causality/DependenceToActOfBeing.lean),
over the shared `GradesFrame` (`F.InAct`, IN_ACT_4; `F.esse`).

- **Fixed respect.** Respect identity in the frame is identity of *content*: humanity
  is not being. Every view considered grants that much (DE1). It is not real
  distinction.
- **Own being.** OwnBeing is read as *esse tantum*: the nature is being itself
  (`OwnBeingByQuiddity`, DEF `ad76481a`). On this reading, a creature whose existence is
  really identical with its essence (Suárez) is not its own being.
- **New senses.** ACTUALIZED_THROUGH (DISAMB `a409105e`) has two senses:
  - ACTUALIZED_THROUGH_1, `DeflatedActualizedBy` (DEF `799e0ff7`): the dependence
    reading, x has both r and a in act;
  - ACTUALIZED_THROUGH_2, the primitive `ActualizationFrame.ActualizedBy` (DEF
    `82ab06d0`): the act reading, r is actual in x through the act a.
- **Further definitions.**
  - The nature as a respect: `quiddity` (DEF `97c4f504`).
  - A nature's capacity: the primitive `CapacityFrame.Admits` (DEF `dbae9538`).

| Statement | Lean | Reading |
| --- | --- | --- |
| `8d7e24dc` first unde | `DependenceIsActualization` | (c)→(d): what x has in act, given that x has being, is actual in x through esse (ACTUALIZED_THROUGH_2) |
| `89d82643` second unde | `ActualizedQuiddityReceivesEsse` | (d)→(e), with q.3 a.4's "oportet igitur", weakest form at the nature: a nature actual through an esse other than itself receives it (RECEPTION_OF_ESSE_1) |
| `073e1411` | `QuiddityInAct` | every being in the domain has its nature in act; the domain is actual beings |
| `7de89edb` (existing) | `ReceivedEsseIsLimited` | received esse is limited |
| `11437cb4` | `PurePerfectionsActualSomewhere` | every pure perfection is had by something |
| `fdd2213a` inclusion | `ActualizedPureIsOfEsse` | a pure perfection actual through esse is a perfection of esse (PERFECTION_OF_BEING_2) |
| `21b08802` | `NoCreatureIsOwnBeing` | no CREATURE_1 has being itself as its nature (q.7 a.2 ad 1, not attributed as a stating claim) |

Results, all verified (Comparator and NanoDa):

- **`ractOneFromDependence`** (`d53d259e`): R-dep, first unde, second unde, nature in act
  and `7de89edb` give R-act₁.
- **`ractTwoFromDependence`** (`f3a50206`): R-dep, first unde, witness and inclusion
  give R-act₂.
- **`creatureReceptionFromActOfBeing`** (`56e315ff`): R-act₁ and `21b08802` give the
  esse-root leaf `29e71e43`.
- **`undeLoadMap`** (`7277b7d1`), premise-free:
  1. given R-dep, the first bridge ⟺ "esse is the actuality of every form had in act";
  2. given R-dep, the first bridge and the nature in act, the second bridge ⟺ "whatever
     is not its own being has its esse received in its nature";
  3. given R-dep, the first bridge and the witness, inclusion ⟺ R-act₂;
  4. on ACTUALIZED_THROUGH_1 the first bridge holds in every frame.
- **`limitationComparison`** (`96fc4767`), premise-free: see §5.
- **`controls`** (`7bc1af16`): finite profiles over two beings and three stand-in
  respects. The first and second bridges each fail on a profile where the other
  premises of `ractOneFromDependence` hold and R-act₁ fails. R-act₂ fails under thin
  inclusion or with no actualization, while R-dep and the witness hold.

  Extensions cannot tell the act relation from the dependence relation. Only the typed
  senses do, so the "non-reception profile" is one model read two ways.
- **`q7BridgeLoadMap`** (`9655a913`, statement `0c1a3ec8`) and **`q7Controls`**
  (`65a56bc5`, statement `6694d214`) cover the q.7 a.1 bridge (§5a).

**Sufficiency and need.** Each derivation is valid, and the controls show each bridge
is needed on those profiles.

**Equivalence.** Given R-dep and the side premises, each bridge is *equivalent* to what
it delivers. Plainly: **the "unde" inference makes the act-of-being commitment
explicit; it does not derive it from dependence.** For R-act₁ and R-act₂ this is
certified by `undeLoadMap`. The first bridge is analytic on the dependence reading, so
the content enters exactly where "through" is read as act.

## 3. Shift or lighten

| Bridge | Ground offered in the text | Granted by the rivals? | Shift or lighten |
| --- | --- | --- | --- |
| First unde (act reading) | (c), R-dep; q.3 a.4: "non enim … significatur in actu, nisi prout significamus eam esse" | Yes. R-dep, and the signification claim (q.3 a.4 ad 2 grants esse as the composition of a proposition) | **Shift.** The ground supports the dependence reading only |
| Second unde (reception) | q.3 a.4 "oportet igitur"; De ente DE4; the q.7 a.1 form–matter parallel | The general act/potency principle, for form in matter and accidents: yes. For esse: no | **Partial, conditional lightening.** DE4 has ordinary instances, but De ente itself says reception is said of intellectual and corporeal substances "aequivoce". The ordinary instances carry over only through an analogy bridge not argued on file |
| Inclusion (R-act₂) | The q.4 a.2 sentence 5c5281dd read constitutively (the sentence under test) | No | **Shift.** No independent text in these passages |

Recipient priority is not a relevant difference. Prime matter receives form though it
"non existit … per seipsam" (q.7 a.2 ad 3). So "the recipient of esse is nothing apart
from esse" does not separate esse from the material case. I record no objection on that
basis.

**De ente cap.4 on God's perfections reads by power-eminence**: "per unam qualitatem …
efficere operationes omnium qualitatum", "in eo unum sunt". That supports the
formal-or-eminent sibling `9a0a4951` (HAVING_EVERY_PERFECTION_1) for subsistent esse.
It does not support R-act₂, that every pure perfection is a perfection of esse as such.

## 4. De ente's independent route to R-act₁

| Step | Content | Quantifier view | Suárez (real identity) |
| --- | --- | --- | --- |
| DE1 conclusion | esse is not part of what a nature is understood to be | grants; this is its own thesis | grants |
| DE1 major, applied to esse | what is outside the understanding of an essence "advenit … faciens compositionem cum essentia" | rejects: existence is not an item that composes | rejects real composition |
| DE2 | at most one thing is esse tantum | grants, vacuously or as an incoherent case (2026-11-23) | grants on the esse-tantum reading; on the real-identity reading it would exclude two creatures (de-ente-esse-source-1628.md) |
| DE3 | what does not exist by its nature has existence from another | can grant the deflated form; brute existence is a separate rival, not re-litigated here | grants: the creature is "actual through the agent" |
| DE4, applied to esse | what receives from another is in potency to it, and what is received is its act | rejects | rejects: receiving *from* an agent is not receiving *in* a subject (DM XXXI.XIII.17–18, as recorded in de-ente-esse-source-1628.md) |

The route's separating step is DE4 with DE1's composition principle, applied to esse.
That is the content of the second unde. **The composition step** is this: an act other
in content than the nature, which the nature has from another, is received in the
nature as in a really distinct potency. It is one commitment under:

- q.4 a.1 ad 3 (e);
- q.3 a.4's second proof;
- De ente DE1 + DE4;
- q.7 a.2's "necesse est … receptum".

q.7 a.1 grounds "maxime formale" on q.4 a.1 ad 3 itself. Count the step once.

## 5. Negated-premise test and limitation at matching scope

**Can the rivals reject the bridges without rejecting anything accepted?**

- **The quantifier view** rejects the first bridge on the act reading, the second
  bridge and inclusion. It keeps R-dep and the first bridge on ACTUALIZED_THROUGH_1.
  - *Floor items.* No conflict identified. DEF-ESSE's act gloss is recorded as
    contested (#2171).
  - *What it gives up.* R-act₁, R-act₂ and what rests on them: the reception framework,
    and the new support option for `29e71e43`. `29e71e43`'s q.7 a.2 support rests on
    the same composition step (§4).
- **Suárez's real-identity view** grants the first bridge on the act reading and
  rejects only the second. So the two "unde" steps separate different rivals: the
  first separates the quantifier view, the second separates both.

**Limitation at matching scope.** Explanandum: whatever is not its own being lacks some
pure perfection. `limitationComparison` (`96fc4767`) certifies three things:

1. the essence-only account derives it from "a being has in act only what its nature
   admits" and "a nature other than being itself excludes some pure perfection";
2. the reception account ("limitatum … ad capacitatem naturae recipientis") derives it
   from reception in the nature, the capacity bridge, and **the same nature premise**;
3. the reception premises imply the essence-only premise on every being that is not
   its own being.

The controls add that R-act₁ with the capacity bridge, but without the nature premise,
does not give finitude. So the explanatory work at this scope is done by the nature's
exclusion, which both accounts share. **Reception of esse is not needed to explain
finitude in perfection.** This does not show that reception is false.

**Many finite beings.** De ente's own plurification modes are (i) an added difference,
(ii) reception of a form in diverse matters, and (iii) absolute versus received.
- Modes (i) and (ii) are on the side of essence and matter. They explain why beings with
  different natures, or the same nature in different matter, are many.
- Mode (iii) only separates the one *esse tantum*, if it is posited, from everything
  else.
- DE5's "the multitude of intelligences would be impossible without potency" needs "a
  being without potency would be esse tantum", which presupposes the act of being.

So **"esse is limited by essence" is not needed to explain why there are many finite
beings**. It is needed only to distinguish them from esse tantum, given that esse tantum
is posited. An essence-only account works as well at this scope.

**R-act-only explananda.** One is "why is esse, of itself unlimited ('maxime formale',
q.7 a.1), limited here?" That is an explanandum only for whoever already holds R-act₂ or
the q.7 a.1 premise. It is not at matching scope.

**Candidate replies for R-act, under the Substantive Objection Standard:**

- *"Essence-only limitation does not explain why the finite nature exists at all."*
  Both accounts appeal to an extrinsic cause of existence here (DE3; Suárez's "actual
  through the agent"). This does not discriminate.
- *Agreement and difference* (analyst formulation, attribution deferred; not on file as
  a registered argument). Many beings agree in being and differ in nature, and what
  things agree in must be a principle distinct from what they differ in.
  - Mechanism against its unrestricted form: everything shares self-identity and
    differs in nature, and no view posits a distinct principle of self-identity. So the
    principle needs a restriction to non-trivial shared perfections.
  - Whether being is such a perfection is the act reading itself.
  - Kept as the strongest open candidate. It discriminates only with a criterion of
    "non-trivial perfection" independent of R-act.
- *Degrees of being* (Fourth Way). The quantifier view's denial is already recorded as a
  kept, sense-relative rival (esse-root-leaves.md, row 14). It is a different explanandum
  and is not assessed here.

### 5a. The q.7 a.1 bridge: from reception toward intensive esse

The #2171 re-check named the candidate bridge from R-act₁ to R-act₂: unreceived esse is
unlimited, so it includes every pure perfection. The text is ST I q.7 a.1 co.:
"infinitum secundum quod se tenet ex parte formae non determinatae per materiam, habet
rationem perfecti. Illud autem quod est maxime formale omnium, est ipsum esse".

`q7BridgeLoadMap` (`9655a913`, premise-free) certifies two things.

1. The locus-(b) composite, that what is its own being really has every pure perfection,
   follows from three premises, without `d164b1ff` or `c4fb87a6`:
   - `7338142d` (own being is no recipient, with Recipient read as "has its esse
     received somewhere");
   - `1304b462` (esse is limited only through reception);
   - "unlimited esse really has every pure perfection".
2. On the **measure reading** of limitation (`LimitedByMeasure`, DEF `f971eabf`: lacking
   some pure perfection), "unlimited esse has every pure perfection" holds in every
   interpretation.

`q7Controls` (`65a56bc5`) runs one source that is its own being and has only being:
- on the **role reading** (only what is received is limited), `7338142d` and `1304b462`
  hold, and "unlimited esse has every pure perfection" fails;
- on the measure reading, that premise holds, and `1304b462` fails: the source is limited
  without being received.

So the bridge **shifts** the intensive content:
- on the role reading, it sits in "unlimited esse has every pure perfection", which is
  R-act₂'s content stated for beings;
- on the measure reading, it sits in `1304b462`, "only reception limits esse". The
  esse-root-leaves assessment already calls `1304b462` "the substantive claim that only
  reception limits esse" on that reading.

A source with only being, the quantifier view's source, rejects the one premise that
carries the content on each reading. The rival grants the step thought to separate the
views (non-reception of own being) and rejects the step that carries the content. Its
ground is the same as before: the thinness of existence. The bridge's grounds in q.7 a.1,
"maxime formale … ut ex superioribus patet", go back to q.4 a.1 ad 3 (§1).

**The option "keep `9a0a4951`, reject real Has"** (from the #2171 re-check) belongs to
the option set here as well. The q.7 a.1 bridge and the locus-(b) composite conclude
*real* having. R-act₂ makes at most "not lacking", the formal-or-eminent `9a0a4951`, a
meaning postulate of subsistent esse. An impersonal source could lack no perfection
eminently or virtually without really having life or wisdom. No defender of that option
is on file, so it carries no weight as a rival until one is sourced. It joins locus (b)
to the power-eminence reading (PR #2166, locus (a) of #2170).

## 6. The rival's positive warrant at matching scope

- **The quantifier view.**
  - (i) *Parsimony at the finitude and plurality scope.* At this scope, a really distinct
    received act adds no derivational content (certified), so positing it costs a
    constituent with no explanatory return. This is a defeasible tiebreaker, valid only
    at this scope. It is defeated by a shared explanandum that only reception explains.
  - (ii) *The success of the quantificational analysis of existence statements*
    (esse-root-leaves.md row 14; attribution deferred). This does **not** discriminate:
    Aquinas grants esse as "compositionem propositionis" (q.3 a.4 ad 2), and the
    analysis concerns existence *statements*.
  - So there is now one item of positive warrant at matching scope on file, (i). The
    #2171 asymmetry, "none on file", is revised to that.
- **Suárez's account** is on file (de-ente-esse-source-1628.md): the creature's own
  nature and the perfection communicated explain its finitude. It is the same essence-only
  structure, held by a view that keeps the act of being. So the limitation comparison
  separates real reception from no reception, not act of being from no act of being.

## 7. Provisional judgment (2026-11-27, unreviewed)

1. **The "unde" inference is explicative, not probative.** Given R-dep, each bridge is
   equivalent to what it delivers (certified). Its stated grounds are granted by every
   rival: R-dep in q.4 a.1 ad 3, signification in q.3 a.4. It shifts the load and does
   not lighten it.
2. **There are two separating steps, at different rivals.**
   - The act reading of "actuality of forms" (first unde) separates the quantifier view.
   - The composition step, real reception (second unde = q.3 a.4 "oportet igitur" = De
     ente DE1 major + DE4 = q.7 a.2 "necesse est"), separates Suárez as well.
   - The composition step is one commitment, counted once.
3. **No argument on file for the composition step must be accepted by a rival who grants
   R-dep and caused existence.** Its ordinary instances (form in matter) carry over only
   through an analogy bridge that De ente's "aequivoce" makes explicit and leaves
   unargued. R-act₁ in the real-reception sense keeps Aquinas's statements and its
   coherent place in the act/potency framework. As an argued thesis it is **weak to
   moderate**. It is not defeated.
4. **At matching scope, reception is not needed.** Finitude is certified; plurality
   follows from De ente's own modes. The essence-only accounts explain as well and have a
   scope-limited parsimony advantage. Standing at this scope: **the essence-only accounts
   are favored by parsimony.** Overall standing of R-act₁ against its rivals:
   **unresolved**. Its distinctive explananda presuppose it, and the strongest open
   candidate for a shared one (agreement and difference) needs a non-question-begging
   criterion.
5. **R-act₂ has no support from the "unde" beyond restatement.** The q.7 a.1 bridge
   also only shifts it (certified):
   - on the role reading the content sits in "unlimited esse has every pure perfection";
   - on the measure reading it sits in `1304b462`;
   - a source with only being rejects whichever carries it.

   De ente cap.4 supports only power-eminence for subsistent esse
   (HAVING_EVERY_PERFECTION_1, `9a0a4951`).
   - The impersonal-source exclusion at locus (b) needs the whole bundle: {OwnBeing,
     `d164b1ff` read intensively (real Has), R-act₂, purity}, or the q.7 a.1 premises in
     its place. Rejecting one member is forced; none in particular.
   - R-act₂ itself has textual warrant only.
   - "Keep `9a0a4951`, reject real Has" is an open logical option, with no defender on
     file. It joins locus (b) to locus (a) of #2170, where an impersonal source is not
     excluded.
6. **Qualification of an existing grade.** esse-root-leaves.md grades `29e71e43`
   "P, moderate to strong" on its q.7 a.2 reading. That reading's "necesse est" rests on
   the composition step, grounded in q.4 a.1 ad 3 (§4).
   - I record this as a qualification for the coordinator. That attempt's assessment is
     not edited here.
   - In the frontier, `29e71e43` now moves to *closed* by rule (a): it is proved from open
     premises, so its obligation moves to the unde bridges and `21b08802`. It is not
     established, and this adds no independent warrant.

These are first grades. Nothing is established or defeated in the frontier sense.

**Revision conditions:**
- An argument for the composition step that a rival granting R-dep and caused existence
  must accept. For example, agreement and difference, with a criterion of non-trivial
  perfection independent of R-act.
- A shared explanandum at matching scope that only reception explains.
- An argued analogy bridge from material reception to reception of esse, answering
  "aequivoce".
- For R-act₂, an argument other than the q.4 a.2 sentence.
- A reading of Suárez's or Scotus's treatment of intensive perfection (unread).

## 8. Shared-warrant map (update)

- **R-dep** (`7067553d`) is granted by all. It carries nothing that separates the views.
- **The act reading of actualization** (first unde, ACTUALIZED_THROUGH_2) is one
  commitment under:
  - DEF-ESSE's contested gloss;
  - `791fa216` on the act reading;
  - the inclusion route to R-act₂.
- **The composition step** (real reception) is one commitment under:
  - the second unde;
  - q.3 a.4's second proof;
  - De ente DE1 + DE4;
  - q.7 a.2 co., and thereby `29e71e43` on both its q.7 a.2 support and its new
    `ractOneFromDependence` option;
  - `7de89edb` on the role reading.

  The reception cluster (`7fcfcee8`, `14325c83`, `7338142d`, `1304b462`) has logically
  distinct members, conditional or negative. Each holds vacuously where nothing is
  received, so they share warrant with the composition step without sharing its content.
- **R-act₂** (intensive esse) has textual warrant only. It is registered as
  `logically_equivalent_to` `c4fb87a6` read as perfection of esse. Its q.7 a.1
  substitute moves its content to "unlimited esse has every pure perfection" (role
  reading) or to `1304b462` (measure reading). Locus (b)'s impersonal-source exclusion
  rests on it together with real having (`d164b1ff`), OwnBeing and purity.
- **Power-eminence** at subsistent esse (De ente cap.4) is the possession reading of
  PR #2166. It supports `9a0a4951`, not R-act₂.

## 9. Next discriminating test

The vertical approach to R-act₁ and R-act₂ now has one discriminating candidate left;
the unde and the q.7 a.1 bridge both only shift the load. **Formalize the
agreement-and-difference argument** and test whether any criterion of "non-trivial
shared perfection" is independent of the act reading. If none is, the vertical line is
exhausted. Then move horizontally:
- to the degrees-of-being node (`5a948c37`, `e462cf2f`), where the quantifier view's
  denial is the kept rival;
- or to the OwnBeing route's E/L obligations (2026-11-24), which an impersonal source
  that rejects R-act₂ must meet.
