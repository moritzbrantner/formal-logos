# The "unde" inference: from dependence on being to the act of being

Fourth checkpoint of the warrant phase (owner direction 2026-11-27, #2103, #143). It
takes up the next test of checkpoint 3 ([mode-of-being-subsistent-esse.md](mode-of-being-subsistent-esse.md),
PR #2171). Can the dependence of every actuality on being (R-dep, `7067553d`), which
every rival grants, warrant the act-of-being theses R-act₁ (`8c64b036`, esse received
and limited) and R-act₂ (`254ee26f`, intensive esse)?

Baseline: main `1c76d343`, with PR #2171 (head `5c6f259d`) merged in, because R-act₁
and R-act₂ are registered there.

[Attempt record](../../corpus/attempts/05f20bb4-1b78-4ccd-b3ff-4d94554c26d1.json) ·
[Batch spec](../../specs/rdep-to-ract.toml) ·
[Lean vocabulary](../../TruthCore/Causality/DependenceToActOfBeing.lean) ·
[Lean results](../../TruthCore/Results/Causality/DependenceToActOfBeing/Solution.lean)

This is a provisional judgment under the systematic loop. It changes no frontier rule
and no existing theorem or Challenge. **Review status:** the challenge at `56e9dab7`
accepted it with qualifications (5 P1, 6 P2). The repairs are in §10; a re-check is
pending.

## 1. The sources, read in full

All five Aquinas texts were read in the materialized witnesses:

| Text | Passage |
| --- | --- |
| ST I q.4 a.1 | `5ae232fc` |
| ST I q.3 a.4 | `c7da7c37` |
| De ente capp.3–4 (Baur/Koch numbering; capp.4–5 in the common numbering) | `7070ccdd` |
| ST I q.7 a.1 | `5f8926e5` |
| ST I q.7 a.2 | `fb608477` |

Suárez, *Disputationes metaphysicae* XXXI, sect. XIII, nn.17–18, was read in the pinned
local copy of the Castellote–Renemann edition (sha256 `1df6c70b`, pp. 80–81). There is no
passage record; attribution goes through this note.

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
- *Third proof.* "sicut illud quod habet ignem et non est ignis, est ignitum per
  participationem, ita illud quod habet esse et non est esse, est ens per
  participationem. Deus autem est sua essentia … Si igitur non sit suum esse, erit ens
  per participationem, et non per essentiam."
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
5. *Equivocity, with its scope.* "Et ita invenitur potentia et actus in intelligentiis,
   non tamen forma et materia nisi aequivoce. Unde etiam pati, recipere, subiectum esse
   et omnia huiusmodi, quae videntur rebus ratione materiae convenire, aequivoce
   conveniunt substantiis intellectualibus et corporalibus."
   - Potency and act are affirmed of intelligences.
   - What is said equivocally is receiving and the like *insofar as they seem to belong
     to things by reason of matter*.
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

**Suárez, DM XXXI.XIII.17–18.**

- *n.17.* "Irreceptum" is said two ways.
  - Unreceived both in and from anything is proper to God, "ipsum esse subsistens".
  - Created esse is "irreceptum in aliquo, quamvis sit receptum ab aliquo". It does
    not follow that it is unlimited.
  - On participation, "non esse imaginandum quod una res sit quae participat, sicut
    essentia, et alia quae participatur, sicut esse, sed quia una et eadem res est
    realitas modo participato et per vim alterius".
- *n.18.* It takes up the objection "esse non receptum in aliquo non habet unde
  limitetur".
  - Answer: created esse is limited "seipso et ex vi entitatis suae", intrinsically by
    its formal entity, and extrinsically by God, "vel effective, quia ab eo recipit
    tantam perfectionem essendi et non maiorem, vel ut a causa exemplari".
  - It admits "metaphysical" contraction, which needs only a "distinctio conceptuum
    cum aliquo fundamento in re". Under it, essence is limited "in ordine ad esse" and
    esse "quia est actus talis essentiae".
  - Physically, created existence is limited by the essence "non ut est potentia in
    qua recipitur, sed quia in re nihil aliud est quam ipsamet actualis essentia".

## 2. The formalization

Vocabulary: [`DependenceToActOfBeing`](../../TruthCore/Causality/DependenceToActOfBeing.lean),
over the shared `GradesFrame` (`F.InAct`, IN_ACT_4; `F.esse`).

- **Fixed respect.** Respect identity in the frame is identity of *content*: humanity
  is not being. Every view considered grants that much (DE1). It is not real
  distinction.
- **Own being has two senses** (DISAMB `1bff3cb4`, OWN_BEING):
  - OWN_BEING_1, *esse tantum*, the nature is being itself (`OwnBeingByQuiddity`, DEF
    `ad76481a`). The unde route uses this sense.
  - OWN_BEING_2, real identity of esse and essence (`EsseReallyIsEssence`, DEF
    `87f9e331`). De ente's stage (b) uses this sense (`a576300f`). A creature really
    identical with its existence (Suárez) has OWN_BEING_2 without OWN_BEING_1.
- **Reception of esse has a registered real-composition sense.** RECEPTION_OF_ESSE_1
  (DEF-ESSE-RECEIVED-IN) leaves the constitution of the receiving principle open. The new
  RECEPTION_OF_ESSE_VERSUS_EXTERNAL_CAUSE_5 (`RealCompositionReception`, DEF `74837d29`)
  requires the receiving principle to be really other than the esse. The registered
  statements (`89d82643`, `8c64b036`, `29e71e43`) use sense 1. Every claim below about
  "real reception" concerns sense 5.
- **"Actualized through" is sense-neutral on this route.**
  - ACTUALIZED_THROUGH (DISAMB `a409105e`) separates the dependence reading
    (`DeflatedActualizedBy`, DEF `799e0ff7`) from the act reading (the field
    `ActualizationFrame.ActualizedBy`, DEF `82ab06d0`).
  - Both have type `B → R → R → Prop`, so neither the Lean types nor bind-check enforce
    the distinction; only the definition records do.
  - Every result here is generic in the frame, so it also holds with the dependence
    relation, where the first bridge is analytic (`undeLoadMap` (4)).
- **Further definitions.** The nature as a respect, `quiddity` (DEF `97c4f504`). A
  nature's capacity, the primitive `CapacityFrame.Admits` (DEF `dbae9538`). The measure
  reading of limitation, `LimitedByMeasure` (DEF `f971eabf`).

| Statement | Lean | Reading |
| --- | --- | --- |
| `8d7e24dc` first unde | `DependenceIsActualization` | (c)→(d): what x has in act, given that x has being, is actual in x through esse (the frame field; sense-neutral) |
| `89d82643` second unde, **content form (strong)** | `ActualizedQuiddityReceivesEsse` | (d)→(e) with q.3 a.4's "oportet igitur": a nature actual through an esse other *in content* than itself receives it (RECEPTION_OF_ESSE_1) |
| `94036513` second unde, **real-otherness form (weak)** | `ActualizedRealOtherQuiddityReceivesEsse` | q.3 a.4's "aliud" read as real otherness: the same, when also the esse is really other than the essence |
| `073e1411` | `QuiddityInAct` | every being in the domain has its nature in act; the domain is actual beings |
| `7de89edb` (existing) | `ReceivedEsseIsLimited` | received esse is limited |
| `11437cb4` | `PurePerfectionsActualSomewhere` | every pure perfection is had by something |
| `fdd2213a` inclusion | `ActualizedPureIsOfEsse` | a pure perfection actual through esse is a perfection of esse (PERFECTION_OF_BEING_2) |
| `21b08802` | `NoCreatureIsOwnBeing` | no CREATURE_1 has being itself as its nature (q.7 a.2 ad 1, not attributed as a stating claim) |

The content form `strengthens` the real-otherness form (relation `09f6c23a`). Its
backing is `secondUndeContentGivesRealOther` (`c5debf00`), and its strictness witness is
`unbundledControls` (`a6f864af`).

Results, all verified (Comparator and NanoDa):

| Result | Theorem | Shows |
| --- | --- | --- |
| `96fc4767` | `ractOneFromDependence` | R-dep, first unde, second unde (content form), nature in act and `7de89edb` give R-act₁. **Declared a near-transcription (single application):** given its side premises the second unde is equivalent to the reception half (`undeLoadMap` (2)). Own being is OWN_BEING_1 |
| `7bc1af16` | `ractTwoFromDependence` | R-dep, first unde, witness and inclusion give R-act₂. **Declared a near-transcription:** inclusion is equivalent to R-act₂ given the rest (`undeLoadMap` (3)) |
| `f3a50206` | `creatureReceptionFromActOfBeing` | R-act₁ and `21b08802` give `29e71e43`. A real specialization of a strictly stronger thesis |
| `7277b7d1` | `undeLoadMap` | premise-free: (1) given R-dep, the first bridge ⟺ "esse is the actuality of every form had in act"; (2) given R-dep, the first bridge and the nature in act, the second bridge ⟺ reception in the nature of whatever is not esse tantum; (3) given R-dep, the first bridge and the witness, inclusion ⟺ R-act₂; (4) with the dependence relation the first bridge holds in every frame |
| `d53d259e` | `limitationComparison` | premise-free; see §5 |
| `56e315ff` | `controls` | finite profiles: the first and second bridges each fail where the other premises hold and R-act₁ fails; R-act₂ fails under thin inclusion or with no actualization |
| `13574c55` | `compositionStepUnbundled` | premise-free: the content form gives the real-otherness form; real otherness of whatever is not esse tantum, with the real-otherness form, gives back the content form; at-most-one real identity with an esse-tantum real-identity being gives real otherness |
| `c5debf00` | `secondUndeContentGivesRealOther` | content form ⇒ real-otherness form (backing of the strength registration) |
| `a6f864af` | `unbundledControls` | Suárez's profile: two creatures each really identical with its existence, not esse tantum, nothing received. At-most-one fails, real otherness fails, the real-otherness form holds vacuously, the content form fails |
| `65a56bc5` | `q7BridgeLoadMap` | premise-free; the q.7 a.1 bridge (§5a) |
| `9655a913` | `q7Controls` | a source with only being under the two readings of limitation (§5a) |

**Sufficiency and need.** Each derivation is valid, and the controls show each bridge
is needed on those profiles.

**Equivalence, and what it shows.** `undeLoadMap` and `limitationComparison` are
*formally immediate*. In particular (3) holds by construction, since inclusion is
R-act₂ restricted to actualized pure perfections. They fix where the load sits. That
the unde inference is therefore **explicative, not probative**, making the act-of-being
commitment explicit rather than deriving it from dependence, is my judgment as analyst,
resting on those equivalences and on §3.

## 3. Shift or lighten

| Step | Ground offered in the text | Granted by the rivals? | Shift or lighten |
| --- | --- | --- | --- |
| First unde | (c), R-dep; q.3 a.4: "non enim … significatur in actu, nisi prout significamus eam esse" | Yes. R-dep, and the signification claim (q.3 a.4 ad 2 grants esse as the composition of a proposition) | **Shift.** The ground supports the dependence reading only, and the route needs no more (sense-neutral) |
| DE1's major premise, applied to esse | "quicquid … non est de intellectu essentiae … est adveniens extra et faciens compositionem cum essentia" | For accidents (whiteness of a man): yes. For esse: the content distinction, yes; the composition, no | **Conditional lightening at most.** It has ordinary instances, and they carry over to esse only if esse is an item that "advenit"; that step is not argued apart from the conclusion |
| DE4, applied to esse | "omne … quod recipit aliquid ab alio est in potentia respectu illius" | For form in matter and light in air: yes. For esse: no | **Conditional lightening at most**, graded symmetrically with DE1's major. De ente affirms potency and act in intelligences and says only that receiving "quae videntur rebus ratione materiae convenire" is equivocal. The material instances support DE4-for-esse through the act/potency notion that Aquinas affirms of intelligences, but receiving *from* an agent must still be shown to be receiving *in* a subject (Suárez, XIII.17) |
| Inclusion (R-act₂) | The q.4 a.2 sentence 5c5281dd read constitutively (the sentence under test) | No | **Shift.** No independent text in these passages |

Reconciling the overall verdict: the two general principles lighten the load only
conditionally on a step that is not argued on file. So **on file, the route does not
lighten the load** (§7.1); it shifts it.

Recipient priority is not a relevant difference. Prime matter receives form though it
"non existit … per seipsam" (q.7 a.2 ad 3). So "the recipient of esse is nothing apart
from esse" does not separate esse from the material case. I record no objection on that
basis.

**De ente cap.4 on God's perfections reads by power-eminence**: "per unam qualitatem …
efficere operationes omnium qualitatum", "in eo unum sunt". That supports the
formal-or-eminent sibling `9a0a4951` (HAVING_EVERY_PERFECTION_1) for subsistent esse.
It does not support R-act₂, that every pure perfection is a perfection of esse as such.

## 4. The composition step, unbundled; De ente's routes

On this route the **one separating step is reception**, the second unde in its content
form (plus inclusion for R-act₂). `compositionStepUnbundled` splits it into:

- **(i) real otherness:** whatever is not esse tantum has its esse really other than its
  essence;
- **(ii) reception given real otherness:** the real-otherness form, the weaker sibling.

The content form follows from (i) and (ii), and gives (ii). The two parts have separate
routes:

- **(ii)** is DE4 with the act reading, the q.3 a.4 "oportet igitur", and q.4 a.1 ad 3
  (e).
- **(i)** has the stronger De ente route, **stage (b)** (de-ente-esse-source-1628.md).
  - Result `860eae63` (`atMostOneEsseIsEssenceFromPlurification`) gives `a576300f`,
    "at most one actual being has its esse identical with its essence" (OWN_BEING_2).
  - Its inputs are the plurification inventory `2495a71d`, no added difference, no
    matter, and the reception premises `6dfe01ab`, `7fcfcee8`, `14325c83`.
  - With a real-identity being that is esse tantum, at-most-one gives (i): conjunct (3)
    of `compositionStepUnbundled`.
  - **It fails at `75b5b027`:** "any two actual beings whose esse is their essence share
    one nature". This is the open #697 individuation gap.
  - **Shared dependencies:** stage (b) uses `7fcfcee8` and `14325c83`, the same
    receptive-potency premises as the reception cluster under (ii). The two parts are not
    independent.

**Where Suárez escapes: at stage (b), not at DE4.** Suárez's creatures each have their
esse really identical with their essence (OWN_BEING_2) without being esse tantum
(OWN_BEING_1).
- So they deny `75b5b027` on OWN_BEING_2: two such creatures do not share one nature.
- With it they deny at-most-one, and so (i).
- Given (i), (ii) is vacuous for them.

`unbundledControls` witnesses exactly this.

| Step | Quantifier view | Suárez (real identity; DM XXXI.XIII.17–18) |
| --- | --- | --- |
| R-dep; signification; DE1 content distinction; caused existence | grants | grants |
| First unde | grants on the dependence reading, which suffices for the route | grants on the act reading too |
| (i) real otherness, via stage (b) | rejects the frame: there is no esse principle to be other or identical | **rejects, at `75b5b027`** |
| (ii) reception given real otherness | rejects | grants vacuously (no creature has real otherness) |
| Reception in the constitution-open sense 1 | rejects (no act of being) | grants at the level of reason: "metaphysical contraction", XIII.18 |
| Reception in the real-composition sense 5 | rejects | rejects ("non ut est potentia in qua recipitur") |

## 5. Negated-premise test and limitation at matching scope

**Can the rivals reject the separating step without rejecting anything accepted?**

- **The quantifier view** rejects reception in every sense, and inclusion. It keeps R-dep
  and the first bridge on the dependence reading.
  - *Floor items.* No conflict identified. DEF-ESSE's act gloss is recorded as contested
    (#2171).
  - *What it gives up.* R-act₁, R-act₂ and what rests on them.
- **Suárez's account** rejects real otherness (i) at `75b5b027`, and reception in sense
  5. It grants a founded reason-level version of sense 1.

**Limitation at matching scope.** Explanandum: whatever is not its own being lacks some
pure perfection. `limitationComparison` (`d53d259e`) shows, formally immediately:

1. the essence-only account derives it from "a being has in act only what its nature
   admits" and "a nature other than being itself excludes some pure perfection";
2. the reception account ("limitatum … ad capacitatem naturae recipientis") derives it
   from reception in the nature, the capacity bridge, and **the same nature premise**;
3. the reception premises imply the essence-only premise on every being that is not its
   own being.

The controls add that R-act₁ with the capacity bridge, but without the nature premise,
does not give finitude. My judgment: the explanatory work at this scope is done by the
nature's exclusion, which both accounts share, so **reception is not needed to explain
finitude in perfection.** This does not show that reception is false.

Suárez's XIII.18 is this essence-only account, held by a view that keeps the act of
being: created esse is limited "seipso", intrinsically by its formal entity and
extrinsically by God.

**Many finite beings.** De ente's own plurification modes are (i) an added difference,
(ii) reception of a form in diverse matters, and (iii) absolute versus received.
- Modes (i) and (ii) are on the side of essence and matter.
- Mode (iii) only separates the one *esse tantum*, if it is posited, from everything
  else.
- DE5's "the multitude of intelligences would be impossible without potency" needs "a
  being without potency would be esse tantum", which presupposes the act of being.

So, in my judgment, **"esse is limited by essence" is not needed to explain why there
are many finite beings.** It is needed only to distinguish them from esse tantum, given
that esse tantum is posited.

**Agreement and difference at its strongest: the participation and degree version.**
- *The argument.* q.3 a.4's third proof: what has esse and is not esse "est ens per
  participationem". The criterion for which shared features need a distinct received
  principle is "more and less": a perfection things have in degrees, as in the Fourth
  Way's degrees of being (`5a948c37`, `e462cf2f`). Self-identity, which every view
  shares without positing a principle for it, has no degrees, so the criterion excludes
  it.
- *The rivals.*
  - **The quantifier view** denies degrees of existence (esse-root-leaves row 14, kept,
    sense-relative), so it rejects the criterion's application to being.
  - **Suárez** grants participation and degrees ("tantam perfectionem essendi et non
    maiorem", XIII.18) and explains them effectively and exemplarly, without a received
    principle (XIII.17: "una et eadem res … per vim alterius").
- *So:* the degree criterion separates the act of being from the quantifier view, but
  not real composition from Suárez. Whether being has degrees is exactly the
  degrees-of-being node.

**Candidate replies for R-act, under the Substantive Objection Standard.**
- *"Essence-only limitation does not explain why the finite nature exists at all."* Both
  accounts appeal to an extrinsic cause of existence (DE3; Suárez's "per vim agentis").
  This does not discriminate.
- *Degrees of being.* See the participation and degree version above.

### 5a. The q.7 a.1 bridge: from reception toward intensive esse

The #2171 re-check named the candidate bridge from R-act₁ to R-act₂: unreceived esse is
unlimited, so it includes every pure perfection. The text is ST I q.7 a.1 co.:
"infinitum secundum quod se tenet ex parte formae non determinatae per materiam, habet
rationem perfecti. Illud autem quod est maxime formale omnium, est ipsum esse".

`q7BridgeLoadMap` (`65a56bc5`, premise-free, formally immediate) shows two things.

1. The locus-(b) composite, that what is its own being really has every pure
   perfection, follows from three premises, without `d164b1ff` or `c4fb87a6`:
   - `7338142d` (own being is no recipient);
   - `1304b462` (esse is limited only through reception);
   - "unlimited esse really has every pure perfection".
2. On the **measure reading** of limitation (lacking some pure perfection), "unlimited
   esse has every pure perfection" holds in every interpretation.

`q7Controls` (`9655a913`) runs one source that has only being:
- on the **role reading**, `7338142d` and `1304b462` hold, and the unlimited-esse premise
  fails;
- on the measure reading, that premise holds, and `1304b462` fails.

So the bridge **shifts** the intensive content: to the unlimited-esse premise on the
role reading, and to `1304b462` on the measure reading.

DM XXXI.XIII.18 takes up exactly the objection "esse non receptum in aliquo non habet
unde limitetur", and answers it. That gives a sourced objection to `1304b462` on the
real-composition sense (esse-root-leaves row 16).

**The option "keep `9a0a4951`, reject real Has"** (from the #2171 re-check) belongs to
this option set.
- The q.7 a.1 bridge and the locus-(b) composite conclude *real* having.
- R-act₂ makes at most "not lacking" a meaning postulate.
- An impersonal source could lack no perfection eminently or virtually without really
  having life or wisdom.
- No defender is on file, so it carries no weight as a rival until one is sourced.

## 6. Positive warrant at matching scope

- **The essence-only family** (the quantifier view and Suárez) has one item of positive
  warrant against real reception (sense 5): **parsimony at the finitude and plurality
  scope.**
  - At this scope a received act in a really distinct potency adds no derivational
    content, and positing it costs a constituent with no explanatory return there.
  - It is a defeasible tiebreaker limited to this scope. A shared explanandum that only
    real reception explains would defeat it.
  - It is credited to the family's shared essence-only account of limitation, which
    Suárez holds explicitly (XIII.18).
- **The quantifier view's distinctive claim**, that there is no act of being beyond
  instantiation, still has **no positive warrant on file**. #2171's record stands.
  - The success of the quantificational analysis of existence statements
    (esse-root-leaves row 14; attribution deferred) does not discriminate: Aquinas grants
    esse as "compositionem propositionis" (q.3 a.4 ad 2).
  - Parsimony against real reception is not parsimony against the act of being: Suárez
    keeps the act of being and shares it.

## 7. Provisional judgment (2026-11-27, repaired after challenge)

1. **The unde inference is explicative, not probative.** This is my judgment on formally
   immediate equivalences: given R-dep, each bridge is equivalent to what it delivers.
   Its stated grounds are granted by every rival: R-dep in q.4 a.1 ad 3, signification in
   q.3 a.4.
   - The general principles DE1 and DE4 lighten only conditionally on an unargued step.
   - So on file the route shifts the load and does not lighten it.
   - `ractOneFromDependence` and `ractTwoFromDependence` are declared near-transcriptions.
2. **On this route the act reading does no work.** The results are generic in the frame,
   and on the dependence reading the first bridge is analytic. The **one separating
   step** is reception, the second unde in content form (plus inclusion for R-act₂).
   - That step bundles (i) real otherness and (ii) reception given real otherness.
   - It is one commitment across q.4 a.1 ad 3 (e), q.3 a.4 "oportet igitur", De ente DE1
     major + DE4, and q.7 a.2 "necesse est". Count it once.
3. **Failure point named.** R-act₁ in the real-composition sense is **weak to moderate**
   as an argued thesis, not defeated.
   - Its strongest route to real otherness, De ente stage (b) (`860eae63` → `a576300f`),
     fails at `75b5b027` (the #697 individuation gap). That is exactly where Suárez's
     real-identity creatures escape.
   - (ii) rests on DE4, which has no warrant on file beyond its material instances, and
     those carry over only through receiving-from ⇒ receiving-in, which Suárez denies.
   - Stage (b) shares `7fcfcee8` and `14325c83` with (ii).
4. **At matching scope, reception is not needed.** Finitude follows formally immediately
   from the shared nature premise; plurality follows from De ente's own modes.
   - Standing at this scope: the essence-only family is favored over real reception by a
     scope-limited parsimony tiebreaker.
   - Overall standing of R-act₁ against its rivals: **unresolved**.
5. **R-act₂ has textual warrant only.** The unde gives it nothing beyond restatement, and
   the q.7 a.1 bridge only shifts it. De ente cap.4 supports only power-eminence
   (`9a0a4951`).
   - Locus (b)'s impersonal-source exclusion needs the bundle {OwnBeing, `d164b1ff` read
     intensively (real Has), R-act₂, purity}, or the q.7 a.1 premises in its place.
     Rejecting one member is forced; none in particular.
   - "Keep `9a0a4951`, reject real Has" is an open option with no defender on file.
6. **The frontier movement is relocation, not progress.**
   - With the two derivations declared near-transcriptions, R-act₁ (`8c64b036`) appears
     as an open leaf.
   - `29e71e43` still closes by rule (a) through `creatureReceptionFromActOfBeing`. Its
     obligation moves to a strictly stronger thesis, R-act₁, which carries a lower argued
     grade and presents the same composition step.
   - Its grade is revised by sense, by coordinator decision (esse-root-leaves.md (f2)):
     strong as textual commitment; weak to moderate on the real-composition sense, with
     Suárez's objection recorded as row 15; moderate to strong on the constitution-open
     sense, which DM XXXI XIII.18 does not reach.

These are first grades. Nothing is established or defeated in the frontier sense.

**Revision conditions:**
- A defence of `75b5b027` on OWN_BEING_2 (the #697 gap), or another route to real
  otherness that Suárez must accept.
- An argument that receiving from an agent is receiving in a subject for esse.
- A shared explanandum at matching scope that only real reception explains.
- A defended thesis that being admits degrees (the Fourth Way node), which would give
  the participation version its criterion against the quantifier view.
- For R-act₂, an argument other than the q.4 a.2 sentence.
- A reading of Scotus's treatment (unread).

## 8. Shared-warrant map (update)

- **R-dep** (`7067553d`) is granted by all. It carries nothing that separates the views.
- **The act reading of actualization** is idle on this route. It remains one commitment
  under DEF-ESSE's contested gloss and `791fa216` on the act reading.
- **The composition step** is one commitment:
  - (i) real otherness: De ente stage (b) (`860eae63`, `a576300f`, the open `75b5b027`);
  - (ii) reception given real otherness: the second unde, q.3 a.4's second proof, De
    ente DE4, q.7 a.2 co.;
  - and thereby `29e71e43` on both its q.7 a.2 support and its `ractOneFromDependence`
    option;
  - `7de89edb` and `1304b462` on the real-composition sense.

  Stage (b) and (ii) share `7fcfcee8` and `14325c83`. The reception cluster
  (`7fcfcee8`, `14325c83`, `7338142d`, `1304b462`) has logically distinct members,
  conditional or negative, that share warrant with the composition step without sharing
  its content.
- **R-act₂** (intensive esse) has textual warrant only. It is registered as
  `logically_equivalent_to` `c4fb87a6` read as perfection of esse. Its q.7 a.1 substitute
  moves its content to the unlimited-esse premise or to `1304b462`.
- **Power-eminence** at subsistent esse (De ente cap.4) is the possession reading of
  PR #2166. It supports `9a0a4951`, not R-act₂.
- **Degrees of being** (`5a948c37`, `e462cf2f`) now carry the participation version of
  agreement and difference.

## 9. Next discriminating test

**The vertical and horizontal tests converge on degrees of being.**
- The strongest form of agreement and difference, the participation and degree version,
  needs being to admit more and less. That is the degrees-of-being node (`5a948c37`,
  `e462cf2f`), where the quantifier view's denial is the kept rival (esse-root-leaves
  row 14).
- On that node Suárez is not a rival: he grants degrees without real composition. So a
  defended "being has degrees" would separate the act of being from the quantifier view,
  but not real reception from Suárez.
- Real reception needs either `75b5b027` defended on OWN_BEING_2 or an argument from
  receiving-from to receiving-in.

## 10. Review repairs (challenge at `56e9dab7`)

| Finding | Disposition | Where |
| --- | --- | --- |
| P1-1 registration inflates closure | **Accepted.** `ractOneFromDependence` and `ractTwoFromDependence` are declared `single_application` near-transcriptions citing `undeLoadMap` (2) and (3). R-act₁ is an open leaf; `29e71e43` still closes through `f3a50206`, and the move is stated as relocation. | spec, results, §2, §7.6 |
| P1-2 the act reading does no work | **Accepted.** The route is sense-neutral. One separating step (reception, plus inclusion). The "only the typed senses do" prose is corrected, since the senses share one type. DISAMB `a409105e` restated. | Lean docs, `8d7e24dc`, `fdd2213a`, `f2013d4f`, `a409105e`, §2, §7.2, §8 |
| P1-3 strongest route; strength label | **Accepted.** `89d82643` is the strong (content) form. The real-otherness sibling `94036513` is registered with `strengthens`. `compositionStepUnbundled` gives (i) + (ii). Stage (b) is added, with its failure point `75b5b027` and its shared `7fcfcee8`/`14325c83`. Suárez's escape is placed there. "Weak to moderate" is kept, with the failure point named. | Lean, spec, §4, §7.3 |
| P1-4 credit parsimony correctly | **Accepted.** Parsimony goes to the essence-only family against real reception, scope-limited. "None on file" stays for the quantifier view's distinctive claim. | §6, §7.4 |
| P1-5 real reception as a sense | **Accepted.** RECEPTION_OF_ESSE_VERSUS_EXTERNAL_CAUSE_5 (`RealCompositionReception`, DEF `74837d29`) is added to DISAMB `5921354b`. Grades are by sense. | DEF, DISAMB, §2, §4, esse-root-leaves (f2) |
| Coordinator decision on `29e71e43` | **Applied.** Graded by sense, with the previous grade kept in `b1fa5613`'s history. Row 15 records the objection. DM XXXI XIII.18 (read) shows that the objection does not reach the constitution-open sense. Row 16 records the same objection for `1304b462`, which supplies row 11's missing justification. | esse-root-leaves.md, attempt `b1fa5613` |
| P2-1 result IDs; link | **Accepted.** IDs corrected (and the swapped q.7 IDs). The PR link is a commit permalink. | §2, §5, §5a, PR |
| P2-2 "certified" | **Accepted.** "Formally immediate"; "explicative" and "not needed" rest on the analyst's judgment. §3 and §7.1 reconciled. | §2, §3, §5, §7 |
| P2-3 agreement and difference at its strongest | **Accepted.** The participation and degree version, with the "more and less" criterion; convergence with degrees of being. | §5, §9 |
| P2-4 own-being senses | **Accepted.** `ad76481a` is linked from argument `a811f5a3` and named in result `96fc4767`'s description. DISAMB `1bff3cb4` (OWN_BEING) added. | spec, DISAMB |
| P2-5 plan on `254ee26f` | **Accepted.** Moved into #2171, with the blocker set to `62ca3d65`'s undecided identification. | #2171 spec |
| P2-6 "aequivoce" | **Accepted.** Quoted with its scope and with "invenitur potentia et actus in intelligentiis". DE1's major premise is graded symmetrically with DE4. | §1, §3 |
