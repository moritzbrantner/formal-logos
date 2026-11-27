# "Omnium perfectiones pertinent ad perfectionem essendi" and subsistent esse

Third checkpoint of the warrant phase (owner direction 2026-11-27, #2103, #143). It
follows checkpoint 1 (PR #2166, possession) and checkpoint 2 (PR #2170, q.4 a.2
preexistence). Checkpoint 2 found that one ST I q.4 a.2 co. sentence (`5c5281dd`)
carries two loci of the case:

- universal transfer `b26c10a0`, through its reading `791fa216`;
- the second proof with ad 3, which is where the theistic content separates from
  an impersonal source (locus (b) of PR #2170).

Baseline: main `3b0910230`.

[Attempt record](../../corpus/attempts/1b16fb17-0487-4a32-b278-e94bc8f38e5d.json) ·
[Batch spec](../../specs/mode-of-being-middle-term.toml) ·
[Lean vocabulary](../../TruthCore/Causality/ModeOfBeingMiddleTerm.lean) ·
[Lean results](../../TruthCore/Results/Causality/ModeOfBeingMiddleTerm/Solution.lean)

This is a provisional judgment under the systematic loop. It changes no frontier
rule or closure, and no existing theorem or Challenge. **Review status:** the
independent semantic challenge at `a13b3024` accepted it with qualifications (5 P1,
7 P2). The repairs are in §9; a focused re-check is pending.

## 1. The source, in full

I read I q.4 a.2 and I q.4 a.1 in the materialized SCTA witnesses (passages
`ddbc72a3` and `5ae232fc`; cache under the worktree's ignored `.cache/`).

**Objection 3 of a.2.** "vivens est perfectius quam ens, et sapiens quam vivens:
ergo et vivere est perfectius quam esse, et sapere quam vivere. Sed essentia Dei est
ipsum esse. Ergo non habet in se perfectionem vitae et sapientiae, et alias huiusmodi
perfectiones."

**Second proof of a.2 co.** "Secundo vero, ex hoc quod supra ostensum est, quod Deus
est ipsum esse per se subsistens: ex quo oportet quod totam perfectionem essendi in se
contineat. Manifestum est enim quod, si aliquod calidum non habeat totam perfectionem
calidi, hoc ideo est, quia calor non participatur secundum perfectam rationem: sed si
calor esset per se subsistens, non posset ei aliquid deesse de virtute caloris. Unde,
cum Deus sit ipsum esse subsistens, nihil de perfectione essendi potest ei deesse.
Omnium autem perfectiones pertinent ad perfectionem essendi: secundum hoc enim aliqua
perfecta sunt, quod aliquo modo esse habent. Unde sequitur quod nullius rei perfectio
Deo desit."

**Ad 3.** "licet ipsum esse sit perfectius quam vita, et ipsa vita quam ipsa
sapientia, si considerentur secundum quod distinguuntur ratione: tamen vivens est
perfectius quam ens tantum, quia vivens etiam est ens; et sapiens est ens et vivens.
Licet igitur ens non includat in se vivens et sapiens, quia non oportet quod illud quod
participat esse, participet ipsum secundum omnem modum essendi: tamen ipsum esse Dei
includit in se vitam et sapientiam; quia nulla de perfectionibus essendi potest deesse
ei quod est ipsum esse subsistens."

**I q.4 a.1 ad 3.** "ipsum esse est perfectissimum omnium: comparatur enim ad omnia ut
actus. Nihil enim habet actualitatem, nisi inquantum est: unde ipsum esse est
actualitas omnium rerum, et etiam ipsarum formarum. Unde non comparatur ad alia sicut
recipiens ad receptum: sed magis sicut receptum ad recipiens."

**What the sentence says.** It has two clauses:

1. a thesis: the perfections of all things pertain to the perfection of being;
2. its stated ground: things are perfect insofar as they have being in some way.

Three readings are defensible. Each already exists as its own statement. "Mode of
being" and "perfection of being" now have their own disambiguations:
MODE_OF_BEING (`8eb007a6`: dependence `064cf1e9`, constitutive DEF-MODE-OF-BEING) and
PERFECTION_OF_BEING (`62ca3d65`: thin `84147eb5`, intensive `0a2bf1a0`).

| Reading | Content | Statement |
| --- | --- | --- |
| **R-dep**, dependence | Nothing has a perfection without having being. This is the ground clause read per respect, as a necessary condition. It is close to q.4 a.1 ad 3's "nihil habet actualitatem, nisi inquantum est". | `196e6606`; `7067553d` (stated by claims `6311aef8`, q.4 a.1 ad 3, and `5fd6b154`, q.3 a.4); MODE_OF_BEING_1 (`f2fa8028`) |
| **R-mode**, constitutive | Every perfection a thing has in act is a mode of its being. | `791fa216`, with the primitive `ModeOfBeing` (DEF-MODE-OF-BEING, MODE_OF_BEING_2) |
| **R-pure**, over real determinations | Every pure perfection is a perfection of being. | `c4fb87a6`, with the primitive `OfBeing` (either PERFECTION_OF_BEING sense) |

Beyond R-dep, the stronger readings draw on two distinct act-of-being theses, now
separate statements:

- **R-act₁** (`8c64b036`, `FiniteEsseReceivedAndLimited`): the esse of whatever is not
  its own being is received in a principle, as act in a receiving potency, and is
  limited. Sources: q.4 a.1 ad 3 ("sicut receptum ad recipiens"), q.3 a.4. In the
  corpus it is carried by the reception and participation vocabulary (`7fcfcee8`,
  `14325c83`, `7338142d`) and the real-distinction premises of the q.3 a.4 routes.
- **R-act₂** (`254ee26f`, `IntensiveEsse`): every pure perfection is a perfection of
  esse itself, a way of being that the act of being includes. This is `c4fb87a6` in
  the PERFECTION_OF_BEING_2 sense, not an independent support for it. Its textual
  basis is ad 3 ("ipsum esse Dei includit in se vitam et sapientiam"; "secundum omnem
  modum essendi") and the q.4 a.1 ad 3 gloss "actualitas omnium rerum, et etiam
  ipsarum formarum".

`7067553d` encodes q.4 a.1 ad 3 only in its dependence form (`InAct x r → InAct x
esse`). DEF-ESSE (`5c308c8c`) glosses esse as "the actuality of all things, even of
forms", but its declaration is that dependence form. The gloss is now recorded in the
definition's note as a contested act-of-being reading, inside an accepted
definition, which the declaration does not certify.

**What the ground yields, and how Aquinas uses it.** Read as a necessary condition,
the "secundum hoc enim … quod" clause yields R-dep, and every rival grants that much.
But Aquinas does not use the ground as a bare necessary condition:

- "secundum hoc … quod" can mean "in virtue of this, that": being perfect *by* having
  being in some way, which is constitutive;
- the second proof infers from the sentence with "unde sequitur" that no perfection
  of anything is lacking to God, which needs more than R-dep;
- q.4 a.1 ad 3 passes with "unde" from the dependence clause ("nihil habet
  actualitatem, nisi inquantum est") to "ipsum esse est actualitas omnium rerum, et
  etiam ipsarum formarum";
- ad 3 speaks of participating esse "secundum omnem modum essendi", treating life
  and wisdom as modes of esse.

So the text uses the ground to support the constitutive reading. Whether the ground
*warrants* that reading turns on the passage from R-dep to an act-of-being thesis.
That inference is not yet formalized, and its bridge is not located (§8).

**Ad 3.** It answers objection 3: being is less perfect than life, God is only being,
so God lacks life. The answer has two parts.

- **First clause.** Esse is more perfect than life only "secundum quod distinguuntur
  ratione". The living is more perfect than what is *only* a being, because the
  living is also a being. This removes objection 3's inference from "vivere est
  perfectius quam esse" to "what is ipsum esse lacks life". It does so without R-act:
  it is a point about what is being *tantum*, against a comparison of rationes.
  Objection 3 is therefore **undercut** by ad 3's first clause.
- **Second clause.** What participates esse need not participate it "secundum omnem
  modum essendi". But "ipsum esse Dei includit in se vitam et sapientiam", because
  "nulla de perfectionibus essendi potest deesse ei quod est ipsum esse subsistens".

The "quia" clause says that no perfection of being *can be lacking*, and that God's
esse *includes* life and wisdom. It does not say that subsistent esse has each as a
real determination (`Has`). The same article meets "not lacking" by eminent
preexistence (first proof) and "ut unum" (ad 1). DISAMB `dc9c0a1b` separates IsPerfect
formal-or-eminent (HAVING_EVERY_PERFECTION_1) from really having pure determinations
(HAVING_EVERY_PERFECTION_2), and `02d16349` lists the formal/eminent distinction as an
open choice. So the stating claim `1c66ee49` now attaches to a new formal-or-eminent
sibling, `9a0a4951` (`OwnBeingLacksNoPerfectionOfBeingInAct`: what is its own being
lacks no perfection of being, being in act in it formally or eminently). Its relation
to `d164b1ff` (real `Has`) is `supports`, with that gap note. This matches SCG I.28
(claim `1c67e58f`, also `supports`). The application to life and wisdom remains
`supports` on `c4fb87a6`.

## 2. Consumer audit

| Premise | Registered consumers | The middle term occurs only in |
| --- | --- | --- |
| `791fa216` | `afb8cba3` (`universalCauseTransfers` → `b26c10a0`, with `2f6b9eff` and `5e281daf`); `a0b0e697` (`ParticularActuality.inheritance` → `ca58266a`, with `9e3109ea`); `2d54eb1b` (`mediatedInheritance` → `ca58266a`, with `9be98ad0`, `ModeThroughBearer`) | `791fa216` and `2f6b9eff`; `791fa216` and `9e3109ea`; `791fa216` and `9be98ad0` |
| `d164b1ff`, `c4fb87a6` | always together: `7d8bbdcb` (→ `fe67d766`), `95c04a6d` (→ `122b112e`), `ff74a7ac` (→ `17498c0a`, first unmoved mover) | `d164b1ff` and `c4fb87a6` |
| `196e6606` (R-dep) | `8ba56e15` (→ `7067553d`), `c2a87347` (→ `65c301a8`) | n/a |

Premise-free tests that bear on the same vocabulary:

- `02d16349` (→ `a39cbf5f`, `WholePowerClassification.ClassificationAudit`): whole
  power and strict purity constrain the perfection-of-being vocabulary. It records
  the formal/eminent distinction as an open repair choice.
- `32ac7e4e` (→ `1b1e7636`, `ModeAudit`): actual esse effects of the same OwnBeing
  source are not OwnBeing. Its inputs include the reception interfaces (R-act₁
  family) and the unreceived-to-OwnBeing interface.

An existing control already instantiates `791fa216` with `ModeOfBeing := InAct`
(`ParticularActuality`, line 113): the primitive is satisfiable trivially.

## 3. The formal results

All four results are verified: `scripts/verify-result.sh` reports Comparator and
NanoDa acceptance.

- **`modesPairIffTotalTransfer`** (statement `04c75ec4`). The pair 791fa216 ∧
  2f6b9eff, existentially closed over the primitive "mode of being", is equivalent to
  the composite: a total cause of a thing's being causes every perfection it has in
  act.
- **`ownBeingPairIffEveryPure`** (statement `8c07547d`). The pair d164b1ff ∧
  c4fb87a6, existentially closed over the primitive "perfection of being", is
  equivalent to the composite: whatever is its own being has every pure perfection.
- **`dependenceReading`** (statement `f2fa8028`). Given `7067553d`, the mode premise
  holds on MODE_OF_BEING_1. On that reading, the total-cause premise is exactly the
  composite in the first result.
- **`controls`** (statement `859b50dd`). One subsistent source and one recipient
  effect, two stipulated pure determinations (being, and a Boolean stand-in for life
  that is no recorded sense of LIVING):
  - **Thin profile** (PERFECTION_OF_BEING_1): `d164b1ff` holds, `c4fb87a6` fails at
    the stand-in, and the source lacks it. On the same profile R-act₁, own being is
    no recipient (`7338142d`) and a nonrecipient's determinations are pure
    (`32695660`) all hold, while R-act₂ fails.
  - **Act profile** (PERFECTION_OF_BEING_2, taken as purity): both premises, their
    composite and R-act₂ hold.

**What the certificates show, and what they do not.** The two equivalences are
instances of a general logical fact: any Barbara decomposition `∃ M, (∀ x, A x → M x)
∧ (∀ x, M x → C x)` is equivalent to `∀ x, A x → C x`. The certificates do not show
anything special about these pairs. What they fix is the bookkeeping: the pair's
consequence is its composite.

**Shift, not lighten: a judgment, not a certificate.** A middle term lightens the
load when something fixes it independently of the composite, so that each premise
has its own warrant. On file, nothing fixes "mode of being" or "perfection of being"
beyond R-dep (which makes one premise near-analytic and leaves the other carrying the
composite) and the act-of-being theses. On the act reading `2f6b9eff` is
near-analytic: causing the whole act of being causes what that act includes. So the
judgment that the decompositions shift the load rests on the absence of independent
fixing beyond R-act. It would change with an independent criterion of "perfection of
being" (revision conditions, §6).

| Pair | Dependence or thin reading | Act reading |
| --- | --- | --- |
| 791fa216 + 2f6b9eff | 791fa216 is near-analytic from `7067553d`, and the whole load sits on 2f6b9eff | 2f6b9eff is near-analytic, and the load sits on 791fa216, i.e. on R-act₂ |
| d164b1ff + c4fb87a6 | d164b1ff holds trivially, and c4fb87a6 fails for life and wisdom | d164b1ff is the subsistent-esse principle, and c4fb87a6 is R-act₂ with purity |

**The R-act₁ → R-act₂ bridge is missing.** The controls certify that R-act₁, with the
reception and purity interfaces, does not give R-act₂ on the stated vocabulary. The
two theses are counted separately.

**A recorded gap, not repaired here.** DEF-MODE-OF-BEING's `lean_declaration` names
the constraining premise `PerfectionsAreModesOfBeing`, not a declaration of
`ModeOfBeing`, which is a parameter. The record does not say so, contrary to
docs/corpus-model.md ("Definition dependencies and formal meaning"). The gap is
recorded on #2103.

## 4. Strongest positive warrant

| Claim | Strongest positive warrant | Shared with |
| --- | --- | --- |
| R-dep | Near-analytic. It is stated by q.4 a.1 ad 3 and q.3 a.4 (`7067553d`) and given as the sentence's ground. | Granted by every rival considered. |
| R-act₁ (esse received and limited, `8c64b036`) | q.4 a.1 ad 3 ("sicut receptum ad recipiens"); q.3 a.4 ("esse est actualitas omnis formae vel naturae"). The explanatory rationale assessed in causal-perfection-transfer (2026-11-24): a received act explains contraction, so an unreceived act has no principled restriction. | The reception and participation framework (sub-bundle A of the 2026-11-18 cluster assessment), the real-distinction premises of the q.3 a.4 routes, and the reception inputs of the route to OwnBeing. **One commitment, counted once.** |
| R-act₂ (intensive esse, `254ee26f`) | Textual: ad 3's "includit in se vitam et sapientiam" and "secundum omnem modum essendi"; the q.4 a.1 ad 3 gloss "et etiam ipsarum formarum". No argument on file derives it from R-act₁ (the controls show R-act₁ does not give it on the stated interfaces). | It *is* `c4fb87a6` in the PERFECTION_OF_BEING_2 sense, and the act reading of `791fa216`. Counted separately from R-act₁. |
| `9a0a4951` (formal-or-eminent whole power) | Stated by ad 3 (claim `1c66ee49`). The second proof gives an analogy: subsistent heat would lack nothing of the power of heat. | — |
| `d164b1ff` (whole power, real `Has`) | Supported by ad 3 (`1c66ee49`) and SCG I.28 (`1c67e58f`). Real having, as against eminent containment, is not settled by either passage. | Under R-act₂, close to a meaning postulate of "subsistent being". |
| `c4fb87a6`, for life and wisdom | Ad 3's treatment of life and wisdom as perfections of being (`supports`). | R-act₂ (identical in the act sense). |
| `2f6b9eff` (a total cause causes each mode) | On the act reading, near-analytic. On the dependence reading, it is the full transfer thesis (concurrence). | The secondary-cause rival `e3da0672` targets it on that reading (2026-11-18 restatement). |

A lead, unread, with no weight: Aristotle's "vivere viventibus est esse" (De anima
II.4), which Aquinas uses for life as the being of living things. If it gives a
constitutive reading of life as a mode of a living thing's esse without R-act₂ in
general form, R-mode would not presuppose R-act₂ for life. The claim that R-mode
needs R-act₂ is therefore limited to the readings examined here.

## 5. Rivals and the negated-premise test

**Denial of R-dep:** some perfection is had without being. No position considered
holds it. It conflicts with `7067553d`, which is stated twice.

**Objection 3 (being is less perfect than life, so ipsum esse lacks life):
undercut.** Ad 3's first clause removes its inference without R-act (§1). It is not a
surviving rival.

**The strongest surviving rival: the quantifier view (thin existence).** This is
separate from objection 3. It does not compare esse with life; it denies that there is
an act of being at all.

- *Account.* Life and wisdom are contents of essences. Existence is the
  instantiation of an essence and adds no content. "Subsistent being", if coherent,
  has no further content, so a source of being need not have life.
- *Prior work.* existence-in-essence-identity.md records this view as "the
  quantifier view", which recognizes no act of being beyond instantiation. That note's
  revision condition (b) asks for "a defended reduction of the act of being to
  instantiation"; none is on file. This note reuses that work and does not re-argue
  it.
- *What it grants:*
  - R-dep;
  - the form of `d164b1ff` on PERFECTION_OF_BEING_1 (the control's thin profile);
  - ad 3's contrast that participated being need not include every mode, read as
    predication.
- *What it denies:*
  - R-act₁ and R-act₂;
  - `c4fb87a6` for life and wisdom.
- *Conflicts.*
  - With accepted floor items: none identified.
  - With act and potency at the level of forms and motion (for example `c85e8ef5`):
    none. Act and potency can be kept with thin existence.
  - With the essence/esse framework read as act and potency: yes. But that framework
    is R-act₁, an open commitment of the routes. Denying R-act₁ and denying the
    framework are one move, not a price paid twice.
- *Kant's thesis.* Kant held that being is not a real predicate. That targets
  existence as a conceptual determination, and neither act-of-being thesis claims esse
  is one. Its relevance to R-act₁ or R-act₂ is not established here, so it carries no
  weight against them. The 2026-11-23 assessment found it does not reach the identity
  case without further premises.

**Standing: unresolved; comparison not run.** The evidence on file is asymmetric.

- R-act₁ has positive warrant on file: the q.4 a.1 ad 3 and q.3 a.4 texts and the
  2026-11-24 explanatory rationale for limitation by received act.
- R-act₂ has textual warrant (ad 3, q.4 a.1 ad 3) but no derivation from R-act₁.
- The quantifier view's distinctive claim, that there is no act of being beyond
  instantiation, has no positive warrant on file. The 2026-11-23 note records the
  view and its consequences, not a defended argument for it.
- At matching scope, the phenomenon is the limitation of finite perfections and what
  the being of a thing includes. The rival's positive account there is that
  limitation is explained by essential content alone. No assessment of that account
  against limitation by received act is on file.

So this is not parity. Because the explanatory comparison has not been run, I do not
convert the asymmetry into a verdict.

**The negated-premise test at locus (b).** Given R-act₂, the purity of life and
wisdom, and the source's being its own being, "whatever is its own being has life and
wisdom" follows (the composite; the control's act profile). Negating that conclusion
for an impersonal source that is its own being forces rejecting **R-act₂ or
OwnBeing**:

- rejecting R-act₂ is open to the quantifier view, which also rejects R-act₁;
- the controls show that keeping R-act₁ while rejecting R-act₂ is consistent on the
  stated interfaces. No source or defender of that combination is on file, so it is
  recorded as a logical option, not as a rival with weight;
- rejecting OwnBeing leads to a determinate-nature source, with the E and L
  obligations of the 2026-11-24 assessment.

**Substantive Objection Standard, both sides.**

| Target | Classification |
| --- | --- |
| R-dep | No substantive objection identified |
| Objection 3 against the source having life | Undercut by ad 3's first clause, without R-act |
| R-act₁ and R-act₂, by the quantifier view | A rival framework (2026-11-23). Unresolved; comparison not run. Positive warrant is on file for R-act₁ and textually for R-act₂; none for the rival's distinctive claim. |
| R-act, by Kant's thesis | Relevance not established; no weight |
| `9a0a4951` | No substantive objection identified |
| `d164b1ff` (real `Has`) | No objection identified. The gap is the reading: ad 3 states not lacking, not real having. |
| `c4fb87a6` for life and wisdom | Holds under R-act₂ (identical in the act sense); fails under the quantifier view |
| `2f6b9eff` on the dependence reading | The secondary-cause rival `e3da0672`, restated (2026-11-18), unchanged |

## 6. Provisional judgment (2026-11-27, repaired after challenge)

1. **The ground and its use.** Read as a necessary condition, the sentence's ground
   yields R-dep, which every rival grants. On R-dep, `791fa216` carries no load: the
   whole transfer load sits on `2f6b9eff` (certified). Aquinas uses the ground to
   support the constitutive reading ("secundum hoc … quod", "unde sequitur", the
   "unde" of q.4 a.1 ad 3). Whether it warrants that reading turns on the unformalized
   inference from R-dep to an act-of-being thesis.
2. **Each pair, existentially closed over its primitive, is equivalent to its
   composite** (certified; a general fact about Barbara decompositions). My judgment,
   not a certificate: the decompositions shift the load rather than lighten it,
   because nothing on file fixes the primitive independently of R-act. On the act
   reading `2f6b9eff` is near-analytic.
3. **Beyond R-dep, two act-of-being theses, counted separately.**
   - R-act₁ (received, limited esse) is one commitment with the reception framework
     and the real-distinction premises.
   - R-act₂ (intensive esse) is `c4fb87a6` in the act sense and the act reading of
     `791fa216`.
   - The R-act₁ → R-act₂ bridge is missing; the controls certify non-entailment on the
     stated interfaces.
4. **Rivals.** Objection 3 is undercut by ad 3's first clause. The quantifier view is
   the strongest surviving rival. Its standing is unresolved, and the comparison has
   not been run. The asymmetry is recorded: R-act₁ has positive warrant on file, R-act₂
   textual warrant, and the rival's distinctive claim none.
5. **Locus (b).** An impersonal source that is its own being must reject R-act₂ or
   OwnBeing. The theistic content of the second proof and ad 3 is conditional on
   R-act₂, OwnBeing and the purity classification. Purity of life and wisdom is
   stipulative: `hPureWisdom` is an explicit input in `WholePowerPerfection`, and
   ad 3 gives examples, not a criterion. Reaching intellect from really had wisdom
   needs a further bridge (`godHasIntellectFromWisdomCapacity` and
   `godHasIntellectFromWholePowerWisdom`, `WholePowerPerfection/Solution.lean` lines
   222 and 244). Those take `WisdomSelfCapacity` and an open recognition premise to
   HAS_INTELLECT_1, and are not registered results. Personhood is a further step
   again. `RootIntellectWill` is a separate immateriality route.
6. **`d164b1ff` stays supported.** Ad 3 states the formal-or-eminent sibling
   `9a0a4951` (claim `1c66ee49`), and supports `d164b1ff`, as SCG I.28 does
   (`1c67e58f`). Real having, as against eminent containment, stays open (DISAMB
   `dc9c0a1b`).

These are first grades. Nothing is established, defeated in the frontier sense, or
closed.

**Revision conditions.**

- A formalized R-dep → R-act inference (q.4 a.1 ad 3's "unde") with a located,
  warranted bridge; or a demonstration that no non-question-begging bridge is
  available.
- A defended argument for or against a real act of being distinct from essence; or a
  defended reduction of the act of being to instantiation (condition (b) of the
  2026-11-23 assessment).
- An explanatory comparison of limitation that favors one side.
- A criterion for which perfections are perfections of being, beyond ad 3's
  examples, or an independent classification of purity.
- A reading of "vivere viventibus est esse" that gives life as a mode of being without
  R-act₂.
- A positive case of a pure perfection that is not a mode of being, under an
  independently warranted classification of purity.

## 7. Shared-warrant map against PR #2166 and PR #2170

Count each item once.

- **R-act₁ is one commitment.** It carries:
  - the reception framework (`7fcfcee8`, `14325c83`, `7338142d`);
  - the real-distinction premises of the q.3 a.4 routes;
  - the reception inputs of the route to OwnBeing (as in `32ac7e4e`).
- **R-act₂ is a second commitment.** It carries:
  - `c4fb87a6` in the PERFECTION_OF_BEING_2 sense (identical with it);
  - `791fa216` on the act reading;
  - through `791fa216`, universal transfer `b26c10a0` on the act reading, and with it
    universal-source preexistence (PR #2170) and its consumers.
- **`5c5281dd` is one sentence.** Read as R-dep it is `196e6606`, `7067553d`. Read as
  R-mode it is `791fa216`. Read as R-pure it is `c4fb87a6`. These are three readings,
  not three supports.
- **That sentence underwrites all three loci of PR #2170.** It is stated by claim
  `5dd2d69f`, which also supports `f8ba2429`, `791fa216` and `c4fb87a6`.
  - Universal transfer `b26c10a0`, through `791fa216`.
  - Locus (b): the second proof with ad 3, through `c4fb87a6` and `d164b1ff`.
  - Locus (a): the bridge from a higher mode to intrinsic possession. Its
    intrinsic-perfection bridges take `c4fb87a6`: `122b112e` via `95c04a6d`, and
    `fe67d766` via `7d8bbdcb`.

  So a judgment of the sentence's reading, and of R-act₂ beneath it, moves all
  three. They are one dependency, not three.
- **The transfer locus.** `b26c10a0` = `5e281daf` + the pair. On the act reading the
  load sits on R-act₂ and `5e281daf`; on the dependence reading it sits on
  `2f6b9eff`. The secondary-cause rival `e3da0672` bears only on the latter.
- **Locus (b)** of PR #2170 = `d164b1ff` (supported) + `c4fb87a6` + OwnBeing. Beyond
  OwnBeing, its content is R-act₂ and the purity classification. Its route to OwnBeing
  uses R-act₁.
- **Possession (PR #2166) is separate.** Possession at the universal source is
  near-analytic on the power reading. The impersonal-source question of PR #2170 is
  located here: in R-act₂ and OwnBeing.

## 8. Next discriminating test

**Formalize the "unde" inference of q.4 a.1 ad 3, from R-dep to R-act, and locate
its missing bridge.** The passage moves from "nihil habet actualitatem, nisi inquantum
est" (R-dep, `7067553d`) to "unde ipsum esse est actualitas omnium rerum, et etiam
ipsarum formarum".

- State the target in each act sense: R-act₁ (`8c64b036`), R-act₂ (`254ee26f`).
- Search for the weakest bridge under which R-dep gives each. For example, "what
  every actuality depends on is the act of each", a passage from a necessary
  condition to constitution.
- Test the bridge against the quantifier view, which grants R-dep. A bridge the rival
  must reject only by rejecting R-act itself begs the question. A bridge with
  independent warrant discriminates.

This is the shared node under universal transfer, universal-source preexistence and
the subsistent-esse attributes. The q.3 a.4 first proof with De ente c.4 (vertical),
and an explanatory comparison of limitation (horizontal), remain the next tests after
it.

## 9. Review repairs (challenge at `a13b3024`)

| Finding | Disposition | Where |
| --- | --- | --- |
| P1-1 claim `1c66ee49` overattributes real `Has` | **Accepted.** Ad 3 says "cannot be lacking" and "includit in se". The claim now states the formal-or-eminent sibling `9a0a4951`, with `supports` to `d164b1ff` and a gap note. `d164b1ff` stays supported, consistent with SCG I.28 `1c67e58f`. | claim, relation, spec, §1, §6.6 |
| P1-2 R-act conflates two theses | **Accepted.** Split into R-act₁ (`8c64b036`) and R-act₂ (`254ee26f`), each a Lean definition. The controls certify that R-act₁ with the reception and purity interfaces does not give R-act₂. Judgment 5 restated: reject R-act₂ or OwnBeing. | Lean, spec, §1, §3, §4, §6.3, §6.5, §7 |
| P1-3 certificates prove a general logical fact | **Accepted.** Records and prose say "the pair, existentially closed over the primitive, is equivalent to the composite". "Shift, not lighten" is stated as a judgment resting on the absence of independent fixing beyond R-act. On the act reading `2f6b9eff` is near-analytic. | `04c75ec4`, `8c07547d`, results, argument meanings, §3, §6.2 |
| P1-4 "the ground supports only R-dep" overstates | **Accepted.** As a necessary condition the ground yields R-dep; Aquinas uses it for the constitutive reading ("secundum hoc … quod", "unde sequitur", q.4 a.1 ad 3 "unde", "secundum omnem modum essendi"). | `f2fa8028` paraphrase, §1, §6.1 |
| P1-5 sense metadata | **Accepted.** `f2fa8028` links the dependence DEF `064cf1e9`, not DEF-MODE-OF-BEING. DISAMB `8eb007a6` (MODE_OF_BEING) and `62ca3d65` (PERFECTION_OF_BEING) added, with DEFs `064cf1e9`, `84147eb5`, `0a2bf1a0`. DEF-ESSE's gloss recorded in its note as a contested reading; audit pins renewed. | definitions, disambiguations, DEF-ESSE, audits, §1 |
| P2-1 consumer table | **Accepted.** `2d54eb1b`'s partner is `9be98ad0`. Tests `02d16349` and `32ac7e4e` added. | §2 |
| P2-2 objection 3 | **Accepted.** Undercut by ad 3's first clause without R-act. The quantifier view is a separate surviving rival. | §1, §5 |
| P2-3 "parity" | **Accepted.** Standing: unresolved, comparison not run. The asymmetry of positive warrant on file is recorded. | §5, §6.4 |
| P2-4 next test | **Accepted.** Formalize the q.4 a.1 ad 3 "unde" inference. | §8 |
| P2-5 wisdom to intellect; purity | **Accepted.** The bridge (unregistered `godHasIntellectFrom…` theorems, recognition premise) is named. Purity is stipulative. | §6.5 |
| P2-6 "R-mode presupposes R-act" | **Accepted.** Qualified by the unread "vivere viventibus est esse" lead. | §4, §6 revision conditions |
| P2-7 R-act records; DEF-MODE-OF-BEING gap | **Accepted.** R-act₁ and R-act₂ are statements with source arguments noted, not mere candidate primitives. The gap is recorded on #2103. | statements, §3 |
