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
rule or closure, and no existing theorem or Challenge. It is **unreviewed** until
the independent semantic challenge recorded in the PR.

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

Three readings are defensible. Each already exists as its own statement.

| Reading | Content | Statement |
| --- | --- | --- |
| **R-dep**, dependence | Nothing has a perfection without having being. This is the ground clause read per respect. It is close to q.4 a.1 ad 3's "nihil habet actualitatem, nisi inquantum est". | `196e6606`; `7067553d` (stated by claims `6311aef8`, q.4 a.1 ad 3, and `5fd6b154`, q.3 a.4) |
| **R-mode**, constitutive | Every perfection a thing has in act is a mode of its being. | `791fa216`, with the primitive `ModeOfBeing` (DEF-MODE-OF-BEING) |
| **R-pure**, over real determinations | Every pure perfection is a perfection of being. | `c4fb87a6`, with the primitive `OfBeing` |

R-mode and R-pure say more than R-dep only on a presupposition. **R-act**: esse is
the act of all acts, "actualitas omnium rerum, et etiam ipsarum formarum", received
by forms "sicut receptum ad recipiens" (q.4 a.1 ad 3). In the corpus,
`7067553d` encodes q.4 a.1 ad 3 only in its dependence form (`InAct x r → InAct x
esse`). R-act's further content appears in the reception and participation
vocabulary: `7fcfcee8`, `14325c83`, `7338142d`, and the real-distinction premises of
the q.3 a.4 routes.

**What the sentence's own ground supports.** The "secundum hoc enim" clause gives
R-dep only. **Ad 3 is the decisive clause.** It answers objection 3, which is this
checkpoint's rival: being is less perfect than life, God is only being, so God lacks
life. The answer:

- what participates being need not participate it "secundum omnem modum essendi";
- ipsum esse subsistens includes life and wisdom, because no perfection of being can
  be lacking to it.

That answer treats life and wisdom as modes, or perfections, of being. It does not
argue that they are. Its "quia" clause states, generally, the whole-power principle
`d164b1ff`. That principle is now recorded as a stating claim, `1c66ee49`. Its
application to life and wisdom is recorded as `supports` on `c4fb87a6`, because the
passage says it of those two only.

## 2. Consumer audit

| Premise | Registered consumers | The middle term occurs only in |
| --- | --- | --- |
| `791fa216` | `afb8cba3` (`universalCauseTransfers` → `b26c10a0`, with `2f6b9eff` and `5e281daf`); `a0b0e697`, `2d54eb1b` (`ParticularActuality.inheritance` and `mediatedInheritance` → `ca58266a`, with `9e3109ea`) | `791fa216` and `2f6b9eff`; `791fa216` and `9e3109ea` |
| `d164b1ff`, `c4fb87a6` | always together: `7d8bbdcb` (→ `fe67d766`), `95c04a6d` (→ `122b112e`), `ff74a7ac` (→ `17498c0a`, first unmoved mover) | `d164b1ff` and `c4fb87a6` |
| `196e6606` (R-dep) | `8ba56e15` (→ `7067553d`), `c2a87347` (→ `65c301a8`) | n/a |

An existing control already instantiates `791fa216` with `ModeOfBeing := InAct`
(`ParticularActuality`, line 113): the primitive is satisfiable trivially.

## 3. The formal results

All four results are verified: `scripts/verify-result.sh` reports Comparator and
NanoDa acceptance.

- **`modesPairIffTotalTransfer`** (statement `04c75ec4`). For some reading of "mode
  of being", 791fa216 and 2f6b9eff hold exactly when a total cause of a thing's being
  causes every perfection it has in act.
- **`ownBeingPairIffEveryPure`** (statement `8c07547d`). For some reading of
  "perfection of being", d164b1ff and c4fb87a6 hold exactly when whatever is its own
  being has every pure perfection.
- **`dependenceReading`** (statement `f2fa8028`). Given `7067553d`, the mode premise
  holds on the dependence reading. On that reading, the total-cause premise is
  exactly the composite in the first result.
- **`controls`** (statement `859b50dd`). One subsistent source, two stipulated pure
  determinations (being, and a Boolean stand-in for life that is no recorded sense of
  LIVING), two profiles:
  - **Thin:** only being is a perfection of being. Here `d164b1ff` holds,
    `c4fb87a6` fails at the stand-in, and the source lacks it.
  - **Act:** every pure determination is a perfection of being. Here both premises
    and their composite hold.

**What the certificates show.** In every registered consumer each pair is its
composite with a primitive middle term. **The decompositions shift the load; they do
not lighten it.** The warrant of each pair is that of its composite, and which member
carries the load depends only on how the primitive is read:

| Pair | Dependence or thin reading | Act reading |
| --- | --- | --- |
| 791fa216 + 2f6b9eff | 791fa216 is near-analytic from `7067553d`, and the whole load sits on 2f6b9eff | 2f6b9eff is near-analytic (causing the whole act of being causes its determinations), and the load sits on 791fa216, i.e. on R-act |
| d164b1ff + c4fb87a6 | d164b1ff holds trivially, and c4fb87a6 fails for life and wisdom | d164b1ff is the subsistent-esse principle, and c4fb87a6 follows from R-act together with purity |

**A recorded gap, not repaired here.** DEF-MODE-OF-BEING's `lean_declaration` names
the constraining premise `PerfectionsAreModesOfBeing`, not a declaration of
`ModeOfBeing`, which is a parameter. The record does not say so, contrary to
docs/corpus-model.md ("Definition dependencies and formal meaning").

## 4. Strongest positive warrant

| Claim | Strongest positive warrant | Shared with |
| --- | --- | --- |
| R-dep | Near-analytic. It is stated by q.4 a.1 ad 3 and q.3 a.4 (`7067553d`) and given as the sentence's ground. | Granted by every rival considered. |
| R-act (esse as the act of every form) | q.4 a.1 ad 3 and q.3 a.4 ("esse est actualitas omnis formae vel naturae"). The explanatory rationale assessed in causal-perfection-transfer (2026-11-24): a received act explains contraction, so an unreceived act has no principled restriction. | The reception and participation framework (sub-bundle A of the 2026-11-18 cluster assessment) and the real-distinction premises of the q.3 a.4 routes. **One commitment, counted once.** |
| d164b1ff (whole power) | Now stated by ad 3 (claim `1c66ee49`). The second proof gives an analogy: subsistent heat would lack nothing of the power of heat. SCG I.28 supports it (claim `1c67e58f`). | Under R-act, close to a meaning postulate of "subsistent being". |
| c4fb87a6, for life and wisdom | Ad 3's treatment of life and wisdom as perfections of being (`supports`). | R-act |
| 2f6b9eff (a total cause causes each mode) | On the act reading, near-analytic. On the dependence reading, it is the full transfer thesis (concurrence). | The secondary-cause rival `e3da0672` targets it on that reading (2026-11-18 restatement). |

A lead, unread, with no weight: Aristotle's "vivere viventibus est esse" (De anima
II.4), which Aquinas uses for life as the being of living things.

## 5. Rivals and the negated-premise test

**Denial of R-dep:** some perfection is had without being. No position considered
holds it. It conflicts with `7067553d`, which is stated twice.

**The strongest rival: the quantifier view (thin existence).**

- *Account.* Life and wisdom are contents of essences. Existence is the
  instantiation of an essence and adds no content. "Subsistent being", if coherent,
  has no further content, so a source of being need not have life.
- *Prior work.* existence-in-essence-identity.md records this view as "the
  quantifier view", which recognizes no act of being beyond instantiation. It also
  assesses Kant's thesis there. That note's revision condition (b) asks for "a
  defended reduction of the act of being to instantiation"; none is on file. This
  note reuses that work and does not re-argue it.
- *What it grants:*
  - R-dep;
  - the form of `d164b1ff` on a thin reading of "perfection of being" (the control's
    thin profile);
  - ad 3's contrast that participated being need not include every mode, read as
    predication.
- *What it denies:*
  - R-act;
  - `c4fb87a6` for life and wisdom.
- *Conflicts.*
  - With accepted floor items: none identified.
  - With act and potency at the level of forms and motion (for example `c85e8ef5`):
    none. Act and potency can be kept with thin existence.
  - With the essence/esse framework read as act and potency (esse received by
    essence): yes. But that framework is an open commitment of the routes, and R-act
    itself. Denying R-act and denying it are one move, not a price paid twice.
  - Aquinas's reply to objection 3 restates R-act; it does not independently defeat
    the rival.
- *Kant's thesis.* Kant held that being is not a real predicate. That targets
  existence as a conceptual determination, and R-act does not claim esse is one. The
  relevance of the thesis to R-act is not established here, so it carries no weight
  against R-act. The 2026-11-23 assessment found it does not reach the identity case
  without further premises.
- *Discriminating test, not performed here.* Three candidates:
  - a defended argument for, or against, a real act of being distinct from essence
    in finite things (the q.3 a.4 first proof, De ente c.4);
  - an explanatory comparison of limitation: received act (R-act) against essential
    content alone (the rival);
  - the reduction asked for in condition (b).

**Within R-act, locus (b) does discriminate.** Given R-act, the act reading of
"perfection of being" with the purity of life and wisdom makes "whatever is its own
being has life and wisdom" follow (the composite; the control's act profile). So an
impersonal source that is its own being is excluded under R-act. An impersonal source
must reject either R-act (the quantifier view) or that it is its own being: a
determinate-nature source, with the E and L obligations of the 2026-11-24 assessment.

**Substantive Objection Standard, both sides.**

| Target | Classification |
| --- | --- |
| R-dep | No substantive objection identified |
| R-act, by the quantifier view | A rival framework, restated from 2026-11-23; parity on corpus evidence; no refutation either way |
| R-act, by Kant's thesis | Relevance not established; no weight |
| `d164b1ff` | No substantive objection identified. It holds on both readings, trivially on the thin one. |
| `c4fb87a6` for life and wisdom | Holds under R-act; fails under the quantifier view. Decided by R-act, not independently. |
| `2f6b9eff` on the dependence reading | The secondary-cause rival `e3da0672`, restated (2026-11-18), unchanged |

## 6. Provisional judgment (2026-11-27, unreviewed)

1. **The sentence's own ground supports only R-dep,** which every rival grants. On
   that reading, `791fa216` carries no load: the whole transfer load sits on
   `2f6b9eff` (certified).
2. **Both premise pairs are composites with a primitive middle term** (certified).
   Their decompositions add no warrant. Their warrant is that of "a total cause of
   being causes every actual perfection" and "whatever is its own being has every
   pure perfection".
3. **What these loci say beyond R-dep rests on R-act**: esse as the act of all acts,
   even of forms (q.4 a.1 ad 3; q.3 a.4). R-act is the same commitment as the
   reception and participation framework and the real-distinction premises. It must
   be counted once.
4. **The strongest rival is the quantifier view.**
   - It grants R-dep and the form of `d164b1ff`, and denies R-act and `c4fb87a6`
     for life and wisdom.
   - It conflicts with no accepted floor item; it gives up the route's own framework.
   - On current corpus evidence the standing between R-act and the quantifier view
     is **parity**. There is no defended reduction of the act of being, and no
     assessment of R-act itself.
5. **Within R-act, locus (b) excludes an impersonal source that is its own being.**
   The theistic content of the second proof and ad 3 is real. It is conditional on
   R-act and on the source being its own being. Stage two's reliance on it is
   therefore reliance on R-act plus the route to OwnBeing.
6. **`d164b1ff` moves from supported to stated** (ad 3, claim `1c66ee49`). On R-act
   it is close to a meaning postulate of subsistent being.

These are first grades. Nothing is established, defeated in the frontier sense, or
closed.

**Revision conditions.**

- A defended argument for or against a real act of being distinct from essence; or a
  defended reduction of the act of being to instantiation (condition (b) of the
  2026-11-23 assessment).
- An explanatory comparison of limitation that favors one side.
- A criterion for which perfections are perfections of being, beyond ad 3's
  examples.
- A positive case of a pure perfection that is not a mode of being, under an
  independently warranted classification of purity.

## 7. Shared-warrant map against PR #2166 and PR #2170

Count each item once.

- **R-act is one commitment.** It carries:
  - `791fa216` on the act reading;
  - `c4fb87a6` for life and wisdom;
  - the reception framework (`7fcfcee8`, `14325c83`, `7338142d`);
  - the real-distinction premises of the q.3 a.4 routes;
  - through `b26c10a0`, universal-source preexistence (PR #2170) and its consumers.
- **`5c5281dd` is one sentence.** Read as R-dep it is `196e6606`, `7067553d`. Read as
  R-mode it is `791fa216`. Read as R-pure it is `c4fb87a6`. These are three readings,
  not three supports.
- **The transfer locus.** `b26c10a0` = `5e281daf` + the pair. On the act reading the
  load sits on R-act and `5e281daf`; on the dependence reading it sits on `2f6b9eff`.
  The secondary-cause rival `e3da0672` bears only on the latter.
- **Locus (b)** of PR #2170 = `d164b1ff` (now stated) + `c4fb87a6` + OwnBeing. Beyond
  OwnBeing, its content is R-act.
- **Possession (PR #2166) is separate.** Possession at the universal source is
  near-analytic on the power reading. The impersonal-source question of PR #2170 is
  located here: in R-act and OwnBeing.

## 8. Next discriminating test

**Assess R-act itself.** Two candidates:

- **Vertical:** the q.3 a.4 first proof and De ente c.4, the real distinction as a
  premise of the routes. Weigh them against the quantifier view's reduction of the
  act of being to instantiation.
- **Horizontal:** an explanatory comparison of limitation, received act against
  essential content.

This is now the shared node under universal transfer, universal-source preexistence
and the subsistent-esse attributes.
