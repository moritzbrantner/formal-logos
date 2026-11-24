# Research checkpoint: actuality entails being in esse

- **Repository** `moritzbrantner/formal-logos`
- **Date** 2026-11-24
- **Target** `7067553d-cad9-5d79-b6b2-912e35051530`, `ActualityOnlyInsofarAsBeingReading`
- **Rival** `630273f8-b7f8-5b6a-895f-5d2ff23e84cc`, `ActualityWithoutBeingReading`
- **Status** Documentation checkpoint revised after the draft's independent semantic challenge. Targeted re-review is pending.
- **Evidence** Original search excerpts refer to `cae86aa7c092ca2d4276b0f8cfb29e3054d21533` and the route count to the historical `fd78b77e6` analysis. The goodness PRD is in [#1917](https://github.com/moritzbrantner/formal-logos/pull/1917).

## 1. Question and result

Does a genuinely actual perfection of a bearer entail that the same bearer has being in esse? Which weaker commitments actually suffice for the existing God-existence and attribute producers?

Select this because the previous route analysis identified it as indispensable to all 25 tested modal-free root derivations, and its meaning directly constrains both causal perfection and the proposed esse-only goodness route. It is distinct from causal superiority, universal causal transfer, intrinsic possession, composition, and the value bridge investigated in #1917. No new attribution to a source or formal status is asserted.

The provisional judgment favors direct existential import where `InAct x r` is genuine real exemplification by the same bearer `x` at the selected world. Its warrant is the bearer’s role in the actualization. Applicability to every input of the downstream `InAct` dictionaries remains open.

Do not solve this by declaring `InAct x esse` definitionally equal to `∃ r, InAct x r`. That would encode the contested direction. Do not identify every actual or necessary mathematical truth with an actual causal bearer of the perfection. Retain the original premise and its direct-assumption option.

## 2. Reuse and exact senses

The existing declaration in [Question4/Article1.lean](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/Question4/Article1.lean) is:

```lean
def ActualityOnlyInsofarAsBeingReading ... : Prop :=
  ∀ x r, InAct x r → InAct x esse
```

It formalizes only the consequence of ST I q.4 a.1 ad 3, not a whole theory of esse. The existing [PerfectionOfBeing](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Results/Causality/PerfectionOfBeing/Solution.lean) argument uses `ca84f62d` (perfect ↔ actual) and `196e6606` (perfection entails esse). As the current [maximum-definition-fork note](https://github.com/moritzbrantner/formal-logos/blob/main/docs/notes/maximum-definition-fork.md) explains, given the former, the latter is equivalent to the target: do not count their combination as independent corroboration. The proof uses only actuality → perfection, which is questionable if perfection means complete realization rather than possession in a respect.

Existing [elimination attempt](https://github.com/moritzbrantner/formal-logos/blob/main/corpus/attempts/actuality-without-being-elimination.json) (`6b73cc5c`) records that the rival is the negating existential of the target and that elimination from the other tested act/potency premises failed. The old formal countermodel remains valid. The [source attempt](https://github.com/moritzbrantner/formal-logos/blob/main/corpus/attempts/meinong-witness.json) (`8a4cbffd`) explicitly requires reading Meinong and mapping Sosein/Sein to act/esse before historical attribution.

Fix `A(x,r) = InAct x r`, `E(x) = m.ExistsAt w x` on one selected world, and a distinguished `esse`. The shared grades binder `IN_ACT_4` leaves the mode of possession open. Formal possession (`IN_ACT_1`), virtual or eminent possession (`IN_ACT_2`), and the inclusive reading (`IN_ACT_3`) are candidate interpretations. Each requires an explicit adapter for its uses of `IN_ACT_4`. The inclusive reading needs warrant covering both branches. [Act senses](../../corpus/disambiguations/in-act.json) · [GradesFrame](../../TruthCore/Causality/GradesFrame.lean)

The relevant interpretations include

- actual intrinsic exemplification, whether of a substantial or accidental actuality;
- real operation (including immanent operation, not necessarily an effect on another);
- real eminent possession or an exercised/unexercised but actual causal power, where independently warranted by the corpus's act-sense bridge;
- intentional or descriptive characterization of an object (`Sosein`), including mathematical and fictional cases;
- existence of a representation, thought, sentence, truthmaker, or event versus existence of its represented object or attributed individual;
- actual existence in the adopted in-re interpretation versus presence as a term or a member of a model's domain.

The formal carrier `Being : Type` is not by itself a guarantee of actual existence. No quantifier rule of Lean makes `E(x)` true for all `x`. The owner-selected [CogitoEsse profile](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Logic/CogitoEsse.lean) treats real existence as act of esse in its intended interpretation; it retains explicit `ExistingInActAt` and does not assert the reverse for arbitrary frames. In particular this is not an Eleatic restriction to causally interacting bodies, nor does it settle the reality of abstracta.

## 3. Source and rival reassessment

### Aquinas

ST I q.4 a.1 ad 3 answers the objection that esse seems imperfect and receptive of all modification. The reply makes esse the act by which other determinations, including form, are actual. Its final sentence draws a distinction between the received formal principle, as in the esse of a human or a horse, and the bearer that exists. The corpus's consequence about actuality and esse is already read here (`6311aef8`) and in q.3 a.4 co. (`5fd6b154`). The selected-world adapter in §4 is an analyst proposal. [Public Dominican translation, reply 3](https://www.newadvent.org/summa/1004.htm) · [Q.4 claim](../../corpus/claims/aquinas-st-i-q4-a1-ad3-actuality-as-being.json) · [Q.3 claim](../../corpus/claims/aquinas-st-i-q3-a4-esse-actuality-of-every-form.json)

### Meinong, §3–4

In *Über Gegenstandstheorie* (1904), §3 p. 8 presents *Sosein* as what characterizes the object itself, including the golden mountain and the impossible round square. Meinong qualifies the independence thesis by saying that warrant for a judgment about *Sosein* in matters knowable only a posteriori depends on knowledge of being. In §4 pp. 11–13, he distinguishes *Existenz* from *Bestand* and rejects the inference from the subsistence of an objective, such as the objective of an object's nonbeing, to the being of its object. In his account the object's own *Sosein* is available to inquiry independently of an existential judgment. [German transcription from the 1913 collection](https://ozekik.github.io/meinong/1904/)

Two mappings are open. The rival needs a bridge from objective characterization (`Sosein x r`) to the real same-bearer `InAct x r` consumed by the causal proofs. It also needs a mapping from the relevant denial of being, given the *Existenz*/*Bestand* distinction, to `¬ E(x)` or `¬ InAct x esse` in the chosen interpretation. The public text was consulted during independent review. Future corpus attribution requires a pinned witness for `MEINONG-GEGENSTANDSTHEORIE-3` and a reassessment of attempt `8a4cbffd` against both mappings.

## 4. Positive metaphysical warrant and exact calibration

An imagined golden mountain, an actually golden object and an existing drawing of a golden mountain are not the same bearer of the same property. The drawing can really have pigment; its subject can be characterized as gold without an actual mountain bearing gold. The difference between a realized property and a describable nature must remain even on a generous ontology of intentional objects.

The reason is **subject-involving actualization**: where the actuality is intrinsically the actuality of this bearer, not of an image or of a proposition about it, the bearer is part of what is actualized. A nonexistent object cannot be that actual bearer unless one rejects precisely this subject-involving reading of intrinsic realization. A process or trope ontology may deny a separate enduring substance; in that case the real event or trope can be the relevant bearer, and the conclusion concerns it rather than an inferred substance. This does not prove hylomorphism, the PSR, a sustaining cause, or modal necessity. For a realist about abstract objects, the same question is whether their determinations are actual in the intended sense; if so the application must count their appropriate being, or supply an explicit restriction. Do not exclude abstracta by stipulation in a generic carrier.

Reuse the open analyst bridge `ConceptualExistenceBoundary.ActualityExists` (`0884890e`) with `actual x := ∃ r, InAct x r` and `Exists x := m.ExistsAt w x`. Unpacking the existential gives the proposed calibration `∀ x r, InAct x r → m.ExistsAt w x`. Its positive warrant applies where the supplied relation records genuine real exemplification by that same individual at `w`. How abstracta fit the selected existence predicate and whether every virtual or power reading meets this calibration remain open. The intended power profile can supply existence via `IntendedProfile.powerExists` once an explicit premise takes the relevant `InAct x r` to that profile's `hasCausalPower w x` on the same carrier and frame. [ConceptualExistenceBoundary](../../TruthCore/Causality/ConceptualExistenceBoundary.lean) · [CausalPowerConcreteness](../../TruthCore/Causality/CausalPowerConcreteness.lean)

The existing omission control `6353cb71`, witnessed by `bbb4600e`, retains a fully characterized actual exemplar with empty existence when `ActualityExists` is omitted. The Parsons-style `nuclearCharacterizationControl` (`b1a51ed4`) supplies a complementary separation: a nuclear-existent object can lack extranuclear existence. Each control tests the relevant implication in its formal interpretation. [Conceptual omission argument](../../corpus/arguments/bbb4600e-3fae-4a72-8e9d-202741c5f268.json) · [Nuclear characterization result](../../corpus/results/b1a51ed4-efd3-47df-8463-e4c47fa2d02c.json)

The calibration and `ExistingInActAt` (`0436de86`) together give `7067553d`. Conversely, `7067553d` with `ActOfEsseSufficesForExistenceAt` (`546975ef`) gives the calibration. The two proposed compositions are

```lean
-- Proposed proof term; uncompiled, explicit hypotheses only.
fun x r h => hExisting x (hImport x r h)
-- Reverse under the already existing converse calibration:
fun x r h => hSuffices x (hBeing x r h)
```

With both esse/existence directions fixed, the calibration and the target are equivalent. The calibration can add independent support only if genuine same-bearer real exemplification warrants it at `w` independently of the target. The interpretation must keep every premise at that same world.

## 5. Exact downstream uses and residuals

### First mover and agency

`firstMoverIsMaximeEns` uses `MovesOnlyAsInActReading` and `7067553d` together once, in `hBeing f r (hInAct f x r hMoves)`. The conjunction entails `∀ f, IsFirstUnmovedMover MovedIn MovesIn f → InAct f esse` by taking the move witness from the first-mover predicate. That pointwise premise can replace both hypotheses in this proof. An independent defense would need to make the first mover's actual agency sufficient for its esse before identifying it with the maximum. [FirstMoverIsMaximeEns](../../TruthCore/Results/Aquinas/SummaTheologiae/FirstMoverIsMaximeEns/Solution.lean)

`causeOfBeingHasBeingOfAgency` applies the target to some act of the same cause `c` to obtain the unscoped conclusion `∀ c x, CausesIn c x esse → InAct c esse`. The mere-possibility argument `existingInActAtFromMerePossibility` derives `ExistingInActAt` (`0436de86`) independently of the target, using excluded middle, `LackingEsseIsMerelyPossible`, and `MerelyPossibleNotExistentAt`. To compose it at the agency consumer, one still needs the same-cause bridge `CausesIn c x esse → m.ExistsAt w c` on the chosen frame. The existing `EsseCausesExistAt` supplies this step for effects `x` that are actual concreta at `w`. The unscoped conclusion needs the unrestricted bridge or a defense that every covered effect is within that restriction. The existing preexistence route is also restricted, to effects in act at esse, while the cause-has-what-it-gives route yields the unscoped conclusion. When using `ExistingInActAt` to support the global target, its warrant must be independent of that target. [Agency, preexistence and giving](../../TruthCore/Results/Case/Catholicism/CauseOfBeingHasBeing/Solution.lean) · [Mere-possibility proof](../../TruthCore/Results/Causality/Round2ExistenceAct/Solution.lean) · [EsseCausesExistAt](../../TruthCore/Causality/Round2Grounding.lean)

### Universal perfection and causal goodness

The full perfection and causal-goodness predicates quantify over every instantiated respect. `perfectOfMaximum` and `supremelyGoodOfMaximum` use `hBeing x r hx` for an arbitrary distinct bearer. In `ee93f52b` (`firstMoverHasPerfectionsOfThings`), the arbitrary distinct-bearer use survives even after one narrows the first-mover identification lemma. The full-description naming argument `3e86eea5` likewise uses `hBeing` for an arbitrary distinct effect to derive causal coverage. Requiring the target only for bearers distinct from a supplied maximum is classically equivalent to the original, since the maximum already has esse. A restriction to existing bearers needs a coverage argument for any discarded `InAct` witness to recover the original endpoints. [Direct root attributes](../../TruthCore/Causality/DirectEsseRootPerfectionGoodness.lean) · [First mover's perfections](../../TruthCore/Results/Aquinas/SummaTheologiae/FirstMoverHasPerfectionsOfThings/Solution.lean) · [Full-description producer](../../TruthCore/Results/Aquinas/SummaTheologiae/MaximeEnsIsGodViaFullDescription/Solution.lean)

Fix n with its actual esse, maximum at esse, the existing `MaximumInBeingCausesAllBeingsReading`, and preexistence and restricted transfer. Then every distinct x with actual esse is covered. For the original full perfection endpoint, the exact remaining pointwise condition is:

```
∀ x r, x ≠ n → InAct x r → (InAct x esse ∨ InAct n r)
```

For `CausesEveryPerfectionOfOthers` the corresponding residual is:

```
∀ x r, x ≠ n → InAct x r → (InAct x esse ∨ CausesIn n x r)
```

The right disjunct supplies the endpoint for that pair. For the left disjunct, let `hAll := hGenus n hMax` and `hCause := hAll x hOther hEsse`. The perfection proof then uses `hPreexist n x r hCause hx`, and the causal proof uses `hTransfer n (hGenus n hMax) x r hOther hCause hx`. To recover full `IsPerfect` from its residual, decide `x = n` as in the original proof and transport `hx` along equality in the self-case. Each old endpoint in turn entails its residual via `Or.inr`. Recovering full `IsSupremelyGood` additionally requires `GoodIn n esse`. The residuals specify the open obligations when a distinct bearer lacks esse: direct possession by `n` for perfection and an edge from `n` for causal coverage.

## 6. Finite controls

The draft's `check_actuality_esse.py` and `check-results.txt` are absent from the checkpoint. Independent review reproduced the counts by enumerating acts for three bearers across three respects, and causal edges from the root to the two distinct bearers. Fix root `n` with esse and a distinct effect `e` with esse and `q`. Retain the root's esse causation of every other esse bearer, plus preexistence and transfer for every actual respect of any effect connected to the root at esse. All 158 retained assignments satisfy both residual equivalences and the equivalence of distinct-bearer scope with global scope. Separately, the 512 assignments of acts to the three bearers and three respects, with existence set by each bearer's esse, satisfy the equivalence between the target and selected-world existential import.

For an explicit structural model, let `n` and `e` have exactly `{esse, q}` initially, let `g` have exactly `{p}`, and let the existence extension at `w` be `{n, e}`. Order `n` above `e` and `g` at esse so that the actual `n` is the maximum. The fixed causal edges are `CausesIn n e esse` and `CausesIn n e q`. Independently vary `InAct n p` and `CausesIn n g p`, leaving all other edges empty. The target fails at `(g, p)` in every row, and the edge to the existing effect `e` keeps the causal background populated.

| `InAct n p` | `CausesIn n g p` | Full perfection | Causal coverage |
|---|---|---|---|
| No | No | No | No |
| Yes | No | Yes | No |
| No | Yes | No | Yes |
| Yes | Yes | Yes | Yes |

Restore the requirement `CausesIn c x r → E(x)` that the effect of a causal edge interpreted at `w` exists there. Since `E(g)` is false, this removes the causal-coverage-only row and the row satisfying both endpoints. The perfection-only row survives. It still counts `(g, p)` as an act in a bearer outside `E`. If `p` merely characterizes `g`, leaving it in a separate description table permits both esse/existence directions and closure for the real-actuality table. Counting it as real exemplification of `g` at `w` instead raises exactly the disputed calibration in §4. The finite assignments settle structural scope under their stated conditions. Whether such a real act without a real bearer is metaphysically possible depends on the interpretation left open here.

The older Lean control `godExistsFromMaximeEnsCausingAllByBeing_omit_hBeing` uses empty causation in an omission test for a different endpoint. The populated model above is an explicit structural test for the residuals and has no new Lean certificate. [Older omission model](../../TruthCore/Case/Catholicism/PreexistenceWithoutTransfer.lean#L393) · [Older omission theorem](../../TruthCore/Results/Case/Catholicism/PreexistenceWithoutTransfer/Solution.lean#L302)

## 7. Rival comparison and review boundary

| Rival or alternative | What can be retained | Remaining crux |
|---|---|---|
| Actualist Thomistic act of esse | Descriptions of nonactual objects are meaningful; actual intrinsic realizations are genuinely of their real bearers. | Warrant for calibration across entitative, operational and eminent possession senses. |
| Meinongian object theory | Objective characterization independent of being, including objects without actual realization. | The two open mappings to real actuality and the selected existence/esse reading in §3. |
| Abstract realist | Actuality may belong to nonphysical bearers; causal inertness does not imply nonbeing. | Whether abstract existence is within the chosen esse interpretation and which causal universal is warranted. |
| Process, trope or bundle ontology | Real events/determinations can be primitive or bearers of actuality; no separately posited substance is required. | Same-bearer calibration for operations and attribution. Cannot be refuted simply by demanding a substance. |
| Strong actuality-without-being rival | Asserts a real actualization while denying esse of its very bearer in the same interpretation. | Explain what makes it real rather than characterized and how the same bearer participates in existential causation. The formal rival remains satisfiable in the old encoding. |

The independent semantic challenge of draft `0d091bf61c06773ff404a65e55c26ac29c1f824e` checked the consumer uses, act senses, public source readings and finite controls. The revisions above address its findings. Targeted re-review of the revised assertions is pending, and a future new source attribution requires its own pinned evidence.

## 8. Integration plan and next discriminating research

1. For a future formal implementation, use the current consumer context and dossier, `truth related 7067553d`, `truth brief`, `truth novelty` and `truth semantics` to compare the proposed scope with existing support.
2. If pursuing the historical attribution, materialize the existing Meinong candidate and test both mappings in §3. Preserve the old contradictory rival as a formal alternative while that interpretation remains open.
3. Consider a source-local first-mover sibling and a selected-world import sibling. Register only meaningful new support, not repeated equivalent forms. Reuse the existing same-bearer operation and existence results. Keep `7067553d` and all frozen Challenges.
4. Test the hard positive case: **a real, immanent operation or actual disposition of a supposedly nonexisting bearer**, not merely a true descriptive or necessary proposition. Compare an actualist, a serious Meinongian and a realist about abstracta under the same interpretation. If the rival's positive realization is specified without esse, inspect the subject-of-realization commitments rather than declare contradiction by naming. If the real-actualization interpretation justifies existential import directly, preserve that primitive option with its semantic boundary. If it does not, leave the universal target open and pursue consumer-specific coverage.
5. Review and run the applicable proof, binding, comparator, model and offline source-record checks for a future formal implementation. Use its own computed frontier comparison and rerun the exclusion test if reporting an updated count. The 25-route figure refers to the historical analysis.

**Reopening conditions:** a genuinely realized intrinsic property or operation of a bearer lacking real esse in the *same* selected interpretation; a justified alternate meaning of `InAct` used by the universal consumers; or a case where an independently existent abstract bearer cannot be assigned appropriate being without equivocation. The current favorable direct judgment is limited to real actuality of the same bearer, not a denial of meaningful nonexistential predication.

The earlier CI run checked draft head `0d091bf61c06773ff404a65e55c26ac29c1f824e` against base `ba8a75398b009932a33f649ec7abcb2069a3e030`. Its "Report the premise frontier" step computed no change. This evidence is for the earlier documentation revision. The revised checkpoint records conditional comparisons and open bridges pending targeted re-review. [Prior frontier report](https://github.com/moritzbrantner/formal-logos/actions/runs/45323535338/job/138207787680)
