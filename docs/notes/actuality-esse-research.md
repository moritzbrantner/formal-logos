# Research checkpoint: actuality entails being in esse

**Repository:** `moritzbrantner/formal-logos`  
**Date:** 2026-11-24  
**Target:** `7067553d-cad9-5d79-b6b2-912e35051530`, `ActualityOnlyInsofarAsBeingReading`  
**Rival:** `630273f8-b7f8-5b6a-895f-5d2ff23e84cc`, `ActualityWithoutBeingReading`  
**Status:** owner-authorized draft documentation checkpoint; structural tests executed; no new registered result, independent semantic challenge, or computed frontier change.  
**Evidence:** GitHub main read-only inspection; search excerpts at `cae86aa7c092ca2d4276b0f8cfb29e3054d21533`; the shared-route count refers to the historical `fd78b77e6` analysis. Goodness PRD checkpoint published separately in #1917.

## 1. Question and result

Does a genuinely actual perfection of a bearer entail that the same bearer has being in esse? Which weaker commitments actually suffice for the existing God-existence and attribute producers?

Select this because the previous route analysis identified it as indispensable to all 25 tested modal-free root derivations, and its meaning directly constrains both causal perfection and the proposed esse-only goodness route. It is distinct from causal superiority, universal causal transfer, intrinsic possession, composition, and the value bridge investigated in #1917. No new attribution to a source or formal status is asserted.

**Provisional judgment:** a real, intrinsic actuality of an individual cannot be merely a determination of a nonexistent intentional object. The direct principle is strong on the intended *real actualization* interpretation, not on an unrestricted predication interpretation. The exact obstacle is whether every input `InAct` in the downstream dictionaries is calibrated to real actualization of the same bearer. This is a semantic applicability condition, not a new proof that every true sentence entails an existing bearer.

Do not solve this by declaring `InAct x esse` definitionally equal to `∃ r, InAct x r`. That would encode the contested direction. Do not identify every actual or necessary mathematical truth with an actual causal bearer of the perfection. Retain the original premise and its direct-assumption option.

## 2. Reuse and exact senses

The existing declaration in [Question4/Article1.lean](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/Question4/Article1.lean) is:

```lean
def ActualityOnlyInsofarAsBeingReading ... : Prop :=
  ∀ x r, InAct x r → InAct x esse
```

It formalizes only the consequence of ST I q.4 a.1 ad 3, not a whole theory of esse. The existing [PerfectionOfBeing](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Results/Causality/PerfectionOfBeing/Solution.lean) argument uses `ca84f62d` (perfect ↔ actual) and `196e6606` (perfection entails esse). As the current [maximum-definition-fork note](https://github.com/moritzbrantner/formal-logos/blob/main/docs/notes/maximum-definition-fork.md) explains, given the former, the latter is equivalent to the target: do not count their combination as independent corroboration. The proof uses only actuality → perfection, which is questionable if perfection means complete realization rather than possession in a respect.

Existing [elimination attempt](https://github.com/moritzbrantner/formal-logos/blob/main/corpus/attempts/actuality-without-being-elimination.json) (`6b73cc5c`) records that the rival is the negating existential of the target and that elimination from the other tested act/potency premises failed. The old formal countermodel remains valid. The [source attempt](https://github.com/moritzbrantner/formal-logos/blob/main/corpus/attempts/meinong-witness.json) (`8a4cbffd`) explicitly requires reading Meinong and mapping Sosein/Sein to act/esse before historical attribution.

Fix `A(x,r) = InAct x r`, `E(x) = m.ExistsAt w x` on one selected world, and a distinguished `esse`. Distinguish:

- actual intrinsic exemplification, whether of a substantial or accidental actuality;
- real operation (including immanent operation, not necessarily an effect on another);
- real eminent possession or an exercised/unexercised but actual causal power, where independently warranted by the corpus's act-sense bridge;
- intentional or descriptive characterization of an object (`Sosein`), including mathematical and fictional cases;
- existence of a representation, thought, sentence, truthmaker, or event versus existence of its represented object or attributed individual;
- actual existence in the adopted in-re interpretation versus presence as a term or a member of a model's domain.

The formal carrier `Being : Type` is not by itself a guarantee of actual existence. No quantifier rule of Lean makes `E(x)` true for all `x`. The owner-selected [CogitoEsse profile](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Logic/CogitoEsse.lean) treats real existence as act of esse in its intended interpretation; it retains explicit `ExistingInActAt` and does not assert the reverse for arbitrary frames. In particular this is not an Eleatic restriction to causally interacting bodies, nor does it settle the reality of abstracta.

## 3. Source and rival reassessment

### Aquinas

Read ST I q.4 a.1, body and reply 3, in the [public Dominican translation](https://www.newadvent.org/summa/1004.htm). Reply 3's context answers the objection that existence seems imperfect and receptive of all modification. The reply argues that esse is the act by which other determinations are actual, including form itself. This motivates a distinction between a principle considered in abstraction and the principle realized in a bearer. The statement's existing pinned Latin reading is retained; this web reading is not a new pinned-source verification.

### Meinong, §3–4

Read the [German transcription](https://ozekik.github.io/meinong/1904/) of Meinong, *Über Gegenstandstheorie*, 1904, §3 pp. 7–9 and §4 pp. 9–13; the web edition was transcribed from the 1913 collection. Section 3 distinguishes judgment concerning being from judgment concerning what a thing is, and explicitly includes the golden mountain and impossible round square in its independence principle. Section 4 treats the object as independent of affirmative or negative existential judgment and does not identify mental presentation with creation of the object. It therefore would be unfair to dismiss Meinong as merely claiming that minds create fictional objects. See also the [Stanford Encyclopedia discussion, §5.1 and §5.4.3](https://plato.stanford.edu/entries/meinong/) for the later distinction between nuclear and extranuclear determinations.

What this warrants: some determinate characterization does not require existence of its intentional object. It does not by itself show that the nonexistent object has a **real, intrinsic actualization** (e.g. a mountain's actual mass or an actual thermal state). The interpretation bridge `Sosein x r → InAct x r` is still OPEN, and the strongest relevant later Meinongian theory should be read if someone supplies that bridge. Do not attribute the corpus's contradictory existential rival to Meinong without it. Do not claim to have refuted Meinong's object theory. Before any claim is registered, resolve `MEINONG-GEGENSTANDSTHEORIE-3`, materialize a pinned witness, compare its pagination/context, and reassess the existing attempt. The external reading is progress on the source lead, not fulfillment of the pinned-witness gate.

## 4. Positive metaphysical warrant and exact calibration

An imagined golden mountain, an actually golden object and an existing drawing of a golden mountain are not the same bearer of the same property. The drawing can really have pigment; its subject can be characterized as gold without an actual mountain bearing gold. The difference between a realized property and a describable nature must remain even on a generous ontology of intentional objects.

The reason is **subject-involving actualization**: where the actuality is intrinsically the actuality of this bearer, not of an image or of a proposition about it, the bearer is part of what is actualized. A nonexistent object cannot be that actual bearer unless one rejects precisely this subject-involving reading of intrinsic realization. A process or trope ontology may deny a separate enduring substance; in that case the real event or trope can be the relevant bearer, and the conclusion concerns it rather than an inferred substance. This does not prove hylomorphism, the PSR, a sustaining cause, or modal necessity. For a realist about abstract objects, the same question is whether their determinations are actual in the intended sense; if so the application must count their appropriate being, or supply an explicit restriction. Do not exclude abstracta by stipulation in a generic carrier.

This supports an analyst calibration at one selected world:

`ActualizationImportsExistenceAt := ∀ x r, InAct x r → m.ExistsAt w x`.

The ordinary warrant is actual realization of the very bearer; it is not the general semantic thesis that all true positive predications imply an existent object. Conjoin with the existing `ExistingInActAt` (`0436de86`), not with a fresh unrelated definition of existence, to obtain `7067553d`. Conversely the latter plus `ActOfEsseSufficesForExistenceAt` (`546975ef`) implies the analyst calibration:

```lean
-- Proposed proof term; uncompiled, explicit hypotheses only.
fun x r h => hExisting x (hImport x r h)
-- Reverse under the already existing converse calibration:
fun x r h => hSuffices x (hBeing x r h)
```

Under both selected-world calibrations, these are equivalent. This is not a second independent proof if the calibration is accepted merely because the desired actuality-to-esse direction is assumed. It is useful because the same-world real-exemplification question can be assessed without requiring a theory of full perfection, causal power, or divine goodness. Do not infer actuality across worlds from a world-free dictionary.

## 5. Exact downstream uses and residuals

### First mover and agency

In [FirstMoverIsMaximeEns](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Results/Aquinas/SummaTheologiae/FirstMoverIsMaximeEns/Solution.lean), `hBeing f r (hInAct f x r hMoves)` is used once at the given first mover. The narrower sibling `∀ f, IsFirstUnmovedMover MovedIn MovesIn f → InAct f esse` suffices (check the exact existing predicate signature before implementation). It can be supported by an independently warranted actual agent/operation interpretation. It must not be justified by the desired identification with the maximum. The existing `MovesOnlyAsInActReading` hypothesis is not itself an existence predicate. If removing it from a sibling, note that the new sibling has a different bundle and analyze the complete proof use; no new premise closure.

[CauseOfBeingHasBeing.causeOfBeingHasBeingOfAgency](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Results/Case/Catholicism/CauseOfBeingHasBeing/Solution.lean) uses the target at the cause witness. Its same module already offers esse-specific preexistence and cause-has-what-it-gives routes; reuse these rather than duplicate them. The existence-to-esse derivation via mere possibility in [Round2ExistenceAct](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Results/Causality/Round2ExistenceAct/Solution.lean) already bypasses the target at that consumer, but needs its own open premises. Do not support `ExistingInActAt` via the new import rule when the proposed support for the target uses `ExistingInActAt` itself: the dependency must not form an ungrounded cycle.

### Universal perfection and causal goodness

The unchanged predicates in `StageTwo.lean` require **every instantiated respect**, not just acts of the source. `perfectOfMaximum` and `supremelyGoodOfMaximum` in [DirectEsseRootPerfectionGoodness](https://github.com/moritzbrantner/formal-logos/blob/main/TruthCore/Causality/DirectEsseRootPerfectionGoodness.lean) apply `hBeing x r hx` for arbitrary distinct effect `x`, arbitrary respect `r`. `IsPerfect` also includes the source itself, with its own case already trivial. The first mover narrowing is insufficient for these consumers. Even the supposed weakening “every actual respect of every other bearer entails that bearer's esse” is classically equivalent to the original at a supplied maximum (the omitted source already has esse). Filtering the carrier to existent objects would change the conclusion unless the real-exemplification calibration ensures no relevant `InAct` witness is discarded.

Fix n with its actual esse, maximum at esse, the existing `MaximumInBeingCausesAllBeingsReading`, and preexistence and restricted transfer. Then every distinct x with actual esse is covered. For the original full perfection endpoint, the exact remaining pointwise condition is:

```
∀ x r, x ≠ n → InAct x r → (InAct x esse ∨ InAct n r)
```

For `CausesEveryPerfectionOfOthers` the corresponding residual is:

```
∀ x r, x ≠ n → InAct x r → (InAct x esse ∨ CausesIn n x r)
```

**Derivation:** the right disjunct directly supplies the relevant conclusion; the left disjunct licenses `hGenus n hMax x hOther`, followed by `hPreexist` or `hTransfer` as in the original proof. Conversely each old endpoint entails its residual by `Or.inr`. The perfection reverse direction's self-case uses the same explicit identity decision as the original proof. The causal residual does not imply source goodness; still supply `GoodIn n esse` from the separate #1917 investigation. The two residuals can hold together without the global bridge in the encoded dictionary. These are exact conditional scope comparisons, not positive warrant on their own: the price of allowing genuinely non-esse-bearing acts is to justify direct possession and/or causal responsibility for those very acts. In particular, causing every actualized *real* perfection is different from causing all true characterizations of nonexistent objects.

## 6. Executed controls

The accompanying `check_actuality_esse.py` enumerates acts across three bearer roles and three respects and edges from the selected root. Fix a distinct actual esse-bearing effect with an actual quality; retain maximum-to-esse-causation, preexistence and transfer at the root. No unrelated cause table, full modal frame or independent metaphysical interpretation is claimed.

- All 158 retained root-projected backgrounds satisfy both residual equivalences and the equivalence of root-exclusion with global scope. The projected model has a genuinely distinct esse-bearing effect, so coverage of effects is not empty.
- Separations show perfection without causal coverage, causal coverage without perfection, and both together despite failure of the unrestricted target. In each separation the second other candidate has a non-esse act. These are structural surrogates; that candidate's real actuality is precisely the unresolved interpretation.
- All 512 calibrated existence/act assignments satisfy the exact equivalence between selected-world existential import and the target.
- A populated, independently characterized nonexistent object is consistent with closure for the real-actuality table, even though closure fails for the description table. Merging the tables without calibration destroys that property; restoring real actualization and real existence restores closure. Both directions of esse/existence calibration can hold while the mixed, uncalibrated act dictionary violates the target.

See the executed transcript `check-results.txt`. No Lean verification or metaphysical realizability assertion.

## 7. Rival comparison and review boundary

| Rival or alternative | What can be retained | Remaining crux |
|---|---|---|
| Actualist Thomistic act of esse | Descriptions of nonactual objects are meaningful; actual intrinsic realizations are genuinely of their real bearers. | Warrant for calibration across entitative, operational and eminent possession senses. |
| Meinongian object theory | Determinate Sosein independent of being, including objects not actually realized. | Whether its determinations are the same actualities consumed by existential causation. The text considered does not establish that identity. |
| Abstract realist | Actuality may belong to nonphysical bearers; causal inertness does not imply nonbeing. | Whether abstract existence is within the chosen esse interpretation and which causal universal is warranted. |
| Process, trope or bundle ontology | Real events/determinations can be primitive or bearers of actuality; no separately posited substance is required. | Same-bearer calibration for operations and attribution. Cannot be refuted simply by demanding a substance. |
| Strong actuality-without-being rival | If actual realization of a nonexistent bearer is asserted in the same sense, `7067553d` is denied. | Explain what makes it real rather than characterized and how the same bearer participates in existential causation. The formal rival remains satisfiable in the old encoding. |

Self-challenge: scope must not be expanded from causal operation to all intrinsic actualities without warrant; no tautological definition change; no world shift; source wording not forced into an act/esse predicate identification; no assertion that the finite surrogate is a complete Meinongian metaphysics; do not weaken the existing endpoint merely by changing carrier; no claim that an exact residual is an independent argument. Same standards apply to the rival accounts. A separate fresh worker and pinned witness are still required for canonical semantic challenge. No source claim, statement, argument, result or prior assessment changed.

## 8. Integration plan and next discriminating research

1. On a warm checkout run `truth related 7067553d`, `truth dossier`, `truth brief`, `truth novelty` and `truth semantics`, including the relevant consumer context and existing assessment. Current remote source/code inspection is a fallback, not a substitute for these gates.
2. Materialize the existing Meinong candidate and distinguish real actualization from characterization. Preserve the old contradictory rival as a formal alternative; update its historical motivation only after reviewed attribution.
3. Consider a source-local first-mover sibling and a selected-world import sibling. Register only meaningful new support, not repeated equivalent forms. Reuse the existing same-bearer operation and existence results. Keep `7067553d` and all frozen Challenges.
4. Test the hard positive case: **a real, immanent operation or actual disposition of a supposedly nonexisting bearer**, not merely a true descriptive or necessary proposition. Compare an actualist, a serious Meinongian and a realist about abstracta under the same interpretation. If the rival's positive realization is specified without esse, inspect the subject-of-realization commitments rather than declare contradiction by naming. If the real-actualization interpretation justifies existential import directly, preserve that primitive option with its semantic boundary. If it does not, leave the universal target open and pursue consumer-specific coverage.
5. Independently review actual proof and model types, source locators and the final provisional judgment. Verify with `lake build`, `truth check`, bundle audit, bind-check, Comparator, NanoDa, generated import/module and source checks as applicable. Compute `truth frontier-diff` and repeat the same exclusion fixpoint on the actual head; the historical 25-route result does not certify a new route count. Actual registered premise effect of this checkpoint: none. No formal corpus or library change in this documentation checkpoint.

**Reopening conditions:** a genuinely realized intrinsic property or operation of a bearer lacking real esse in the *same* selected interpretation; a justified alternate meaning of `InAct` used by the universal consumers; or a case where an independently existent abstract bearer cannot be assigned appropriate being without equivocation. The current favorable direct judgment is limited to real actuality of the same bearer, not a denial of meaningful nonexistential predication.

**Publication disposition:** This note is a draft research checkpoint, not a certified integration. The companion scratch proof and structural tests were delivered locally; their reported results are retained above, not represented as new Lean verification. No existing assessment is superseded until the independent semantic challenge and required checks are complete.
