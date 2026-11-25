# Actual inquiry and its necessary presuppositions (#930, #932, #1007)

Proposed bounded research continuation, 2026-11-25. Base `bff18fce135d73ffe2e00933a56decdb2a1c89af`. Attribution deferred; no source claims, new definitions or floor markings. Independent challenge and local semantic/verification preflight pending. This note owns the actual-episode application and synthesis, not the psychological or conventional grounding investigations in #1990/#1991 or the rival intake in #1989.

## Starting point and scope

An inquiry token can be actual without achieving its intended epistemic end. Separate occurrence of an intelligible question, truth-directed undertaking, correctness of an answer, actual grasp of grounds, warrant to accept, and preference-independent force. No factivity follows from mere assertion; no reason to believe follows just from a reason to investigate. The proposed route is from an actual accessible truth test, not from an abstract agent stipulated to be rational.

Reuse [the existing retorsion mapping](orphan-graft-map.md#6-retorsion-graft-audit-1926-1963-1007-1008), [epistemic underminers](epistemic-underminer-boundaries.md) and [reasons preconditions](epistemic-reasons-preconditions.md). F1 (`c425f0c5-6c3f-5115-ba04-3e61bd049e3b`) is case-predicate noncontradiction, not every logical rule or a theory of logical truthmakers. F6 (`f56b2ee7-c69e-5e3b-85b0-e671d907ba58`) says some agent has an epistemic reason to believe some content; it is not the claim that everyone must believe what the evidence supports. Both retain their legacy floor markings and stated limitations.

## Initial witness: a checkable inquiry

The explicit research input names seven distinct issue/PR labels: 930, 932, 1007, 1987, 1989, 1990, 1991. Consider the determinate question whether that displayed collection contains an odd number of distinct labels. Pair 930 with 932, 1007 with 1987, and 1989 with 1990; 1991 remains. That is a concrete proposed proof about the specified collection, not a claim about how many issues exist in the repository or the mental state of its owner. Reading the record and checking exhaustive coverage, disjointness and the residue can provide a local reason for the odd answer under the ordinary accuracy-directed interpretation. Mere display or software execution does not establish a person's uptake. The three-pair report alone would not distinguish six items from seven.

Existing routes: `146b502b` excludes universal reason denial relative to F6; `ec80b13d` shows only self-undermining without F6. `b3ddb7c4` reaches F6 under warranted acceptance and the two evidence calibrations; `decf920c` projects the same belief-specific concession through reverse presentation. Neither should be cited as an unconditional proof of actual uptake. `b50727e1` uses F6 plus selected-world reason-bearer presence and the existing existence-in-act contract for concrete population `56f68b40`, a premise of direct-esse argument `72391d4d`. The last two bridges are not supplied by mere inquiry.

Next: inspect exact existing semantics and use this concrete episode for scoped denial tests, a finite comparison and candidate closure; document the difference between evidence available to a reader and observed justified assent.


## Actual tally, contrast cases, and what the observation warrants

The selected list was actually inspected and the following calculations actually executed in Python. The labels are the research input, not a hypothetical observed list in a stipulated agent's mental state. The distinctness, pairing, complete coverage, and remainder checks passed. The proof is also transparent without relying on the interpreter: three disjoint pairs and one leftover make seven. Fix the meaning of *odd*, the members of the displayed collection, and the question of its cardinality. This truth is not changed by wishing for an even count. The supplied material remains publicly checkable; whether a particular subject attends to and understands it is a distinct application question.

The earlier [belief-witness test](epistemic-reasons-preconditions.md#which-consideration-gives-a-reason-to-believe-this-content-1007-2026-11-25) compared hypothetical reports about parity. This continuation supplies the complete input and checked residue. It also tests a further content that the earlier suspension control expressly left outside its domain: the narrower fact supported by an inconclusive report. Let the finite comparison domain contain the eight prefixes of the displayed list (lengths 0 through 7). Let P mean the report has three complete pairs and one residue, Q mean the count is odd, C mean the report has three complete pairs, and M mean its cardinality is six or seven.

| Evidence/conclusion | Result | Concrete witness or reason |
| --- | --- | --- |
| P ⇒ Q | valid | exhaustive pairing; the only P state has length seven |
| Q ⇒ P | invalid | the length-one prefix is odd but lacks three pairs |
| C ⇒ Q | invalid | length-six prefix has three pairs and even parity |
| C ⇒ not Q | invalid | actual length-seven list has three pairs and odd parity |
| C ⇒ M | valid | division with remainder by two; both compatible lengths satisfy M |

All five premises are satisfiable and all conclusions are non-tautological in the chosen domain. The valid P ⇒ Q is not identity or a vacuous implication; its converse fails. It is informative in the sense of a distinct, strictly weaker consequence, not ampliative beyond the information of its premise. C can therefore give the accuracy-directed investigator a reason for M even when it gives no deductive resolution of Q. The pair report does not by itself warrant the assertion that *probabilities* are equal: that needs the likelihood conditions in #1980. The diagnostic claim that C fails to entail either parity answer has its own positive basis: the two explicitly exhibited states. It is not the same claim as Q, and does not turn withholding on Q into believing Q. A blanket suspension or someone who lacks the report is not shown to have a belief reason by these facts.

This gives an actual-data route to a belief reason even for an investigator who rationally withholds on the main question. It weakens the application demand from successful answer to actual access to a supporting, non-undercut basis for *some* content. Use the same subject and report; change the belief target explicitly. A local warrant for the epistemic merit of the inference is direct: a complete check isolates a real difference between the two possible conclusions, while no amount of liking the even answer alters the indicated residue. The merit and evidence-relative correctness are not the further claim of end-independent force. The aim-relative account gives an actual accuracy-seeking subject a reason for M from the report, or Q from the full tally. A global reason nihilist can admit that the observation favors the answer in a purely descriptive/informational sense while denying normative favoring. That denial is opposed by the direct judgment that a good check counts for belief, not refuted by a bare truth table.

### Reproduction (executed; finite control, not a Lean result)

```python
labels = (930, 932, 1007, 1987, 1989, 1990, 1991)
assert len(set(labels)) == len(labels)
pairs = tuple(zip(labels[::2], labels[1::2]))
residue = labels[2*len(pairs):]
assert tuple(x for pair in pairs for x in pair) + residue == labels
assert (len(pairs), len(residue)) == (3, 1)
worlds = tuple(labels[:n] for n in range(len(labels) + 1))
report = lambda w: divmod(len(w), 2)
coarse = lambda w: report(w)[0]
odd = lambda w: report(w)[1] == 1
full = lambda w: report(w) == (3, 1)
pair3 = lambda w: coarse(w) == 3
meta = lambda w: len(w) in (6, 7)
fiber = tuple(w for w in worlds if pair3(w))
assert tuple(map(len, fiber)) == (6, 7)
assert set(map(odd, fiber)) == {False, True}
for p, q, expected in [
    (full, odd, True), (odd, full, False), (pair3, odd, False),
    (pair3, lambda w: not odd(w), False), (pair3, meta, True),
]:
    assert any(p(w) for w in worlds) and any(not q(w) for w in worlds)
    assert all(not p(w) or q(w) for w in worlds) == expected

def invariant(project, holds):
    return all(project(s) != project(t) or holds(s) == holds(t)
               for s in worlds for t in worlds)

assert not invariant(coarse, odd)
assert invariant(report, odd)
assert invariant(coarse, meta)
for force in ('aim-relative', 'independent', 'none'):
    merits = {d: all(odd(w) for w in worlds if report(w) == report(labels))
              for d in ('accuracy', 'comfort')}
    assigned = {d: merits[d] and (force == 'independent' or
                (force == 'aim-relative' and d == 'accuracy')) for d in merits}
    assert all(merits.values())
    assert tuple(assigned.values()) == {
        'aim-relative': (True, False), 'independent': (True, True),
        'none': (False, False)
    }[force]
print(pairs, residue, tuple(map(len, fiber)))
```

The finite prefixes are combinatorial control states, not a claim that these are all metaphysically possible worlds. Force is assigned, not measured. Merit does not vary with preference *because the content, observation, consequence relation and actual evidence are held fixed*. A report-channel fault, a changing subject matter or altered meanings would require a different analysis. This is a test of exact information and omission of normative bridges, not a complete account of cognitive realization, normative authority or logical grounding. Both force-positive profiles preserve the local epistemic result. The force-free profile has the same informational structure but omits force, and cannot itself settle whether that interpretation is philosophically adequate.

Reuse `TruthCore.Logic.ReflectiveCoherence.Entails` with fixed interpreted worlds and `TruthCore.Results.Logic.CorrectionCriterion.characterization` (`0590fe21`): P/Q and C/M entailments are fiber tests, while odd changes over the coarse fiber. The latter theorem says `AdmitsCriterion observe Correct ↔ FiberInvariant observe Correct`, not that a criterion is known, accessible, or normatively authoritative. Here an explicit finite algorithm exists as an additional concrete fact. Existing `e03147fa` proves identity for a supplied content; P ⇒ Q also addresses a narrower denial of nonidentity semantic consequence, conditional on the stated interpretation, without claiming a new registered result.

## Necessary presuppositions: candidate-by-candidate assessment

Use three distinct tests: (A) falsity of a universal denial from an actual same-domain witness; (B) incompatibility of an asserted or factively defended denial with the performance conditions it claims; (C) absence of reason to adopt the view on its own terms. C alone does not establish falsity. A truth-directed *attempt* may be mistaken, incompetent or interrupted; criteria for successful, warranted or communicative achievement are not all necessary for every attempt. The following direct judgments are proposed for independent challenge.

| Candidate P and strongest positive warrant | Denial and substantive restriction | Weakest retained claim and corpus use |
| --- | --- | --- |
| Actual inquiry/occurrence: an actual asking, checking or judging episode supplies its own occurrence. | The accurate performed denial of all such episodes is impossible in the same occurrence predicate; unperformed or false denial survives. A static-reality view need not deny episodes. | Some episode occurs in the selected interpretation; `bfda68fd`, `cc1a4204` (cognitive realization still required for a textual assertion). No temporal succession, substance or ontic grounding inferred. |
| Truth: the displayed collection has odd cardinality, demonstrable by exhaustive pairing; the even answer about that very collection is false. | Global no truth conflicts with the true witness when truth captures this content. Presenting a denial as true does not make it true. Deflationism, semantic indexation, and local truth relativism may accept the fixed content. | A true content and a failed alternative in the specified truth interpretation, not correspondence ontology or truth independent of all cognition. See TruthPilot and the explicit capture discussion in [orphan graft §6.5](orphan-graft-map.md#65-one-proof-three-applications). |
| Meaning/intelligibility: the parity question and its answer have distinguishable application conditions; the two report cases can be discriminated. | A genuinely meaningful assertion of no meaningful content is a counterinstance. Strings, imitation, ambiguous attempts or questions not asserting an answer evade the assertion antecedent. Rich pragmatic or conventional semantics can preserve local meaning. | At least one meaningful, sufficiently determinate content for this actual interpreted task. `bec15d81` requires actual assertion and cognitive meaning; successful communication of a question does not require already believing its answer. No Platonic propositions or universal intelligibility. |
| Logical validity: P ⇒ Q is valid in the fixed profile, with P nonempty and Q non-tautological; C ⇒ Q fails on the concrete length-six alternative. | A rationally defended denial of all validity must either renounce the validity of its own inference or conflict with a valid witness when it belongs to its scope. An invalid argument may have a true conclusion. Identity-exempt denial still encounters P ⇒ Q; a restriction to ampliative inferences is not tested by this deduction. | Some nonidentity semantic consequence and a counterexample to a different inference in a specified nontrivial frame. Existing `e03147fa`, `b203c461`, #1084/#1086; #1990 and #1991 compare grounding. No global selection of classical logic or unrestricted validity across frameworks. |
| F1, noncontradiction: for the same fixed collection and parity predicate, a correct verdict cannot both affirm and deny it in the same sense, under Lean negation. | Two people accepting incompatible answers is not a contradiction in the world; a dialetheic negation need not be Lean's negation. | F1 exactly `CasePredicateNonContradiction`, and its scope-preserving instances. `a7ecf1fe` proves the encoded denial impossible; retain D-L when interpreting an external logic. No assumption that contradictory beliefs or paraconsistent reasoning cannot occur. |
| Correction: checking complete coverage and a residue detects the invalid jump from C to Q; the same method can test an erroneous parity answer. | A denial of any correctness distinction contradicts these semantic verdicts if it includes them. A failed or undiscovered correction is possible; simply adopting a new rule or changing a belief does not constitute factual correction. | At least a content-indexed distinction between correct and incorrect answers/inferences and a concrete discriminating method in this profile. CorrectionCriterion.characterization and `TranscendentalPractice.InquiryAccessBoundary`; no universal epistemic access or assertion that actual belief revision occurred. |
| Judgment: an understood proof permits a subject to endorse Q on the basis of the check; when checking M the subject need not settle Q. | The denial of all beliefs is inconsistent with sincere belief in that denial, not with quoting it, asking a question, or suspending. The current text and computation do not observe anyone's assent. | Conditional actual judgment/belief witness from a sincere assertion (`2f466ae8`); separate performance evidence needed. Meaningful inquiry as a whole is weaker than belief in its answer. |
| Epistemic reason (thin F6): an available check favoring a particular true answer, or the narrower M under coarse data, directly warrants a local belief-directed reason judgment; correctness does not require assent. | F6 contradicts global reasonlessness in the very relation (`146b502b`). Reasonlessness implies no reason to believe itself (`ec80b13d`), not falsity without F6. Purely descriptive information, reason to check, or reason to suspend are not sufficient on their own. Goal-relative force can concede the local reason. | Some agent has some epistemic reason to believe some content, not necessarily Q or the denial. Direct case-specific warrant, and the legacy floor basis; actual access and the support-to-reason reading remain explicit. No universal obligation or guaranteed truth of reason-supported beliefs. |
| Rational justification: understanding and properly using a transparent, non-undercut proof of a specified conclusion can provide warrant. Mere correctness of the printed answer is insufficient. | No justification can be self-undermining if offered *as* justified; the conjunction of actual warrant and universal denial contradicts. Skeptical suspension or correct guessing is compatible with a lack of warrant. Reliabilist warrant need not be reflective articulation. | A local sufficient justification is a defensible candidate when actual uptake, reliability/defeat conditions and relevant warrant standard are established. Reuse `1db47fd9` and `b3ddb7c4`; the first already takes reason uptake. No new actual warrant certified by the transcript. |
| Preference-independent correctness/standards: with the report, its subject matter and truth criterion fixed, the answer and P ⇒ Q are not changed by preference labels. | Acceptance/frequency or comfort alone cannot classify the fixed answer across the coarse evidence fiber; changing meanings changes the comparison. Sophisticated functional/conventional accounts can retain the same content-relative standard. | Independence of the selected truth/validity test from a change of mere desire *holding the content and evidence fixed*. This is not ontological independence of a standard from all minds, nor `BeliefAnswerability`. #1990/#1991 retain the grounding question. |
| Preference-independent epistemic force: one may directly judge that getting a fact right is a reason for an indifferent subject, not only a means to their chosen aim. | The goal-relative account preserves content, evidence, actual inquiry and the actual reason while varying force at an indifferent preference. Constitutive-aim accounts may restrict the preference domain, and categorical duty is a further thesis. | The local positive authority judgment remains prima facie; `ActualForceConcession` plus `BeliefAnswerability` yields the stronger conclusion under its stated assumptions. No new argument that the latter holds for indifferent agents; `2ca463c2` remains distinct from F6. |

The truth and inference claims have local direct evidence in the selected interpretation. The existential occurrence/meaning claims use actual-witness application and must not be broadened to unobserved agents or domains. Actual justification and thought-as-bearer claims need more than this check. Preference-independent correctness is a genuine distinction from preference-independent force; it is not a complete account of objective normative authority.

## Consequences from the existing floor: exact scope and non-entailments

The existing kernel-level definitions are:
`CasePredicateNonContradiction` quantifies over `Being : Sort u`, `Respect : Sort v`, predicates and arguments, with conclusion `¬ (P x r ∧ ¬ P x r)`.
`ThereAreEpistemicReasons R := ∃ a p, R a p`.
Use the existing reason bearer and content from the latter witness. The following are constructive consequences, not new registered graph edges; elementary existential projections are not counted as substantive new proof discoveries:

- Some reason bearer and some belief content inhabit the corresponding encoded domains. In particular `Nonempty Agent` and `Nonempty Content`; each fails for an empty carrier. No ontic presence follows from type inhabitation alone.
- There exists a subject not reasonless about every content and a content not reasonless for every subject. Both witnesses come from the same pair. This does not imply that any other agent has a reason for the content, that every agent has a reason, or that there are two numerically distinct agents.
- Universal no epistemic reasons is false in this relation (existing `146b502b`). If a denial-content is true iff that universal denial holds (the existing `ExpressesNihilism`), its truth is excluded by F6. If the denial merely fails to have a reason, it does not follow that it is false; the truth capture and global scope matter.
- For that very pair, the reason attribution holds and its Lean negation cannot also hold. F1 permits the case-predicate instance with agent as first carrier and content as second; treating the predicate as one of the metaphysical case predicates requires the intended interpretation. The local contradiction already follows by Lean negation from the positive reason witness, so adding F1 supplies no extra proof strength here.
- F6 neither decides the truth of p nor requires actual belief or warrant; the reason may be pro tanto or defeated by stronger contrary reasons. It supplies no reason for the denial itself, no reason to believe every consequence, and no general truth-predicate interpretation.
- An actual truth-directed episode that supplies no belief reason (merely wishing, asking a question without information, or suspending on the target) does not contradict F6 as long as some other content/subject has a reason. Nor does actual occurrence imply any F6 witness under a reasonless interpretation without a substantive reason-attribution judgment.

Illustrative Lean projections on the existing declarations; **proposed only**, not elaborated or registered in this connector session. They identify the exact weak content of the claimed deductions.

```lean
import TruthCore.Logic.EpistemicReasons
import TruthCore.Logic.CaseNonContradiction
open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.CaseNonContradiction
universe u v
example {A : Sort u} {C : Sort v} {R : A → C → Prop}
    (h : ThereAreEpistemicReasons R) :
    Nonempty A ∧ Nonempty C ∧
    (∃ a, ¬ ∀ p, ¬ R a p) ∧ (∃ p, ¬ ∀ a, ¬ R a p) := by
  obtain ⟨a, p, hr⟩ := h
  exact ⟨⟨a⟩, ⟨p⟩, ⟨a, fun hn => hn p hr⟩,
    ⟨p, fun hn => hn a hr⟩⟩

example {A : Sort u} {C : Sort v} {R : A → C → Prop}
    {Holds : C → Prop} {n : C}
    (h : ThereAreEpistemicReasons R)
    (hexpr : ExpressesNihilism R Holds n) : ¬ Holds n := by
  obtain ⟨a, p, hr⟩ := h
  exact fun ht => (hexpr.mp ht) a p hr

example {A : Sort u} {C : Sort v} {R : A → C → Prop}
    (h : ThereAreEpistemicReasons R)
    (nc : CasePredicateNonContradiction.{u,v}) :
    ∃ a p, R a p ∧ ¬ (R a p ∧ ¬ R a p) := by
  obtain ⟨a, p, hr⟩ := h
  exact ⟨a, p, hr, nc A C R a p⟩
```

The most promising application is not one of these elementary projections. It uses the actual parity/disjunction proof and `SurvivingBasisGivesReason` at an observed accessible basis. At a fixed subject a, basis b and content q (Q for the complete report, M for the coarse report), the existing theorem needs `f.supports a b q` and `¬ f.undercuts a b` and the reason-calibration. The latter's registered form is universal over the frame; for this single proposed application only the local implication is needed. Do not generalize the local judgment to that universal. If the local attribution is granted, F6 follows immediately; treating it as a proof of the calibration would be circular. Positive warrant for the attribution comes from the transparent information distinction and the ordinary epistemic sense of 'counts in favor', not the existential introduction itself.

## Downstream connections and proposed assessment

- F1 supplies the existing adopted-potency nonoverlap argument (`ADOPTED-POTENCY-NONOVERLAP`), but neither valid inference nor the local parity predicate establishes act/potency of a concrete being, causal priority or pure actuality. Preserve that distinct interpretation and existing route.
- F6 supplies the reason-bearer route `b50727e1` to `56f68b40` **only** with selected-world presence `ada25623` and esse contract `0436de86`. The direct-esse argument `72391d4d` still needs its other premises. An episode can also feed the existing Cogito route via `cc1a4204` and the representation bridge; see #1979/#1980. No new connection is asserted on the graph.
- The proof's available factual content and its possible grasp distinguish actual intelligibility from mere verbal persuasion. It is relevant to the intrinsic-intellect and causal-perfection inquiry (#1855/#1866), but no transfer from created understanding to intrinsic understanding in its source follows without establishing actual understanding, its status as a positive perfection, and the causal adequacy/perfection bridge for the same sense. An impersonal foundation may realize or produce truth-sensitive creatures; this test does not defeat it.
- The epistemic reason/ontic sufficient reason distinction (#756) remains: grounds that favor a belief need not explain why the fact or its subject exists. No PSR, necessary being, universal obligation or personal ultimate source follows from these presuppositions alone.

Proposed provisional judgment: the directly inspectable episode strongly supports a determinate truth, a nontrivial valid inference and a counterexample to a nearby invalid inference; evidence-relative correctness persists through the mere change of a preference. The actual-evidence route to F6 is stronger than the old suspension-only comparison in that it supplies a *different true belief content* supported by the incomplete report. It offers an ordinary positive reason judgment without requiring that the investigator already knows or believes the answer. The validity/informational contrast is conclusive in the specified finite interpretation; uptake and normative attribution are not externally observed, and neither goal-relative force nor psychologically realized or constrained conventional standards are excluded. An account that denies all reasons yet presents a merely causal or informational explanation of inquiry remains epistemically self-undermining when it seeks rational adoption, but no fresh unconditional philosophical refutation is claimed beyond the existing floor-relative incompatibility.

## Handoff and validation

No new Lean module, corpus statement, argument, result, relation, definition, attribution or floor marking is registered. No premise change intended; the actual computed frontier comparison is pending. The Python evidence checks above passed locally; exact floor declarations, the relevant merged attempts, #1987's scoped audit and #1989/#1990/#1991 draft summaries were inspected via the GitHub connector. The repository clone failed to resolve github.com from the container; Lean, Lake, Cargo, the local installed toolchain and a fresh independent semantic challenge worker are unavailable. The linked repository-local reuse skill and canonical work-loop were inspected remotely. This is an unreviewed research checkpoint, not a mechanically verified new theorem or a completed research program.

Next concrete test: ask the selected investigator (not a stipulation that every rational agent succeeds) to reconstruct the two compatible lengths from the coarse report, then distinguish the exhaustive full tally from the invalid inference. Record whether the subject understood the basis, which conclusion it supported, and whether an actual reason was conceded; assent to parity is not necessary. If the subject grants the evidence-relative judgment but disputes genuine force, test the explicit local favoring/Reason calibration, not another generic retorsion. The separate indifferent-preference transfer remains the #930 normative relevance question. No further categorical authority conclusion should be registered from the present controls.

On a prepared clone, run the required related/dossier/brief/semantics/novelty and issue briefs before registration. In particular:

```sh
python3 scripts/worker_env.py --check
cargo build --locked --release -p truth
for id in c425f0c5 f56b2ee7 6b4e3331 2ca463c2 ada25623 0436de86; do
  target/release/truth related "$id"
  target/release/truth dossier "$id"
  target/release/truth brief "$id"
  target/release/truth semantics "$id"
done
target/release/truth novelty "coarse evidence supports a different determinate belief content while parity remains unresolved"
target/release/truth context b50727e1
target/release/truth context 146b502b
target/release/truth semantics --premise f56b2ee7 --premise ada25623 --premise 0436de86 --conclusion 56f68b40
target/release/truth check
python3 scripts/bundle_audit.py
target/release/truth attribution-check --base "$(git merge-base HEAD origin/main)"
target/release/truth frontier-diff --base "$(git merge-base HEAD origin/main)"
target/release/truth frontier-diff --base "$(git merge-base HEAD origin/main)" --frontier-root 8626f8a5
```

Use an isolated preview/local Lean run for the proposed projections if useful; if a substantive new argument is justified, freeze Challenge, implement Solution, and apply binding, Comparator and NanoDa before registering it. Independent review must challenge the final actual episode interpretation, the proposed merit-to-reason judgment, the fixed-content scope, and the downstream witness alignment. Self-sweep: no historical claims; no truth from assertion alone; controls have explicit carriers and force assignments; no normative strength from preference invariance; no local-to-universal upgrade; no root discharge claimed. Keep #930/#932/#1007 open and #1995 draft.

[Research attempt and scoped unreviewed assessment](../../corpus/attempts/342199e6-8ad7-4835-873e-5bdab8fb3b82.json).


## Continuation: inquiry supplies a truth about its own actual occurrence

2026-11-25, second investigation from `4947b39822c77d1d08e5eaf85a08bcb2f1a62223`. This is a narrower epistemic use of the Cogito, not a competing bearer/actuality research branch. It addresses F6 and the global undercutter, using the existing actual-thought proposition `e81971f1-601c-57f5-be2d-c4b0624d0cad`.

The previous tally supports a narrower conclusion even when it cannot resolve its external target. Can a conscious inquiry itself provide a basis that survives doubt about *every external target*, including deceptive reports and a fabricated past? Unlike the tally application, the proposed evidential ground is the currently apprehended questioning, not the accuracy of a record or memory of earlier successful reasoning.

### 1. The precise challenge and direct warrant

Consider actually attending to one's present conscious questioning of some proposition p, without trying to settle p. The proposed positive judgment is **some thought is occurring**, not "p is true", "I am a substantial enduring self", or "my faculties are generally reliable". In this case the very occurrence which is attended to supplies the fact whose absence is denied. There is no prior inference from a statistically reliable indicator of thought to an unobserved thought.

The relevant distinction is between:

- **Occurrence presented in the activity itself:** genuine present conscious questioning, apprehended as such. The subject need not remember an earlier episode. Being mistaken about the subject matter of the questioning does not turn the questioning into a nonoccurrence.
- **A representation or report of occurrence:** a transcript, memory, belief, computational verdict, or other sign that such an episode is occurring. Its truth conditions need not be satisfied by its production. Such a report can be generated in the absence of the relevant conscious episode.

The first description takes actual conscious acquaintance as a specific application input, not as a conclusion from behavior, nor as a definition of all representations. It is available in first-person inquiry; the present session cannot inspect the owner's private experience or attest a machine's phenomenology. A bare sensation that is not a thought supports the weaker occurrence claim, not `ThoughtOccurs`. Use the cognitive questioning case to apply the latter. A genuine appearance of something as conscious can be an occurrence without settling its classification as a particular kind of thought.

The exact positive warrant for `ThoughtOccurs` is therefore indexical and noninferential at its core: attend to the episode rather than infer it from a source history. The simple existential inference then preserves that very witness. This is evidence of **actual** occurrence, not merely the logical theorem that if an episode occurs, it occurs. The availability of that application is the remaining first-person premise. Compare [the prior Cogito premise assessment](cogito-esse-1113.md) (`95c5138f`, `1722a80f`, `e81971f1`), [first-person access in the receptivity study](contingency-receptivity-c2.md), and the older [historical counterfeit boundary](ultimate-explanation-and-knowledge-737.md). The new comparison concerns the effect of representational defeat on a different use of a current episode as evidence; it does not reprove the existing performed-denial result or turn a contingent actual occurrence into necessary existence.

### 2. A skeptical alternative cannot preserve every kind of evidence

Let W be a comparison domain, e a possible episode witness, Occurs(w,e) the existing thought-occurrence reading at a supplied index, and Seen(w,e) the proposed *factive first-person acquaintance with that episode as a present thought*. This is a proposed local interpretation of evidence, not an independently registered predicate. Its two application conditions are:

1. At the actual index w0, some episode is so apprehended: ∃e, Seen(w0,e).
2. Throughout the comparison, Seen(w,e) implies Occurs(w,e) for that witness.

Write A(w) for ∃e, Seen(w,e), and Q(w) for ∃e, Occurs(w,e). A counterfactual need preserve the evidence-kind A, not the numerical identity of the particular episode across worlds. Then A entails Q everywhere in the specified comparison, and Q obtains at w0. A counterexample to Q cannot be in A's evidence cell. The counterpart can preserve A while making the original external proposition p false. A report-only comparison can preserve the text and make Q false, because that comparison lacks the factive evidence bridge. If the skeptic allows that very case, the question is whether the selected evidence is merely a report or an actually apprehended episode.

This is a same-domain, nontrivial restriction: there are states with no thought at all and states with thought but no questioning of p. It is not the vacuous assertion that all worlds have the target occurrence. The distinction also does not rely on how probable the deceptive alternative is.

**Proposed Lean check**, using the existing `CogitoSubject.ThoughtOccurs` rather than adding an ontology or a proof registration:

```lean
import TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoSubject

example {W E : Type} (Occurs Seen : W → E → Prop) (w0 : W)
    (actualAccess : ∃ e, Seen w0 e)
    (accessFactive : ∀ w e, Seen w e → Occurs w e) :
    ThoughtOccurs (Occurs w0) ∧
      ¬ ∃ w, (∃ e, Seen w e) ∧ ¬ ThoughtOccurs (Occurs w) := by
  have witness (w : W) : (∃ e, Seen w e) → ThoughtOccurs (Occurs w) := by
    rintro ⟨e, he⟩
    exact ⟨e, accessFactive w e he⟩
  refine ⟨witness w0 actualAccess, ?_⟩
  rintro ⟨w, ha, hn⟩
  exact hn (witness w ha)
```

The proof is conditional on explicitly factive access; it would be a simple witness projection and not a substantive new theorem by itself. The philosophical work is the local ground interpretation and discriminating scope of the skeptical defeater. The result says no comparison state with A lacks Q, not that no conceivable state lacks Q. It does not infer accessibility, knowledge, actuality of thought or modal necessity from a Lean carrier. F1 excludes Q and its same-sense Lean negation at a fixed index; no general dialectical defeat of nonclassical logics is involved.

### 3. Why one defeated representation need not destroy all epistemic support

Reuse the exact `ReliabilityFrame` in `TruthCore/Logic/GlobalThesisBoundaries.lean` (definition `26cbf25d`). It indexes undercutters by subject and **basis**, not by subject, basis and target. Hence care is needed in translating a content-specific defeat. One episode can give two grounds, distinguished by their evidential roles:

- bExternal: use the episode's representation as evidence for an external proposition p.
- bOccurrence: use the present apprehension of the episode itself as evidence for Q.

These need not be independent physical sources, two episodes, or even two observations. A single experience may ground both. Their distinctness in the frame represents the distinct epistemic grounds, not a guarantee of independent epistemic warrant. If Basis is instead defined as the raw episode token, the old frame has no content-specific undercut relation; the proposed separation is not legitimate under that reading without an interpretation bridge. The two-use interpretation is justified here by different dependencies: bExternal needs a connection from representational content to subject matter; bOccurrence needs the episode's present occurrence and its apprehension.

The familiar defeater theorem `bab6bc66` (`undercutSoleBasisPrecludesWarrant`) requires sole-basis dependence and warrant-needs-undefeated-support. The #1615 audited defeat result `8f0f44e5` additionally requires its actual process audit and specified policy. Neither says that a defect in an external representation defeats every use of the episode. A counterfeiting scenario can falsify p while satisfying both the occurrence and the acquaintance; it cannot by itself be a counterexample to that acquaintance's bearing on Q. An undercutting objection that challenges the very presence or identification of the acquaintance is different from a representational rebutter and remains a live test.

Under the local reason calibration of `6b4e3331`, an available non-undercut bOccurrence gives Reason(a,Q) and F6, even if the first basis is defeated and every external answer remains suspended. Thus the epistemic dispute moves from general reliability of a faculty to **whether this present, directly apprehended occurrence counts for the belief that some thought occurs**. This attribution is a substantive local evaluative judgment, not a definition of an episode or a consequence of correctness alone. `b3ddb7c4`'s warranted-acceptance route is not needed when using the direct surviving basis; no prior belief or knowledge of Q is required. The exact inference, proposed on existing declarations:

```lean
import TruthCore.Logic.EpistemicReasonBearer
open TruthCore.Logic.GlobalThesisBoundaries
open TruthCore.Logic.EpistemicReasonBearer
open TruthCore.Logic.EpistemicReasons

example (f : ReliabilityFrame) (R : f.Agent → f.Content → Prop)
    (a : f.Agent) (bExternal bOccurrence : f.Basis) (q : f.Content)
    (bad : f.undercuts a bExternal)
    (good : f.supports a bOccurrence q)
    (retained : ¬ f.undercuts a bOccurrence)
    (counts : SurvivingBasisGivesReason f R) :
    bExternal ≠ bOccurrence ∧ UndefeatedSupport f a q ∧
      R a q ∧ ThereAreEpistemicReasons R := by
  have hr := counts a bOccurrence q good retained
  refine ⟨?_, ⟨bOccurrence, good, retained⟩, hr, ⟨a, q, hr⟩⟩
  intro heq
  exact retained (heq ▸ bad)
```

The distinctness is a consequence *inside that interpretation*, because one basis is undercut and the other is not. It does not prove actual separation, availability or retention, and does not assume that an independently justified warrant for the audit is supplied. The formal witness projection is only an unelaborated application sketch, not a new registered result. In particular, do not infer survival of bOccurrence from the fact that bExternal was defeated.

### 4. Executed finite comparisons

The preceding checkpoint's Python reproduction was rerun successfully. The new reproduction below enumerates twelve states and every subset containing the selected actual state (2048 restrictions), of which 1024 admit the specified deceptive comparison state. It also checks eight explicit reason/defeat structural profiles. The finite states represent a fixed comparison interpretation, not exhaustive metaphysical possibilities or an actual report of someone's inner life.

```python
from itertools import product
# Episode-kind, external truth, public marker of inquiry.
W = tuple(product(('none', 'asks-p', 'other-thought'),
                  (False, True), (False, True)))
w0 = ('asks-p', True, True)
counterfeit = ('asks-p', False, True)
report_only = ('none', True, True)
A = lambda w: w[0] == 'asks-p'
Q = lambda w: w[0] != 'none'
P = lambda w: w[1]
T = lambda w: w[2]
assert A(w0) and Q(w0) and P(w0) and T(w0)
assert A(counterfeit) and Q(counterfeit) and not P(counterfeit)
assert T(report_only) and not A(report_only) and not Q(report_only)
assert all(not A(w) or Q(w) for w in W)
assert any(Q(w) and not A(w) for w in W)
assert any(not Q(w) for w in W)
other = tuple(w for w in W if w != w0)
count = deceptive = 0
for include in product((False, True), repeat=len(other)):
    H = (w0,) + tuple(w for w,i in zip(other,include) if i)
    F = tuple(w for w in H if A(w))
    assert F and all(Q(w) for w in F)
    assert not any(A(w) and not Q(w) for w in H)
    count += 1
    if counterfeit in H:
        assert any(P(w) for w in F) and any(not P(w) for w in F)
        deceptive += 1
assert (count, deceptive) == (2048, 1024)
assert not all(not T(w) or Q(w) for w in W)

# Distinct uses of a source, not independent source tokens.
B = ('ext', 'occ')
C = ('P', 'Q')
support = {('ext', 'P'), ('occ', 'Q')}
profiles = []
for ext_defeat, occ_defeat in product((False, True), repeat=2):
    defeated = {'ext': ext_defeat, 'occ': occ_defeat}
    survivor = {p for p in C
        if any((b,p) in support and not defeated[b] for b in B)}
    assert ('P' in survivor) == (not ext_defeat)
    assert ('Q' in survivor) == (not occ_defeat)
    for calibrate in (False, True):
        R = survivor if calibrate else set()
        assert bool(R) == (calibrate and bool(survivor))
        if ext_defeat and not occ_defeat and calibrate:
            assert R == {'Q'}
        profiles.append((ext_defeat, occ_defeat, calibrate, tuple(sorted(R))))
assert len(profiles) == 8
```

A encodes actual episode-kind, not an independently tested first-person access mechanism; matching A is a structural surrogate for the factive access profile, which additionally requires actual apprehension in the philosophical reading. A ⇒ Q holds by the explicit classification, not by a numerical experiment proving introspection reliable. The reason profiles assign the support and defeat relations; the calibration-off control empties R deliberately and does not prove no reason in an actual subject. Both undercutters can be set true together; the experiment thus leaves wholesale defeat coherent at this purely structural level. It isolates the *additional* conditions needed to carry the observed external error across to the occurrence ground.

### 5. A sharper fork for universal epistemic skepticism

| Claim or rival | Test | Result |
| --- | --- | --- |
| Every actual evidence basis has an evidence-preserving possible error about its own target | Compare the directly apprehended current thought against Q. | In the factive-access reading, false in the comparison domain: any ¬Q state lacks A. A mere-report reading survives; it must contest the actual-access interpretation. |
| All external appearances, traces and histories may mislead | Preserve A and flip p. | Compatible with Q. It is not a mechanism for falsifying the occurrence conclusion; no general external-world knowledge inferred. |
| All cognitive faculties may be unreliable | Distinguish prediction, representation, inference, and direct presence. | Lack of general predictive reliability does not establish defeat of every particular basis; a broader objection must target the ability to recognize the present episode. |
| There are no epistemic reasons | Apply the local ordinary reason judgment for Q. | If the subject has a reason to believe Q, the universal denial contradicts F6's witness. A reasonless-truth view survives the formal controls without the reason calibration; if it seeks rational adoption it still incurs the existing self-undermining consequence. |
| All metaphysical facts are inaccessible through rational inquiry | Q is about actual thought occurrence, not just a formal truth or a report. | On a scope including this modest ontological fact and on the actual-awareness/warrant reading, the denial encounters a counterinstance. A restriction to unexperienced external entities, ultimate grounds or substantial bearers survives; no necessary-being theorem follows. |
| Preference-independent authority fails | Preserve the occurrence and evidence while varying desire and interest in accuracy. | The evidence's bearing on Q survives; the goal-relative account can still withdraw force for an indifferent subject. This comparison does not establish categorical obligation. |

The important pressure is that a skeptic who admits an actual conscious, directly apprehended inquiry cannot retain the **same evidence** while removing all occurrence of thought. Merely saying "the thought is deceptive" changes the target of the objection from the existence of the act to its content or epistemic adequacy. To deny this local positive reason requires a substantive further theory, for example global defeat of even immediate acquaintance or the claim that only accuracy-dependent instrumental force counts. The latter can grant F6 for actual accuracy-directed inquiry. A report-only account must explain why first-person conscious awareness is absent or nonfactive; the report-only control cannot settle that actual question.

This provides a more direct positive route to thin F6 than requiring a subject to master the external count. It is also a cross-family warrant for the Cogito occurrence input `e81971f1`: its first-person application is directly defensible even under wide external skepticism. The remaining metaphysical steps are still precisely those in #1979/#1980: occurrence-to-representation, bearer and selected-world presence/esse. In particular, neither the factive access hypothesis nor the existence of a propositional content identifies a substantial bearer or demonstrates a pure perfection of intellect in the ultimate ground.

**Proposed judgment and next discriminating test.** The limited epistemic invulnerability of *the occurrence conclusion to representational falsity* is well supported by the same-witness distinction. It is not invulnerability to every undercutter. The stronger judgment that the selected subject actually has a reason for Q is supported prima facie by immediate acquaintance and the direct accuracy distinction, without appealing to past success; its first-person application is not observed in this session. A substantive challenger should provide a concrete account of the remaining local undercutter: can it leave genuine conscious acquaintance intact while defeating epistemic support for bare occurrence, rather than replacing acquaintance with a mere seeming/report of acquaintance? Compare externalist, internalist and nihilist accounts at that exact witness. The next independent test should also distinguish the fact that the episode occurs from the correct classification of that episode as *thought*, retaining the weaker phenomenal occurrence if classification fails. Do not repeat a generic countermodel with all reason predicates empty as if it answered that question. The selected goal-relative force rival remains viable, and the stronger end-independent relevance problem remains open.

No changes to corpus closure, proof registrations or attribution. Local DNS failure and absent Lean/Lake/Cargo reconfirmed; no independent challenge worker. The new proof sketches are not elaborated. Retain the required preflight and verification commands above; add `truth related e81971f1`, `truth dossier e81971f1`, `truth brief e81971f1`, `truth semantics e81971f1`, `truth context bab6bc66`, `truth context 8f0f44e5`, and `truth novelty "present acquaintance and distinct evidential uses under global representational defeat"` (using target/release/truth). Reopen the current handoff after an independently challenged interpretation and actual first-person application; this checkpoint does not settle #930, #932 or #1007.
