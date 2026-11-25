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


## Continuation: can immediate awareness fail to supply an epistemic reason?

2026-11-25, third investigation from `10532a8c7f6d1dbad04dba53d672524880043c64`. Target: the positive local warrant for F6, not another derivation of categorical epistemic duty. Inspect the previous checkpoint, the existing `AssertionRetorsion.ExperienceOccurs` and `NoExperienceOccurs` declarations (statements `77e57686-d710-4505-9272-589cf5af6fe8`, `4ef2306a-42b9-442f-a774-674a2ab5e024`, definition `663c48ce-4166-4632-86d9-85eeef0c258b`), `EpistemicReasonDefinitionFork.Frame`, and the #930 [reason-role analysis](epistemic-reasons-preconditions.md). The #1979 [reviewed witness assessment](../../corpus/attempts/69a4a681-8caa-4b34-8fc4-84d8ae522e7b.json) and the prior [Cogito assessment](cogito-esse-1113.md) are retained; do not duplicate their bearer argument.

### 1. Weaken the evidence requirement: a nonfactive seeming can itself be the witness

The previous checkpoint's direct-thought route took actual apprehension as factive about an episode's being a thought. The strongest skeptical reply attacks that very classification. Do not answer it by defining all awareness as accurate knowledge.

Use a weaker question, **does anything occur phenomenally now?** Attend to the present question or appearance. The subject need not establish whether the episode is perception, hallucination, doubt, reasoning, a sensation, or something correctly described by a particular metaphysical theory. If a seeming is genuinely phenomenal, then its own occurrence is an experienced episode. An actual hallucination may misrepresent its object without being a nonexistent hallucination. A false conceptual classification of an experienced episode can leave the phenomenal occurrence untouched.

This is the distinction between a proposition presented *by* an appearance and the actual occurrence *of* the appearance. We do not infer the presented proposition's truth, an external object, or a true higher-order belief that the appearance has a particular kind. Nor do we define the positive epistemic reason as part of phenomenal occurrence. The first-person datum is the actual presentation, not a fallible transcript that says it exists. Its positive existential import is grounded in the fact that a non-veridical phenomenal appearance is still an instance of the very general phenomenon being considered. This is not the thesis that everything seems as it really is.

The strengthened argument is witness-replacing rather than witness-fixing. Suppose the original alleged episode is entirely misidentified or absent. If the subject is now actually experiencing the assessment of a proposed skeptical objection, *that* episode supplies the positive existential. It need not be numerically the same as the earlier episode. All the witnesses must be in the selected present domain. A bare report of the assessment, unconscious disposition, or earlier memory is not enough. The objection is not self-refuting merely because its formulation appears in a file. An actual phenomenal episode of considering it gives the counterinstance to the universal no-experience claim.

A genuine cognitive judgment would also be an occurrence of thought on the existing realization reading. But the weaker phenomenal argument does not require conceptual thought. A nonconceptual sensation is a relevant comparison; someone who experiences it without conceptual competence need not thereby have a propositionally available reason. For the actual **reason** application, select a subject who is asking the weaker question, can grasp the difference between occurrence and nonoccurrence, and has the present episode available as an instance. This is a first-person exercise a reader can perform, not observation of the owner's mental states or a claim of machine consciousness.

Use `ExperienceOccurs Occurs Experienced` for the existential shape. Here the occurrence carrier/predicate includes phenomenal episodes generally, not just thought. The consumer `08cef374` of the same record uses *thought* occurrence and the experienced-thought bearer principle `ac0a151f`; the present weaker interpretation must **not** be plugged into that consumer. If the selected experienced episode is actual questioning in the cognitive sense, the stronger typed application remains available with that classification. Otherwise it is an explicit missing bridge. The separate F6-to-reason-bearer consumer `b50727e1` does not identify the reason bearer with the episode itself.

Proposed constructive Lean application of the existing declaration (not elaborated or registered):

```lean
import TruthCore.Logic.AssertionRetorsion
open TruthCore.Logic.AssertionRetorsion

example {W E : Type}
    (Occurs Experienced Primary Challenge : W → E → Prop) (w0 : W)
    (hActual : (∃ e, Primary w0 e) ∨ (∃ e, Challenge w0 e))
    (hPrimary : ∀ w e, Primary w e → Occurs w e ∧ Experienced w e)
    (hChallenge : ∀ w e, Challenge w e → Occurs w e ∧ Experienced w e) :
    ExperienceOccurs (Occurs w0) (Experienced w0) ∧
      ¬ ∃ w, ((∃ e, Primary w e) ∨ (∃ e, Challenge w e)) ∧
        NoExperienceOccurs (Occurs w) (Experienced w) := by
  have witness (w : W)
      (h : (∃ e, Primary w e) ∨ (∃ e, Challenge w e)) :
      ExperienceOccurs (Occurs w) (Experienced w) := by
    rcases h with ⟨e, he⟩ | ⟨e, he⟩
    · exact ⟨e, hPrimary w e he⟩
    · exact ⟨e, hChallenge w e he⟩
  refine ⟨witness w0 hActual, ?_⟩
  rintro ⟨w, he, hn⟩
  exact hn (witness w he)
```

The two bridges record actual phenomenality of the evidence-producing episodes, not factivity of their contents. This is an elementary witness projection, not by itself a new philosophical proof. It could fail as an application if the alleged primary or challenge episode were only a report. The new warrant comparison concerns the weaker target which remains true despite that misrepresentation of content; it still needs actual experience and the content interpretation.

### 2. Separate counterevidence from a genuine higher-order undercutter

Fix the proposition Q: some phenomenal episode occurs within the selected present scope. Let A be the event that a primary phenomenal episode is present, D the event that considering a putative defeater is itself a present phenomenal episode, and M a public or remembered marker of a purported episode. The following are comparisons within one profile, not a claim that its finite worlds exhaust metaphysical possibility.

- **Rebuttal:** a supposed case with A or D and ¬Q is impossible under the very interpretation of A, D and Q. In particular, replacing the primary episode with a genuinely experienced illusion preserves Q. This is more specific than a general denial of external-world knowledge.
- **Loss of classification:** credible disagreement about whether the presentation is a thought, the product of a particular faculty, or correctly described by a theory can undercut those stronger conclusions. It need not deny the weaker existence of an appearance. An undercutter of even that classification needs to address what is actually given and what the subject grasps. A nonconceptual or merely dispositional subject might not have any access to the proposition Q as such. Such a case does not yet answer the selected competent-inquiry case.
- **Report/availability:** evidence only in the form M is compatible with ¬Q in the structural comparison. A process audit can legitimately undermine such testimony or a subject's ability to tell what a marker signifies. Do not treat identical reports as identity of a genuine phenomenal standpoint. The control with matching report but no phenomenon does not establish the metaphysical possibility of a nonconscious duplicate of a human.
- **Higher-order defeat:** actual information that one frequently misclassifies internal states can affect one's confidence that this is the relevant kind or that one is competent to apply a concept. A subject may even rationally defer to a trusted critic about a classification. What it does not supply by itself is a scenario with an actually present phenomenal episode and no phenomenal episode. An actual experience of reflecting on the critique supplies a new occurrence witness. A merely unapprehended critique, or uncertainty whether an experience is available under the selected description, need not do so. Thus the self-instantiation blocks a specific rebutter or non-indicativeness mechanism, not every theory of higher-order defeat or actual justified belief.

There is an exact informational consequence that does not require a prior about external-world reliability. For any probability measure on the comparison, if A has positive mass and A entails Q, then Pr(Q | A) = Pr(A ∩ Q) / Pr(A) = 1. The same holds for D or A ∨ D. If Pr(Q) was strictly below one, the conditioning increases it; if it was already one, there is no strict increase. The latter does not imply that A cannot sustain existing support. In contrast, conditioning on M alone can leave Q uncertain. A state where a genuine phenomenal episode exists but the subject conditions only on a report may have the wrong epistemic basis selected; existence of evidence does not establish uptake.

The probability statement characterizes an interpreted evidence relation, not the subject's actual credences, certainty, reliability, or entitlement. A critic may instead contest whether the subject is justified in taking the present basis to be A or D. A higher-order report H can change a subject's confidence in that very application, even while Q is true. Where the subject actually experiences considering H, that occurrence should not be removed from the description of their *total* available evidence. If the comparison treats H merely as report content, it is not testing this stronger evidence condition.

This improves the #1985/`8f0f44e5` comparison without assuming its normative defeat policy or reversing the implication from warrant to surviving basis. The process that generates a false external verdict is not thereby a bypass of the present occurrence's self-instantiating evidential role. But showing a distinct support relation does not show that any particular subject's basis is not undercut. The `ReliabilityFrame` continues to require explicit availability, support and undercut status; `bab6bc66` still concerns a specified undercut sole basis.

### 3. Does this evidence give a reason for belief? The strongest local case and limits

The original question admits two important readings of immediate awareness.

1. **Occurrence or nonconceptual presence alone.** It can be phenomenally present without a subject having the proposition, attending to it, or being able to recognize its bearing. The weak occurrence does not entail a propositionally available reason in every account. An infant's sensation is a concrete reason to distinguish this reading from a competent subject answering a factual question, not a claim that no infant has evidence in any sense.
2. **Occurrence actually available to a competent subject as an instance of the proposition they investigate.** Select the exercise of answering whether any experience occurs, not simply a desire to know some unrelated external p. The subject sees (in the non-visual, epistemic sense of grasps) the bearing of this presentation on the modest existential. No prior record, induction from a track record, conclusion already believed, or universal introspective infallibility is needed. Even if the subject suspends belief, the basis is intelligibly favorable to believing Q rather than ¬Q.

For the second reading, the proposed positive warrant is **instance-to-existential recognition**: the subject is presented with something that would need to be absent for the negative answer to be correct. Preserving the presentation while accepting the negative would count an actual instance as absent. This is not just the statistical success of a process, nor a desire that Q be true, nor a practical method for producing assent. It is the relation of the particular presented ground to the subject matter of the belief. It directly supports the ordinary judgment that this counts in favor of believing Q. No independent proof of every basic evaluative judgment is required by the canonical research policy. But the favorable bearing is not an axiom equating information and normative force.

A sharper comparison uses any truth-directed scoring standard that strictly prefers correct to incorrect acceptance and puts suspension between them (possibly tied with correct acceptance). In every state preserving A or D, accepting Q is strictly more accurate than accepting ¬Q under that comparison. Withholding avoids the error but need not achieve the positive epistemic end; a pure error-avoidance score can tie suspension and correct acceptance. No prior weighting matters to the strict comparison between the two belief targets. Further practical costs can affect all-things-considered choice without changing the truth-directed comparison. This is a concrete reason why the observed presentation is relevant **for that belief** rather than just for acting, attending, or suspending. It is not another proposal that any accuracy improvement confers categorical duty; the #930 [accuracy-regret results](epistemic-reasons-930.md) already establish related conditional accuracy facts. The contribution here is the self-instantiating actual-ground restriction and its weaker target, not novelty of scoring dominance.

Use the existing `EpistemicReasonDefinitionFork` interfaces: for the same a, consideration r and attitude `believe q`, establish `assessable q`, `applies a r (believe q)`, and `favors a r (believe q)`. Here the merit judgment has the concrete presented instance and existential contrast as its support. If the ordinary-role interpretation is accepted, the reverse direction of `OrdinaryDefinition` attributes that reason; reverse `ConsiderationPresentation` then yields `Reason a q` and F6. These are existing conditional calibrations (cf. `decf920c`, `6b4e3331`), not newly established universal premises. Use only the local judgment at that witness; the global calibrations remain open on wider frames. A pure instrumental account can grant this local reason for a subject actually seeking the accuracy of this question. Merely being curious about a different question or having some generic goal does not establish that aim for Q.

The stronger rival admits all of that evidence-relative merit and its local cognitive access but denies that the presentation has genuine reason-giving force. Its strongest forms differ:

| Rival | What it can concede | What must still be tested |
| --- | --- | --- |
| Higher-order skeptic | Q is true; the direct presentation would favor Q if properly identified. | A concrete defeat of the actual subject's access or ability to recognize the existential bearing. Falsity of other represented contents is not that defeat. |
| Error-avoidance skeptic | Believing Q is accurate and believing ¬Q is inaccurate; withholding avoids false assent. | No obligation to settle Q follows. But the tie with withholding does not deny a belief-directed favorable consideration unless the account adds a rule that only uniquely optimal attitudes have reasons. |
| Goal-relative epistemic norm | The presentation favors Q and gives the accuracy-seeking investigator an actual reason. | It can still deny force outside the relevant aim. This is compatible with F6, and the local exercise does not establish `BeliefAnswerability` at indifferent preferences. |
| Global normative nihilism | Q and the information relation hold, but no consideration genuinely counts as an epistemic reason even for this inquiry. | This conflicts with the ordinary local reason judgment, not merely with truth. The existing `ec80b13d` rules out a reason for rational adoption of nihilism on its own terms; `146b502b` refutes it given F6. Treating the local reason as established by the latter would be circular. |
| Occurrence-only ontology | A genuine episode occurs, perhaps without a distinct substance or enduring bearer. | This supports the weak occurrence; it does not decide the metaphysical bearer principle. If it denies any possible subject of reasons, a separate challenge must address the actual subject-of-epistemic-access interpretation. |

There is a further targeted dialectical dilemma. If a critic presents the proposed undercutter as **a genuine epistemic reason to believe the proposition that this apparent access is defective**, they concede thin F6 for that other content regardless of whether they succeed against Q. If they instead claim merely a cause of suspension, a reason to investigate, or a reason to withhold, F6 does not follow from that claim alone. If the critic offers the universal reasonless thesis as a fact without claiming a reason to believe it, its truth is not refuted by retorsion alone. If they impose an independent-certification requirement as merely a necessary condition on all belief reasons, its rejection of the current basis is not inconsistent merely because that basis entails Q. Their account owes a positive justification of the restrictive requirement in this case (not an endless regress of prior proofs by default). This is the same-scope use of the established nihilism and belief-specific controls, not a new universal retorsion theorem.

**Provisional assessment.** On the competent, actually truth-directed reading, the local positive attribution is strongly warranted prima facie: the instance is present, its bearing on the existential is understood, no appeal to the accuracy of a separate source is needed, and the false alternative is excluded by the very evidence. No substantive defeater of that bearing has been identified which preserves the stipulated actual evidence and the subject's competent access to it. This does not rule out an undercutter of the access, or establish sufficient warrant, belief, or categorical force. The genuine normative nihilist can deny the basic evaluative judgment while preserving the information facts; this leaves a live philosophical disagreement, but the denial itself is not a counterexample to the positive warrant. The strongest goal-relative account can grant thin F6 in this very inquiry. A reason for suspension in addition to the reason for Q need not cancel the latter pro tanto. The direct judgment is more defensible than a generic inference from external reliability, but its actual first-person application is not observed by this session.

### 4. Reproducible finite checks (executed)

The comparison below explicitly separates phenomenal occurrence from thought, report, external truth, and a further episode evaluating the objection. Both episode slots can be absent; the second need not be the first. A thought can be unexperienced. This tests witness replacement without a fixed numerical identity or a factive assumption about the external content. The label "phenomenal-nonthought" denotes a nonconceptual phenomenal episode, not a judgment which itself counts as thought. The two slots are all the episodes relevant to the finite test; no general claim of exhaustive episodes is made.

```python
from itertools import product
from fractions import Fraction
kinds = ('none', 'unexperienced-thought', 'phenomenal-nonthought', 'phenomenal-thought')
phen = lambda k: k.startswith('phenomenal-')
thought = lambda k: k in ('unexperienced-thought', 'phenomenal-thought')
# Primary episode kind, evaluation episode kind, public marker, external truth.
W = tuple(product(kinds, kinds, (False, True), (False, True)))
Q = lambda w: phen(w[0]) or phen(w[1])
T = lambda w: thought(w[0]) or thought(w[1])
A = lambda w: phen(w[0])
D = lambda w: phen(w[1])
M = lambda w: w[2]
P = lambda w: w[3]
assert len(W) == 64
assert all(not (A(w) or D(w)) or Q(w) for w in W)
assert any(not A(w) and D(w) and Q(w) for w in W)
assert any(A(w) and not T(w) for w in W)
assert any(T(w) and not Q(w) for w in W)
assert any(M(w) and not Q(w) for w in W)
assert {P(w) for w in W if A(w)} == {False, True}
assert {T(w) for w in W if A(w)} == {False, True}
assert {Q(w) for w in W if M(w)} == {False, True}
# A positive-probability phenomenal ground, a mere marker, and an independent
# actual episode of evaluating a proposed defeater. Weights need not be uniform.
H = (('phenomenal-thought', 'none', True, True),
     ('phenomenal-nonthought', 'none', True, False),
     ('none', 'none', True, False),
     ('none', 'phenomenal-thought', True, False),
     ('none', 'none', False, True))
assert set(H) <= set(W)
prob_checks = 0
for weights in product(range(4), repeat=len(H)):
    total = sum(weights)
    if not total:
        continue
    prior = Fraction(sum(x for w, x in zip(H, weights) if Q(w)), total)
    for evidence in (A, D, lambda w: A(w) or D(w)):
        mass = sum(x for w, x in zip(H, weights) if evidence(w))
        if not mass:
            continue
        posterior = Fraction(sum(x for w, x in zip(H, weights) if evidence(w) and Q(w)), mass)
        assert posterior == 1 and posterior >= prior
        assert (posterior > prior) == (prior < 1)
        prob_checks += 1
    if all(weights):
        assert 0 < Fraction(sum(x for w,x in zip(H, weights) if M(w) and Q(w)),
                            sum(x for w,x in zip(H,weights) if M(w))) < 1
# Truth-directed payoff only: correct/incorrect/suspend scores are independent
# of the occurrence. Compare every admissible integer score triple in range.
score_checks = 0
for c, i, s in product(range(-2, 3), repeat=3):
    if not i <= s <= c or c == i:
        continue
    for w in W:
        if not (A(w) or D(w)):
            continue
        assert Q(w)
        q, notq, suspend = c, i, s
        assert q > notq and q >= suspend
        assert (q > suspend) == (c > s)
        score_checks += 1
print('states', len(W), 'nonempty conditioning tests', prob_checks, 'state-score comparisons', score_checks)
# Omission controls for the stronger epistemic conclusion. Preserve the same
# episode and information while varying attribution and force; not psychology.
for counts, aims, independent in product((False, True), repeat=3):
    # Presentation/attribution at believe Q, plus separate force rule.
    reason = counts
    actual_force = reason and (aims or independent)
    assert not actual_force or reason
    if counts and not aims and not independent:
        assert reason and not actual_force
print('attribution/force controls', 8)
```

Actual output: 64 states, 2736 nonempty conditioning tests, 1440 state-score comparisons, eight structural attribution/force controls. These checks are finite arithmetic and explicit omission models. The conditional probability identity and score inequalities have the elementary general arguments above; no probability measure over metaphysical possibilities or actual decision rule is inferred. The information-inclusion conclusion follows by construction of Q from phenomenal occurrences, and the last controls assign attribution rather than test human normativity. The code confirms the advertised distinctions rather than deriving any novel Lean result or claiming that every competing metaphysics is represented.

### 5. Exact downstream consequence and allocation

The modest occurrence proposition is about actuality, not just logical consistency. It is neutral regarding external world, temporal change, substance, and causal explanation. Its truth is not made by wishing that the occurring episode did or did not occur, while it obviously depends on there being an experience; this is no argument for a mind-independent truthmaker ontology. F1 applies to the same occurrence and respect under the encoded negation. A content-level truth predicate still needs the relevant capture interpretation. Reason and causal explanation remain distinct.

If the competent actual inquirer makes the local reason attribution, the existing thin F6 incompatibility applies to global epistemic nihilism. With the separate selected-world representation/presence and esse contract, `b50727e1` remains the route to `56f68b40` and `72391d4d`. For a distinct route through `77e57686`, do not feed the broadened episode interpretation into the existing *thought*-bearer consumer `08cef374` without fixing the stronger same-episode sense. No new edge, floor marking, premise discharge, objective moral obligation, metaphysical PSR, necessary being or intrinsic divine intellect follows here.

The live next comparison is narrower: **does a higher-order defeater remove the competent inquirer's access to the existential bearing, or does it preserve that access and reject the reason-giving force of a fully available presented instance?** Seek an actual counterexample with the subject grasping the instance and its bearing, not a report-only example or a mere skeptical stipulation. A theory which conditions reasons on such access, rather than requiring general faculty validation, can grant the thin reason while disputing full warrant. If no substantive defeating mechanism is supplied, preserve the positive local judgment; do not treat absence of a discovered objection as a proof. The separate normative relevance transfer to wholly indifferent preferences is the already isolated #930 problem, not another consequence of this episode. A reader's actual self-application could supply direct first-person evidence, but the repository cannot certify that subjective fact for everyone.

No new proof registrations or source attributions. Full local conventions/preflight and Lean verification remain unavailable (no Lean/Lake/Cargo, no GitHub DNS in the container, no warm checkout); no fresh independent challenge worker is available. The proposed semantic assessment is unreviewed. In addition to the previous handoff run `target/release/truth related 77e57686`, `dossier 77e57686`, `brief 77e57686`, `semantics 77e57686`, `context 08cef374`, `context 0c9d64e6` and `novelty "nonfactive phenomenal seeming and renewed skeptical challenge instantiate the weaker present occurrence"` with the same CLI. Challenge review must focus on the scope of occurrence, the difference between actual presence and propositional access, the role-to-reason reading, and not treating the finite control as a proof of the latter. Self-sweep: no imported historical position; same-scope witnesses; report-only and access-loss alternatives retained; no probability claim about actual histories; no generalization to every subject or force at an indifferent preference; no reuse of the thought-specific consumer under the broader reading. Keep #1995 draft.


## Continuation: higher-order defeat, partial access and surviving local reasons

2026-11-25, fourth checkpoint from `d84beef90a2db244abb3b9782eb962f55b6bcbd2`. The target is F6's positive local application, particularly the claim that a higher-order defeater can eliminate **every** belief-directed reason even when a subject has a direct presented instance of the existential under investigation. Retain the earlier distinctions between phenomenal occurrence, thought, the reason relation, sufficient warrant, and preference-independent force. This checkpoint is not a new grounding or psychological-competence theory.

### 1. Give the higher-order skeptic a positive replacement account

Consider the same question Q: does any experience occur in the present inquiry scope? A subject has what appears to be a direct instance and is informed by an otherwise credible assessor that their current procedure confuses automatic introspective reports with actual presentations. This is a constructed analogue of the misleading higher-order testimony discussed in the existing [externalist entitlement study](externalist-entitlement-and-regress.md), not a claim about an actual clinical intervention, its prevalence or the source author's verdict on the Cogito.

The mechanism is not just that an alternative might be possible. The assessor's evidence could supply grounds to doubt the subject's recognition of which procedure is currently operative. A genuinely competent subject can be misled *about their own competence in a particular episode*. This is a substantive kind of objection to an inference from actual access to sufficient warrant. The older `LOGIC-JUSTIFICATION-INTROSPECTION` (`901bfc2f`) already separates actual first-order knowledge/justification from knowledge of justification in its nontransitive profile; the current question concerns the reverse demand for a higher-order status as a prerequisite even of a pro tanto reason. Do not assume either knowledge, positive introspection, or perfect reflection from genuine access.

Distinguish three targets:

- Q: the weak present existential, not truth of the presented external content, not an accurate classification as thought, not an enduring subject.
- M: a fallible marker (a report, verdict or appearance-*report* of access). Its occurrence as a marker is not stipulated to be an experienced episode.
- A: an actual phenomenal instance available as such. A subject's justified recognition that their available basis is of type A rather than M is a distinct assessment. D is another actually experienced episode of considering the challenge. If D is present within the same scope, it supplies the existential even when the primary A was misidentified.

The credible higher-order report H can change the subject's assessment of M or their confidence that the basis is A. The truth of what H says is not the occurrence of H. A public report about the procedure, even a report asserting that there are no experiences, can be false. If the subject genuinely experiences considering H, that act is D, not merely H. A model allowing H with no Q therefore represents a report-level comparison, not a subject who actually experiences considering H.

There is a precise, testable difference between the rival's informational explanation of defeat of M and normative defeat of genuinely available A. The latter might be a theory of warranted access or sufficient justification even when first-order evidence is real; it must not be misrepresented as an actual counterexample to Q. The former can be explicitly realized.

### 2. Three mechanisms of report-level defeat and their effect on the reason target

Use the existing positive-likelihood comparison of [#934](contrastive-worldview-934.md), `TruthCore.Results.Logic.ContrastiveWorldview.updateConstraints` (`82e41e84` certificate), and the conditional-likelihood comparison of [#1396](correlated-testimony-1396.md), rather than proposing a new Bayesian library. An assigned non-dogmatic prior is distinct from an actual investigator's warranted credence. In the following profiles Q and ¬Q are the binary hypotheses. H is a higher-order report flag, M a positive marker. The row totals for H are 8 in Q and 24 in ¬Q; the row totals outside H are 24 in Q and 8 in ¬Q. Outside H, M is present in 18 of the Q cases and 2 of the ¬Q cases. Vary only the number of positive markers inside H as specified:

| Profile | Q,H,M / ¬Q,H,M weights | Pr(Q) | Pr(Q given M) | Pr(Q given H) | Pr(Q given H,M) |
| --- | --- | --- | --- | --- | --- |
| Attenuation / net rebuttal | 4 / 6 | 1/2 | 11/15 | 1/4 | 2/5 |
| Neutralization of M | 2 / 6 | 1/2 | 5/7 | 1/4 | 1/4 |
| Reversal of M | 2 / 12 | 1/2 | 10/17 | 1/4 | 1/7 |

All eight original cells are positive in all three profiles. H is adverse evidence in each; M alone favors Q in each. Holding H fixed, in the first profile M still increases the probability of Q above 1/4, even though the joint posterior falls below the original 1/2 and also below the posterior on M alone. In the second M is neutral given H, and in the third it becomes adverse given H. These are distinct informational effects. A lower joint posterior, or a justified decision not to accept Q, does not show the complete cancellation of every pro tanto supporting consideration. For accounts that identify pro tanto merit with positive conditional bearing, the first case has a positive consideration that survives the adverse evidence. For accounts with a different basing or defeat criterion, that attribution remains a substantive interpretation.

Now refine the Q,H,M cell of each profile with two nonempty, disjoint evidence cases A and D, each of unit weight, leaving any remaining cases without established access. Neither A nor D occurs in a ¬Q cell. This is not a probability of actual human experience; it is an explicit structural comparison between report-only and direct-presence interpretations. In every profile the marginal report-level result stays unchanged. The conditional probability of Q given H,M,A, or H,M,D, is one. These examples exhibit actual access in the selected positive cell with both reports, and report-only ¬Q cells; they do not claim that a subject can access A in the latter cells.

The general reason is independent of the chosen weights: whenever an event E consists of actual presented phenomenal instances in this scope, E is included in Q. For any further information set H with positive joint mass Pr(E∩H)>0,

    Pr(Q | E∩H) = Pr(Q∩E∩H) / Pr(E∩H) = 1.

If 0 < Pr(Q | H) < 1, then Pr(E | ¬Q,H)=0 and Pr(E | Q,H)>0, hence E strictly favors Q conditional on H. If Pr(Q | H)=1, E adds no strict probability increase but that is saturation, not evidence for ¬Q. If Pr(E∩H)=0, conditioning is undefined: the selected probability model has excluded the joint evidence (or assigned zero mass to it), not exhibited a state preserving positive-mass E,H in which Q is false. The last two cases matter; it is incorrect to infer a new strictly supporting reason merely from every posterior equal to one, or to identify a zero-probability cell with metaphysical impossibility.

The strict-positivity premises in `ContrastiveWorldview.Comparison` and `CorrelatedTestimony1396.Row` exclude the factive event's zero false-positive likelihood. The elementary event inclusion above treats that boundary directly; it is not advertised as an application of those theorems at an inadmissible argument. A finite enumeration checks the arithmetic below, not a new verified corpus result.

This comparison clarifies the strongest surviving higher-order reply. H can provide a genuine reason for doubting that one's apparent access is actually of type A, and a conciliatory/internalist theory may consequently withhold sufficient warrant even when actual A is present. The objection can concern the person's entitlement to employ A as evidence, not the logical bearing of A under the retained interpretation. Showing that H cannot alter the latter does not prove that it cannot alter entitlement. Conversely, the mere report-level defeater does not establish cancellation of the actual evidence's pro tanto normative bearing. That requires a further principle of defeat with that scope.

### 3. Access uncertainty does not automatically neutralize apparent evidence

The previous checkpoint compared known factive access against a mere report. A more demanding rival can deny justified certainty that the current basis is genuine access while retaining some credence in it. Test that case explicitly, rather than assume either perfect or no access.

Fix H and a non-dogmatic Q prior. In a supplied mixed channel, a latent mode C is capable of giving a genuine access-based positive verdict E; the alternative mode is a fallible report. In C a positive E occurs only when Q, with sensitivity t=Pr(E|Q,C,H)>0. C need not produce E in every Q case. The other mode produces E with likelihoods mQ,mN under Q,¬Q. Here E is the **output or apparent access report** of the mixed channel, not itself the phenomenal presentation A. Assume the mode probabilities given Q,H and ¬Q,H are equal to alpha (conditional independence of the mode and Q in the H profile). It is not assumed that actual phenomenal access is independent of occurrence. Only the choice of channel mode is so modeled.

Then

    lQ = alpha*t + (1-alpha)*mQ
    lN = (1-alpha)*mN
    lQ - lN = alpha*t - (1-alpha)*(mN-mQ).

For a nonzero likelihood of the report, the sign of this difference is the sign of the report's posterior shift relative to the H-conditional prior (direct Bayes algebra at zero likelihoods if needed).

- If the fallback marker is neutral (mQ=mN), alpha>0 and t>0 imply a strict positive likelihood difference. A skeptic who merely reduces confidence in genuine access need not eliminate all support from the apparent report. The effect can be arbitrarily small as alpha approaches zero; no sufficiency threshold follows.
- If the fallback is reverse-diagnostic (delta=mN-mQ>0), support is positive exactly when alpha>delta/(t+delta), neutral at equality, and adverse below the threshold. This is an explicit mechanism by which uncertainty plus an adverse alternative can cancel the informational bearing of the appearance-report.
- The conditional mode-independence premise is consequential. With distinct alphaQ and alphaN, a neutral fallback m yields difference alphaQ*(t-m)+alphaN*m. A low-sensitivity access-capable mode can be more common in Q states, and the neutral fallback more common in ¬Q states. With alphaQ=3/4, alphaN=1/4, t=1/4 and m=3/4, the likelihoods are 3/8 and 9/16. The neutral-fallback conclusion fails. This is a concrete selection mechanism, not evidence that it actually operates in present reflection.

This is a narrower but more informative rival comparison: an account questioning access must specify whether its alternative is merely noninformative, negatively diagnostic, or subject to a selection mechanism. The first does not suffice for neutralization under the stated equal-mode condition. No claim is made that an actual higher-order skeptic must assign these priors, that all epistemic reasons are likelihood gains, or that the genuine occurrence itself has a probability of being false. The mixture models a subject's *uncertainty about access*, with fallible report states, not a counterexample to an actually available and correctly understood phenomenal instance. The degenerate all-zero likelihood combinations are included in the algebraic sign enumeration but excluded from any posterior claim.

### 4. Reassess the reason bridge, not just belief or warrant

The existing `ReliabilityFrame` uses a basis-specific undercut relation; `WarrantNeedsUndefeatedSupport` is a necessity direction, not sufficiency. `SurvivingBasisGivesReason` (`6b4e3331`) is the open pro tanto calibration. The existing definition of thin F6 is existential and does not require belief, truth of the supported content, sufficient warrant, or an all-preference force condition. In particular a reason need not be factive just because the present proposed ground happens to be so.

Use the following fixed case contrasts before treating any new claim as an argument for F6:

| Subject's epistemic position | Strongest local positive account | Strongest remaining objection |
| --- | --- | --- |
| Genuine presentation, understands its existential bearing, no applicable access defeater | The actual presented instance supplies a positive reason for the existential; no general introspective reliability or independent certification premise is needed for this local recognition. | Nihilism denies reason-giving merit even here. An account requiring an additional reflective credential must justify its relevance to the local reason, rather than just to certainty or knowledge. |
| Genuine access and correct grasp, credible misleading higher-order testimony about one's capacities | A reason for the conclusion can remain while there is a competing reason to doubt the method or withhold full assent. The testimony does not produce an actual present negative instance. | A higher-order internalist can require the subject's warranted recognition of the basis as a condition of epistemic reason status, not merely of sufficient warrant. This is a substantive normative calibration proposal; the information result alone does not decide it. |
| Only a fallible marker is legitimately accessible, plus higher-order information | Conditional support can persist or be neutralized or reversed, as in the three concrete profiles. F6 does not require a factive source. | Subject may have no positive belief-directed reason for Q when the marker is neutralized; need warrant for the actual channel/selection model and the reason interpretation. |
| Mere uncertainty about access, with no independently supported adverse calibration | Uncertainty by itself need not cancel support; the mixed-channel comparison exhibits the precise conditional persistence and failure cases. | Lack of entitlement to use any favorable model can still be contested. No stipulated probability licenses an actual attribution. |
| Global reasonlessness urged as a result of the higher-order inquiry | If the assessor supplies a genuine reason to believe the adverse calibration or the defeating proposition, F6 obtains for that subject and that content, even if no Q reason survives. | The critic may offer only a rule of suspension, a causal explanation, or withhold rational endorsement of their own policy. Existing belief/suspension and nihilism controls leave those positions coherent. |

**A narrower challenge to the restrictive calibration.** Suppose someone proposes that every reason to believe requires a separately justified proposition certifying the reliability of that reason's basis. This is stronger than requiring competent grasp, and stronger than an assessment of adequate warrant for accepting a conclusion. To defend this restriction as rationally warranted by an offered belief-directed reason already grants F6; it cannot be used to establish global absence of all reasons while the defender grants that very attribution. Merely pointing out the need for an independent credential in one particular case does not show that the restriction holds universally. On the other hand, a nonnormative presentation of the policy can remain consistent with global reasonlessness, and an infinitist can accept reasons in an unending structure. Neither an anti-regress argument nor `REGRESS-SCHEMA-PACKAGE` (`74e00870`) automatically refutes the latter: that package concerns explicit well-founded/inductively generated warrant profiles, not a general equivalence of reason and higher-order certification. Do not install the controversial universal prerequisite in the definition of F6. The existing #930 and #1007 distinction between a reason to believe and a reason merely to suspend remains.

The local positive warrant is thus not just the absence of discovered objections. There is an actual-instance-to-existential evidential relationship, and it has a robust conditional comparison even under adverse higher-order reports. The rival's own strongest mechanism is represented rather than dismissed: it may remove access, undermine higher-order entitlement, or neutralize a fallible cue. On the ordinary pro tanto interpretation, it is reasonable to retain a local positive reason judgment in the competent actual inquiry with no defeating access mechanism. The additional claim that higher-order access is mandatory **even for a pro tanto reason** still requires substantive defense. A goal-relative account can grant this reason to a subject actually seeking the answer. A global nihilist can reject the evaluative bridge altogether; it does not follow from the probability calculation that such a position is false. F1 and F6's existing markings remain unchanged.

### 5. Executed reproducible tests

```python
from fractions import Fraction as F
from itertools import product

def report_profile(h_q_m, h_n_m):
    # Q, H (higher-order report), M (first-order marker), multiplicity.
    return [(True,True,True,h_q_m), (True,True,False,8-h_q_m),
            (False,True,True,h_n_m), (False,True,False,24-h_n_m),
            (True,False,True,18), (True,False,False,6),
            (False,False,True,2), (False,False,False,6)]

def prob(rows, predicate, cond=lambda _: True):
    denominator = sum(w[-1] for w in rows if cond(w))
    if not denominator:
        return None
    return F(sum(w[-1] for w in rows if cond(w) and predicate(w)), denominator)

Q = lambda w: w[0]
H = lambda w: w[1]
M = lambda w: w[2]
HM = lambda w: H(w) and M(w)
for name, a, b, expected in [('attenuation',4,6,F(2,5)),
                             ('neutralization',2,6,F(1,4)),
                             ('reversal',2,12,F(1,7))]:
    rows = report_profile(a,b)
    assert all(w[-1]>0 for w in rows)
    prior, first, higher, combined = (prob(rows,Q),prob(rows,Q,M),
                                    prob(rows,Q,H),prob(rows,Q,HM))
    assert prior == F(1,2) and first > prior and higher == F(1,4)
    assert combined == expected and combined < prior
    assert (combined > higher, combined == higher, combined < higher) == {
        'attenuation':(True,False,False), 'neutralization':(False,True,False),
        'reversal':(False,False,True)}[name]
    print(name, prior, first, higher, combined)
    # Refine the Q,H,M cell with two distinct experienced grounds.
    # H and M are markers only. Not all Q worlds supply access.
    refined=[]
    for q,h,m,n in rows:
        if q and h and m:
            refined += [(q,h,m,True,False,1),(q,h,m,False,True,1)]
            if n>2: refined += [(q,h,m,False,False,n-2)]
        else: refined += [(q,h,m,False,False,n)]
    assert prob(refined,Q,HM)==combined
    A=lambda w: w[3]
    D=lambda w: w[4]
    for E in (A,D,lambda w:A(w) or D(w)):
        assert prob(refined,Q,lambda w:HM(w) and E(w)) == 1
    assert any(Q(w) and not A(w) and D(w) for w in refined)
    assert any(not Q(w) and HM(w) for w in refined)

# Seven states (Q,A,D,H); actual A or D entails Q.
S=((True,True,False,True), (True,False,True,True),
   (True,False,False,True), (False,False,False,True),
   (True,True,False,False), (True,False,False,False),
   (False,False,False,False))
count=excluded=dogmatic=strict=0
for weights in product(range(3),repeat=len(S)):
    if not any(weights): continue
    rows=[(*w,n) for w,n in zip(S,weights)]
    for flag in (False,True):
        cond=lambda w: w[3]==flag
        pre=prob(rows,Q,cond)
        if pre is None: continue
        for E in (lambda w:w[1],lambda w:w[2],lambda w:w[1] or w[2]):
            post=prob(rows,Q,lambda w:cond(w) and E(w))
            if post is None:
                excluded+=1; continue
            assert post==1
            if pre==1:
                dogmatic+=1
            else:
                assert post>pre
                assert prob(rows,E,lambda w:cond(w) and not Q(w))==0
                assert prob(rows,E,lambda w:cond(w) and Q(w))>0
                strict+=1
            count+=1
assert count==dogmatic+strict
print('conditional restrictions:',count,'zero mass:',excluded,'already certain:',dogmatic,'strict support:',strict)
for rq,rh,susp,wq in product((False,True),repeat=4):
    f6=rq or rh
    assert not (f6 and not rq and not rh)
    if rh: assert f6
    if not rq and not rh and susp: assert not f6
    if rq and not wq: assert f6
print('reason/warrant/suspension controls:',16)

# Mixed channel for apparent rather than established access.
grid=[F(i,8) for i in range(9)]
strict=neutral=reverse=0
for alpha,t,mq,mn in product(grid,repeat=4):
    lq=alpha*t+(1-alpha)*mq
    ln=(1-alpha)*mn
    delta=mn-mq
    assert lq-ln==alpha*t-(1-alpha)*delta
    if mq==mn and alpha>0 and t>0:
        assert lq>ln
    if delta>0 and t+delta>0:
        assert (lq>ln)==(alpha>delta/(t+delta))
        assert (lq==ln)==(alpha==delta/(t+delta))
    if lq>ln: strict+=1
    elif lq==ln: neutral+=1
    else: reverse+=1
assert strict+neutral+reverse==9**4
print('mixed-channel controls:',strict,neutral,reverse)
a_q,a_n,t,m=F(3,4),F(1,4),F(1,4),F(3,4)
lq=a_q*t+(1-a_q)*m; ln=(1-a_n)*m
assert (lq,ln)==(F(3,8),F(9,16)) and lq<ln
print('dependent-mode control:',lq,ln)
```

Executed in the container with Python exact fractions: the three reported posteriors passed; 7,776 positive-mass conditioning comparisons passed (5,184 strict gains, 2,592 saturated at one; 5,022 joint zero-mass cases recorded separately, not counted as conditioning); 16 structural reason/warrant/suspension assignments and 6,561 mixed-channel likelihood-sign comparisons passed (4,871 positive, 305 equal, 1,385 negative; signs alone do not certify a defined posterior when both likelihoods vanish). The explicit dependent-mode counterexample passed. These checks support the displayed arithmetic and controls, not actual normative attributions, exhaustive rival coverage or Lean verification.

### 6. Handoff: the next crux after informational defeat

The earlier diagnosis of no discovered mechanism defeating the *bare occurrence's informational bearing while retaining the actual presented instance* is retained within its scope. Revise the stronger informal reading that no higher-order objection can matter when the original episode is real: misleading higher-order evidence can undermine entitlement or access without making the original state false. We have now given that rival a positive model and separated three kinds of informational defeat. A theory that demands higher-order credentialing even for a pro tanto reason remains a live restrictive normative alternative, not a demonstrated rebuttal to the present local merit judgment. The narrower mathematical claim is that H cannot make actual E favor ¬Q in the specified positive-mass event comparison while retaining E⊆Q. The mixed-channel result extends the investigation to fallible apparent access with explicit conditions, without assuming epistemic transparency.

**Next discriminating proposition:** does genuine epistemic support require the subject to have a further justified belief certifying the support relation, even when the subject directly apprehends the relevant occurrence and grasps its bearing? Compare the actual directly recognized instance against a concrete misleading higher-order assessor. Investigate the weakest possible credential principle, whether an already understood rule requires further independent application credentials, and whether the critic who imposes the credential requirement can coherently give a belief-directed reason for accepting it while denying all reasons. Reuse `LOGIC-JUSTIFICATION-INTROSPECTION` and the existing regress and rational-basing families; no automatic epistemic-to-ontic PSR transfer. Do not re-prove a general regress theorem or treat a surviving infinitist as reasonless. If the critic grants ordinary local epistemic reasons but disputes force for indifferent subjects, reallocate that stronger question to the existing #930 investigation.

The downstream paths remain those already named: `6b4e3331` or the local ordinary-role/reverse-presentation application to F6, then `b50727e1` with `ada25623` and `0436de86` to concrete population `56f68b40` and `72391d4d`. The broader phenomenal occurrence interpretation is not a premise of the thought-specific bearer consumer. No new graph registrations, claims, definitions, floor markings or root discharge. The fourth checkpoint is explicitly unreviewed. No independent semantic challenger or prepared clone was available; local `git ls-remote` failed DNS and Lean/Lake/Cargo are absent. Run the existing preflight, including `truth context LOGIC-CONTRASTIVE-WORLDVIEW`, `truth context LOGIC-JUSTIFICATION-INTROSPECTION`, `truth context REGRESS-SCHEMA-PACKAGE`, and `truth novelty "higher-order report defeat versus directly presented existential and partial access"`, before any registration. Independent challenge should test the same subject and evidence across the profiles, the mixed-channel independence premise, the zero-mass boundary and the difference between support and normative force. Keep #1995 draft; no merge.


## Continuation: must a reason have a further justified credential?

2026-11-25, fifth checkpoint from `ed293a1318e21a47b24be5ab518dbc0a2e5cb0f1`. Target: whether an actual pro tanto reason requires a further justified belief certifying that it is a reason. Reuse the fixed F6 sense, not a categorical ought or the stronger notion of justified belief. Relevant prior work: [rational basing](epistemic-underminer-boundaries.md#rational-basing-the-particular-transition-must-exercise-the-capacity), [introspection](carneades-epistemology-introspection.md), [externalist entitlement](externalist-entitlement-and-regress.md), [Agrippa](agrippa-justificatory-adequacy.md), [infinitism](infinitist-justification-adequacy.md), and [self-certification](reading-only-self-certification.md). The earlier studies already establish the structural regress and knowledge-introspection boundaries; the present work tests the interface from *belief-directed reasons* to actual credential requirements, with the direct occurrence case as its positive warrant. No new historical attribution.

### 1. The credential demand has several importantly different strengths

Consider an actually experienced, competent inquiry into whether any phenomenal occurrence exists. Its presented occurrence is an instance of the existential Q; its truth does not require correct representation of a different object. The person might recognize that bearing before explicitly considering whether they have a reason, whether their reason is sufficient, or whether their cognitive method is reliable. Contrast this with an automatic verbal marker. The latter can reproduce the same answer without the relevant evidence or uptake.

The strongest objection is not that metacognition is generally useful. It is that a consideration cannot be an epistemic reason for a subject unless the subject has already earned the epistemic right to employ it. A credible higher-order assessor can undermine the subject's confidence in a procedure or in the classification of the evidence. The proponent may therefore demand justified recognition of a reason's status. The following distinctions determine what that proposal actually entails:

| Proposed condition on a reason | What it requires | What it does not entail |
| --- | --- | --- |
| Availability | The relevant consideration is accessible or appropriately available to the subject. | Explicit belief that it is a reason. |
| Understanding / competent grasp | The subject recognizes its bearing on the question, possibly by exercising a capacity rather than forming a separate judgment about support. | A further proposition about epistemic status. |
| Explicit metabelief | The subject believes a content certifying this consideration's support for this target. | Justification of the metabelief or independent prior support for it. |
| Justified metabelief | That very credential belief is justified. | That its justification is inferential, has another belief-directed reason, or is independently prior. |
| Reason-supported credential | An epistemic reason supports believing the credential. | An acyclic or well-founded ordering of these reason instances. |
| Independently prior reason-supported credential | A genuine reason for the credential stands strictly prior in a supplied epistemic order to the reason being certified. | Well-foundedness of that order; it may descend indefinitely. |
| Well-founded independently prior credentialing | The previous demand is imposed universally and the dependence is well-founded. | Compatibility with F6, as shown below. |

These are selected distinctions, not a claim of a linear strength order among every theory of access or a historical school classification. In particular, some availability accounts need not require conscious understanding; some justified-metabelief accounts allow simultaneous support or a prior standing credential. A justified belief need not be true unless factivity is added. A true general belief about the reliability of a faculty does not guarantee the epistemic merit of each particular token. Neither a mere lack of reflective knowledge nor lack of an ability to verbalize one's reason establishes the absence of a reason. The existing `LOGIC-JUSTIFICATION-INTROSPECTION` result (`901bfc2f`) supplies a factive nontransitive control for higher-order ignorance with first-order justification; it does not itself establish or refute a reason-specific credential requirement.

A further distinction concerns **possession versus employment**. A reason may be available without assent, use, actual belief or awareness of its sufficiency. A demand that one check credentials *before relying on* a belief in a high-stakes inquiry is a different condition from saying that no reason exists before the check. Evidence could supply a reason to check a method in the first place. Keep the proposed necessity precisely on the epistemic status the proponent intends.

### 2. F6 and the exact strict-credential incompatibility

Fix a subject. A reason instance is a consideration and a belief-content, not merely a content or a physical source. Use the existing `EpistemicReasonDefinitionFork.Frame.CountsAsReason a r (f.believe p)` to identify such an instance, and `ConsiderationPresentation` to relate this to thin `Reason a p`. A new credential proposition c is required to concern that very subject, consideration and target, not merely some reason somewhere. The fact that c is believed, justified, or supported by another consideration s remains separate. Let v=(s,c) be the reason instance for the credential and u=(r,p) the original instance.

Separate the proposed inputs:

- **C (universal credential)**: every actual belief-directed reason instance u has a believed and justified content c which certifies u. This is the higher-order requirement under investigation, not an accepted definition of reason.
- **T (transmission to a prior reason)**: for such a credential, there is an actual belief-directed reason instance v for believing c, and v is strictly prior to u in the relevant epistemic dependency. This combines a reason-for-credential condition with a priority condition. Even if one believes that justification always has reasons, independent priority is an additional claim. Distinguish these in any future registered fork.
- **W (well-foundedness)**: the selected priority relation has no inaccessible dependence, in the precise `WellFounded` sense. This is a premise about the reason-dependence interpretation, not a general consequence of F1 or F6. No causal or temporal PSR follows.

Under C and T, each actual reason instance has a predecessor which is itself an actual reason instance of the *same* subject. Under W there cannot be any such instance. Proof: well-founded induction; assume an instance u is active. C supplies the justified credential c, T supplies an active predecessor v. By the induction hypothesis no predecessor is active, contradiction. Consequently the following is a **conditional incompatibility**:

    F6 ∧ ConsiderationPresentation ∧ C ∧ T ∧ W.

With F6 and the presentation fixed, at least one of C, T, W must fail. One can fix W only on a closed selected dependency subdomain containing the reason witness and all its required prior credential reasons. Without that closure, the reasoning does not exclude a credential reason outside the subdomain. If W and T are retained, C fails: there is no consistent universal demand that every reason be independently certified in this manner. This is not the stronger proposition that some reason is independent of all epistemic grounds, or that all knowledge has an irreducible foundation. A basic reason has an available ground; independence from a further credential is not being groundless.

The proof uses the well-founded induction pattern already present in `TruthCore.Logic.Regress.Graph.controls_of_wellFounded` and `REGRESS-SCHEMA-PACKAGE` (`74e00870`). No need for a second structural regress library. The new work is the same-instance epistemic interface and the exact open requirements. A possible local Lean application, **proposed only, not elaborated or registered**:

```lean
import TruthCore.Logic.EpistemicReasonDefinitionFork
import TruthCore.Logic.Regress
open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

example (f : Frame)
    (Believes Warrant : f.Agent → f.Content → Prop)
    (Certifies : f.Agent → f.Content → (f.Consideration × f.Content) → Prop)
    (prior : f.Agent → (f.Consideration × f.Content) →
      (f.Consideration × f.Content) → Prop)
    (hPresent : ConsiderationPresentation f)
    (wf : ∀ a, WellFounded (prior a))
    (credential : ∀ a r p, f.CountsAsReason a r (f.believe p) →
      ∃ c, Certifies a c (r,p) ∧ Believes a c ∧ Warrant a c)
    (transmit : ∀ a r p c, f.CountsAsReason a r (f.believe p) →
      Certifies a c (r,p) → Believes a c → Warrant a c →
      ∃ s, f.CountsAsReason a s (f.believe c) ∧ prior a (s,c) (r,p)) :
    ¬ ThereAreEpistemicReasons f.Reason := by
  rintro ⟨a, p, hp⟩
  obtain ⟨r, hr⟩ := (hPresent a p).mp hp
  have no (x : f.Consideration × f.Content) :
      ¬ f.CountsAsReason a x.1 (f.believe x.2) := by
    induction (wf a).apply x with
    | intro y _ ih =>
      intro hy
      obtain ⟨c, hc, hb, hw⟩ := credential a y.1 y.2 hy
      obtain ⟨s, hs, hprior⟩ := transmit a y.1 y.2 c hy hc hb hw
      exact (ih (s,c) hprior) hs
  exact no (r,p) hr
```

The type keeps the same witness, target and agent, and does not assert factivity or sufficiency of a credential. `Certifies` is an explicitly interpreted relation; the theorem does not establish that any actual content has this meaning. The proof would show incompatibility under its hypotheses, not a metaphysical fact that actual credential dependence is well-founded. The former `6b4e3331` (surviving basis counts as a reason) and `b3ddb7c4` (reasons from warranted acceptance and specified calibrations) are relevant but do not imply T's independent priority. No reverse inference from full warrant to a further justified metabelief is made.

There is also a narrower finite-episode consequence that does not need an all-history well-foundedness thesis. If the rival requires a prior **actual use** of a reason for a credential before every actual use of a reason, and requires those earlier uses to occur in the same finite closed review trace, then a nonempty trace is impossible. Its earliest reason-use cannot have a prior reason-use within the trace. This is a direct finite minimality argument; an infinite sequence of dispositions or reasons that could be supplied on demand does not satisfy an actual-prior-use requirement. It does not follow that an actual subject has no standing reasons before the trace, that there is a first belief in their lifetime, or that a finite duration excludes infinitely many events. A standing credential from outside the trace is a genuine escape from this *local* obstruction, not proof of its own adequate support.

### 3. Why the distinct-credential demand alone is not a regress proof

The finite controls below show that serial dependence plus a nonempty active set requires a cycle in a finite carrier. Requiring each credential reason to be numerically distinct removes the self-loop but not a cycle of length two or more. These graphs are structural surrogates. A cycle of edges between reason instances need not be semantically realizable by claims which literally and separately certify each predecessor; that requires a content interpretation, and a cycle alone is not an adequate coherentist account.

There is another difference between recursive propositional content and epistemic priority. If every certification must be a distinct, explicit higher-order content which embeds its certified content as a proper subexpression, ordinary finite syntax forces strictly increasing syntactic depth along the sequence. An infinite succession of available contents is then required by unrestricted repeated certification of even one reason. But this result uses the strict content-embedding requirement; a general rule about reasons can cover multiple instances and a belief about its applicability may be implicit or standing. The same general content might be used to certify several reason instances. The mere word "higher-order" does not establish syntactic increase, distinctness, or strict dependence. Syntactic growth is also not epistemic viciousness by itself: an infinitist can grant reasons of increasing depth without requiring occurrent construction of infinitely many beliefs.

A more modest credential theorist can accept a standing general principle with local recognition of its application. The decisive question is whether they still require *another actual justified belief about reason status* at every application, or whether the standing principle and the subject's operative grasp suffice. The latter may be a genuine competence/access account rather than a strong explicit metabelief requirement. Do not force it into the strict-regress branch.

### 4. A direct ground is not an arbitrary stopping point

The Agrippan concern remains: why allow one endpoint but not its contrary? There is a positive difference between stopping with a bare proposition and stopping with the presented instance in the present inquiry.

Use the earlier actual list of seven research labels and the selected visible item 1991. The narrow proposition "the displayed list is nonempty" follows from an identifiable displayed member. One need not first prove a general theory of testimony, certify every previous observation, or already believe "my observation constitutes an epistemic reason" in order to inspect that member. If the issue is whether the labels correctly report an actual repository's state, those further empirical questions matter; for the claim about the displayed collection itself, the member is directly relevant. The still weaker phenomenal case avoids dependence on the external text's reliability: an actual experienced instance satisfies the present existential whether its represented content is true or false.

Compare two candidates: (i) the bare assertion that the list is nonempty with no presented member, and (ii) an identifiable actual member in the designated collection. The epistemically relevant difference is not that one assertion was labeled an axiom or is psychologically compelling. The latter gives a truth-condition witness for the existential. In the phenomenal case, preserving the actual experience while denying all experience removes the very witness that has been retained. The positive evidence thus discriminates the conclusion from its contrary in the same scope. This answers the equal-standing concern **for this ground**, not the sufficiency or ultimate justification of every basic belief.

For the competent inquiry, actual recognition of the evidence's bearing is distinct from forming a justified separate belief about the epistemic status of that recognition. The rational-basing investigation already motivates the operative, content-guided exercise of a capacity as a positive account (and contrasts it with automatic association and bypass). A person can inspect the member, understand membership and infer the existential without articulating an epistemology. Their performance is evidence of an operative competence. The stronger rival may attribute an implicit metabelief even if they never articulate it. Lack of articulation alone does not refute that reading. To discriminate, ask whether the alleged metabelief has a separately assessable content and epistemic role: can its absence, suspension or acquisition vary while the same first-order evidence and competent grasp remain? If "implicit certification" simply means that the subject is able to apply the rule competently, the proposal has weakened to the grasp condition rather than demonstrated the necessity of a further justified belief. A nonconceptual sensation alone still does not show a propositionally available reason.

A **general** credential ("this method correctly recognizes instances of Q") does not supply an instance. A **factive specific** evidential certificate ("this presented instance is an actual instance") can entail Q, but its relevance depends on the actual instance, not just on the independent fact of holding a credential belief. In this case there is a noncircular way for the same direct ground to support both the object conclusion and a judgment about its evidential bearing: the latter can arise from grasp of the presented instance and the existential rule, rather than inference from one's already held conclusion Q or an assumed justifiedness of that conclusion. That does not automatically justify the further normative proposition that the instance genuinely counts as a reason. Nor does it show that a separate explicit credential is always irrelevant. Shared evidence is not in itself circular epistemic dependence; a certificate whose only purported ground is the very unearned epistemic status it is supposed to confer presents a different problem. Applying the demand to an actual subject requires evidence about their actual basis and not just which statements are coextensive.

This is the positive basis for the modest foundational claim: **a directly available instance can provide first-order pro tanto merit without a separately established metabelief about that merit**. The conclusion is a direct evaluative warrant judgment within the ordinary truth-directed reading, not a theorem from the semantic entailment alone. It does not assert that the subject always has sufficient warrant for assent, that a higher-order report never defeats access, or that every ultimate reason is noninferential. It preserves the prior #930 dispute over preference-independent force.

### 5. Strongest surviving rivals and the self-application pressure

- The reflective internalist can require justified recognition of one's grounds *for full rational acceptance*, yet allow the underlying pro tanto merit or standing reason to precede it. This is compatible with F6 and with the local case. Requiring a credential for sufficient warrant need not be a credential requirement for possessing every reason.
- A stronger internalist may require the credential even for a genuine reason, but let the credential be noninferentially justified without an independently prior reason instance, or give it support simultaneously from the same directly available evidence. This rejects or weakens T, not F6. It still owes an account of why such a credential is necessary beyond the competent grasp.
- An infinitist can retain C and T while denying W; potential availability of further reasons is not an actually completed finite trace. Their positive account of reason enhancement cannot simply be equated with independent prior certification of each reason. See the existing infinitist study; neither its structural compatibility nor the above proof settles adequacy.
- A holistic account may give mutually dependent judgments standing from a specified nonlocal condition. This is not the assertion that a closed cycle of opaque reason labels confers warrant by itself. It must explain what distinguishes appropriate coherence from an equally coherent contrary belief system. Our controls test only seriality and cycle, not the adequacy of that account.

The skeptical proponent cannot use C and T and W to conclude **global** reasonlessness while simultaneously conceding a genuine reason to believe C, T, W, their conjunction, or that conclusion. Any such reason is already an F6 witness; their own norm must then cover it if the scope is genuinely universal. This is the existing nihilism incompatibility (`146b502b`) plus the new explicit antecedent bundle, not an unconditional contradiction in the mere act of entertaining a view. A reason merely to suspend, a causal story about why someone withholds, or a restricted credential requirement for a particular kind of empirical report can survive. If the proponent exempts their own reason from the universal credential rule, that is a concrete scope concession, not by itself a refutation of a restricted rule. If they concede a reason but deny independent priority or well-foundedness, the incompatibility does not select which of those claims fails.

The principal insight is not an unrestricted trilemma about all justification. It is that the universal strong demand cannot both **explain away every reason** and **be rationally warranted by a belief-directed reason** within a well-founded prior-credential interpretation. This gives a separate discriminating application of F6. The direct-occurrence case supplies positive warrant for not imposing that demand on every reason; a strong credential theorist can still reject that local normative attribution. The thin reason judgment is more defensible than the claim that every justified belief is basic or that every epistemic standard is universally binding.

### 6. Reproducible structural controls (actually executed)

```python
from itertools import product

# Each node represents a reason instance of one subject. An outgoing edge is
# an independently supplied credential whose justified content has this reason.
# An edge between active reason nodes is the combined credential/justification
# link, not by itself a semantic certificate of either reason.
def inspect(n, edges, active):
    successor = lambda i: {j for j in active if (i,j) in edges}
    serial = all(successor(i) for i in active)
    distinct_serial = all(successor(i)-{i} for i in active)
    cycle = False
    for i in active:
        frontier = set(successor(i)); reached = set()
        while frontier-reached:
            v = frontier-reached
            reached |= v
            frontier |= set().union(*(successor(j) for j in v))
        cycle |= i in reached
    return serial, distinct_serial, cycle

profiles=serial_nonempty=distinct_nonempty=acyclic_nonempty=0
for n in range(1,4):
    E=tuple(product(range(n), repeat=2))
    for bits in product((False,True),repeat=len(E)):
        edges={e for e,x in zip(E,bits) if x}
        for flags in product((False,True),repeat=n):
            active={i for i,x in enumerate(flags) if x}
            serial,distinct,cycle=inspect(n,edges,active)
            profiles+=1
            if active and serial:
                serial_nonempty+=1
                assert cycle
            if active and distinct:
                distinct_nonempty+=1
                assert cycle and serial
            if active and not cycle:
                acyclic_nonempty+=1
                assert any(not any((i,j) in edges for j in active) for i in active)
print('finite dependency profiles:',profiles,'serial:',serial_nonempty,
      'distinct serial:',distinct_nonempty,'nonempty acyclic:',acyclic_nonempty)
assert inspect(1,{(0,0)},{0}) == (True,False,True)
assert inspect(3,{(0,1),(1,2),(2,1)},{0,1,2}) == (True,True,True)
assert inspect(3,{(0,1),(1,2)},{0,1,2}) == (False,False,False)

trace_cases=0
for n in range(1,11):
    for flags in product((False,True),repeat=n):
        uses=[i for i,x in enumerate(flags) if x]
        if not uses: continue
        earliest=uses[0]
        assert not any(j<earliest for j in uses)
        assert not all(any(j<i for j in uses) for i in uses)
        # A prior standing credential outside the trace is a local escape.
        assert all(any(j<i for j in [-1]+uses) for i in uses)
        trace_cases+=1
print('nonempty finite use traces:',trace_cases)

status_cases=0
for rq,bc,jc,rc in product((False,True), repeat=4):
    justified_belief=bc and jc
    require_credential=not rq or justified_belief
    j_requires_reason=not justified_belief or rc
    if rq and require_credential and j_requires_reason:
        assert rc
    if rq and not bc:
        assert not require_credential
    if rq and justified_belief and not rc:
        assert require_credential and not j_requires_reason
    status_cases+=1
print('credential status cases:',status_cases)

# General method validation and a presented instance have different truth
# conditions. The specific factive evidential certificate is NOT a normative
# reason attribution.
worlds=[(q,v,a) for q,v,a in product((False,True),repeat=3) if not a or q]
assert len(worlds)==6
Q=lambda w:w[0]; V=lambda w:w[1]; A=lambda w:w[2]
C=lambda w:V(w) and A(w)
assert {Q(w) for w in worlds if V(w)}=={False,True}
assert all(not A(w) or Q(w) for w in worlds)
assert all(not C(w) or Q(w) for w in worlds)
assert any(A(w) and not V(w) for w in worlds)
assert any(V(w) and not A(w) for w in worlds)
print('method/instance profiles:',len(worlds))
```

Executed with Python in the container: 4,164 finite dependency/active-set profiles, including 2,001 nonempty serial profiles (every one cyclic), 604 nonempty distinct-serial profiles (every one cyclic), and 1,101 nonempty acyclic profiles (every one has an active instance with no active credential successor). The 2,036 nonempty finite trace tests, 16 status assignments and six method/instance profiles passed. Counts include repeated active subgraphs within different carrier/edge assignments and are not distinct philosophical positions or research merit. The structural status controls explicitly assign the relevant normative fields; they do not establish any actual justified belief or actual agent. The trace test omits actual credential content and proves only the rank boundary for a finite closed prior-use roster. The six profiles allow actual instances without method validation and vice versa, not actual reason attribution absent a disputed calibration.

### 7. Assessment, downstream and next discriminating question

**Provisional assessment:** reject the unrestricted *independently prior reason-supported credential* requirement as a necessary condition for every reason if F6 and a well-founded credential interpretation are retained. The weaker requirement of competent access may be defensible without introducing another belief. The unrestricted justified-metabelief requirement alone has not been deductively refuted: one can allow basic metajustification, simultaneous or holistic support, or an infinite credential structure. The stronger positive warrant in the selected direct case comes from the actual instance discriminating the existential from its denial and the content-guided exercise of competence. It gives a concrete non-arbitrary stopping candidate; it does not prove that every foundational belief is justified or that the only adequate epistemology is foundationalism.

The next decisive proposition is **whether direct recognition of the bearing of an actual presented instance itself provides a noninferential entitlement to treat that instance as a reason, without a prior justified metabelief**. Compare operative rule-grasp with a separately representable implicit credential on the same episode; require the latter to explain an independent epistemic contribution, not merely rename competence. A concrete misleading assessor can motivate checking one's access, but a reason to check and a reason for the existential may coexist. Distinguish prima facie support, all-things-considered justification, and the reason's own source from reasons to believe propositions about that source. The actual first-person application and independent challenge remain required before relying on the local judgment as reviewed support. If the credential theorist accepts the local reason and only disputes preference-independent force, the dispute returns to #930; if they accept the local reason but deny independent priority, pursue the adequacy of their proposed replacement, not a duplicate structural regress theorem.

Downstream: F6 `f56b2ee7`, its exact global rival `38f44eff`, and the existing calibration `6b4e3331` retain their status. The new conditional incompatibility uses F6 as an input; do not use it to establish F6 against the rival circularly. For a positive actual reason witness, the existing `b50727e1` route to `56f68b40` and `72391d4d` still requires selected-world presence and esse; neither the well-founded credential comparison nor a possible basic epistemic reason implies a well-founded metaphysical causal order, an ontic PSR, necessary existence, or a personal source. No graph edge, claim, definition, proof registration or floor marking changed.

The prior head's CI run 45639133212 completed successfully; that is prior-head evidence, not this checkpoint's CI or a certification of these proposed applications. Reconfirmed no local Lean/Lake/Cargo and GitHub DNS failure via `git ls-remote`; no prepared checkout or independent review worker. Full CLI preflight, local conventions verification and independent semantic challenge pending. On the prepared clone reuse `target/release/truth context LOGIC-JUSTIFICATION-INTROSPECTION`, `context REGRESS-SCHEMA-PACKAGE`, `context b3ddb7c4`, `dossier f56b2ee7`, `related f56b2ee7`, `brief f56b2ee7`, `semantics f56b2ee7`, and `novelty "belief-directed reason requires a separately justified prior credential"` before proof registration. No new mechanically checked conclusion or actual frontier delta is claimed; the proposed proof is an unelaborated local application. Self-sweep: C/T/W separate, no scope expansion from actual trace to lifetime, no assumption that justification always requires a prior reason, no model over-reading, no attribution beyond the existing notes, no categorical force or metaphysical grounding transfer. Keep #1995 draft; do not merge.


## Graph registration: credential incompatibility and the warrant consequence

The owner requested reusable graph arguments. The Challenge was frozen in
`2833b5f83d2564155af03e9735deb8a2eaaa687a` before the Solution;
the registered graph checkpoint is `a9626d5d7da6205b4f7243395226e9ea470a7994`.
See [batch specification](../../specs/epistemic-credentialing.toml) and
[Solution](../../TruthCore/Results/Logic/EpistemicCredentialing/Solution.lean).
These are solution-present **draft** registrations, pending kernel, binding,
Comparator/NanoDa and independent semantic review, not established premises.

| Statement/result | Exact content |
| --- | --- |
| [C](../../corpus/statements/ffb08b22-4304-472d-b9e7-a49d8d34fbd3.json) | Each active attributed belief reason has a believed, warranted credential about that instance. |
| [T](../../corpus/statements/4e30a1c1-0402-4155-8a57-a1df8af7daf6.json) | Each such credential for an active reason has an actual prior attributed reason for its content, for the same subject. |
| [W](../../corpus/statements/89607c0b-af1e-4dbd-ad30-a32bf0303261.json) | The supplied epistemic priority relation is well-founded for each subject. |
| [134bb9d9](../../corpus/results/134bb9d9-335f-443b-a7c1-9ee8d5450bfa.json) | Existing consideration presentation `1b74e22c` + C + T + W entail existing thin nihilism `38f44eff`. |
| [2efdb275](../../corpus/results/2efdb275-6cb9-48d9-92dd-56c6dbd06e4c.json) | F6 + presentation + T + W entail the exact negation of C (`d008f164`). The conditional refutation relation points to C. |
| [97736a08](../../corpus/results/97736a08-f098-4525-88c0-d5a72dbe7e59.json) | The full five-member conjunction is incompatible. The result has no premises because its conclusion is the negation of that conjunction, not because any member is established. |
| [25e0c5b2](../../corpus/results/25e0c5b2-ed95-4563-994f-1d103a96eade.json) | Thin nihilism + `0e2bbd59` (warrant requires surviving support) + `6b4e3331` (surviving support supplies a belief reason) entail `cbe1661b`, no warranted acceptance in that ReliabilityFrame. Composes existing `b3ddb7c4` and `146b502b`. |
| [1583ce3d](../../corpus/results/1583ce3d-4c08-4a3b-a81a-50f2f52e9cdc.json) | Four finite omission interpretations and one infinite strict transitive successor-priority interpretation isolate each of the five members. |

The new credential data extends the existing epistemic-reason Frame without
redefining Reason or warrant. T uses the same subject and credential content;
it does not follow from a justified credential alone. W is an explicit open
order premise. The infinite omission is a structural surrogate: successor
contents are assigned reason and warrant status, not proved to possess actual
infinitist warrant. The other omissions are finite, including a thin reason
without consideration presentation. The resulting incompatibility is not a
pairwise contradiction between F6 and C.

For later belief-warrant disputes, an opponent who demands indefinitely more
independently prior reasons must distinguish a particular request for evidence
from the universal credential policy. Under the latter policy, T, W and
presentation, no thin belief reason survives. If their warrant account also
requires the two existing calibrations, no warranted acceptance survives
either. Conversely an actual warranted acceptance under those calibrations
supports F6, and F6 excludes C when T, W and presentation hold. This composition
requires matching agent/content carriers and the identical thin reason relation
between the credential and reliability frames. It does not establish those
calibrations, F6's independent warrant, or any metaphysical well-foundedness.
Do not use the F6-dependent negation to defend F6 circularly. The new conditional
refutation of C does not count as a defended floor conclusion merely because
it was registered. No root premise or floor metadata is changed.

The positive question remains whether actual direct grasp of a presented
instance supplies a noninferential reason without an independently prior
justified metabelief. The existing F6-to-concrete-population route remains
separate. No unsupported arbitrary-frame executable configuration is added:
the current configuration registry restricts admitted parameter profiles;
the exact bundled theorem, named argument premises and omission controls
provide the reusable comparison.

Verification: the GitHub connector reread each of the five result, argument,
inference and Comparator records. Their IDs, ordered premise lists, conclusion
IDs, theorem names, empty permitted-axiom lists and NanoDa settings matched the
intended declarations. Both relation endpoints and predicates were checked.
Challenge/Solution declarations were preserved when replacing the five sorry
bodies. This is a structural registration audit, not Lean verification.
The local environment cannot resolve github.com and lacks a prepared clone,
Lean/Lake/Cargo. The records and import lists were produced remotely according
to the inspected batch schema and import-rendering rules; the canonical
generators and local corpus tools could not run here. Before relying on this
draft, on a prepared clone run:

```sh
python3 scripts/worker_env.py --check
python3 scripts/argument_batch.py records specs/epistemic-credentialing.toml --write --fix
scripts/root-imports.sh --write
cargo build --locked --release -p truth
lake build TruthCore.Results.Logic.EpistemicCredentialing.Solution
target/release/truth check
python3 scripts/bundle_audit.py
target/release/truth bind-check --result 134bb9d9-335f-443b-a7c1-9ee8d5450bfa
scripts/verify-result.sh 134bb9d9-335f-443b-a7c1-9ee8d5450bfa
target/release/truth bind-check --result 2efdb275-6cb9-48d9-92dd-56c6dbd06e4c
scripts/verify-result.sh 2efdb275-6cb9-48d9-92dd-56c6dbd06e4c
target/release/truth bind-check --result 97736a08-f098-4525-88c0-d5a72dbe7e59
scripts/verify-result.sh 97736a08-f098-4525-88c0-d5a72dbe7e59
target/release/truth bind-check --result 25e0c5b2-ed95-4563-994f-1d103a96eade
scripts/verify-result.sh 25e0c5b2-ed95-4563-994f-1d103a96eade
target/release/truth bind-check --result 1583ce3d-4c08-4a3b-a81a-50f2f52e9cdc
scripts/verify-result.sh 1583ce3d-4c08-4a3b-a81a-50f2f52e9cdc
target/release/truth dossier ffb08b22-4304-472d-b9e7-a49d8d34fbd3
target/release/truth dossier d008f164-5e50-480e-aa5c-888c5ca652ce
target/release/truth context 134bb9d9-335f-443b-a7c1-9ee8d5450bfa
target/release/truth context 25e0c5b2-ed95-4563-994f-1d103a96eade
target/release/truth frontier-diff --base "$(git merge-base HEAD origin/main)"
```

Independent challenge must inspect the credential semantics, exact same-subject
instance, prior-reason and warrant interpretations, omission controls and
cross-frame composition. Do not mark the PR ready or merge without those
checks. No new computed frontier delta is claimed.
