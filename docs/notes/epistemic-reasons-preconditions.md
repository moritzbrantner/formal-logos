# What must obtain if there are epistemic reasons?

Analyst investigation for [#930](https://github.com/moritzbrantner/truth-core/issues/930),
2026-11-05. F6 is accepted common ground; this note does not reopen its defense.
Attribution is deferred. The conceptual arguments are offered for assessment,
not claims about a historical author's view. The dated conditional-encoding
section below now links checked logical and finite-model results, without
certifying actual normative warrant.

**Conclusion:** accepting epistemic reasons commits us to actual epistemic
favoring: some consideration makes a belief or other relevant attitude better
supported in an epistemic respect. Under the ordinary factual-belief reading,
that respect concerns answering the question correctly or being warranted in
one's answer. A mere propensity to produce belief, or the desirability of
having it, cannot by itself fill that role. This is a constraint on adequate
accounts of reasons, including reductive accounts. It does not establish an
irreducible normative substance, a personal ground, or a reason to seek truth
that overrides every other consideration.

## Three starting points that must stay distinct

1. **Thin encoding.** `STMT-THERE-ARE-EPISTEMIC-REASONS` is
   `TruthCore.Logic.EpistemicReasons.ThereAreEpistemicReasons Reason`, defined as
   `∃ a p, Reason a p`. `Reason a p` means that agent `a` has an epistemic reason
   to believe content `p`. The declaration does not encode a particular
   consideration, truth conditions, support, desire, causation or authority.
   An arbitrary nonempty relation satisfies the formula. Logic alone cannot
   recover the missing interpretation from its name.
2. **Ordinary epistemic-role interpretation.** The accepted existential is
   understood as about considerations counting in favor of attitudes *as
   answers to a question*, rather than merely making those attitudes pleasant
   or producing them. The argument below explains and defends this reading.
   It is semantic and philosophical work additional to the bare Lean formula.
3. **Preference-independent reasons.** Whether at least some epistemic
   support retains pro tanto force for a person who does not want an accurate
   answer is a stronger question. Objective here means this limited
   independence from the subject's desire for the supported answer or for
   accuracy; it does not mean agent-neutral, infallible, overriding,
   irreducible, or independent of every mental/social fact. This independence
   is argued separately in #930; F6's encoding does not specify it.

A genuine goal-relative epistemic reason can meet interpretation 2: its
favoring holds relative to a truth-directed project. Someone who denies even
such favoring denies F6 in this reading. Someone who accepts it but denies 3
is a surviving rival. No change of terminology settles that disagreement.

The transcendental inference is: **there is an epistemic reason; an epistemic
reason cannot obtain without C; therefore C obtains.** It requires a warranted
second premise. Believing the first gives a rational commitment to established
prerequisites; it does not show that one already explicitly believes every
prerequisite or accepts a theory called transcendentalism. Nor does `P → C`
establish that C exists necessarily, at every possible world.

The ordinary-role existential is registered separately as
`STMT-THERE-ARE-ORDINARY-ROLE-EPISTEMIC-REASONS`; the stronger authority
existential as `STMT-THERE-ARE-PREFERENCE-INDEPENDENT-EPISTEMIC-REASONS`.
Both remain **OPEN** as actual normative-instance claims. Conditional calibration
results and finite comparison controls are now encoded, without a new self-evidence
marking or transfer of F6 approval. `DISAMB-EPISTEMIC-REASON-EXISTENCE-ROLE-AUTHORITY` links their three
precise sense definitions and identifies their relationship to unchanged F6.
The earlier version left these analyst propositions without Lean declarations
because encoding would not establish their instantiation or philosophical warrant.
That was an unnecessary obstacle to the owner’s conditional-definition investigation:
they now bind `SomeOrdinaryReason` and `SomePreferenceIndependentReason` in
`Logic/EpistemicReasonDefinitionFork.lean`. The additional consideration-presentation
and meaning-calibration propositions remain explicit open inputs. `interpretation_of` is a source-claim relation, so no
such attribution record is fabricated for this analyst fork.

## A complete argument: support cannot be replaced by production

Consider the factual question whether a jar contains an even number of tiles.
An intelligible, competently obtained count can favor the answer “even.” A
pleasant picture, selected without examining the jar and offered solely to
make that answer attractive, does not thereby support that answer. Both can
influence belief. The contrast concerns their epistemic bearing, not how
strongly they influence someone. A count can fail to convince; an attractive
picture can convince very effectively.

The argument has three premises:

- **A.** Some consideration really is an epistemic reason for some attitude
  (accepted F6, interpreted as above).
- **B.** A consideration is an epistemic reason only if it counts in favor of
  its target in a respect relevant to answering the question correctly or
  being warranted in the answer. Warrant allows uncertainty, defeaters and
  justified error; it is not defined as guaranteed truth.
- **C.** Merely causing an attitude or making its possession rewarding does
  not, by those features alone, supply that favorable bearing.

Therefore **some actual epistemic favoring obtains, and any adequate account
must accommodate the favorable bearing rather than substitute sheer causal
influence or reward for it.** The conclusion concerns at least one reason and
its role. It does not assert that all subjects have reasons for every question.

**Why accept B?** A factual belief presents an answer as how things stand.
Enjoying an imagined answer is a different attitude even if the sentence and
pleasure are the same. An assessment of a consideration *as a reason for the
factual answer* must therefore bear on the answer's epistemic merits. If an
account says only that the consideration makes the answer desirable or
psychologically inevitable, it has changed which success it explains. This
is a reason to retain B rather than a stipulation that every truth-directed
practice already generates categorical duties. B concerns what qualifies an
already accepted epistemic reason, not why anyone must enter the practice.

**Why accept C?** The count can favor “even” for someone who remains
unconvinced, while reassurance can produce that belief without supplying
information about the tiles. Favoring and production thus answer different
questions. Similarly, a reward for believing “even” tells us what would pay,
not whether the jar contains an even number. Rewards can become evidence:
for instance, a trusted observer's offering the reward only after counting.
Then their epistemic bearing comes from the informative connection, not from
the reward's desirability alone. This argument excludes a *bare* production
or reward account. It does not exclude an account that explains favorable
bearing through natural causal relations that reliably track the answer.

A and B supply the positive conclusion; C identifies the explanatory
constraint on accounts of it. This is conceptual and case-based warrant,
not a Lean derivation of normativity from descriptive facts. B is defended
here but remains open to philosophical challenge, not newly classified as
self-evident. No new root premise or closure is registered.

## Why these are prerequisites, and what they exclude

The necessity claim is stronger than saying that support would be useful.
Remove the assessable target altogether and there is no answer or attitude
for the alleged reason to favor. Remove every favorable bearing and the
consideration no longer counts in favor of that target in any epistemic
respect; only producing, liking or describing the attitude remains. Remove
applicability to every subject/target and there is no instance left to satisfy
F6 in this reading. Thus denying each *thin role condition entirely* removes
the accepted kind of reason, rather than just making reasoning harder.
This does not require that all targets have only one permissible attitude,
that favoring is comparative in a total ordering, or that all reasons are
evidence in the narrow sensory sense.

A more discriminating consequence is available with one further premise:
**in an ordinary undefeated counting case, relevant contrary observations can
change which answer is supported while the person's desires stay fixed.**
This is evidence-responsiveness. Compare a person who wants an even total and
carefully counts an even total with a person with the same desires who
carefully counts an odd total, with competence, background and defeaters held
fixed. The latter observation does not become support for “even” merely
because the person still wants it. Observation is relevant because it bears
on the total; bare wishing supplies no such bearing. This is an independently
motivated contrast, not a claim of demonstrated metaphysical duplicates.

If reason direction were a function of desires *alone*, equal desires would
always give the same direction. Evidence-responsiveness supplies equal-desire
cases with different support; the two conditions cannot both hold. Hence
**desires alone cannot determine epistemic support in those cases.** This is
a conceptual application of the existing equal-data fiber condition in
`CorrectionCriterion`, not a new mathematical theorem or registered finite
model. The additional responsiveness premise does the philosophical work.
F6 by itself does not ensure such contrasting cases exist.

The result leaves the strongest instrumental rival intact: desires can
select the goal, while evidence determines which answer serves that goal.
It excludes only a desire-only explanation of support, not every goal-relative
account and not reliable causal/naturalistic constitutions that include the
relevant evidence relations. If the rival denies that factual endorsement
has any epistemic merits apart from desire satisfaction, it rejects B; if it
accepts those merits but restricts their force to chosen projects, the
remaining dispute is preference-independent authority.

## Strong objections and what they change

**“You have defined normativity into reasons.”** F6 already accepts some
reasons, rather than merely some beliefs. Extracting their favoring role is
legitimate if that is what was accepted. It would be circular to use B to
convince a global nihilist that reasons exist, or to derive categorical
reasons from merely participating in inquiry. This argument does neither.
Its substantive test is whether an account preserves the distinction between
a consideration supporting an answer and one merely producing it. An owner
who meant only a causal disposition by F6 would need to select that different
starting meaning; ordinary epistemic favoring would then remain unestablished.

**“Reliability is natural and causal.”** Agreed: perceptual and testimonial
mechanisms may make considerations epistemically relevant by connecting them
to the subject matter. A naturalist can propose that reliable, appropriately
functioning belief formation constitutes the relevant support. C does not
require causal duplicates with different reasons, or show that no natural
property realizes the normative role. The open burden is to explain why the
specified reliability/function counts as epistemic support, including
accidental reliability and misleading-environment cases. Those challenges
are not a refutation of every possible naturalist explanation.

**“A false belief can be justified; truth connection is too strong.”** B
requires bearing on correctness or warrant, not actual truth of the favored
answer, known evidence, increased numerical probability in every case,
knowledge, or a perfect method. A misleading but competently used count can
justify an incorrect answer. Logical or mathematical reasons need not supply
new statistical information. Particular accounts of justification may place
different restrictions on cases; nothing here settles internalism,
externalism or whether reasons themselves must be facts.

**“The standard applies only if I want the truth.”** This is the strongest
surviving authority objection. B and C do not defeat it. One may accept
truth-relative epistemic support yet deny any reason for the indifferent
agent to follow it. The positive response in #930 is that factual endorsement
continues to answer a question even when a comforting error is useful. That
supports correction as an epistemic merit; the additional conclusion that
this merit retains normative force without the agent's project remains a
separate argued bridge. Accuracy mathematics alone cannot settle that bridge.

**“A reason must be accessible or motivational.”** Reasons one has,
justification available to one, rational belief based on a reason, and actual
motivation are different. F6 does not quantify over reasoning performances.
This investigation establishes no universal access condition. It also does
not deny that an adequate particular account might require some availability.

## Ranked necessary conditions

“Entailed” below means entailed under the indicated interpretation, not a
new kernel-verified result or a globally accepted philosophical necessity.

| Candidate | Status and precise scope |
| --- | --- |
| A subject, a target content/attitude, and an applicable instance of favoring | Entailed by accepted reason existence in its intended reading. Formal existential witnesses alone do not prove physical agents actually exist; an actual-world interpretation would have to say what the domain represents. The subject need not already believe the content. |
| Epistemic assessability of the target | Entailed under interpretation 2: there must be something for the answer or attitude to get right, or a warrant standard relevant to it. This does not require a complete theory of truth or an accessible exact test. |
| Favorable epistemic bearing rather than mere production or payoff | Entailed under B; B and C have the independent semantic/case argument above. No irreducibility is inferred. |
| Relevant applicability to that subject/target/circumstance | Entailed in the ordinary reading of a reason *for* someone. Not every reason applies to everyone; more information or different circumstances can alter what is supported. No universal impartiality follows. |
| Some favoring independent of the subject's desire for accuracy | Independently argued but open; supplied only if interpretation 3 is selected and defended. It is not guaranteed by the thin F6 formula or B. |
| Preference-independent favoring for the selected objective reason | Entailed once interpretation 3 is accepted. Cross-agent invariance needs relevant circumstances fixed and a further argument. |
| Belief-independent truth conditions for every possible content | Not established. Factual truth can concern mental or socially constituted facts; there is no inference to a comprehensive correspondence metaphysics. |
| Actual possibility of epistemic error, disagreement, correction or a second agent | Not necessary on the present premises. A reason can favor a true answer even if its subject never errs; the examples diagnose meaning without establishing that all reason-bearing settings admit error. |
| Factivity of every reason or truth of every supported belief; logical omniscience; infallible access | Not established. These strengthen F6 and B. |
| A normative role with no possible natural/functional realization | Not established. Role indispensability does not imply ontological irreducibility. |
| A truthmaker, universal PSR, necessary individual, personal author, overriding duty or moral realism | Not established. Each needs a distinct defended bridge; none is a prerequisite demonstrated here. |

## Which explanatory options remain?

A reliable natural/functional account can explain the epistemic bearing through
world-tracking and cognitive function; it still owes an account of its
normative significance. An irreducible impersonal account can take favoring
facts as basic; irreducibility itself is not established. A constitutive or
practice account can explain how correctness organizes factual endorsement;
it still owes the bridge from the role to authority for an indifferent agent.
A goal-relative account can retain reasons within a chosen epistemic project
while denying that last bridge. These are serious explanatory options, not
Lean models establishing metaphysical possibility, and not equally complete
merely because listed. A personal-ground account is another option requiring
its own explanatory case. Global error theory conflicts with accepted F6;
self-undermining alone has not refuted it.

The result is positive but limited: **an account which eliminates every
instance of epistemic favoring fails to accommodate the accepted starting
point; an account which explains favoring by natural facts need not eliminate
it.** “Real” here means that the favoring claim is actually correct in the
selected sense. It does not prejudge substance, reduction, truthmakers or
mind-independence. A theory must preserve this role or explain openly why it
rejects F6; no ontology is selected simply by naming the role normative.

## Exact reuse, rejected proof and remaining question

Read F6's related search and dossier, the existing nihilism result, and the
#929 access/agency boundaries. The exact existing retorsion is
`TruthCore.Results.Logic.EpistemicNihilismRetorsion.nihilismSelfUndermining`:
nihilism entails no reason to believe nihilism, not its falsity.
`TruthCore.Results.Logic.CorrectionCriterion.characterization` concerns an
exact extensional classifier iff correctness is invariant on equal-data
fibers. It does not give human access or bind an agent to a norm.
`TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess.boundary` and
`TruthCore.Results.Logic.TranscendentalPractice.AgencyDuty.boundary` preserve
those access/authority distinctions. #756's epistemic/ontic boundary, #932's
discursive-authority investigation and #933's grounding question remain
separate; no undelivered bridge from them is used.

The merged PR #1045 argument is linked in
[the correction note](epistemic-reasons-930.md). It was inspected read-only at `ffe53ec53150bacad511a1a5ff1b8b2fcb926993`,
contains the earlier #930 argument and mathematical accuracy controls. Its
proofs are not imported or restated here. No accuracy cost has been used as a
normative premise in this investigation.

A new Lean theorem `∃ a p, Reason a p → ...` deriving nonempty domains would
add no philosophical content. Adding a new predicate “epistemic favoring” and
assuming `Reason → Favoring` would merely transcribe B. Those decorative proof shapes remain rejected. The subsequent conditional
encoding instead separates assessability, applicable considerations, favoring,
production, reward, and preference-indexed force; it includes calibration
propositions, a checked definition fork and concrete comparison controls. These
controls do not certify actual normative warrant. The two consequential analyst
readings remain separate open statements with linked definitions and disambiguation. This note and the linked attempt preserve the argument rather than
advertise a manufactured proof count.

Premise comparison: F6 retained as accepted common ground. B adds the openly
defended ordinary-role interpretation; C defends a distinction used to assess
explanations. Neither is classified as a newly closed premise. Preference
independence is not added as an undisputed input. No philosophical or root
premise is discharged; the original two open sibling statements and their sense records added
reusable interpretation metadata. The later conditional encoding below adds
formal inferences and models, while preserving open actual-instance and
authority burdens and adding no root route.

The next consequential question in #930 is whether being an epistemic merit
of factual endorsement itself supplies a pro tanto reason for a person wholly
indifferent to accuracy. The goal-relative reply must be answered on its own
terms. Ontological grounding is downstream of fixing that authority claim.


## Encoded definition comparison (owner clarification, 2026-11-06)

`TruthCore.Logic.EpistemicReasonDefinitionFork.Frame` keeps F6's thin
`Reason : Agent → Content → Prop` independent of the consideration-indexed
`CountsAsReason` relation. `ConsiderationPresentation` is the explicit bridge
from a thin belief reason to some consideration attributed as a reason for that
belief. It is needed: the `unpresented` control has a nonempty thin relation and
a vacuously correct ordinary calibration but no attributed consideration.

Four candidate definition propositions calibrate `CountsAsReason`: ordinary
epistemic role, preference-independent role, bare production, and bare reward.
These are pointwise semantic conditions on one fixed profile, not a census of
historical schools. The normative relations `favors` and `force` remain
independently interpreted inputs. `favors` means that the consideration makes
the attitude better supported as an answer under the selected epistemic standard;
`force` means that it counts pro tanto in favor of taking the attitude for the
subject with the supplied preference. This is distinct from psychologically
producing that attitude or paying for it. Whether a concrete consideration
actually warrants the judgment, and how its authority is constituted, remain
philosophical application burdens; the model names do not discharge them.

The exact statement
`STMT-EPISTEMIC-REASON-DEFINITION-CANDIDATES-COVER` says that at least one of
these calibrations holds. Its complementary
`STMT-EPISTEMIC-REASON-ADDITIONAL-DEFINITION-REMAINS` says that none holds in the
selected profile. Excluded middle gives their structural fork, not the stronger
claim that the named list alone covers all relevant interpretations. The latter
can be used as an explicit open premise in a conditional elimination: if bare
production and reward are rejected, one of the two role analyses remains.
Together with F6 and consideration presentation, either supplies an ordinary-role
witness. The calibration transport and structural-coverage results are explicitly
labelled transcriptions; they do not independently defend the calibrations.

The checked `BoundaryCertificate` retains its named finite profiles:

- `goalRelative`: a count is attributed and favors a belief without producing
  it, and its favorable bearing can coexist with the content being false.
  Actual pro tanto force holds at the supplied accuracy preference, but fails
  at the comfort preference. This is a formal illustration of the role/authority
  distinction, not evidence that an actual mistaken count is warranted.
- `independent`: exactly the same profile with only the `force` field changed.
  The ordinary reason now has force at every supplied preference. No change to
  evidence or factual truth produces this stronger commitment automatically.
- `bareProduction`: reassurance is attributed as the reason because it produces
  and rewards belief; the epistemic-favoring relation still selects the count.
  The production and reward calibrations hold but there is no attributed reason
  satisfying the ordinary role. Thus those calibrations plus thin F6 do not
  entail the stronger ordinary-role existential.
- `compatible`: production, reward, ordinary role and independent force are
  coextensive in one interpretation. This prevents the insufficiency controls
  from being promoted to a blanket refutation of natural or functional accounts;
  coextension does not establish property identity or a metaphysical reduction.
- `remaining`: thin reason attribution is nonempty and has a consideration
  presentation, while all four calibration propositions fail. This is a genuine
  counterprofile to named coverage. It is a rival only to that coverage claim,
  not automatically to every claim about actual epistemic support.

`EP-ROLE-INDEPENDENT-STRENGTHENS-ORDINARY` registers the exact strength order
between the two existential statements: forgetting preference-independent force
retains the ordinary-role witness. This does **not** order their calibration
propositions: the calibrated attribution relation may contain fewer instances
under the strong definition, so the two analyses need not be coextensive.

No owner approval, new source claim, actual warrant, overriding duty, or root
closure is supplied by this batch. Source attribution remains deferred. The
remaining research is to discriminate the actual calibrations and their
admissible preference class, not to wait for the owner to choose a word meaning
before studying its consequences.

## Authority continuation: evidence, incentives and an indifferent believer (2026-11-17)

**Proposed outcome for the coordinator's independent semantic challenge.** At
baseline `956c8280973ea7d9ed085de07c6b2b50c4c9cf06`, the next test in
[epistemic-authority](epistemic-authority.md#connection-plan-unconnected) has a
positive goal-relative answer: a content-sensitive account can distinguish
evidence from an incentive without assigning preference-independent force to
either. This removes an alleged explanatory necessity of the authority bridge;
it does not refute that bridge. The overall judgment on
`2ca463c2-bd1f-5a13-a395-0e2c57a5ad8f` remains **underdetermined**. Ordinary
correction judgments supply prima facie support for authority, but correctness,
incentive discrimination and actual rational basing do not themselves decide
between that judgment and its strongest instrumental interpretation. F6 is
retained throughout. No ontological or root inference is supplied.

### Reconciliation and fixed question

#930's current comment records #1045/#1046/#1068 as merged. The subsequent
authority comparison already contains the registered
`EpistemicAuthority.goalRelativeExcludesAuthority` and `controls` results
(`3f585aa7-636f-4a79-8eab-3f7925367f8d`,
`2930b66a-b5e3-4f3f-b2d3-758d84c0e54d`). Their frozen types were inspected
through `context`; no new certification of those unchanged proofs is claimed.
The target's `related`, `dossier`, `brief` and a novelty search also retrieve
the prior definition-fork and moral/epistemic-parity investigations. The
ordinary-role and F6 dossiers were inspected. The target has no registered
root route; F6 does. This continuation serves the proposed preference-independent
reason bridge toward #933/#143, rather than claiming that bridge already exists.
The separate sense-registration repair in #1376 is not undertaken here.

Fix one factual question, its evidence, competence and defeaters. Vary whether
the subject wants an accurate answer or instead wants a comforting belief.
Indifference means absence of an accuracy end relevant to this question,
including an instrumental need for its accuracy; it does not mean lack of
belief, absence of all motivation or inability to reason about other matters.
The target is an actual **pro tanto reason for this believer**, not merely a
correct answer, an obligation to inquire, a full-belief license, motivation or
access to all the relevant facts. A local result is not automatically the
target's invariance across *every supplied* preference alternative.

### A positive replacement account of the evidence/incentive distinction

Use a binary fact W, an imperfect report S and a reward offer B. W and B are
independent fair bits. Conditional on either W, S matches W with probability
3/4. B offers a fixed benefit for acquiring the belief W=1, regardless of W;
it is an independent incentive, not payment conditional on an accurate answer.
The eight worlds (W,S,B) have weight 3/16 when S=W and 1/16 otherwise. The
weights are positive and sum to one. The distribution and interpretation are
analyst assumptions, not measured reliability, warranted human priors or a
psychological account of acquiring beliefs voluntarily.

| Observed report S | Offer B | P(W=1 given S,B) | P(W=1 given B alone) |
| --- | --- | --- | --- |
| 0 | 0 | 1/4 | 1/2 |
| 0 | 1 | 1/4 | 1/2 |
| 1 | 0 | 3/4 | 1/2 |
| 1 | 1 | 3/4 | 1/2 |

Here there is a concrete basis for separating the roles: S discriminates the
world states; B changes the payoff of a belief without discriminating those
states. On the supplied probabilistic support criterion S favors its matching
answer, and B alone favors neither answer. A goal-relative account can accept
that support assessment at *both* preference alternatives while assigning
epistemic pro tanto force only at the accuracy alternative. At the indifferent
alternative it grants the report's support relation but denies that this
supplies the subject a reason to conform. A practical reason to cause a
comforting belief, if granted, need not be a reason supporting its content.
No cardinal aggregation of practical and epistemic reasons is assumed.

This account does not label comfort wrong-kind merely because it is comfort.
If a reward is offered only when a competent observer has found W=1, learning
of the offer can instead discriminate W. The same event can then have an
evidential role and an incentive role. It counts on the evidential side because
of that informative dependence; changing the reward's attractiveness alone
does not supply it. Conversely, when S is made independent of W, its displayed
evidential advantage disappears. These explicit changes identify what matters
to the classification rather than assuming that reports are always evidence
or rewards never are. Actual warrant for an agent to use the distribution is
a further question.

The construction answers a structural challenge to instrumentalism: **the
right-kind/wrong-kind distinction does not require that the support relation
already have force for every preference.** It supplies a positive explanatory
mechanism in this finite domain. It is not evidence that actual evidential
merit lacks normative force, a complete naturalization of personal belief,
or a metaphysical possibility proof of a wholly accuracy-indifferent person.
The checked old `goalRelative` frame already separates the latter force field;
the new calculation gives the support distinction determinate informational
content instead of another arbitrary favoring flag.

The following exact-rational enumeration reproduces the four rows. It also
checks both possible supported answers at both aim settings. This is a finite
Python calculation, **not** a new Lean/Comparator/NanoDa certificate or corpus
model registration. No threshold-to-full-belief inference is made.

```python
from fractions import Fraction as F
from itertools import product

rows = [(w, s, b, F(3 if s == w else 1, 16))
        for w, s, b in product((0, 1), repeat=3)]
assert sum(m for _, _, _, m in rows) == 1

def posterior(test):
    selected = [(w, m) for w, s, b, m in rows if test(w, s, b)]
    return sum(w*m for w, m in selected) / sum(m for _, m in selected)

assert posterior(lambda w, s, b: True) == F(1, 2)
for s, b in product((0, 1), repeat=2):
    q = posterior(lambda w, x, y: x == s and y == b)
    assert q == F(3 if s else 1, 4)
    assert posterior(lambda w, x, y: y == b) == F(1, 2)
    print(s, b, q)
    for aim, answer in product((False, True), (0, 1)):
        merit = (answer == s)
        force = aim and merit  # the rival's explicit normative assumption
        if not aim:
            assert not force
```

The probability identities are calculated; the last force rule is stipulated
and checked for its consequences, not inferred from the probabilities. A new
theorem merely replaying that rule would not warrant it. The existing
`goalRelativeExcludesAuthority` already supplies the relevant conditional
consequence from `GoalRelativeForce` and `IndifferenceAvailable`.

### What the constitutivist and basing routes add

The issue's constitutivism challenge was read in Côté-Bouchard,
[*Can the aim of belief ground epistemic normativity?*](https://link.springer.com/article/10.1007/s11098-016-0657-8),
§§3–5, pp.3187–3195 (2016; DOI 10.1007/s11098-016-0657-8). He separates
functional, personal-aim and normativist versions. The functional version needs
a reason to function properly; the personal version cannot simply identify
belief formation with a desire or intention for truth; correctness under a
constitutive norm still leaves its reason-giving authority to explain. His
target is a general necessary-authority grounding strategy, not a refutation
of our weaker existential. This consulted primary-source lead is retained for
research; formal historical attribution and passage/claim registration are
deferred. The constructions and assessment here are ours.

The live consequence is precise. Showing that factual belief has a correctness
condition identifies its subject matter; showing that the agent necessarily
has some beliefs identifies participation. Neither shows that this particular
belief must improve to preserve agency. A general practical need for enough
accurate beliefs can support selected accuracy-promoting measures, yet leaves
the harmless, unused tile belief untouched unless its accuracy contributes to
that need. That is the relevant scope difference, not a generic assertion that
constitutivism might fail. Defending an irreducibly normative constitutive
condition is a legitimate positive proposal, but then its reason-giving
content must be warranted rather than inferred from a purely functional aim.

#1646's [rational-basing findings](epistemic-underminer-boundaries.md#rational-basing-the-particular-transition-must-exercise-the-capacity)
add personal understanding, actual procedural exercise and effective uptake,
distinguishing an inference from a matching bypass. They strengthen an account
of **how** evidence actually governs a belief; they do not say that every
evidence-responsive performance has preference-independent authority. The rival
can grant such basing in accuracy-directed inquiry and its absence in a
wishfully acquired belief. Calling the latter poorly based need not contradict
its denial of force for an indifferent subject. Conversely, a naturalized
account could identify objective evidence-responsiveness with reason-giving
merit and accept authority. Naturalism and goal-relativity are not equivalent
positions; an account of content/basing is compatible with either force rule.

### Walk the remaining positive argument and its rival

The strongest positive case remains the ordinary correction judgment: a
competent indication against an already endorsed factual answer counts against
maintaining that answer even when its bearer would prefer the error. Its
prima facie support comes from our assessments of this very endorsement as
mistakenly maintained, and our recognition of contrary evidence as a reason
despite the absence of a payoff. This can be a basic evaluative recognition;
it need not first be deduced from a prior proof of every norm. It is stronger
than observing that S carries information, however, and must not be presented
as the uniquely possible explanation of that observation.

The rival's positive response now has three articulated components: the
informational relation explains support direction; the factual-belief role
explains why this standard evaluates this attitude; the subject's ends explain
when the standard gives the subject a reason. It can therefore explain the
preference-invariant *classification* of poorly supported belief and deny the
preference-invariant *reason for its holder*. This targets the inference from
the former to the latter, with an actual replacement mechanism rather than a
merely conceivable error. Its commitment is to withhold that reason in the
genuinely indifferent case. No contradiction with thin F6 or the checked
accuracy results has been identified. Calling this commitment a defeat simply
because it denies the proposed bridge would beg the question.

A further possible defense appeals to the good of successful understanding
for its bearer. In an understood count, answering the question successfully
specifies a positive cognitive achievement, not merely a source of pleasure.
This supplies a candidate bearer-good explaining the correction assessment.
It still needs the normative premise that this good supplies its bearer a
pro tanto reason even when unwanted. Merely replacing “correct” by “good as a
belief” has not supplied that premise: the rival already grants that evaluative
classification. A bearer-good argument must establish why this good has that
force, rather than assume all functional success is reason-giving. Nor does a
common causal origin of the capacity and its good answer that question without
a causal-to-normative bridge, as #1646 explicitly recognizes.

Thus the attempted inferential routes converge: evidence/incentive separation,
functional constitution, agency participation, and actual basing all provide
substantive information, but none of the inspected arguments transfers it into
force for the indifferent bearer without the same evaluative commitment.
Retorsion does not break the tie: the rival can reason under its actual aim
without accepting force at another preference. This is a documented limit of
these approaches, not proof that authority cannot be basic or otherwise defended.

### Proposed judgment, self-sweep and reassessment

The comparative improvement is a successful response to the earlier demand
that instrumentalism explain the evidence/incentive distinction. That demand
alone no longer favors preference-independent authority in the selected finite
case. The ordinary correction judgment remains positive prima facie support;
the cumulative evidence does not yet select between its authoritative and
goal-relative interpretations. This is the worker's **proposed** assessment,
pending the coordinator's independent challenge, not a replacement proof status
or a newly reviewed coordinator conclusion.

Rejected approaches: another accuracy-dominance or threshold-policy result
(both rivals accept the arithmetic); coding `Merit → Force` as a new proof
(transcription of the disputed premise); treating every believer as wanting
truth (excludes the question's subject); treating an actual inference as a
categorical commitment at every counterfactual preference (scope change);
declaring naturalism either refuted or vindicated by this local model
(neither follows). No new interpretation fork or reason predicate is introduced.

Claim/type self-sweep: no statement, definition, argument, result, Challenge or
Solution is changed. The old exclusion uses **both** goal-relative force and
an indifferent alternative. The new table witnesses informational support and
its distinction from an independent payoff only under the supplied finite
distribution; its force rule is an explicit extra assumption. The table proves
neither actual warrant nor actual indifferent belief. Correctness, force,
obligation, belief license, rational basing and access remain separate. The
source reading above is a consultation note, not a new attributed corpus claim.

**Reassessment point.** The structural evidence/incentive question is answered
within this domain; the authority question remains open at the bearer-good or
direct evaluative premise. A genuinely different next test is to examine a
specific account of why successful understanding benefits its bearer and why
that benefit supplies an unwanted pro tanto reason, using this same harmless
private belief. It must discriminate reason-giving good from mere functional
success, allow suspension rather than demand inquiry, and retain the strongest
goal-relative response. If supported, compare its scope with the registered
preference class before using it toward #933. Reopen the present informational
test if a proposed rival cannot handle rewards that are also informative, or
if its operative evidence standard changes. Repeating the finite support table
or renaming the authority premise would not supply that next test.

### Verification and exact premise comparison

Live conventions resolved to source revision
`15f348b072188255da837578eaafc8a98f12fdf0`. The persisted Python block was
executed with exact rational arithmetic. Corpus validation, offline attribution
check, documentation/import generator checks and whitespace validation passed.
No proof input changed; no new build, binding, Comparator or NanoDa acceptance
is claimed. Coordinator-owned semantic review and final CI remain pending.

Computed with `python3 scripts/worker_env.py -- target/release/truth
frontier-diff --base 956c8280973ea7d9ed085de07c6b2b50c4c9cf06`:

```text
open premises reaching the root: 494 (353 bare, 90 supported, 51 stated) -> 494 (353 bare, 90 supported, 51 stated)
expanded-route diagnostic (lowest cost): Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16) -> Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16)
distinct verified support alternatives: 494 -> 494
verified support alternatives added: 0
no change
```

Intended and actual formal premise effects: **none**. The contribution is the
discriminating semantic calculation and the defended scope of the remaining
authority question, not a formal connection or a closed premise.
