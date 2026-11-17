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

## Successful understanding as a good for its bearer (2026-11-17 continuation)

**Complete proposed outcome for fresh independent challenge.** The specific
account tested here treats personally grasping a true explanatory relation as
a small constituent of living well, independently of enjoying or wanting that
grasp. It gives a more substantive candidate bearer-good than accuracy or
proper functioning alone: the person actually understands something, rather
than merely containing a correct output. The local benefit claim has positive
evaluative warrant and is provisionally supported. The further claim that this
benefit gives its indifferent bearer an actual pro tanto reason has a direct
evaluative defense below, but remains disputed by a fully specified
goal-relative account. Even granting that reason, a reason to sustain cognitive
activity is not automatically an epistemic reason to believe a particular
content. The exact preference-independent epistemic-force target remains
**underdetermined**, with a more informative candidate support path and narrower
remaining burdens. Neither the accepted evidence/incentive finding nor F6 is
withdrawn or re-defended.

This starts from worker commit
`79bb37a45c3a72c61b51eb75b32bcd617ca29c55`. The coordinator reports that its
bounded outcome passed independent challenge without repair. That review does
not cover this continuation. Publication/check status belongs to the coordinator;
the earlier pending-CI text above is a record of its checkpoint, not updated here.
Current `related`, `context`, target `dossier`/`brief`, question `brief` and
`novelty` retrieval were inspected. The role/force definitions remain
`58ca78b4-33a8-5c4f-a3ee-e206d193f52a` and
`603ba4fa-53ac-5de1-b0de-393209fa8faf`. No new vocabulary or formal sense is
needed to assess this proposed warrant for their application.

### One account, rather than every success made valuable by definition

The proposal is an analyst account of **personal cognitive achievement as a
constituent of the bearer's life**. In the private tile case, the competent
person can grasp why arranging seven tiles into three pairs and one leftover
supports the odd answer. The relation is true; the count is competently made;
the person understands pairing and oddness; and this understanding actually
connects the count to the answer. The #1646 personal-basing criteria distinguish
that exercise from merely possessing arithmetic skill, producing the right
word, or supplying an explanation after a comforting answer was installed.
Those are application conditions, not proof that every actual episode meets
them. Warrant, actual success and personal exercise remain separate.

The account's evaluative claim is that this actual grasp is a modest good
**for the person whose activity it is**. It is a constituent good, rather than
a means to later useful beliefs, pleasure, prestige or a reward. No permanent
increase in competence is assumed: exercising an existing capacity well can
be the proposed good even if nothing is learned for future use. It does not
follow from the bare fact that a capacity is human, biologically normal or
efficient. Nor does it mean this person's life is better overall than every
alternative life. Pleasure, distress, time and other goods can matter too.

Selected source checks constrain this reconstruction rather than supply an
authority theorem:

- The existing pinned `ARIST-EN-I-7` witness
  (`fa974dc9-ae9b-5b8d-818a-bdbf8bca109b`, Perseus Greek edition
  `urn:cts:greekLit:tlg0086.tlg010.perseus-grc2`) was materialized and reread.
  At 1097b2–6 intellect and excellence can be chosen for themselves even without
  further consequences; 1098a16–20 concerns excellent activity across a complete
  life. This does not itself establish that every unwanted trivial cognitive
  exercise benefits its bearer. Reuse the source boundaries in
  [natural-goodness-function-and-authority](natural-goodness-function-and-authority.md#what-the-positive-argument-actually-supplies).
- Pritchard, [*Knowledge, Understanding and Epistemic Value*](https://www.pure.ed.ac.uk/ws/files/8457781/PRITCHARD_2009_Knowledge_understanding_and_epistemic_value.pdf),
  §§4–5, pp.23–25, and §§13–15, pp.37–41 (2009), connects understanding with
  cognitive achievement and discusses its noninstrumental value. His trivial-
  achievement discussion permits both small value and a more qualified account;
  it does not settle the value of this tile episode or its reason-giving force.
- Hurka, [*Value Theory*](https://thomashurka.com/wp-content/uploads/2014/02/value-theory.pdf),
  §2, PDF pp.9–11, and §3, pp.11–16, distinguishes actual from informed desire
  accounts and discusses perfectionist goods independent of desire, including
  connected knowledge. This is a value proposal, not a deduction of our
  agent-indexed epistemic reason from cognitive success.

The latter two are consulted primary-author research leads; new historical
corpus claims and witness registration remain deferred. The specific account,
tile application and judgments here are ours. It is not attributed wholesale
to any of these authors. In particular, noninstrumental value, value for a
bearer and reason-giving authority must not be conflated.

### The actual tests of benefit

Keep the private question harmless and unused. The evidence, basic competence
and availability of the simple inference are held fixed; nobody else relies
on the answer. The subject is indifferent to accuracy and has no further end
served by getting this question right. At the starting point they can be
drawn toward the comforting even answer; they are not stipulated to know that
answer false while also believing it. The following are analytic comparisons,
not reports of psychological experiments or certified possible-world models.

First compare **actual grasp with a lucky correct answer**. Both answers can
be odd and equally pleasant, while only one results from personally seeing the
pairing relation. The achievement account ascribes an additional constituent
good to the first episode. Its rationale is that an intelligible part of the
world is now grasped in the person's own cognitive activity. The lucky token
has the same truth value but is not that person's accomplishment of grasping
why. This tests personal achievement rather than truth alone. The stronger
claim that the person is better off in this respect is an evaluative judgment,
not a further arithmetic identity.

Next compare **retaining that grasp with its loss**, while keeping general
arithmetic skill, pleasure, projects and subsequent practical outcomes fixed.
The proposed setback is loss of a piece of one's understood relation to the
world, even when one does not miss it. This makes clear whose good is at issue:
the loss concerns this person's lived cognitive activity, not merely a less
accurate machine, a disappointed observer or an impersonal increase in truth.
It also prevents an appeal to unnoticed future usefulness from doing the work.
The comparison supports the account to the extent that we recognize that
local setback even under these controls. It is not an observation establishing
that recognition universally. The same evaluative recognition contributes to
ordinary correction judgments; it is not independent corroboration from an
unrelated source of warrant.

Finally distinguish **a tiny good from a demand to keep accumulating it**.
The count is trivial and uses an already developed skill. It need not constitute
a major achievement or a newly enhanced capacity. Those exact features limit
the strength of an analogy with substantial intellectual discovery. They do
not by themselves show that its constituent value is zero. Conversely, the
value of a whole life of understanding cannot simply be divided into positive
value for every isolated cognitive episode. The proposal assigns a modest
positive value to this actual, personally grasped relation; its local warrant
is weaker than a whole-life comparison, and the assignment remains defeasible.

These comparisons provide content on which the account can fail: if a correct
token counts equally without personal grasp, the account has lost its
achievement basis; if a bare increase in functional efficiency counts as
benefit, it has lost its personal basis; if only future payoff or enjoyment
makes the grasp good for its bearer, it has lost its proposed noninstrumental
status. No opaque `GoodUnderstanding` flag or formal model is introduced to
make these assessments automatic.

### Does that good give the unwilling bearer a reason?

The positive argument has three distinguishable commitments:

1. This genuine grasp is a constituent good for its bearer, not just good as
   an output under a standard. The preceding comparisons defend this premise.
2. A feasible way to preserve or complete this constituent good counts
   defeasibly in favor for that bearer, even when it satisfies no relevant
   desire. This is a normative relevance judgment, not part of the definition
   of benefit.
3. Where attending to the already available evidence preserves or completes
   that grasp, this gives the person a pro tanto reason for that attention or
   cognitive exercise. Actual feasibility and the connection to the good are
   required; a merely imagined opportunity supplies neither.

The direct defense of 2 is that a genuine benefit in one's own cognitive life
is a consideration one can recognize as favoring its preservation without
first finding an additional payoff or desire it serves. In the loss comparison,
“it is my understanding that would be lost” identifies a personally relevant
stake; “I do not care” establishes absence of motivation, not itself absence of
that stake. Our ordinary correction judgments make this a live evaluative
recognition, rather than an inference from a neutral performance measure.
This is legitimate prima facie warrant. It need not await an endlessly prior
argument for every good-to-reason judgment, and its openness is not evidence
that it is false. But its normative content is expressly acknowledged: the
person's having a stake does not logically force the relevance judgment.

The proposed reason can be small, outweighed and unsatisfied without fault.
There is no demand to open the jar, collect more evidence, maximize cognitive
achievement or contemplate every available truth. Suspension or disengagement
remains an available alternative; the account alone establishes neither an
obligation to enter inquiry nor the epistemic permissibility of every
suspension in the face of decisive evidence. Retaining arithmetic competence
while declining this exercise is not a malfunction or loss of agency. This
prevents a reason concerning one good from turning into a duty to exercise
every capacity at every opportunity.

### The strongest goal-relative response and what would discriminate

The strongest response grants the personal exercise, the factual explanation
and the achievement's excellence. It then locates benefit in what contributes
to the person's informed ends or appreciative engagement. In the stipulated
case neither requires accuracy or this understanding. It therefore denies a
benefit in the welfare sense while accepting good performance. This attacks
premise 1 through a specific account of good-for, not by asserting that error
is conceivable. Its independent attraction is that it explains why skilled
but unwanted trivial exercises need not improve a person's life merely by
being excellent; the subject's own concerns help distinguish benefit from
perfection imposed by an assessor.

The achievement account's response is that actual personal understanding is
already a mode of the person's cognitive life, rather than an alien trait
installed only for an observer. Factual grasp, not a favorable observer rating,
is what the person has gained. An indifferent or displeased response can
coexist with that small constituent good and introduce a competing cost. This
explains how someone can be benefited in one respect without being better off
overall or consenting to assistance. This is a positive alternative to an
inference from “unwanted” to “necessarily no benefit”; it does not establish
that every instance of personal activity is beneficial. The account still owes
the local evaluative assessment.
The rival is entitled to deny that assessment; this is a substantive welfare
disagreement, not a contradiction in its account of evidence.

A still stronger concession grants even the unwanted bearer-good and rejects
premise 2: goods provide the agent reasons only through relevant ends. It can
call understanding a good in that person's life without making every such
good authoritative for the person. This preserves the exact value/force
distinction under investigation. The positive reply is the direct relevance
judgment above. Neither a new function claim nor a greater quantity of
achievement settles that normative disagreement. No conflict with thin F6 has
been shown: the rival grants reasons in cases where the relevant ends obtain.

There are two genuine discriminators, rather than another accuracy table.
On the **benefit** question, a loss of genuine personal grasp with pleasure,
informed concerns and later outcomes fixed is a local setback on the proposed
account and no welfare loss on the rival's. On the **force** question, someone
can grant that setback and ask whether it counts even slightly in favor of
preserving the grasp when no end is served. A zero answer then targets 2,
rather than erasing what 1 says. These are normative comparisons; no behavioral
prediction or arithmetic calculation has been shown to decide them. Permission
to decline a benefit, or rejection of coercion to supply it, is not by itself
evidence of zero pro tanto force. Nor does calling a loss a setback establish
such force without the relevance judgment.

### Exact preference scope and the epistemic target

The old finite vocabulary has `Preference.accuracy` and `Preference.comfort`.
Under the latter the current target includes a genuinely accuracy-indifferent
profile, rather than merely a person who wants accuracy less strongly. A
subject who enjoys understanding for its own sake, needs the accurate answer
for another aim or would endorse it after ordinary correction of factual
mistakes may already have a reason on the rival's account. Such cases do not
test the stipulated absence of every relevant accuracy/understanding end.
Correcting a mistaken means-belief is not by itself a procedure for changing
that fundamental indifference. An idealization that installs appreciation of
understanding because it is rationally required adds the contested normative
assessment; “informed” alone does not establish it.

For the achievement proposal, varying the accuracy desire while leaving the
actual grasp intact does not remove its personal achievement. Whether its
benefit and force persist at every compared preference is the evaluative
proposal, not a consequence of the two labels. Mere indifference and active
aversion can also differ: aversion may add distress or a cost of exercising
the capacity. The account permits those competing considerations and has not
shown that benefit, weight or permissible action is invariant across all such
profiles. Pro tanto force might persist even when the total verdict reverses;
that possibility needs its own application judgment. No exhaustive psychology
or universal preference-class coverage is claimed.

Most importantly, even accepting 1–3 yields a reason concerning **attention,
preservation or exercise**, not automatically `f.force a r (f.believe p) d`.
The ordinary-role target concerns a consideration's favorable bearing on the
answer. An opportunity to achieve understanding is not extra evidence that
the odd answer is true. The competent count supplies that evidence. Wanting
or having reason to achieve something valuable does not make an unsupported
answer fit to believe. The positive route can therefore motivate engaging with
the evidence independently of a current accuracy desire while still leaving
open why that evidence itself has epistemic force for the indifferent believer.
It must not use a practical reason to cause a cognitive state as if it were
already an epistemic reason supporting its content.

This distinction matters for fallibility and suspension. Successful grasp of
the actual count is factive in this application; ordinary evidential support
need not be. With incomplete evidence, correctly grasping why one's evidence
is inconclusive can be a cognitive success without a categorical belief that
the jar is odd. The benefit proposal thus neither requires successful factual
understanding whenever there is an epistemic reason nor licenses believing
an answer just to obtain the good of understanding it. A further account must
explain which epistemically fitting responses realize the good under the actual
warrant conditions. Defining that fit as whatever has categorical force would
merely restate the target.

### Proposed judgment and substantive reassessment

For this private, competent episode, the personal-achievement account supplies
a **provisionally supported candidate constituent benefit**, with identified
content beyond correctness or causal function. The paired personal-grasp and
loss comparisons, the existing basing analysis and ordinary evaluative
recognition support it. The small scale and absent appreciative engagement make
the informed-end rival a serious substantive challenge; no decisive refutation
of that rival is claimed. The reason-to-preserve proposal has positive direct
evaluative warrant, but benefit-to-force remains **underdetermined** against
the rival that grants the benefit and denies its authority without an end.
No prior proof of every premise is demanded in issuing this assessment.

The target `2ca463c2-bd1f-5a13-a395-0e2c57a5ad8f` also remains underdetermined:
even the proposed reason would first concern a valuable cognitive activity,
and has not been shown to be the same consideration's epistemic force across
every supplied preference. The new route adds a positive support option for
goal-independent cognitive engagement, not a derived instance of that target.
No root, God, irreducibility, source-person or obligation conclusion follows.

Rejected approaches: equating personal excellence with welfare by definition;
using a large life-fulfilment intuition as proof about each trivial episode;
claiming loss of competence where only an exercise is forgone; assuming an
indifferent agent must have a latent truth end; assuming factual idealization
installs that end; treating a reason for attention as evidence for an answer;
and encoding the proposed evaluative premises as opaque flags. The accepted
finite evidence/incentive result is unchanged and is not repeated here.

**Reassessment point:** the selected account and its scope are now explicit.
The next consequential fork is whether the proposed personal benefit is
accepted while reason-giving relevance is denied, or benefit itself is denied
without informed engagement. These target different premises. Further work
should defend or challenge the exact local setback/relevance judgments with
an account of good-for and reasons, not add another success metric. If the
coordinator retains the positive engagement route, its further epistemic
application must explain how reasons for a cognitive activity relate to the
fitting evidence-based response, including suspension under inconclusive
evidence. Reopen the local benefit assessment if personal grasp is absent,
purely imposed excellence is doing the work, or a hidden instrumental payoff
is discovered. These are substantive conditions, not an arbitrary work cap.

Self-sweep: this is a prose warrant investigation, with no changed statement,
definition, argument, result or Lean type. Personal exercise and success are
application assumptions, benefit and normative relevance are defended
evaluative judgments, and the epistemic-force mapping is explicitly open.
No certified model, actual-agent observation, new source attribution to a
corpus proposition or formal establishment is advertised. All proposed new
judgments require the coordinator's fresh independent challenge before being
used as reviewed support.

Verification for this continuation: live convention source revision remains
`15f348b072188255da837578eaafc8a98f12fdf0`. Corpus validation, offline
attribution check (no changed stating claims), documentation/import generator
checks and whitespace validation passed. The selected existing Aristotle
witness was materialized and read; no full-source verification was performed.
No Lean input changed and no new build, binding, Comparator or NanoDa evidence
is claimed. The previous finite calculation is unchanged and was not rerun.
Fresh independent semantic challenge and coordinator-owned final CI cover
this continuation separately from the accepted previous checkpoint.

Exact computed delta from `python3 scripts/worker_env.py -- target/release/truth
frontier-diff --base 79bb37a45c3a72c61b51eb75b32bcd617ca29c55`:

```text
open premises reaching the root: 494 (353 bare, 90 supported, 51 stated) -> 494 (353 bare, 90 supported, 51 stated)
expanded-route diagnostic (lowest cost): Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16) -> Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16)
distinct verified support alternatives: 494 -> 494
verified support alternatives added: 0
no change
```

Intended and actual formal premise effects: **none**. The proposed local
benefit judgment is additional philosophical support for a candidate route,
not a new formal premise, a certified transfer or a root discharge.

## Granted benefit: does preservation favor action without an end? (2026-11-17)

**Complete proposed outcome for fresh challenge.** Grant the exact local
constituent benefit accepted at the preceding checkpoint. On that grant,
retain premise 2 as **provisionally supported**: a feasible preservation of
this person's genuine cognitive good counts pro tanto in favor for that person
even absent a relevant end. This is a substantive local evaluative judgment,
not an analytic consequence of calling something beneficial. The strongest
benefit-granting denial connects reasons to sound deliberation from the
agent's existing motivational/evaluative resources. Its explanatory rationale
is serious, but does not by itself establish that those resources exhaust the
grounds of normative favoring. The direct positive warrant is retained rather
than suspended merely because that rival survives.

Separately, the retained action reason supports fitting engagement with the
evidence under explicit process/application conditions. The joint explanation
below gives a defensible **conditional local support option** for the
evidence's own force: the good grounds the significance of responding, while
the count is the actually used consideration specifying the fitting answer.
This is a proposed normative explanation, not something already proved by
the action reason. Its transmission and attribution steps and exact
preference-class application remain visible below.
There is no new formal target instance or root closure. This qualified local
assessment advances the granted-benefit branch; it does not declare the
general reasons-internalism dispute resolved.

Baseline: `681e855ef09e80031c35649e9deae067b5bd7be4`. The coordinator reports
no repairs from independent challenge of that checkpoint and accepts its
qualified local benefit assessment. That accepted result, the earlier
evidence/incentive finding and their source limits are reused. Their publication
and CI status is not reassessed here. Current target `related`, `dossier`,
question `brief`/`novelty`, ordinary-role/F6 dossiers and the goal-relative
exclusion `context` were inspected. No new formal vocabulary is introduced.

### Fix the concession; do not reopen the benefit dispute

The grant is that personally grasping the true count/parity relation is a
small constituent good **for this bearer**, independently of current enjoyment,
approval or usefulness to a further project. It is not just competent output,
an observer's ideal or an unacknowledged means to pleasure. Preserve the same
private question, competence, evidence and absence of others' reliance.
Preservation is feasible in the specified episode. The subject has no relevant
accuracy, understanding or self-improvement end, including an instrumental one.
Nothing assumes that the person simultaneously knows the comforting answer
false and believes it, or can change belief by an immediate act of will.

An account denying that such an unwanted good benefits the subject challenges
the grant and belongs to the preceding branch. It is not the rival tested
here. The present rival grants the benefit in the same sense, then denies
that preserving it favors action unless a live practical commitment can make
it relevant. It cannot support this denial merely by reverting to “only wanted
things are good for people.” Conversely, granting the benefit does not by
itself concede our independent favoring judgment.

### Positive warrant for favoring, with its actual scope

The positive consideration is the person's own concrete stake: the available
choice preserves rather than loses a genuine constituent of that person's
cognitive life. This is relevant to evaluating the choice **for that person**.
It is not a demand to create every good, a claim about other people's welfare,
or a verdict that a better cognitive score wins the whole choice. With the
benefit granted, the remaining positive judgment is that this preservation
speaks in favor at all, rather than acquiring its entire significance from
the separate fact that the person wants it.

There are two grounds for retaining that judgment. First, our ordinary
recognition of a personal setback supplies direct evaluative warrant: one can
recognize “that would preserve something genuinely good in my life” as a
consideration without deriving its significance from another payoff. This is
the same family of warrant as the already retained correction judgments;
there is no claim of an independent evidential ancestry. Second, indifference
changes the person's concerns but leaves the granted beneficiary, good and
preservation relation intact. For the positive assessment, those three facts
explain why the consideration bears on this person's choice. A desire can add
a further consideration or explain motivation without creating this one.
This second rationale supports a substantive relevance standard; it is not a
proof that every possible standard must disregard motivational relations.

The reasoning stops at the defensible evaluative recognition of this stake's
relevance. Demanding a prior proof of every such recognition would discard
the warrant actually being offered. Equally, saying “benefit” and passing it
through a new `Benefit → Reason` predicate would add no warrant. Benefit and
favoring remain distinct commitments even when both are provisionally accepted.
The scope is **some pro tanto favoring from this granted benefit**. It implies
neither an overriding recommendation, an obligation, blame for declining,
permission for others to compel the activity, nor a reason to maximize every
capacity's exercise. No unobserved pleasure or future need is inserted.

### The benefit-granting internalist mechanism and its justification

The strongest denial is not “no current desire, therefore no reason.” It says
that a reason must be available through sound deliberation from the person's
existing motivational/evaluative resources. Deliberation may correct error,
exercise imagination and form new concerns; it is not confined to calculating
means to a fixed list of desires. If none of those routes connects the granted
benefit to action, the rival withholds force while leaving the benefit intact.
Its positive mechanism joins reason attribution to how a person could act
**for that consideration**, rather than merely undergo an assessor-preferred
change. It thereby distinguishes rationally motivated response from conversion
by manipulation or rhetoric.

Primary-author check: Williams, [*Internal and external reasons*](https://kevinjpatton.com/teaching/phil_3050/readings/Bernard%20Williams%20-%20Moral%20Luck.pdf),
in *Moral Luck* (1981), pp.101–111, was read, especially pp.104–110. He allows
evaluative dispositions and new motivations in deliberation, considers
unwanted needs at pp.105–106, and argues from reasons' possible explanatory
role to a challenge about rationally acquiring motivation at pp.106–110.
He distinguishes a reason from an overall verdict. The opening formulation of
[*Internal reasons and the obscurity of blame*](https://www.cambridge.org/core/books/abs/making-sense-of-humanity/internal-reasons-and-the-obscurity-of-blame/963978B639E1BD60FB5C1F3D1D38BF7F)
(1995, p.35, publisher's displayed excerpt) was also consulted. No whole-chapter
reading of the latter is claimed. These are research leads, with new historical
corpus attribution deferred; the cognitive-good concession and assessment are
our reconstruction, not positions attributed to Williams.

The independent attraction of the mechanism is explanatory accountability:
in a genuine response for a reason, the consideration must enter the agent's
thought and contribute to action. The existing basing findings support taking
that difference seriously. The rival's further **necessary-condition** claim
is that rational availability must originate within the existing motivational
resources; mere recognition of the benefit is insufficient without that route.
It is a genuine claim about normative reasons, not merely a report that this
person is unmotivated. The objection therefore cannot be answered just by
repeating that pro tanto reasons may lose an all-things-considered contest.
The rival already permits that.

The positive reply grants the explanatory requirement for an actual exercise
without granting the exclusivity claim. A person could preserve the grasp
because they recognize both the concrete benefit and its practical relevance;
that is a content-guided explanation, not mere causal redirection. The
exclusivity thesis challenges whether such recognition can be rationally
acquired without a suitable starting concern. The positive account treats
recognizing a genuine personal stake as a potential basic evaluative insight,
rather than requiring its authority to come from a further end. This proposes
a substantive account of rational uptake; it does not demonstrate that any
motivationally isolated agent must arrive at it through a neutral algorithm.

Nor does the positive reply simply infer a reason from the existence of a
new motive. A motive acquired by conditioning or persuasion does not establish
the judgment's warrant. Its offered warrant remains the concrete beneficiary/
benefit/preservation relation and the direct relevance judgment. Conversely,
the possibility of explaining action by a desire plus a belief does not show
that the consideration's **normative ground** is that desire. A subsequent
desire to preserve the good could express recognition of a reason rather than
create it. The rival can reject that explanatory order, but causal description
alone does not select between them.

This isolates the remaining conflict: whether sound practical assessment can
recognize the granted benefit as relevant without a preexisting connecting
concern. The rival supplies an intelligible, motivated restriction; the positive
account supplies a direct evaluative counterproposal. Neither is required to
deduce its entire theory from nonnormative facts. The rationale for restricting
motivation's rational origins does not defeat the local relevance recognition
merely by redescribing it as an external reason. On the granted benefit, I
therefore retain minimal favoring as **provisionally supported**, rather than
infer zero force or demand suspension just because a coherent internalist
alternative remains. This is not a refutation of that alternative, a proof of
actual motivational access, or a diagnosis that every indifferent person is
irrational. It is a scoped warrant judgment whose disagreement is explicit.

This strengthens the preceding checkpoint's withholding of a local favoring
verdict **on the explicit benefit grant**. The basis is a reassessment of the
existing direct warrant against the now specified internalist restriction,
not a new observation or another independent proof. The mere survival of a
rival does not cancel that warrant. The internalist may likewise retain its
starting constraint; the present verdict records a qualified working assessment,
not a demonstrated comparative defeat or a change in formal establishment.

### Deliberative resources are not the same as a chosen accuracy end

The internalist's necessary condition is broader than the existing
`GoalRelativeForce f accuracyAim` control. A disposition to reconsider one's
evaluations, a commitment to one's own good or an appreciative response to
newly understood content may supply a route even without an antecedent desire
for the answer's accuracy. If present, that is an internalist reason in a case
where the simple accuracy-aim condition could fail. It must not be called a
defeat of the stronger internalist account merely because that account grants
a reason to someone indifferent to accuracy.

For a zero-force prediction under the stronger account, absence of a relevant
end must be supplemented by absence of a suitable sound deliberative route
from those other resources. The first absence alone does not prove the second.
Acquiring a new concern later also does not by itself show that the reason
was present before that acquisition; its earlier presence is the normative
claim being defended, rather than something inferred from the later action.
This continuation does not invent a hidden connecting resource in the assigned
subject. It tests the denial under its strongest no-route supposition, while
retaining the positive assessment of favoring even on that supposition.
No claim is made that actual people satisfying it have been identified.
Likewise, openness to reasoning is not silently defined as already wanting
accuracy, flourishing or whatever a favored theory calls rational.

### Separately test transmission to an evidence-based response

Retaining premise 2 gives a reason to preserve or exercise the particular
valuable grasp. It does not prescribe an arbitrary method or answer. The
positive further proposal is **constitutive transmission** in this local case:
where an evidence-based response is part of the actual personal grasp whose
preservation is favored, that reason also counts defeasibly for maintaining
that response *as part of the grasp*. This is another normative step, defended
by the fact that the exercise and its properly based response are not two
unrelated outcomes. The reason's object cannot be secured by keeping an output
while replacing the very understanding for whose sake it is favored.

This is narrower than “a reason for an end supplies a reason for every means.”
It requires an actual constitutive connection and an appropriately feasible
process; merely promising cognitive benefit does not license an attitude.
It also does not say that every particular calculation, witness or causal
input is indispensable. Redundant bases and alternative methods remain as in
#1646. The proposal concerns the fitting response within the selected grasp,
not a unique implementation or a duty to continue this particular inquiry.
Its normative transmission content is offered for assessment, not certified
by a theorem about logical entailment or causal necessity.

There is a substantive reason to favor this limited bridge. Wishful bypass
cannot preserve the personally understood relation merely by reproducing its
answer. The response must remain appropriately sensitive to the count's
content and warrant, because those are what the person grasps. The account
therefore favors a fitting response through the evidence rather than a
comforting response or an unsupported belief produced for its benefits.
This uses the already developed personal-basing criterion and source-aware
understanding account; it is not another metric or finite comparison table.

However, two considerations still perform different jobs. The bearer-good
explains why engaging or preserving is favored; the count explains which
answer is supported. A reason concerning a state can be transmitted to its
constitutive attitude without thereby proving that the count **itself** has
the `force` attributed to an ordinary epistemic reason in the existing Frame.
A complete value-grounded account could make that attribution through a
joint normative explanation: the count has favorable bearing, and the good of
personally answering makes that bearing practically authoritative here. Its
dependence on a value premise would not disqualify it by definition. Neither
the role definition nor the value of understanding requires irreducible
epistemic authority or forbids such a grounding account.

The strongest surviving reply at this second step can thus grant the reason
for valuable engagement, and even the limited transmission, while calling
the inherited reason practical or achievement-directed. It reserves epistemic
force for the evidential relation and denies that state-directed favoring
already establishes that relation's authority. This identifies the exact
attribution gap, not evidence that the positive grounding account is false.
The weaker constitutive bridge is provisionally supported. An argument that
merely changes the word “practical” to “epistemic” would not supply the stronger
attribution. The following joint explanation addresses that step.

**Joint grounding proposal.** Distinguish the consideration favoring the
answer from the ground of its reason-giving significance. The count is what
the person uses to answer the question; preserving the personally understood
relation is why that appropriately based response matters in the granted
account. The good is not a second observation about the jar. Nor is the count
a merely accompanying fact while an independent incentive fixes the answer.
Its content must actually select and sustain the response as part of the
grasp, under the sufficient, undefeated warrant assumed for this episode.
Together with the retained favoring and constitutive transmission, those
conditions supply the proposed explanation of why **this count**, in this
context, counts for maintaining its fitting answer even when accuracy is not
an end.

The discriminating difference from an incentive to hold a predetermined belief
is substantive. An incentive can still favor causing that belief when the
evidence undermines it. The granted good of actual understanding cannot be
realized by severing the evidential relation while retaining a pleasing answer.
If the person follows a bypass, the proposal loses its personal-grasp ground;
if the count does not support the answer, it loses its evidential ground.
Where the evidence warrants a different response, the proposal follows that
response rather than the comforting content. These are explanation/application
tests, not another finite table or a deduction of force from covariance alone.

This is a reason to accept the stronger local attribution within the account:
the count does the answer-selecting work *within a grasp whose
preservation already counts for the bearer*. The evaluative ground does not
replace the count as the reason used in the inference. A normative reason
need not contain, as part of the consideration presented to the subject, the
whole theory explaining why that consideration has force. Conversely,
simultaneous presence of a good and a supported belief is insufficient; the
actual fitting and basing connections just specified do the additional work.

The existing ordinary-role definition permits a project-relative interpretation,
and the independent-role definition adds preference-independent force, not an
irreducibility or pure-origin condition. Thus an account grounding evidential
force in an unwanted cognitive good is not excluded merely because its
explanation also concerns the bearer's flourishing. It cannot be rejected in
these selected senses just by calling its ultimate ground practical. Relevant
challenges include denying the retained normative transmission, showing that
the count is incidental to this response, or defending a stricter criterion
of epistemic force and establishing that it is the target's criterion.

I therefore provisionally retain the joint explanation as a **conditional local
support option** for the count's epistemic force, on the explicit benefit,
favoring, constitutive-transmission, warrant and actual-basing commitments.
Those jointly required commitments are not claimed established by an
entailment theorem or reducible to the action reason alone. The internalist
denial at premise 2 remains an objection to the whole route. This account
offers a reasoned way to make the stronger attribution; it does not force
every coherent theory to make it or establish its application to every
ordinary believer.

Suspension and fallibility constrain the proposal. In the already successful
counting episode, preserving the actual grasp may involve maintaining its
supported answer. Before successful understanding is attained, a reason to
seek or preserve it is not a warrant to treat the hoped-for answer as true.
Where the evidence remains inconclusive, grasping its limits may instead
support suspension or a qualified confidence. This is not an assertion that
any suspension is fitting under decisive evidence. Ordinary warranted error
also remains possible; the factivity of successful understanding cannot be
transferred to every ordinary-role reason. Neither a reason for attention
nor the proposed transmission supplies direct voluntary control of belief.

### Preference scope, outcome and precise exhausted approach

The retention of premise 2 is conditional on the **same actual local benefit,
bearer and feasible preservation** at the compared preferences. Within that
scope, absence of an accuracy or understanding end is not treated as a
force-removing condition. The judgment does not claim equal weight or equal
overall choices at `Preference.accuracy` and `Preference.comfort`. An aversion
may add a competing cost; whether a more demanding profile also changes the
benefit, feasibility or normative applicability must be checked rather than
assumed. The two labels do not certify a psychological census. To apply the
registered universal `∀ d` clause, the joint account would need the benefit,
application and transmission conditions throughout that exact supplied class,
then application of the joint explanation to the same ordinary-role
consideration. This continuation establishes no such formal instance and does not repair #1376.

Compared with the previous checkpoint, the new assessment is **positive local
favoring on the explicit benefit grant**, with a developed internalist objection
and response. It is not a renewed dispute over whether the benefit exists.
The limited activity-to-response bridge also has a positive defense, and the
joint explanation supplies a conditional local support option for the target's
consideration-indexed force. Its full preference-class application and actual
instantiation remain open; thin F6, the accepted local benefit and
the accepted evidence/incentive finding retain their earlier status. No root
or God inference follows.

**Precisely exhausted approach:** trying to settle premise 2 by enriching the
description of cognitive success, future utility or personal benefit is now
exhausted for this branch, because the strongest rival grants that benefit.
The explanatory argument was then tested at its actual stronger form, including
sound deliberation and possible new motivations; it converges on the exact
dispute about what rational evaluative recognition can supply, not a discovered
contradiction or an inability to state a reason. A further performance measure,
claim of latent desire or generic omission model would not discriminate.
This is not exhaustion of the question or evidence against the retained
basic relevance judgment.

The next materially different test, if the coordinator retains this proposal,
is an **application audit of the joint explanation**: establish whether the
same consideration actually governs the fitting response and whether the
granted good and feasible process persist at each selected preference. In a
case of warranted error, distinguish a reason for the evidence-supported
response from an actual successful grasp that is not present; the factivity
of the latter cannot do the former's work. The present account has not shown
coverage there. The private successful episode is a candidate local instance,
not a claim that every epistemic reason requires achieved understanding.
If instead the local relevance judgment is challenged, the challenge should
target its beneficiary/benefit/preservation rationale or defend the internalist
restriction on rational motivation's origins. Merely observing indifference
or restating that benefit and force differ does not test the defended step.

Claim/type self-sweep: no corpus statement, definition, argument, result or
Lean declaration changes. The new positive assessments are explicitly
provisional, scope-bound and pending fresh independent challenge. The source
reading is a research consultation, not a new historical claim record. No
formal model, theorem, actual-agent observation, rival refutation or root
discharge is claimed. The existing exclusion theorem still requires both its
goal-relative-force premise and an indifferent preference; its controls do
not encode this newly assessed benefit or normative transmission. They cannot
be cited as certification of either assessment.

Verification for this continuation uses the unchanged prepared setup and live
convention source revision `15f348b072188255da837578eaafc8a98f12fdf0`.
Corpus validation, offline attribution check (no changed stating claims),
documentation/import generator checks and whitespace validation passed. No
Lean input changed; no new build, binding, Comparator or NanoDa certificate is
claimed. No prior finite calculation was repeated. Coordinator-owned fresh
semantic challenge and final CI remain separate from these local checks.

Computed with `python3 scripts/worker_env.py -- target/release/truth
frontier-diff --base 681e855ef09e80031c35649e9deae067b5bd7be4`:

```text
open premises reaching the root: 494 (353 bare, 90 supported, 51 stated) -> 494 (353 bare, 90 supported, 51 stated)
expanded-route diagnostic (lowest cost): Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16) -> Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16)
distinct verified support alternatives: 494 -> 494
verified support alternatives added: 0
no change
```

Intended and actual formal premise effects: **none**. The new assessments
provide qualified philosophical support for a local engagement route, not a
certified instance of the preference-independent epistemic-reason target.

## Application audit: one witness, the whole preference class (2026-11-17)

**Outcome for fresh independent challenge.** The successful private episode
is a conditionally applicable pattern for the accepted joint explanation,
across the entire explicitly supplied two-preference class, **if the same
actual grasp, basing and feasible preservation are supplied at both values**.
The repository currently supplies an analyst case, not a documented actual
episode meeting those conditions. No actual successful instance is thereby
established. Two focused Lean checks confirm a concrete reason not to use the
old finite `independent` profile as that episode: its fixed count/answer has
force at every supplied preference while its content is false, and every
attitude in that profile is already a belief image. It certifies neither
factive understanding nor a distinct suspension attitude.

The original factive-success ground does not cover a warranted false answer.
Suspension cannot be substituted for belief midway through a fixed-witness
comparison. A genuine grasp of the evidence's limitations could support a
different application, but its actual occurrence, target-attitude connection
and full preference mapping are additional obligations. Earlier benefit,
favoring and transmission assessments retain their accepted, qualified status;
failure of this wider application does not defeat the successful pattern.

Baseline is `340b1ee3847ef8bc1668a6df78658bedf060e903`. The coordinator reports
that its independent challenge required no repairs; this audit is a new
outcome. Prior publication and CI statements are not updated. Live conventions
again resolve to `15f348b072188255da837578eaafc8a98f12fdf0`. Current target
`related`, `dossier`, question `brief`/`novelty` and the eligible-uptake result's
`context` were inspected, along with the exact declarations below. No new
source attribution, definition, normative flag or proof registration is added.

### Freeze the witness before evaluating preferences

For the successful analyst case fix the same bearer a, the particular count
consideration r, the odd content p, the factual-belief attitude t = believe p,
and the circumstances c, including actual truth, evidence, competence,
defeaters and the episode's actual inferential route. This is not an
instantiation of `Content.even`: seven's oddness must not be represented by
silently changing that constructor's meaning. A generic `Frame` can represent
the intended content, but no such actual-case binding has been supplied here.

The entire supplied comparison class is exactly
`{Preference.accuracy, Preference.comfort}`. The second retains the selected
absence of a relevant accuracy/understanding end; its label does not also
establish inability, distress, a bypass or loss of the cognitive good. There
is no third unexamined value in this inductive type, and no claim that it
enumerates all human preference profiles. Within this comparison the episode
is held fixed and its force assessed at each preference. Changing its actual
route, target or background to obtain a better answer at one value would
change the case, not complete this audit.

`IndependentInstance f a r t` is exactly `OrdinaryInstance f a r t ∧
∀ d, f.force a r t d`. Thus one fixed witness must work at both values;
separate existential witnesses, different considerations or a different
attitude at each preference do not suffice. `actualPreference` ensures an
actual value is included, not that the other value was actually enacted.

| Application item | Accuracy value | Comfort/indifference value | What establishes it in this audit |
| --- | --- | --- | --- |
| Same a, r, p, t and c | Fixed | Identically fixed | Declared comparison, not inference from a preference label. |
| r's applicable evidential bearing on p | Supplied | The same supplied bearing | `EpistemicRole` has no preference coordinate; actual application remains a semantic/warrant burden. |
| Actual personal basing of this t on this r | Assumed for the analyst success case | The same route is required | The four #1646 process conditions, not `force`, output agreement or truth alone. No actual episode record supplied. |
| Factive personal grasp and its bearer-benefit | Conditional on that actual success | The same successful grasp must remain present | Accepted benefit assessment applies to the specified grasp without an end; neither label supplies a grasp. |
| Feasible preservation of that grasp | Explicit scenario assumption | The same available means must remain feasible | Needs a concrete method and ability; wanting to preserve and being able to preserve are different. No actual method/ability evidence supplied. |
| Force of this r for this t | Proposed through the accepted joint explanation | The same proposal, without importing an accuracy end | Qualified normative assessment under all preceding conditions, not a field already certified by the finite controls. |

This is a complete audit of the declared class, with separate application
conditions; it is not an assertion that the unknown conditions passed. If a
concrete comfort-profile episode instead has a different route, that would
need its own assessment. No such failure is invented here. Likewise, merely
imagining a hidden bypass is not evidence against an otherwise well-supported
basing attribution.

### What the existing declarations actually supply

`Frame` has fields for evidence-role attribution, `Holds`, production, reward
and preference-indexed force. It has **no actual-belief or episode/basing
field**. Its evidence-role fields also have no preference coordinate. They
cannot demonstrate that a real route survives a motivational change; their
constancy is part of the representation. The four-condition actual-basing
account in [the #1646 note](epistemic-underminer-boundaries.md#proposed-sufficient-account-for-the-selected-scope)
is an interpreted application proposal, not an exported Lean definition of
personal understanding.

The existing `EpistemicUnderminers.SomeEligibleReasonUptake` supplies an
existential `Reason a p ∧ Believes a p ∧ Eligible a p`.
`EligibleReasonUptakeWarrants` is the separate pointwise bridge to `Warrant`.
Its registered result `1db47fd9-6ab1-4fa1-a9dd-0aa9457d8146` consumes **both**
premises. `Eligible` packages basing, adequacy and undefeatedness without
analyzing them; `Warrant` is explicitly nonfactive. It neither proves actual
personal grasp nor supplies the missing preference comparison. An existential
uptake somewhere cannot be substituted for uptake by our fixed a of p through
r. With an appropriate pointwise triple and the calibration, one can apply
`hBridge a p hReason hBelieves hEligible`; no duplicate theorem is needed.
The relation to this particular r still requires the consideration presentation
and actual process interpretation.

`RevisionUptake.revise` and its existing screening theorem supply only routing
facts. Inversion is sensitive too, and an available recommendation need not
be the active basis of a belief. Those controls must not be promoted to the
missing personal application evidence.

The following focused consequences of unchanged vocabulary were elaborated
with Lean. They keep the **same** subject, count and belief in the first check,
and explicitly exhaust both supplied preferences. The earlier direct `decide`
draft failed to synthesize decidability for the wrapped profile propositions;
the constructive proof below checks the same advertised claim without adding
an axiom or changing a definition. This is a local declaration audit, not a
new registered result or a new Comparator/NanoDa certificate.

```lean
import TruthCore.Logic.EpistemicReasonDefinitionFork

open TruthCore.Logic.EpistemicReasonDefinitionFork

example :
    IndependentInstance independent () Consideration.count
      (independent.believe Content.even) ∧
    ¬ independent.Holds (independent.about (independent.believe Content.even)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩
  · intro d
    cases d <;> exact ⟨rfl, rfl⟩
  · intro h
    cases h

example (t : independent.Attitude) :
    ∃ p : independent.Content, independent.believe p = t := by
  exact ⟨t, rfl⟩
```

These are consequences of the existing false-count profile and its identity
belief constructor, not evidence that an actual person has a warranted error.
No `Believes`, `Warrant` or full basing witness is present in that profile.
The general `Frame` need not have this restricted attitude type. A distinct
suspension attitude can be represented there with an explicit content mapping;
the old finite profile cannot supply it just by renaming `Content.rain`.

### Exact success, error and suspension coverage

The successful pattern is locally adequate **as a supplied analyst case**:
given actual personal grasp, the granted benefit and feasible preservation,
the accepted favoring/transmission/joint explanation can be applied to this
same r and t at both preferences. None of those assumptions contradicts the
absence of an accuracy end. This is not a proof of psychological realization
or an observed actual witness. The finite `independent` profile is expressly
not its certificate: its supported `.even` answer is false.

For **warranted error**, fix a separate application with p false but the
subject's belief adequately and undefeatedly based on the available evidence.
Keep that error case's bearer, r, t and circumstances fixed throughout its
own full preference comparison. It is not the successful case with truth
silently changed at the comfort value. On the stipulated false content there
is no successful factive understanding of p to preserve. The original ground
therefore does not apply, regardless of whether basing and warrant obtain.
This does not show there is no epistemic reason, no good cognitive activity,
or no independent reason at that error case. The ordinary-role definition
and the Lean check above keep those questions apart.

One concrete alternative is a **true grasp of the evidence's defeasible
bearing**, despite a false answer about the jar. That could be an instance of
the same kind of cognitive good with a different understood relation. But it
must really be present: replacing “understands p” by “understands why e favors
p” changes the ground, and the latter does not follow from a warranted false
belief. It can also coexist with withholding p. Its transfer to our particular
belief attitude would need the actual basing and fitting-response connection,
not merely the old benefit label. The present audit does not establish that
mapping or coverage of all warranted errors.

For **suspension under inconclusive evidence**, t = believe p stays the target
in the original comparison. Switching to suspend p at one preference cannot
complete its `∀ d` claim. A separate suspension candidate would keep the same
suspending attitude about p fixed at every preference, and independently
supply the appropriate evidential-role, basing, benefit and preservation
conditions. A true grasp of why the evidence is inconclusive offers a candidate
ground for that separate case; absence of grasp of p's truth need not preclude
such metaevidential understanding. But an unperformed reflection cannot supply
it. Neither the existing finite attitude type nor the belief-only
`SomeEligibleReasonUptake` declaration certifies that application.

Under **decisive evidence**, the availability of suspension or disengagement
still does not prove that suspension is epistemically fitting. Conversely,
pro tanto force for a supported belief is not a full-belief obligation or a
demand to investigate. The route adds no general stance-selection policy.
Its successful pattern, warranted-error gap and separate suspension candidate
are therefore different coverage results, not rival preferences filling one
existential witness.

The strongest substantive alternative for the uncovered error cases assesses
the agent's **proper response to available evidence**, rather than requiring
actual truth of the answer or achieved understanding. It has a positive
mechanism in the existing nonfactive eligibility/warrant account: the evidence
can be appropriately used even when it misleads. The substantive difference
from our original ground is actual success, not mere unusualness of the case.
This warrants retaining that alternative as a scope-relevant route; it does
not establish its authority for an indifferent agent. A goal-relative version
can still grant all the evidential and basing facts while restricting force.
No new objection to the accepted successful instance is inferred from it.

### Actual-case blocker and substantive reassessment

No identified actual bearer/episode was supplied for this analyst jar case.
The missing evidence is specific: identification of the count token and
target attitude; grounds for the actual count/truth and the evidence's warrant;
an actual content-guided inferential contribution to that attitude rather than
a matching later explanation; personal grasp under the four existing basing
conditions; and a concrete, available way to preserve it. The alternate
preference also needs an admissible fixed-case interpretation that preserves
those conditions. A label, a theorem about some profile or an existential
uptake at another content supplies none of these identifications.

An ordinary documented episode with well-supported first-person or observed
reasoning could supply prima facie application evidence. Exhaustive
neuroscience, an independent proof of every premise and speculative hidden-
bypass exclusion are not prerequisites. The matched inference/bypass protocol
already proposed in #1646 is useful if a concrete process question arises;
it is not a new universal gate. This worker has no such episode evidence to
assess, and none of the existing source passages reports this particular case.

The application audit is complete at that boundary. Actual successful
application is **blocked by the missing case evidence**, not refuted. The
original factive route's noncoverage of a false target is resolved; the
metaevidential and suspension extensions require distinct mappings, not an
assumed factive ground. Prior provisional benefit, favoring, transmission and
joint-explanation judgments remain intact; no full target or root is promoted.

The next genuinely different useful route is to assess authority for the
**properly based, warranted response without achieved factual understanding**.
It can reuse the existing nonfactive eligibility/warrant declarations and
direct correction warrant, then test whether proper responsiveness itself
supplies a bearer-good or whether a true metaevidential grasp is actually
needed in the selected instance. The difference matters: the latter is a
narrower route and cannot become a mandatory higher-order support-belief for
all rational inference, given the regress/active-treatment distinctions already
recorded in #1646. Such work addresses the uncovered error/suspension cases;
another description of the successful count would not. An actual-case version
of the present successful route should reopen only when the concrete episode
and full-class application evidence above become available.

Self-sweep: the two Lean examples establish only existing-profile properties.
No actual belief, warrant, personal basing, benefit or feasible preservation is
inferred from them. Success and error are separate circumstances; each keeps
its witness fixed across the entire declared class. Suspension is not swapped
in for the successful belief. No new source claim, corpus proposition, opaque
normative predicate, registered theorem or closure change is introduced.

Verification: the persisted Lean block elaborated without diagnostics after
the decidability repair described above, using
`flock /tmp/moenarch/truth-core-heavy.lock python3 scripts/worker_env.py --
lake env lean /tmp/epistemic-930-application-audit.lean`. The file contained
the displayed imports/examples; the block is retained here for reproduction.
No library module or proof input was edited. This focused Lean check is not
Comparator/NanoDa verification or evidence of an actual human application.
Corpus validation, offline attribution check (no changed stating claims),
documentation/import generator checks and whitespace validation passed.
Independent challenge of this full outcome and coordinator-owned final CI
remain pending; prior accepted assessments are reused.

Computed with `python3 scripts/worker_env.py -- target/release/truth
frontier-diff --base 340b1ee3847ef8bc1668a6df78658bedf060e903`:

```text
open premises reaching the root: 494 (353 bare, 90 supported, 51 stated) -> 494 (353 bare, 90 supported, 51 stated)
expanded-route diagnostic (lowest cost): Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16) -> Catholicism is true: the Catholic Church is a…, from Fork node: the intended reading of… and 7 more [8df2faad] (cost 16)
distinct verified support alternatives: 494 -> 494
verified support alternatives added: 0
no change
```

Intended and actual premise effects: **none**. The contribution is an exact
application/coverage audit and checked existing-profile consequences, with a
specific evidence blocker and a distinct next research route.
