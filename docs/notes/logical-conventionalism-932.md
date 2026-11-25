# Logical conventionalism: correctness, application and authority (#1989 / #932 / #1084)

Draft analyst investigation, attribution deferred. Baseline main
`a9819b148bd4a7c089cff9dc07f95c209452511e`; intake #1989 head
`eeb7e0e7225dd0dc37c851effa53467a62b0b6fe`. This branch is independent of
the intake edit: the question is taken from it, not a dependency on its
unmerged text. No new graph edge, floor or proof status is claimed.
[Research attempt and scoped proposed assessment](../../corpus/attempts/1ecb1a9a-ba62-4cf6-a7ee-a114f61542b5.json).
Local checkout, installed conventions, executable dossier/novelty/semantic
checks and independent worker challenge are unavailable in this connector
session. This is a provisional research draft, not an accepted judgment.

## Target and first discriminating test

Can all logical correctness be constituted by convention without a
nonconventional standard of reasoning? Distinguish four levels: sign
choice (notation), content assignments (meaning), stipulated schemata
(inference permission), and whether a particular transition is a correct
instance of the schema (application). Also separate correct instantiation,
semantic preservation and the epistemic force of a valid inference.
Stipulation may select a rule; selection of an abstract rule need not
supply competent execution or a reason to adopt it.

Reuse the existing
[rule-following regress](../wittgenstein.md#rule-following-198-201-202-the-shape-of-the-regress),
`WITTGENSTEIN-INTERPRETATION-REGRESS` and
`TruthCore.Results.Wittgenstein.InterpretationRegress.interpretationRegress`.
For the application-determination reading, let items include applications
and further rule expressions, D(a) mean that what accords with the rule
at a is fixed, and I(i,a) that i is a further interpretation of a.
The theorem takes both (1) for every determined a there exists a
determined i interpreting a, and (2) WellFounded I, to conclude
every a is undetermined. `regressFork` adds the incompatible existential
D(a). Relevant input IDs are `7c056d7f-d0b5-5315-bc54-068dcb618858` and
`5218e5c6-d9fc-5ddb-9861-42e1bd00aef7`; the determination existential is
`a132eba0-a11b-53da-a901-8d290dccf850`. Reuse, do not register a
duplicate theorem.

An additional convention only instantiates this regress if it is a
further rule expression whose own determinate application is necessary
for the earlier item's determination. Not every convention theory has
that premise. A primitive grasp or a constitutive practice can reject it;
an infinitist rejects well-foundedness. Neither move is a contradiction.
What fixes the primitive application, and whether the fixation is
conventional in the explanatory sense at issue, remains the discriminating
question.

Target F1 `c425f0c5-6c3f-5115-ba04-3e61bd049e3b` (case-predicate
noncontradiction), not a wholesale endorsement of classical logic; F6
`f56b2ee7-c69e-5e3b-85b0-e671d907ba58` (thin existential epistemic
reason), not categorical obligation. The [plural closure
certificate](plural-closure-boundary-1084.md) supplies the actual
incomparable relations and omission controls; the authority bridge in
#932 is open. Next test: hold content and admissible valuations fixed
while varying permitted symbolic operations, then compare primitive
rule grasp, implicit definition, indexed closure and adoption authority
on the same task.


## Fixed-content application test: specification is not execution or soundness

Use the existing result `CORRECTION-CRITERION-EXACT-FACTORIZATION`
(`0590fe21-edb9-5915-9837-62560c8f40e2`),
`TruthCore.Results.Logic.CorrectionCriterion.characterization` and
[its note](wittgenstein-criterion-and-correctness.md#the-analytical-result).
For supplied data projection o and correctness predicate K, a classifier
of K using only o exists iff K is constant on each fiber of o. Apply this
only to **incomplete convention data**: the same assent token, or the
same finite training trace, can coexist with correct and incorrect
applications of the specified rule. For example two maps on inputs 0,1,
f=(0,1), h=(0,0), agree at the observed input 0, disagree at 1. Fix f
as the specified table. On the application at 1, the output 1 is correct
and 0 incorrect, while the data consisting only of assent and the old
trace agree. This is a structural two-state witness for the factorization
criterion, not a model of complete social practice or facts about meaning.
Restoring the specified table and actual input/output to o restores
an exact classifier (table equality). Thus the result does **not**
establish that a complete interpreted convention cannot determine correct
instances. It establishes the insufficiency of the specified coarse
data. It also does not give the agent knowledge of the classifier.

Fix p and q as determinate Boolean propositions, implication as material
implication (not a fresh symbol with unspecified meaning). Compare two
stipulated calculi: C permits modus ponens, C+ additionally permits
affirming the consequent. In both, the move p,p→q ⊢ q is a permitted
instance of modus ponens. In C the move q,p→q ⊢ p is not that instance;
in C+ it is a correctly instantiated permitted schema. Under p=F,q=T
both premises of the second move are true and its conclusion false.
Modus ponens has no such valuation. The same action can be a correct
application of an unsound rule and a mistake if presented as an
application of a different rule. Changing the rule is not correcting a
misapplication of the old rule. No empirical assumption about how agents
recognize p or q is part of the valuation test.

More formally, write A for adoption of a syntax relation R, Perm_R(s)
for a permitted step, Apply_R(s) for the actual step being an instance
of that rule under the supplied matching conditions, and Sound_M(R)
for universal truth preservation over supplied models M. These are
analyst shorthands, not new corpus sense declarations. The rival
`A(R) → Sound_M(R)` with unchanged M and arbitrary R has a counterexample
by taking R to include affirming the consequent. The rival
`A(R) → every attempted application is an instance` with unchanged R
has a counterexample in C. These conclusions need the actual attempted
step in their scope; adopting a fully specified R can indeed determine
which steps are instances. They do not test the substantially stronger
practice account that includes rule content, public correction,
counterfactual usage and criterion-governed execution in what a
convention consists in.

## Implicit definition: give the stronger account its own test

Grant that a stipulation can constitute a new connective's meaning or
a calculus's derivability relation, not merely attach a label to a
previously existing object. No independently established prior meaning
for a fresh connective is required. The conventionalist can demand
existence of an interpretation, coherence of the rules, and conservativity
on old content (where the point is a definitional extension). But the
strong **unrestricted** version allowing arbitrary introductions and
eliminations to be jointly truth-preserving fails even for one valuation.

Take old p,q with p=T,q=F allowed. Introduce a fresh binary connective ⋆
by the two rules p ⊢ p⋆q and p⋆q ⊢ q, allowing composition. For soundness
of the first at this valuation p⋆q must be true; for soundness of the
second it must not be true. No choice of its truth value suffices.
Syntactically both steps are perfectly licit, and p ⊢ q follows without
any ⋆ in the endpoints, violating conservativity over the fixed old
Boolean consequence. No appeal to a further philosophical norm or an
empirical claim is needed for this **conditional** obstruction.

Deletion/repair controls: if the elimination rule is dropped, projection
onto p gives a sound introduction; if the introduction is dropped,
projection onto q gives a sound elimination. If the p=T,q=F case is
removed, projection onto p makes both sound on the remaining models.
That last repair changes the admissible old cases; it is not a harmless
implicit definition on the original interpretation. A noncompositional
practice or a connective whose validity relation is defined solely
syntactically can also adopt both as permissions; it owes no Boolean
soundness unless it claims it. The test distinguishes an actual
constraint on truth-preserving extension from an intrinsic ban on
stipulation.

A coherent implicit definition can survive: introduction of ∧ by
p,q ⊢ p∧q and eliminations p∧q ⊢ p and p∧q ⊢ q uniquely determine
its Boolean truth table given old truth and designation. The first
forces true at (T,T); the eliminations force false at (T,F),(F,T),(F,F).
Once the admissible cases, designation, and requirement of preservation
are fixed, these are consequences of the stipulation, not further
votes. The constitutive account can accept those constraints as
internal to the framework. It has not established that adoption
creates truth in the already-fixed subject matter, nor that the
metastandard is convention-independent in its metaphysical ground.
The ordinary use of consistency, preservation or conservativity to
admit implicit definitions is the live choice-of-standard issue, not
a proof that all such definitions are circular.

## Pluralism: exact reuse, not a collapse of meaning or authority

Use `PLURAL-CLOSURE-BOUNDARY`
(`9e982ff3-03c5-571c-b16f-8b9c183f14c7`),
`TruthCore.Results.Logic.PluralClosureBoundary.checks` from #1084/#1086.
Its fixed syntax and truth/falsity-bit connective algebra has designation
by truth bit. K3 forbids atomic Both, LP forbids atomic Neither. These
relations share tables and designation; their admissible valuation sets
differ. If a richer notion of meaning includes the whole admissible-case
space, they do not thereby have identical meanings in that richer sense.

Let g=p∨(q∧¬q), e=q∨¬q, C=p∧e. K3 gives g⊢p; LP gives ∅⊢e;
both give conjunction introduction. Neither gives g⊢C:
K3 p=T,q=Neither gives g=T,C=Neither; LP p=F,q=Both gives
g=Both,C=F. These are the original countervaluations. One pool containing
g closed under both contains C by the original joint theorem, not by
identifying either consequence relation. K3's own theory of g and LP's
own theory of g reject C while satisfying their own closures, and remain
a survivor when separately indexed. Classical p=F,q=F supplies a both-
closed pool with neither g nor C (deletion of initial acceptance);
classical p=T,q=F supplies a both-closed pool with g,C but not ¬p.
Use the actual closed-theory witnesses, not raw valuations as substitutes
for closure. The latter are only the individual semantic failure witnesses.

If the full interpretation M, admitted valuations, preservation test,
premises and conclusion are identical, semantic consequence is one
extensional relation; an affirmative and a negative verdict on the same
tuple cannot both be correct **on that definition**. Different syntactic
calculi may still differ in strength while both sound (one incomplete).
To claim a conflict of sound and complete calculi for one fixed M
would require opposite verdicts of that same relation. Different
consequence relations may both be legitimate if the case space,
preserved property, task or framework is indexed. Thus the #1084
countermodels test a common unindexed closure policy, not the unique
correct logic, and do not force pluralists to relinquish fixed
connective tables, conditional validity or primitive reasoning.

### Supplemental finite check (executed, not Lean verification)

The following enumerates the new Boolean obstruction, its deletion
controls, the complete conjunction table, coarse trace ambiguity and
the original two #1084 countervaluations. The closure certificates remain
the prior Lean results; this command does not prove them again.
The complete displayed finite enumeration passed locally.

```sh
python3 - <<'PY'
from itertools import product
V = list(product((False, True), repeat=2))
imp = lambda p, q: not p or q
assert not [(p,q) for p,q in V if p and imp(p,q) and not q]
assert [(p,q) for p,q in V if q and imp(p,q) and not p] == [(False,True)]
assert not any(t and not t for t in (False,True))
assert all(not p or p for p,q in V)  # introduction, project p
assert all(not q or q for p,q in V)  # elimination, project q
assert all(not p or q for p,q in V if (p,q)!=(True,False))
for p,q in V:
    allowed = [t for t in (False,True)
               if (not (p and q) or t) and (not t or p) and (not t or q)]
    assert allowed == [p and q]
f,h = (False,True),(False,False)
assert f[0] == h[0] and f[1] != h[1]
T,F,N,B = (True,False),(False,True),(False,False),(True,True)
neg = lambda a: (a[1],a[0])
conj = lambda a,b: (a[0] and b[0],a[1] or b[1])
disj = lambda a,b: (a[0] or b[0],a[1] and b[1])
for p,q,eg,ec in [(T,N,T,N),(F,B,B,F)]:
    g,e = disj(p,conj(q,neg(q))),disj(q,neg(q))
    assert g == eg and conj(p,e) == ec and g[0] and not conj(p,e)[0]
assert all(not disj(p,conj(q,neg(q)))[0] or p[0]
           for p,q in product((T,F,N),repeat=2))
assert all(disj(q,neg(q))[0] for q in (T,F,B))
print("finite convention witnesses passed")
PY
```


## Regress of justification is a separate thesis

Determination says which application accords with a rule; justification
says why adoption, retention or use of a rule is epistemically warranted.
The two can come apart: a truth table can specify a perfectly determinate
but unsound calculus, and an agent can competently apply a rule without
having a further verbal reason for adopting it. The earlier regress
theorem's two omission controls are exact: `needsOnlyThroughInterpretation`
uses Unit, empty I, D always true; `needsNoEndless` uses Nat,
I(i,a) iff i=a+1, D always true. They preserve determination while dropping
one of the two named premises. Neither supplies a philosophical account of
how D is fixed. No contradiction follows from a merely circular pattern of
adoptions or a chain that has been stipulated to be determinate.

For the justification reading reuse `REGRESS-SCHEMA-PACKAGE`
(`74e00870-e0d4-5467-8c09-a75b2a922ce5`) and
`TruthCore.Results.Logic.RegressSchema.justificationTransfer`.
On the distinct `Justification` adapter, if every rule has a nonempty
premise set and c has inductively `GeneratedWarrant`, there is a finite
dependency path from c to a noninferential foundation. Every premise
of a used rule must have generated warrant; the existence of **one**
path is necessary, not sufficient (the all-premise control has Boolean
claims, one rule with both true and false as premises and false as
conclusion, only true as foundation; a path to true does not warrant
false). For the source-free successor model, the rule for n has sole
premise n+1, and there is no noninferential foundation. No n has
generated warrant; the graph transmission with intrinsic=False can
nevertheless have every node in its greatest fixed point. The package
does not identify stipulated all-on membership with warrant.

Apply only conditionally: a convention's justificatory claim is c; a
rule expressing its dependence on further conventions has its actual
necessary justificatory inputs as premises. The nonempty-premise
condition and the use of inductively generated all-premise warrant are
additional commitments; circular support is not a proof in that model.
This adaptation needs a substantive bridge from the rival's alleged
justification to `GeneratedWarrant`. It is **not** an assertion that
actual rational justification must be finitely generated. An infinitist
can deny that bridge, a coherentist can deny that warrant is merely
transmitted along the edges and supply holistic evidence, and an
externalist can supply a genuinely warrant-conferring formation without
a further accessible convention. See
[externalist entitlement](externalist-entitlement-and-regress.md).
The price of a source-free infinitist account is a positive noninductive
entitlement criterion; its all-on graph alone is no such criterion.
Conversely, a convention-independent foundation is not entailed by the
existence of an inductive foundation: it might be a primitive constitutive
practice if the practice genuinely confers the relevant status.

### Primitive grasp and the actual transition

The strongest noninterpretive account need not represent each use of
a rule by an additional proposition. Compare the already investigated
[actual basing account](epistemic-underminer-boundaries.md#rational-basing-the-particular-transition-must-exercise-the-capacity).
A person accepts p and p→q, understands their contents, and actively
draws q on that basis. Another accepts those contents and produces the
same q because a cue already fixed the output before checking the
premises. Same accepted rules, premises and final sentence; only the
first transition is stipulated to exercise the relevant inferential
capacity. The second might still have an independent reason for q;
the countercase concerns warrant from **this** inferential transition.
An account of norm-guided practice can explain this difference by
counterfactual correction and exercise of a learned capacity. A
mechanical syntax checker can also implement a fully specified matching
relation without an endless sequence of other checkers. Neither case
settles whether correctness is grounded in social practice, the
content relation, a primitive rational capacity or a combination.

A token assent that the rule is in force is therefore not an explanation
of whether or why it was correctly applied. A rich constitutive account
that makes the relevant capacity and its standards primitive survives
the interpretation regress by denying the iteration premise. It still
has to distinguish being corrected from a change in what counts as
correct, e.g. a mistaken antecedent match versus revising the rule
so that affirming the consequent is permitted. This is not an objection
requiring the agent to formulate another rule to grasp the first one;
it asks for the ground of the distinction the constitutive account
itself makes. A noninterpretive grasp can be convention-trained or
socially realized. Treating it as primitive does not prove that its
status is nonconventional in origin.

## Rational choice and the conventionalist's own authority

Use one task: preserve truth of the same old propositions, given fixed
Boolean content and admissible valuations. Under this task the MP and AC
rules above have unequal merits: at p=F,q=T, AC permits a true-to-false
transition, MP never does. Hence any selection criterion requiring
truth preservation of every permitted move rejects C+ under these
inputs. It need not choose a unique calculus (a weaker sound calculus
could also satisfy the criterion). Choosing notation for efficiency,
a local derivability relation for a formal exercise, or a model class for
a specific domain has a different goal; those choices need not be judged
by the identical task. An instrumentalist can explain the selection:
given the common accuracy aim, pick a preserving calculus; where goals
differ, compare consequences but withhold categorical authority. This
is a reasoned choice relative to an end rather than arbitrary fiat.

The question recurs for the choice of the standard. Justifying an
accuracy constraint by a further convention can explain its local
acceptance or conditional policy consequence. It cannot establish
that arbitrary replacement standards preserve the same old contents.
If a meta-convention is accepted by both communities, the local
argument may speak to both even if their object calculi differ.
A defender can also merely describe which communities adopt what
standards, without claiming that dissent is irrational. Neither
account claims universal reasons for adoption.

For a bounded self-application control let A accept a standard S and B
not accept S. Fix the thesis t (the same content about conventions).
The **local-only** thesis gives a necessary condition for even a pro tanto S-based epistemic reason: `SBasedReason(B,t) → Accepts(B,S)`. A weaker thesis restricting only sufficient warrant permits a nonadopter to have some S-based evidence for t while reasonably suspending judgment. Let the
conventionalist's offered argument be S-based and let B reject S.
Then the claim that this S-based argument supplies B an epistemic
reason to believe t is incompatible with the local-only claim for B.
The no-transfer model sets S-based reason true for A and false for B;
it leaves t's truth unconstrained. Restoring B's acceptance removes
this obstacle; a reason independent of S is a different route not
denied by a restriction of S-based reasons alone. If t instead says
**all** epistemic reasons derive solely from standards their recipients
accept, then claiming any reason for B with no accepted supporting
standard contradicts t, provided the same reason predicate, audience,
content and scope are retained. Mere assertion to B is not the
concession of a reason for B. The descriptive truth of t, locally
reasoned belief in t, practical persuasion, framework-independent
validity and binding force for a dissenter are different properties.
This is a scope incompatibility, not a proof of t's falsity.

The stronger assumption that an argument rationally compels every
competent dissenter irrespective of adoption supplies exactly the
cross-framework bridge at issue. Its truth-directed warrant is not
shown by recording that the audience accepts S. The alternative of
shared factual accuracy can discriminate C from C+ in the example even
without both audiences endorsing accuracy as their goal; whether that
gives B a reason to adopt C is a further normative question. This is
the #932 authority gap, not a global truth retorsion.

Reuse `TruthCore.Results.Logic.EpistemicAuthority.authorityFromAnswerability`:
`ActualForceConcession f` + `BeliefAnswerability f` yield
`SomePreferenceIndependentReason f`. The first requires an ordinary
belief reason with force at the subject's actual preference; the second
requires invariance of force under all supplied preferences with
subject, consideration and content fixed. The goal-relative account
with `IndifferenceAvailable` gives the opposite conclusion by
`goalRelativeExcludesAuthority`; `authorityRivalBundleInconsistent`
checks all four inputs cannot coexist. The goal-relative control has
F6, consideration presentation, ordinary definition and an actual
force concession but not answerability or the stronger existential.
`indifferentAgent` preserves thin reasons without actual force;
`forceless` preserves answerability without actual force. Restricting
the comparison class by `ConstitutiveAim` can yield independence on
that class; it does not give an indifferent subject a reason.
See [#930 authority](epistemic-authority.md#formal-structure-and-registration-boundary);
direct graph registrations of the two target-concluding lemmas are
deferred there. Do not identify preference independence with
framework independence: a person could hold preferences fixed and
change logical conventions. The extra transfer from one standard to
an unaccepting audience is still open, not proved by these controls.

## Proposed overall assessment and revision conditions (unreviewed)

Separate two meanings of "nonconventional": (i) not fixed by the
particular act of assent, current consensus, or permission choice
under investigation; (ii) not ultimately constituted by any
convention or practice whatsoever. There is substantial positive
warrant for (i) in ordinary truth-directed inquiry: participants
can identify a mistake while retaining the rule, and fixed-content
countervaluations constrain which rules preserve truth without a new
decision each time. The common ability to distinguish the very same
premise from a substitute, to recognize an instance, and to
distinguish preservation from permission makes the comparison
possible. The strong conclusion (ii) requires a further theory of
the grounding of semantic content, correct recognition and authority.
Analytic or conditional standards need not have metaphysically
nonconventional origins. Both realist and sophisticated constitutive
accounts explain why one move can be wrong without a fresh vote;
the finite controls alone do not discriminate those accounts.

| Version (analyst scope, not an exhaustive taxonomy) | Disposition and exact cost |
| --- | --- |
| Notational convention | Survives; shared translations can preserve content and consequence. |
| Meaning-constituting convention / constrained implicit definition | Survives where the stipulation fixes content and meets claimed interpretation constraints. No arbitrary preservation guarantee; two-rule obstruction requires old cases, both rules, composability for conservativity. |
| Conventional syntactic validity / complete stipulated rule matching | Survives; derivability or instancehood relative to adopted rules, not semantic soundness or skill in applying them. |
| All adoption is sufficient for actual correct application | Fails for bare assent with fixed rule and an actual misapplication. A rich practice supplying the entire rule and token correctness criterion is a different, surviving thesis. |
| Every determined application requires another determined conventional interpretation, with well-founded dependence | Incompatible with the determination existential by existing regressFork; rejecting either condition survives. |
| All justification supplied by further conventions | A source-free chain fails under generated all-premise warrant; infinitist, coherentist, externalist and primitive entitlement accounts survive if they supply the specified positive conferrer. |
| Arbitrary permitted rules preserve fixed old truth | Countervaluation under Boolean semantics; definition cannot rescue it without changing the claimed soundness, old meaning or case space. |
| Framework-relative semantic validity / logical pluralism | Survives indexed cases and pools; not two incompatible verdicts of an identical full consequence relation. Common-pool joint closure adds C under the exact #1084 bundle. |
| Primitive socially constituted rule grasp and correction | Serious surviving global grounding proposal. Can distinguish error within a practice and not require further interpretations. Its adequacy for determinate truth-directed content and its normative ground remain open. |
| Local/goal-relative adoption authority | Survives; can grant thin F6 and actual reasons among aiming subjects while withholding authority for nonadopters. |
| Universal rational authority solely from recipient-local acceptance | Incompatible when it grants an S-based pro tanto reason for t to an actual B who rejects S while requiring acceptance of S for that very reason. A shared meta-standard or independent reason is a different, potentially surviving account. Reasonless descriptive truth is not refuted. |

Proposed assessment: a purely arbitrary adoption-sufficiency account
does not explain truth-directed logical correctness in the fixed
cases. The best conventionalist reply is not arbitrary adoption but
meaning-constituting, norm-governed practice with primitive grasp and
framework-indexed consequence and reason. It can survive the precise
countermodels and need not deny F1 or F6. It must preserve substantive
rational distinctions, not derive all of them from a succession of
bare choices. Calling those distinctions nonconventional in sense
(i) is warranted in the selected task. Calling them nonconventional
in sense (ii) is not yet a demonstrated consequence. The remaining
competition is between a truth-/content-grounded standard and an
account where sufficiently rich practice constitutes the standard
itself; test the latter's ability to explain publicly corrected error
under unchanged meanings and a counterfactual community-wide error
without silently redefining the intended contents. A realist has the
parallel burden of explaining access to and exercise of its standard,
not just naming it. A practice account with no full content assignment
cannot be compared as if it preserves the complete assignment.

F1 is exactly
`TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction`:
for all beings, respects, predicates P, x, r, not (P x r and not P x r)
inside Lean. Reuse `LOGIC-CASE-NON-CONTRADICTION-NOT-DENIABLE`
(`a7ecf1fe-a234-5de6-bb72-bf76309c5ea3`), theorem
`TruthCore.Results.Logic.CaseNonContradiction.noCasePredicateContradiction`.
Both the proof and the ordinary application comparison require
determinate distinctions; the latter does not establish this
universal F1 interpretation, excluded middle, or classical logic.
LP's object-language Both is not Lean's P∧¬P. The bridge from the
thin distinction needed for this task to all same-respect case
predicates in reality is not furnished by a Boolean countervaluation.

F6 is exactly `ThereAreEpistemicReasons Reason := ∃ a p, Reason a p`.
An ordinary aim-relative reason can be a witness; no categorical
obligation is required. The accepted F6 does not assert that this
conventionalist, this reason or this content instantiates it.
`EPISTEMIC-NIHILISM-SELF-UNDERMINING`
(`ec80b13d-0c87-5f71-bc70-16b42dc4c0e6`),
`TruthCore.Results.Logic.EpistemicNihilismRetorsion.nihilismSelfUndermining`,
`reasonedBeliefRefutesNihilism` and
`nihilismConsistentAndUnbelievable` separate self-undermining and
falsity. The last model has one agent and content, empty Reason,
nihilism true. A conventionalist who grants actual local epistemic
reasons does not deny F6 at all. If a variant denies every actual
epistemic reason, reuse that scope test; do not infer a reason from
mere performance. For the shared #1989 witness
`TruthCore.Results.Logic.TruthPilot.NotEveryPropositionFails.notEveryPropositionFails`,
the proof extracts a holding proposition P from the existing
`somePropositionHolds` witness, instantiates universal failure at P,
and applies the resulting negation to its witness. The invalid
replacement instantiates at False and supplies no witness of False.
The successful transition versus the attempted replacement is
assessable in the fixed encoded logic; authority outside that logic,
an actual subject's understanding and warrant require their own
bridges. No inference to categorical authority, immaterial intellect, God
or a root premise discharge is delivered.

## Reproduction and handoff

Full supplemental finite command above executed and returned
`finite convention witnesses passed`. No new Lean module, result,
definition, argument, source or relation is registered; the computed root premise comparison against the integration base reports no change.
The exact old theorem types and existing countermodels are cited
rather than repeated as new certificates. No new source reading is
asserted. This draft's prose/type self-sweep checks fixed vs changed
model class, preservation vs permission, determination vs generated
warrant, local vs preference-independent vs categorical reason and
each reuse boundary. The attempt records the independent review and the scope of its dissenter correction.
The new finite examples are checked only by the displayed exhaustive
Python enumeration; they are not bound corpus results or certified
interpretation profiles.

The first connector session supplied the finite diagnostic. The integration checkout reproduced it, checked the existing endpoints and validated the corpus record. The live question for #932 is whether a specific practice can explain corrected error with its meaning fixed and give a dissenter reason for the same task. #1084 supplies the checked common-closure theorem.
