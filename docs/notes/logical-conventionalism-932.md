# Logical conventionalism: correctness, application and authority (#1989 / #932 / #1084)

Draft analyst investigation, attribution deferred. Baseline main
`a9819b148bd4a7c089cff9dc07f95c209452511e`; intake #1989 head
`eeb7e0e7225dd0dc37c851effa53467a62b0b6fe`. This branch is independent of
the intake edit: the question is taken from it, not a dependency on its
unmerged text. No new graph edge, floor or proof status is claimed.
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
The initial finite enumeration (MP/AC, two-rule incompatibility,
trace and matrix countervaluations) passed locally; see final checkpoint
for extended verification.

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
